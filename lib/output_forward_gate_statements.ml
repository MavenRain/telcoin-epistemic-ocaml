(** The OUTPUT_FORWARD_GATE statement family, encoded over the
    {!Output_forward_gate_model} interpreted system. All three statements were
    mined from telcoin-network and re-grounded line by line against this
    checkout (git HEAD [0c59c15b], working tree). File citations refer to
    Telcoin-Association/telcoin-network.

    What the family is about: every committed consensus output reaches the EVM
    through exactly one seam - the epoch manager's live-forwarding loop
    (run_epoch.rs:561-619) feeding the engine's bounded FIFO backlog
    (engine/lib.rs:120-124, :227-252). Three properties of that seam are stated
    here, and they are the three arms of one question: is the executed chain the
    consensus chain, once, in order, with nothing missing?

    - S1 is the [Stale] arm (run_epoch.rs:575-583): nothing executes twice.
    - S2 is the [Gap] arm (run_epoch.rs:584-591): nothing committed is skipped.
    - S3 is [pop_front] (engine/lib.rs:124): nothing is overtaken, which is what
      makes the manager's single execution receipt certify the whole prefix.

    Reading guide for the K operands:
    - [K (V2, _)] in S1 conjunct C is the ENGINE's knowledge. Its entire state is
      [queued] plus [parent_header] (engine/lib.rs:49-80), so [stale_skipped] -
      a fact about the FORWARDER, namely that it dropped a re-delivery - is not
      in its view and cannot be inferred from it. This conjunct is the R4 sibling
      hunt turned into a theorem: the reason no downstream path repairs the
      deleted [Stale] arm is precisely that the engine cannot see what the arm
      does.
    - [K (V1, executed_1)] in S3 conjunct B is the FORWARDER's knowledge, and it
      is the inference run_epoch.rs:232-238 actually makes: having replayed
      several outputs, the manager waits on
      [wait_for_consensus_execution(last_hash)] for the LAST one only and
      concludes the earlier ones executed too. [executed_1] is a fact about the
      engine's private history: V1's view carries only the LAST update it
      consumed (see the modeling admission in {!Output_forward_gate_model}), so
      the knowledge is carried by the engine's FIFO discipline and not by V1's
      own observation - which is exactly why {!Output_forward_gate_model.Queue_pop_back}
      destroys it.
    - [rebroadcast_unread] is the hidden environment fact: a copy of an
      already-forwarded output sitting unread in the 100-slot broadcast ring
      (consensus_bus.rs:317), left there by the previous epoch's shutdown drain
      (subscriber.rs:394-403). It is in nobody's view and it is what keeps the
      forwarder's view classes non-singleton at the operative states of S3. *)

open Output_forward_gate_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a situation that never arises *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** [A\[p W q\]] via the kernel identity [~E\[~q U (~p /\\ ~q)\]]: weak until is
    not a constructor. *)
let weak_until p q =
  Formula.Not
    (Formula.Eu
       (Formula.Not q, Formula.And (Formula.Not p, Formula.Not q)))

(** S1 - live-forwarder-skips-stale-redelivery-so-no-output-executes-twice
    [safety]. The same consensus output legitimately reaches this node's
    forwarder more than once - the previous epoch's subscriber re-broadcasts
    saved outputs best-effort while shutting down (subscriber.rs:394-403) and
    the state-sync path re-broadcasts every reconstructed output
    (subscriber.rs:154-180). The statement is that the live path recognises the
    duplicate and drops it, so nothing is executed - or leader-counted - twice.

    (A) no stale forward: AG( ~stale_forwarded ). [check_output_continuity]
    returns [Stale] for [number <= last_forwarded] (run_epoch.rs:883-885) and
    the [Stale] arm warns and [continue]s without calling [process_output]
    (run_epoch.rs:575-583). The watermark it compares against is what actually
    reached the engine, because it is assigned only after the send succeeds
    ([to_engine.send(output).await?; self.last_forwarded_consensus_number = ..],
    run_epoch.rs:548-550, doc :527-529).

    (B) no double execution: AG( ~double_executed ). This is why (A) matters:
    execution is not idempotent. [execute_consensus_output] increments the
    leader's reward count once per delivered output, unconditionally and before
    any other work (payload_builder.rs:30), and even the empty-output early
    return keeps that increment (payload_builder.rs:84-97, doc :20-21) - so a
    second delivery double-counts on every output shape, empty or not.

    (C) the engine cannot see the de-duplication:
    AG( stale_skipped -> ~K_V2(stale_skipped) ). The engine's whole state is
    [queued] plus [parent_header] (engine/lib.rs:49-80); the skip happened
    upstream and left no trace it can read. R3 ignorance witness, both members
    reachable: any state in which the forwarder has skipped the re-delivery, and
    the state with the identical backlog and [parent_header] in the world where
    no re-broadcast was ever buffered ([rebroadcast = Absent]). Since the
    re-broadcast never touches the engine, the two are [View_engine]-identical
    and disagree on [stale_skipped]. This conjunct is the formal statement of
    the sibling hunt: the de-duplication is invisible downstream, so it cannot be
    repaired downstream.

    Mutation pin: {!Output_forward_gate_model.No_stale_arm} deletes
    run_epoch.rs:575-583, so the delivery falls through to [process_output],
    which queues the number a second time and assigns the watermark backwards
    (run_epoch.rs:550). (A) and (B) both fail. No sibling repairs it - the engine
    keeps no set of executed numbers and makes no number or hash comparison
    (engine/lib.rs:49-80, :227-252), [execute_consensus_output] compares only
    batch and digest counts (payload_builder.rs:51-76),
    [heal_finalized_to_persisted_tip] explicitly never moves the execution tip
    (tn-reth/lib.rs:872-875), and [replay_missed_consensus] is deliberately not
    continuity-checked (run_epoch.rs:878-882) so it is not a backstop. NOT
    pinned to the other two mutations: neither creates a second delivery of one
    number, and the mutation suite tests that S1 survives both. *)
let s1 =
  let no_stale_forward = Formula.Ag (Formula.Not (atom Stale_forwarded)) in
  let no_double_execution = Formula.Ag (Formula.Not (atom Double_executed)) in
  let dedup_invisible_to_engine =
    Formula.Ag
      (Formula.Implies
         ( atom Stale_skipped,
           Formula.Not (Formula.K (Validator.V2, atom Stale_skipped)) ))
  in
  {
    name = "live-forwarder-skips-stale-redelivery-so-no-output-executes-twice";
    bucket = Statements.Safety;
    formula =
      Formula.And
        (no_stale_forward, Formula.And (no_double_execution, dedup_invisible_to_engine));
    antecedent = atom Rebroadcast_handed;
  }

(** S2 - lagged-output-gap-halts-the-epoch-instead-of-executing-a-hole
    [safety]. The consensus_output channel is a tokio broadcast whose sender
    never blocks and never reports a drop ([let _ = self.send(value); Ok(())],
    sync.rs:172-188) and whose receiver, on overflow, logs and resumes at a
    later message ([Err(Lagged(n)) => { warn!(..); continue; }],
    sync.rs:205-217). The loss is therefore silent by construction: a forwarder
    that falls behind is handed a well-formed later output and nothing else. The
    statement is that this is caught rather than executed.

    (A) the gap is never quietly disposed of:
    AG( gap_pending -> A[gap_pending W epoch_errored] ), the kernel's weak-until
    [~E[~q U (~p /\\ ~q)]]. Once a delivery above [w + 1] is in hand, the only
    judgement the gate can make is [Gap] (run_epoch.rs:888-889), whose arm
    returns [Err("consensus output gap: expected {} but received {} - restarting
    to replay missed consensus from the DB")] (run_epoch.rs:584-591); that error
    leaves [run_epoch] at the [?] on run_epoch.rs:352-354, before [close_epoch]
    and before the leftover drain, and the epoch loop aborts on it
    (node.rs:1225-1227), ending the node. So the delivery either sits in hand or
    is answered by the error - nothing else consumes it.

    The WEAK until is deliberate and is the R5 admission behind this conjunct.
    The strong form [AF epoch_errored] would also prove on this model, but only
    because the model omits the race at run_epoch.rs:344-392: the [tokio::select!]
    there runs [wait_for_epoch_boundary] against node shutdown and the epoch task
    manager exiting, either of which can drop the future with the gap delivery
    still unjudged. The weak-until is what survives that race. That branch cannot
    smuggle the gap through either: the received message is gone with the dropped
    future, and phase 2 of the leftover drain forwards exactly
    [(last_sent + 1)..=latest_db] (close_epoch.rs:137-159), which is contiguous
    by construction, so conjuncts (B) and (C) hold in the preempted branch too.

    (B) no gap forward: AG( ~gap_forwarded ). The gap number never reaches
    [process_output].

    (C) no execution hole: AG( ~exec_hole ) - the executed chain never skips a
    consensus number that is already written in stone in the consensus chain
    (every output is saved before it is broadcast, subscriber.rs:286) and is not
    merely waiting in the engine's backlog. This is the safety content: erroring
    keeps execution a prefix of consensus, which is what makes the restart's
    DB replay sound.

    Mutation pin: {!Output_forward_gate_model.No_gap_arm} deletes
    run_epoch.rs:584-591 and treats [Gap] as [Next]. The lagged number is
    forwarded and executed while the committed number below it was never
    forwarded at all: (A) fails because the delivery leaves the forwarder's hand
    without the epoch erroring, (B) and (C) fail outright.
    No sibling notices - [output.parent_hash()] occurs exactly once in the whole
    engine and reth layer, as a tracing span field (payload_builder.rs:41), and
    the engine extends [parent_header] from whatever it pops
    (engine/lib.rs:227-230, :262-268), so nothing ever compares an output's
    consensus linkage against the last executed one. The CVV-side
    [wait_for_execution(base_execution_block)] (consensus/state.rs:421-422) runs
    in the consensus task and gates the NEXT commit, so it can only fire after
    the hole is already executed. NOT pinned to the other two mutations: the
    mutation suite tests that S2 survives both. *)
let s2 =
  let gap_never_quietly_dropped =
    Formula.Ag
      (Formula.Implies
         ( atom Gap_pending,
           weak_until (atom Gap_pending) (atom Epoch_errored) ))
  in
  let no_gap_forward = Formula.Ag (Formula.Not (atom Gap_forwarded)) in
  let no_execution_hole = Formula.Ag (Formula.Not (atom Exec_hole)) in
  {
    name = "lagged-output-gap-halts-the-epoch-instead-of-executing-a-hole";
    bucket = Statements.Safety;
    formula =
      Formula.And
        ( gap_never_quietly_dropped,
          Formula.And (no_gap_forward, no_execution_hole) );
    antecedent = atom Gap_pending;
  }

(** S3 - committed-outputs-execute-in-order-so-one-receipt-certifies-the-prefix
    [fairness]. The engine serves its backlog strictly in commit order, and the
    epoch manager's knowledge rests on that discipline.

    (A) no overtaking: AG( ~exec_out_of_order ). The backlog is a [VecDeque]
    pushed at the back on arrival ([self.queued.push_back(output)],
    engine/lib.rs:249) and popped at the FRONT for execution
    ([self.queued.pop_front()], engine/lib.rs:124), with at most one execution
    in flight because [pending_task] is a single [Option] and the next is
    spawned only when it is [None] (engine/lib.rs:227-230, and the comment there:
    "it's important that the previous consensus output finishes executing before
    inserting the next task"). The fairness content is that the queue is bounded
    ([MAX_QUEUED_OUTPUTS = 8], engine/lib.rs:31-38) and reward-bearing: each
    executed output increments its leader's reward count
    (payload_builder.rs:30). Under saturation, FIFO is the only thing that stops
    an already-committed round's author from being served behind arbitrarily
    many later ones.

    (B) one receipt certifies the whole forwarded prefix:
    AG( receipt_2 -> K_V1( forwarded_1 -> executed_1 ) ). This is the inference
    the epoch manager actually makes: after replaying several outputs it waits on
    [wait_for_consensus_execution(last_hash)] for the LAST one only -
    "Only wait for consensus that was actually forwarded to the engine"
    (run_epoch.rs:232-238) - and proceeds as though the earlier ones executed.
    The knowledge is not V1's own observation: its view carries only the last
    execution update it consumed, never the executed set. It is carried by the
    engine's FIFO discipline, one hop away and invisible to it. The operand is
    an implication rather than a bare [executed_1] because the claim the code
    relies on is about what the forwarder ITSELF handed over - the scope stated
    at run_epoch.rs:232-233 - and that is also what keeps this conjunct
    attributable to the FIFO gate alone (see the mutation paragraph).

    R2 evidence for (B), both halves discharged in the suite:
    - the operand is not rigid: [EF ~(forwarded_1 -> executed_1)] holds, since an
      output can sit forwarded-but-unexecuted in the engine's backlog;
    - the view class at the operative state is not a singleton:
      [EF( receipt_2 /\\ ~rebroadcast_unread /\\ ~K_V1(~rebroadcast_unread) )]
      holds, which is possible only if a second reachable state shares V1's view
      there - the state in the world where a copy of an already-forwarded output
      IS sitting unread in the broadcast ring, a fact V1 cannot see;
    - and the knowledge is contingent: [EF ~K_V1( forwarded_1 -> executed_1 )].

    Mutation pin: {!Output_forward_gate_model.Queue_pop_back} replaces
    [pop_front()] with [pop_back()] at engine/lib.rs:124. With both outputs
    queued the engine executes 2 first, so (A) fails outright and (B) fails at
    the state where the manager holds the receipt for 2 while 1 is still queued
    - the inference at run_epoch.rs:232-238 becomes unsound. No sibling
    re-orders it: [execute_consensus_output] makes no number or
    parent-consensus-hash comparison (payload_builder.rs:22-76), the upstream
    mpsc (node.rs:838) is FIFO but only feeds [push_back] and cannot constrain
    what the engine pops, and [check_output_continuity] (run_epoch.rs:574) runs
    BEFORE the send, so it constrains enqueue order only and never observes the
    mutation. Conjunct (B) puts [forwarded_1] inside the K operand precisely so
    that {!Output_forward_gate_model.No_gap_arm} does not refute it: under that
    mutation output 1 is never forwarded at all, so the operand holds vacuously
    in the states the gap adds to V1's class, and the mutation suite asserts that
    S3 does survive it. Stating the operand as a bare [executed_1] would have
    made S3 flip under BOTH gates and cost the attribution. *)
let s3 =
  let no_overtaking = Formula.Ag (Formula.Not (atom Exec_out_of_order)) in
  let receipt_certifies_prefix =
    Formula.Ag
      (Formula.Implies
         ( atom Receipt_2,
           Formula.K
             ( Validator.V1,
               Formula.Implies (atom Forwarded_1, atom Executed_1) ) ))
  in
  {
    name = "committed-outputs-execute-in-order-so-one-receipt-certifies-the-prefix";
    bucket = Statements.Fairness;
    formula = Formula.And (no_overtaking, receipt_certifies_prefix);
    antecedent = atom Receipt_2;
  }

(** The family's statements: the two continuity arms of the forwarder's gate and
    the engine's queue discipline that carries the manager's knowledge. *)
let all = [ s1; s2; s3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure degrades
    every row to [proved = false] rather than raising. *)
let reports () =
  let row proved st = { Report.name = st.name; bucket = st.bucket; proved } in
  Result.fold
    ~ok:(fun sys ->
      List.map
        (fun (st, r) ->
          row (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false) r) st)
        (prove_all sys))
    ~error:(fun Checker.Empty_init -> List.map (row false) all)
    (make ())
