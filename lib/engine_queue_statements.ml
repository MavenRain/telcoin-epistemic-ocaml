(** The engine-slot statement family over the {!Engine_queue_model} interpreted
    system: the tn-engine event loop's bounded backlog and the single execution
    slot in front of the EVM. Mined from telcoin-network, every citation
    re-opened in the working tree of git HEAD 0c59c15b.

    The three statements target three DIFFERENT gates on the same
    (upstream, backlog, slot, tip) pipeline, and each is pinned by the deletion
    of its own gate:
    - S1 the EXCLUSIVITY of the slot ([self.pending_task.is_none() &&],
      engine/lib.rs:227): at most one execution task exists, and it always builds
      on the block that is actually committed;
    - S2 the BOUND on the backlog ([self.queued.len() < MAX_QUEUED_OUTPUTS],
      engine/lib.rs:245): saturation is turned into upstream backpressure rather
      than into unbounded buffering, and the block is temporary;
    - S3 the REMOVAL in the grant ([self.queued.pop_front()],
      engine/lib.rs:124): occupying the slot is a one-shot grant, so nothing
      queued behind an output can be starved by it.

    READING GUIDE FOR THE K OPERANDS.

    This family has NO positive [K]. That is a finding about the mechanism, not
    an omission. Everything the engine loop decides on - [queued.len()],
    [pending_task], [parent_header] - is local: the backlog depth is exported
    only as the Prometheus gauge [ENGINE_METRICS.queued_outputs.set(...)]
    (engine/lib.rs:251, :271) and appears in no header, certificate, vote or
    request/response payload, and slot occupancy is never exported at all. So any
    [K_i(phi)] whose operand is a fact about i's OWN engine would be a projection
    of i's own view - precisely the collapsed [K] that rule R1 rejects - and there
    is no wire channel that would let one node know a fact about another node's
    engine. What the mechanism does support, and what the family therefore
    asserts, are two IGNORANCE claims, each with a concrete reachable witness
    pair (see the [contingency] group of test/t_engine_queue.ml):

    - S2 conjuncts D and E: [~K_V0(peer_at_bound)] and [~K_V0(~peer_at_bound)] at
      a state where V0's own backlog is at the bound. Operand: whether ANOTHER
      node's engine is saturated. It is not in V0's view because it is in no
      message, and the model's [peer] component is resampled on every transition,
      so at every non-initial local configuration both peer values are reachable.
      The two directions together are the claim that a saturated node cannot tell
      a fleet-wide execution stall from its own local one - which matters because
      the two call for opposite responses.
    - S3 conjunct C: [~K_V1(executing)]. Operand: whether V0's execution slot is
      occupied. V1's view here is deliberately the STRONGEST a peer can have in
      the real code - its own backlog occupancy plus V0's last published
      execution tip, the one execution fact that leaves the node (engine update
      at tn-reth/lib.rs:962-973 -> [recent_blocks.push_latest],
      node.rs:1305-1322, recent_blocks.rs:40-60). Even with the tip, a peer
      cannot distinguish "V0 finished output n and is idle" from "V0 finished
      output n and is already executing n+1", because nothing about
      [pending_task] is published. So the one-shot discipline of S3 is enforced
      locally and is unobservable from outside: no peer can police it, which is
      exactly why the removal in [pop_front] has to be the enforcement. *)

open Engine_queue_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - single-execution-slot-chains-each-output-onto-the-committed-head
    [safety].

    (A) exclusivity: AG( ~two_in_flight ). The engine holds at most one in-flight
    execution task. Two things enforce it and the model carries both: the field
    is [pending_task: Option<PendingExecutionTask>], a single [Option] and not a
    collection (engine/lib.rs:52-54), and the grant is guarded by
    [if self.pending_task.is_none() && !self.queued.is_empty()]
    (engine/lib.rs:227-230) whose in-code rationale is stated at :223-226: "only
    insert task if there is none ... it's important that the previous consensus
    output finishes executing before inserting the next task to ensure the parent
    sealed header is finalized".

    (B) chaining: AG( executing -> parent = committed_head ). Whenever a task is
    in flight, the [parent_header] it cloned at spawn (engine/lib.rs:126) is the
    highest block already written to the database (tn-reth/lib.rs:941-944). This
    is the "strict chain" half: output n+1 is built on the header output n
    actually produced. It holds because the ONLY writer of [parent_header] after
    construction is the release arm, [self.pending_task = None;
    self.parent_header = finalized_header] (engine/lib.rs:264-268), and (A) makes
    the release arm run before the next capture.

    Conjunct (B) is stated against the COMMITTED head rather than against
    [parent_header] itself on purpose: [parent = parent_header] is a tautology of
    the spawn code and would be unfalsifiable, whereas "the parent is the block
    that is actually on disk" is exactly what a second concurrent task destroys.
    The model also carries the empty-output path
    ([execute_consensus_output] returns [canonical_header] unchanged when there
    are no batches and the epoch is not closing, payload_builder.rs:84-97), so
    this conjunct deliberately does NOT say the tip strictly advances - it does
    not, and a statement that said so would be false.

    The conjunct is also not quietly assuming that the execution task is the only
    writer of the chain. It is: [save_blocks] occurs exactly once in the whole
    tree (tn-reth/lib.rs:943), inside [finish_executing_output], whose only
    non-test caller is [execute_consensus_output] (payload_builder.rs:189-192) -
    i.e. the body of the blocking task the slot grants. Nothing else can advance
    the committed head while a task is in flight, which is why "parent = the
    committed head" is a statement about the slot and not about the database.

    Mutation pin: {!Engine_queue_model.No_slot_exclusion} deletes the
    [self.pending_task.is_none() &&] conjunct at engine/lib.rs:227. The loop then
    spawns a second blocking task while the first is running; both clone the same
    [self.parent_header] (:126), and the assignment at :229 drops the first
    receiver, so the first task's blocks are committed
    (tn-reth/lib.rs:941-944) while engine/lib.rs:268 never installs its header.
    (A) fails at the two-task state, and (B) fails one step later, at the state
    where the surviving task is still building on the now-superseded parent. No
    sibling path repairs it, and the hunt is recorded on the mutation
    constructor: state lookup by parent hash cannot object to a duplicate
    (tn-reth/lib.rs:736-739), [save_blocks]/[commit] has no contiguity or
    duplicate-height check (:941-944), [push_latest] has no dedup and no
    monotonic round check (recent_blocks.rs:40-60), and the only identity-keyed
    guard is startup-only, its own doc conceding "replaying output the engine
    already applied causes double execution"
    (node/start_epoch.rs:60-64, :71-93). *)
let s1 =
  let exclusive = Formula.Ag (Formula.Not (atom Two_tasks_in_flight)) in
  let chains_onto_head =
    Formula.Ag
      (Formula.Implies (atom Executing, atom Parent_is_committed_head))
  in
  {
    name = "single-execution-slot-chains-each-output-onto-the-committed-head";
    bucket = Statements.Safety;
    formula = Formula.And (exclusive, chains_onto_head);
    antecedent = atom Executing;
  }

(** S2 - engine-backlog-bound-backpressures-upstream-and-reopens [safety].

    (A) the bound holds: AG( ~(|queued| > MAX) ). [MAX_QUEUED_OUTPUTS = 8]
    (engine/lib.rs:31-38); the only writers of [queued] are the [push_back] at
    engine/lib.rs:249, which is reachable only through the gated select arm at
    :245, the [pop_front] at :124 and a [cfg(test)] helper at :179-182.

    (B) saturation becomes backpressure, not buffering:
    AG( (|queued| >= MAX /\\ to_engine_nonempty) -> AX to_engine_nonempty ).
    While the gate at engine/lib.rs:245 is closed the consensus-output arm is
    disabled, so the engine does not touch the channel and the epoch manager's
    awaited [to_engine.send(output).await?] (run_epoch.rs:547-551) stays blocked -
    which is the intended behaviour stated verbatim at engine/lib.rs:34-37 ("the
    engine stops polling the consensus stream, pushing backpressure into the
    [to_engine] channel (and ultimately the EpochManager forwarder) instead of
    buffering here"). The upstream channel is itself bounded at
    [TO_ENGINE_CAPACITY = 64] (node.rs:60-68, :838) whose doc says a deeper
    channel "would defeat the engine's bound by buffering the backlog one hop
    upstream" - so the model carries the upstream channel as a component and this
    conjunct is about the ENGINE not draining it, not about the channel's depth.

    (C) the block is temporary:
    AG( |queued| >= MAX -> AF( |queued| < MAX \\/ engine_stopped ) ). Each
    completion releases the slot (engine/lib.rs:266) and the next loop iteration
    grants it again by removing a head (:227-230, :124), so the gate re-opens on
    every execution; the comment at engine/lib.rs:242-244 makes the same argument
    ("while the backlog is full there is always a pending execution task to wake
    the loop, and each completion re-opens the gate"). This is the conjunct that
    separates a bound from a deadlock.

    The [engine_stopped] disjunct is not a hedge, it is the honest scope. The
    release arm begins [let finalized_header = res.map_err(Into::into)
    .and_then(|res| res)?] (engine/lib.rs:264), so an ordinary execution error -
    [ConsensusOutputUnevenBatches] (payload_builder.rs:57-76), [UnknownAuthority]
    (:104-107), a closed engine-update channel (:92-95) - ends [run], and [run] is
    a critical task whose body is [Ok(res?)] (node/src/engine/inner.rs:75-87), so
    nothing restarts it and the backlog stays where it is forever. Stating the
    bare [AF |queued| < MAX] would have been true only because the model omitted
    that path, which is precisely the defect rule R5 forbids; the model carries
    the path and the conjunct is stated modulo it. The disjunct costs the pin
    nothing: {!Engine_queue_model.Reexecute_head} leaves an all-successful path on
    which the backlog never shortens and the engine never stops, so (C) still
    fails there.

    (D) and (E) the ignorance pair:
    AG( (|queued| >= MAX /\\ peer_at_bound) -> ~K_V0(peer_at_bound) ) and
    AG( (|queued| >= MAX /\\ ~peer_at_bound) -> ~K_V0(~peer_at_bound) ). A
    saturated node cannot tell whether the rest of the fleet is saturated too.
    Backlog depth is local by construction: the only export is the Prometheus
    gauge at engine/lib.rs:251 and :271, and no message type carries it. Both
    directions are asserted because only the pair rules out the degenerate
    reading in which V0 happens to be right; the reachable witness pair is two
    states with identical [View_engine] and opposite [peer], and
    test/t_engine_queue.ml asserts both halves.

    On the view asymmetry these two conjuncts rest on: V1 is handed V0's
    published execution tip but V0 is handed no peer component at all. Enriching
    V0 symmetrically could not create the missing knowledge, and the suite proves
    that rather than asserting it - [published-tip-hides-backlog-depth] shows
    that V1, holding V0's published tip, still cannot tell whether V0's gate is
    shut, because backlog depth is not a function of the tip.

    Behaviour pinned upstream by crates/engine/tests/it/main.rs:222-327
    ([test_queued_outputs_bounded_with_backpressure]), which pre-fills the
    backlog to the bound, asserts [to_engine.capacity() == 0] is unchanged across
    the first poll (:297, :303-307) and then that every output still drains and
    executes exactly once (:315-324).

    Mutation pin: {!Engine_queue_model.No_queue_bound} deletes the
    [self.queued.len() < MAX_QUEUED_OUTPUTS] conjunct from the select arm at
    engine/lib.rs:245. (A) fails as soon as a third output is ingested, and (B)
    fails one step earlier still, at the saturated state from which the engine now
    drains the channel. No sibling path repairs it: [TO_ENGINE_CAPACITY = 64] is a
    supply once the engine stops refusing, not a bound on the [VecDeque], and
    there is no eviction, [truncate] or second capacity check anywhere in
    crates/engine/src/lib.rs. Conjunct (C) also fails under
    {!Engine_queue_model.Reexecute_head} - a backlog whose head is never removed
    never shortens - and the mutation suite asserts that honestly rather than
    claiming S2 is Reexecute_head-insensitive. *)
let s2 =
  let bound_holds = Formula.Ag (Formula.Not (atom Queue_over_bound)) in
  let backpressure =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Queue_gate_closed, atom Upstream_undelivered),
           Formula.Ax (atom Upstream_undelivered) ))
  in
  let gate_reopens =
    Formula.Ag
      (Formula.Implies
         ( atom Queue_gate_closed,
           Formula.Af
             (Formula.Or
                (Formula.Not (atom Queue_gate_closed), atom Engine_stopped)) ))
  in
  let saturation_is_opaque =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Queue_gate_closed, atom Peer_saturated),
           Formula.Not (Formula.K (Validator.V0, atom Peer_saturated)) ))
  in
  let health_is_opaque =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             (atom Queue_gate_closed, Formula.Not (atom Peer_saturated)),
           Formula.Not
             (Formula.K (Validator.V0, Formula.Not (atom Peer_saturated))) ))
  in
  {
    name = "engine-backlog-bound-backpressures-upstream-and-reopens";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [
          bound_holds;
          backpressure;
          gate_reopens;
          saturation_is_opaque;
          health_is_opaque;
        ];
    antecedent =
      Formula.And (atom Queue_gate_closed, atom Upstream_undelivered);
  }

(** S3 - execution-slot-is-a-one-shot-grant-no-output-monopolises-it [fairness].

    (A) no starvation:
    AG( queued(o_B) -> AF( executed(o_B) \\/ engine_stopped ) ). Every queued
    output is eventually served, or the engine died and serves nothing again -
    see S2 conjunct (C) for why the second disjunct is in the statement rather
    than assumed away (engine/lib.rs:264 propagates any execution error out of
    [run], and node/src/engine/inner.rs:75-87 does not restart it). The grant
    removes the head
    ([if let Some(output) = self.queued.pop_front()], engine/lib.rs:124) and moves
    it into the task ([BuildArguments::new(reth_env, output, parent)], :128), so
    the backlog strictly shortens on every grant and whatever sits behind an
    output advances one place. The chosen witness [o_B] is the EMPTY,
    non-epoch-closing output, whose execution is skipped
    (payload_builder.rs:84-97) but which still emits its engine update at
    payload_builder.rs:92-95 - so "executed" here is "was granted the slot and
    its task resolved", which is exactly what the queue discipline owes it.

    (B) one-shot grant: AG( ~(grants(o_A) > 1) ). An output occupies the slot
    exactly once. This is a property of grant-BY-REMOVAL: because [pop_front]
    consumes, nothing can re-select the same output, and the release arm
    (engine/lib.rs:262-266) only clears the slot - it never puts anything back.
    The fairness content is that the scheduler is author-blind: [pop_front] reads
    no leader identity, no reputation score and no output size, so no authority
    whose round produced an output can hold or re-acquire the serial resource
    that every other authority's output has to pass through.

    (C) the discipline is unobservable from outside: AG( executing ->
    ~K_V1(executing) ). See the family reading guide - V1's view here already
    carries V0's last published execution tip (tn-reth/lib.rs:962-973 ->
    node.rs:1305-1322 -> recent_blocks.rs:40-60), which is the strongest peer
    view the code supports, and it still does not separate "idle after output n"
    from "already executing output n+1". This is not decoration: it is the reason
    (A) and (B) have to be structural. No peer can detect a node that re-serves
    its own backlog head, so nothing outside the node could ever repair a broken
    [pop_front].

    Mutation pin: {!Engine_queue_model.Reexecute_head} deletes the removal from
    [self.queued.pop_front()] at engine/lib.rs:124 - take the head without
    consuming it. (B) fails at the second grant of the same output; (A) fails
    because the backlog never shortens, so [o_B] never reaches the slot on any
    path. No sibling path repairs it, and the hunt is recorded on the mutation
    constructor: no already-executed check keyed on the consensus digest in
    [execute_consensus_output] (payload_builder.rs:22-36), no duplicate rejection
    in [finish_executing_output] (tn-reth/lib.rs:941-944), no dedup and no
    monotonic round check in [push_latest] (recent_blocks.rs:40-60), and the one
    identity-keyed guard, [replay_missed_consensus] (node/start_epoch.rs:71-93),
    is startup-only. Distinct from the output_forward_gate family's FIFO
    statement, whose gate is [pop_front] vs [pop_back] in the same line: that
    mutation changes WHICH end is served and leaves the one-shot property intact,
    this one changes whether serving consumes at all and leaves the order
    intact. *)
let s3 =
  let no_starvation =
    Formula.Ag
      (Formula.Implies
         ( atom Ob_queued,
           Formula.Af (Formula.Or (atom Ob_resolved, atom Engine_stopped)) ))
  in
  let one_shot = Formula.Ag (Formula.Not (atom Oa_granted_twice)) in
  let slot_is_opaque =
    Formula.Ag
      (Formula.Implies
         ( atom Executing,
           Formula.Not (Formula.K (Validator.V1, atom Executing)) ))
  in
  {
    name = "execution-slot-is-a-one-shot-grant-no-output-monopolises-it";
    bucket = Statements.Fairness;
    formula = Formula.conj [ no_starvation; one_shot; slot_is_opaque ];
    antecedent = atom Ob_queued;
  }

(** The family's statements. *)
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
