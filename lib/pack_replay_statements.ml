(** The three PACK_REPLAY statements over {!Pack_replay_model}: what a signed
    consensus result does and does not tell a peer (S1), and what a restart
    owes the numbers the pack already holds (S2, S3).

    {2 Reading guide for the [K] operands}

    - [K_w(packed(n))] - [w] is the observing peer, whose view is ONLY the set
      of [ConsensusResult] messages it received
      ({!Pack_replay_model.View_observer}). [packed(n)] is a fact about the
      SIGNER's durable pack, which [w] has no access to and which the wire form
      does not carry (primary/src/network/mod.rs:440-447). It is not rigid
      either: it is false at the initial state and at every state reached before
      the corresponding save. What makes it known across [w]'s whole
      indistinguishability class is exactly the save-before-publish ordering of
      subscriber.rs:286 vs :299-313 - which is why deleting the save refutes it.
    - [~K_w(executed(n))] - the same message carries no execution evidence.
      Persistence and execution are decoupled by the engine's bounded backlog
      (engine/src/lib.rs:31-38, :223-230, :245) and the decoupling is stated in
      the source at subscriber.rs:151-153. The witness pair is two reachable
      states with byte-identical received-message sets and different execution
      tips.
    - [~K_v(observed_result(n))] - the SIGNER's ignorance, about the one
      component of the model it cannot see. [publish_consensus] hands the
      encoded blob to gossipsub and returns (primary/src/network/mod.rs:
      430-452); nothing acknowledges delivery, so for every state in which [v]
      has published, the twin in which the peer has not yet received it shares
      [v]'s entire view.

    No positive [K] is ever asserted for [v]: its view is the whole state minus
    [rcvd], so a positive [K_v] over any other component would be a projection
    of its own view and worthless (R1). *)

open Pack_replay_model

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

(** S1 - published-consensus-result-implies-persisted-not-executed [security].

    AG( observed_result(n) -> K_w(packed(n)) /\ ~K_w(executed(n)) ) together
    with AG( signed_result(n) -> ~K_v(observed_result(n)) ), for both modelled
    numbers.

    Conjunct A ([observed_result -> K_w(packed)]). A validator writes the output
    to its consensus chain and persists it BEFORE it signs and gossips the
    corresponding [ConsensusResult]:
    [save_consensus(output.clone(), consensus_chain).await?;]
    (subscriber.rs:286) then [request_signature_direct(...)] /
    [publish_consensus(...)] (:299-313); the save is durable, being
    [save_consensus_output] followed by [persist_current] under the comment
    "Make sure we have persisted the consensus output before we execute"
    (state-sync/src/lib.rs:105-114). So every reachable state in which the peer
    holds that signature has the number in the signer's pack, at every state of
    the peer's indistinguishability class - which is what [K_w] means here. A
    failed save cannot leak past the gate either: [save_consensus] is called
    with [?] and its error is documented as a critical node failure
    (state-sync/src/lib.rs:101-114), so the signature at :299-313 is never
    reached.

    Conjunct B ([observed_result -> ~K_w(executed)]). The same signature says
    nothing about execution. The engine buffers up to
    [MAX_QUEUED_OUTPUTS = 8] outputs (engine/src/lib.rs:31-38, gate at :245) and
    executes exactly one at a time (:223-230), so a signer can be several
    outputs behind on execution while its signature is already on the wire; the
    source states the decoupling directly at subscriber.rs:151-153. The wire
    form has no execution field at all
    (primary/src/network/mod.rs:440-447).

    Conjunct C ([signed_result -> ~K_v(observed_result)]). The publisher gets no
    delivery receipt: [publish_consensus] encodes the [ConsensusResult] and
    hands it to [self.handle.publish] on the gossip topic
    (primary/src/network/mod.rs:440-451). So the signer never knows whether any
    particular peer has the evidence that binds it.

    MUTATION PIN. {!Pack_replay_model.No_save_before_publish} deletes the
    [save_consensus] at subscriber.rs:286 and leaves the publish, adding the
    transitions in which [pubd] advances with [saved] still at [T0]; conjunct A
    then fails at every state in which the peer has received a signature. No
    sibling repairs it: the shutdown drain's [save_consensus] (:394-397) only
    covers outputs still in [waiting] - never-published ones - the follow-path
    writer is not spawned for an active CVV (state-sync/src/lib.rs:67-71), and
    restart cannot retro-fill because [get_missing_consensus] reads the pack
    (state-sync/src/lib.rs:148-182). *)
let s_1 =
  let durable received packed =
    Formula.Implies (atom received, Formula.K (observer, atom packed))
  in
  let no_execution_evidence received executed =
    Formula.Implies
      (atom received, Formula.Not (Formula.K (observer, atom executed)))
  in
  let no_delivery_evidence published received =
    Formula.Implies
      (atom published, Formula.Not (Formula.K (signer, atom received)))
  in
  {
    name = "published-consensus-result-implies-persisted-not-executed";
    bucket = Statements.Security;
    formula =
      Formula.Ag
        (Formula.conj
           [
             durable Received_1 Saved_1;
             durable Received_2 Saved_2;
             no_execution_evidence Received_1 Executed_1;
             no_execution_evidence Received_2 Executed_2;
             no_delivery_evidence Published_1 Received_1;
             no_delivery_evidence Published_2 Received_2;
           ]);
    antecedent = atom Received_1;
  }

(** S2 - persisted-unexecuted-output-is-inevitably-executed-after-restart
    [liveness].

    AG( restarted /\ packed(n) /\ ~executed(n) -> AF executed(n) ), for both
    modelled numbers.

    The consensus chain legitimately runs ahead of execution - outputs are saved
    at subscriber.rs:286 and only broadcast for execution at :317 - so a crash
    in that window leaves committed-but-unexecuted numbers in the pack. On
    restart the node computes the gap between its execution tip and its pack tip
    and re-forwards every output in it: [get_missing_consensus]
    (state-sync/src/lib.rs:148-182) with the scan gated at :169-178, driven by
    [replay_missed_consensus] (start_epoch.rs:71-107), which loads each output
    (:89-90) and forwards it through [process_output] (:93). This runs BEFORE
    live consensus exists - run_epoch.rs:220-238 replays and then blocks on
    [wait_for_consensus_execution] at :236, while [create_consensus] is not
    reached until :258 - so nothing that reached the chain is stranded.

    The recovery is entirely local: it consults no peer, which is what makes it
    available under a partition.

    MUTATION PIN. {!Pack_replay_model.No_replay_scan} deletes the
    [if last_db_block.number > last_executed_block.number { ... }] scan at
    state-sync/src/lib.rs:169-178, so the returned vector is always empty and
    the replay forwards nothing; the node then enters live consensus with a
    permanently unexecuted number. The gap is unrecoverable from there because
    the live forwarder's watermark is primed from the PACK tip at startup
    (node.rs:824-833), so those numbers classify [OutputContinuity::Stale] and
    are skipped (run_epoch.rs:566-583, :866-891), and Bullshark reads its
    restored last-committed rounds from the same pack
    (storage/src/consensus_pack.rs:1196-1213). The one genuine sibling scanner,
    [send_leftover_consensus_output_to_engine] Phase 2 (close_epoch.rs:133-159),
    keys off the in-memory [last_forwarded_consensus_number] and only runs on a
    same-process non-boundary exit (run_epoch.rs:408-423) - which is why the
    antecedent carries [restarted] explicitly. The state-sync FOLLOW loop would
    re-fetch the hole (it starts from the EXECUTION tip,
    state-sync/src/lib.rs:195-197 with
    primary/src/consensus_bus.rs:693-703), but it is spawned only for
    [CvvInactive]/[Observer] (state-sync/src/lib.rs:67-71) and the only demotion
    of a live active CVV, [behind_consensus]
    (primary/src/network/handler.rs:137-213), fires on round-lag or epoch-lag,
    which a one-number hole does not produce. *)
let s_2 =
  let recovers packed executed =
    Formula.Implies
      ( Formula.conj [ atom Restarted; atom packed; Formula.Not (atom executed) ],
        Formula.Af (atom executed) )
  in
  {
    name = "persisted-unexecuted-output-is-inevitably-executed-after-restart";
    bucket = Statements.Liveness;
    formula =
      Formula.Ag
        (Formula.conj
           [ recovers Saved_1 Executed_1; recovers Saved_2 Executed_2 ]);
    antecedent =
      Formula.conj
        [ atom Restarted; atom Saved_1; Formula.Not (atom Executed_1) ];
  }

(** S3 - replayed-boundary-output-still-closes-the-epoch [liveness].

    AG( restarted /\ packed(n2) /\ ~executed(n2) -> AF epoch_concluded ), where
    [n2] is the output whose commit timestamp has reached the epoch boundary.

    The epoch-close flag is deliberately not part of an output's serialized
    form: [Serialize] writes only [self.inner] and [Deserialize] hard-codes
    [close_epoch: false] (types/src/primary/output.rs:79-104), with the comment
    that any consumer that deserializes an output MUST recompute the flag via
    [EpochManager::process_output]. The replay path does exactly that and
    nothing more: it loads the output from the pack
    ([get_consensus_output_current], start_epoch.rs:89-90,
    storage/src/consensus.rs:730-736), computes only a LOCAL [is_epoch_close]
    boolean for its own return value (:91) and hands the output to
    [process_output] (:93), whose
    [if output.committed_at() >= self.epoch_boundary { output.set_epoch_close();
    }] (run_epoch.rs:536-539) is the single site that stamps it. The flag then
    drives the actual close: [close_epoch_for_last_batch] (output.rs:235-244)
    feeds [TNPayload.close_epoch] (tn-reth/src/payload.rs:88-104), which is the
    sole gate on the [concludeEpoch] system call
    (tn-reth/src/evm/block.rs:794, :390-399), and it is also what makes the
    engine execute an empty boundary output at all
    (engine/src/payload_builder.rs:84-97). So a node that crashed after
    persisting the boundary output but before executing it still closes the
    epoch on restart.

    MUTATION PIN. {!Pack_replay_model.No_boundary_recompute} deletes
    run_epoch.rs:536-539. The replayed boundary output then reaches the engine
    with [close_epoch = false], executes as an ordinary block and never
    concludes the epoch on chain.

    WHY THE [restarted] ANTECEDENT IS LOAD-BEARING. The live path sets the same
    flag itself one frame earlier - [// update output so engine closes epoch] /
    [output.set_epoch_close();] at run_epoch.rs:603-604, inside
    [wait_for_epoch_boundary], before it calls [process_output] at :611 - so the
    deletion is FULLY repaired for live boundary detection. The model carries
    that repair ({!Pack_replay_model.exec_live_step} concludes the epoch under
    every mutation), so a version of this statement without [restarted] would be
    claiming something the live path already guarantees. The leftover drain is
    in the same position as the replay path, not a repair for it: it forwards
    through [process_output] (close_epoch.rs:127, :148) and never calls
    [set_epoch_close] itself. And the engine cannot infer the boundary: it
    consults only [output.close_epoch()]
    (engine/src/payload_builder.rs:84-97). *)
let s_3 =
  let boundary_gap =
    Formula.conj
      [ atom Restarted; atom Saved_2; Formula.Not (atom Executed_2) ]
  in
  {
    name = "replayed-boundary-output-still-closes-the-epoch";
    bucket = Statements.Liveness;
    formula =
      Formula.Ag
        (Formula.Implies (boundary_gap, Formula.Af (atom Epoch_concluded)));
    antecedent = boundary_gap;
  }

(** The family's statements. *)
let all = [ s_1; s_2; s_3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st = Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

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
