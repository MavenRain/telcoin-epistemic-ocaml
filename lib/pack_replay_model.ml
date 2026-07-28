(** Finite interpreted system for the PACK_REPLAY family: the
    save -> publish -> execute -> crash -> replay cycle around the consensus
    pack of one active committee validator. File citations refer to
    Telcoin-Association/telcoin-network at 0c59c15b (working tree) and every
    one of them was opened in this checkout.

    {2 The modelled mechanism}

    Two consensus outputs of one epoch are followed end to end: [N1], an
    ordinary output, and [N2], the output whose commit timestamp has reached
    [self.epoch_boundary] - the epoch's closing output.

    THE PRODUCER. An active CVV runs
    [Subscriber::handle_consensus_output] (subscriber.rs:280-325). For each
    completed output it does three things IN THIS ORDER:

    - [save_consensus(output.clone(), consensus_chain).await?;]
      (subscriber.rs:286). This is durable, not best-effort:
      [consensus_chain.save_consensus_output(consensus_output).await?;] then
      [consensus_chain.persist_current().await?;] under the comment
      ["Make sure we have persisted the consensus output before we execute."]
      (state-sync/src/lib.rs:105-114).
    - signs and gossips a [ConsensusResult]:
      [request_signature_direct(&encode(&to_intent_message(
      consensus_result_hash)))] (:299-302) then
      [self.network_handle.publish_consensus(epoch, round, number,
      this_digest, ..., sig)] (:303-313). The wire form carries the epoch,
      round, number, consensus-header hash, signer key and signature and
      NOTHING about execution (primary/src/network/mod.rs:430-452).
    - broadcasts the output for execution:
      [self.consensus_bus.consensus_output().send(output)] (:317).

    The sibling save path is deliberately elsewhere: the same-function
    ordering above is the ONLY writer on this path. The shutdown drain
    (subscriber.rs:385-412) does call [save_consensus] at :394-397, but only
    for outputs still sitting in [waiting] - i.e. outputs that never reached
    [handle_consensus_output] and were therefore never published. The
    follow/catch-up writer ([handle_sync_output], subscriber.rs:154) is not
    spawned at all for an active CVV
    ([NodeMode::CvvActive => {}], state-sync/src/lib.rs:67-71).

    THE CONSUMER. The engine executes strictly behind: a bounded backlog
    ([MAX_QUEUED_OUTPUTS = 8], engine/src/lib.rs:31-38, enqueue gate at :245)
    and a SINGLE in-flight execution task (:223-230). So persistence and
    signature can be several outputs ahead of execution, which is exactly what
    subscriber.rs:151-153 says out loud: ["This save will essentially mark this
    consensus output as written in stone ... This does NOT imply execution
    although it will be sent off for execution."]

    THE CRASH. A hard crash loses the engine queue and the in-memory
    [last_forwarded_consensus_number], and leaves committed-but-unexecuted
    numbers in the pack. The pack tip and the persisted execution tip both
    survive ([heal_finalized_to_persisted_tip] moves the finalized MARKER only,
    never the persisted execution tip the replay watermark derives from -
    tn-reth/src/lib.rs:872-875).

    THE REPLAY. At epoch start [get_missing_consensus] scans the gap
    (state-sync/src/lib.rs:148-182), gated at :169-178 by
    [if last_db_block.number > last_executed_block.number { for
    consensus_block_number in last_executed_block.number + 1..=last_db_block.
    number { ... } }]. [replay_missed_consensus] (start_epoch.rs:71-107) loads
    each output with [get_consensus_output_current] (:89-90,
    storage/src/consensus.rs:730-736) and forwards it through
    [process_output] (:93). This runs BEFORE live consensus is created:
    run_epoch.rs:220-238 replays and waits for execution, and
    [create_consensus] is only reached at :258.

    THE BOUNDARY FLAG. [close_epoch] is intentionally NOT serialized -
    [Deserialize] hard-codes [close_epoch: false] (types/src/primary/output.rs:
    79-104) - so every forwarding path must recompute it. The single recompute
    site the replay path traverses is inside [process_output]:
    [if output.committed_at() >= self.epoch_boundary { output.set_epoch_close();
    }] (run_epoch.rs:530-539). The flag is load-bearing all the way to chain
    state: [close_epoch_for_last_batch] (output.rs:235-244) feeds
    [TNPayload.close_epoch] (tn-reth/src/payload.rs:63-107) which is the sole
    gate on the closing system calls
    ([if let Some(randomness) = self.ctx.close_epoch { ... }],
    tn-reth/src/evm/block.rs:787-822, [concludeEpoch] at :390-399). It is also
    the only thing that makes the engine execute an EMPTY boundary output at
    all (engine/src/payload_builder.rs:78-97).

    {2 The sibling paths this model MUST carry (R4/R5)}

    - LIVE BOUNDARY. [wait_for_epoch_boundary] sets the very same flag itself,
      one call frame earlier: [// update output so engine closes epoch] /
      [output.set_epoch_close();] (run_epoch.rs:594-611). Deleting the
      [process_output] recompute therefore leaves LIVE boundary detection fully
      intact. The model reproduces this: {!exec_live_step} concludes the epoch
      under EVERY mutation, and that is precisely why S3 carries an explicit
      restart antecedent instead of reading as a general "a boundary output
      closes the epoch".
    - LEFTOVER DRAIN. [send_leftover_consensus_output_to_engine]
      (close_epoch.rs:99-162) re-scans the DB (Phase 2, :133-159) and would
      cover a save/execute gap - but only on a NON-boundary exit WITHIN the
      same process: it reads the in-memory [self.last_forwarded_consensus_number]
      (:138), and the boundary path discards the channel instead
      (run_epoch.rs:408-412). After a hard crash that state is gone. It also
      forwards through [process_output] and never calls [set_epoch_close]
      itself, so it is in the SAME position as the replay path, not a repair
      for it. The model has no same-process epoch exit, so it does not carry
      this path; S2 and S3 carry [Restarted] antecedents so that the scoping is
      explicit rather than implicit.
    - LIVE RE-FORWARD AFTER RESTART. There is none. The live forwarder's
      watermark is primed from the PACK tip at startup
      ([self.last_forwarded_consensus_number = state_sync::last_consensus_parent
      (...).1], node.rs:824-833, and [last_consensus_parent] returns
      [max(last_db, last_executed)], state-sync/src/lib.rs:131-144), so an
      output at or below it classifies as [OutputContinuity::Stale] and is
      skipped with [continue] (run_epoch.rs:566-583, :866-891). Bullshark does
      not re-sequence it either: its restored last-committed rounds are read
      from the same pack ([read_last_committed],
      storage/src/consensus_pack.rs:1196-1213). This is why {!Live} has no
      execution transition: a number the replay skipped is never revisited.

    {2 Components}

    Every number-valued component is a monotone PREFIX tip over
    [T0 < T1 < T2] - "the highest number for which this has happened" - because
    the subscriber processes outputs strictly in order (subscriber.rs:335-340,
    [FuturesOrdered]) and the engine executes them one at a time
    (engine/src/lib.rs:223-230).

    - [saved]  the pack tip (subscriber.rs:286 -> state-sync/src/lib.rs:105-114);
    - [pubd]   the highest number v has signed and gossiped a [ConsensusResult]
               for (subscriber.rs:299-313);
    - [rcvd]   the highest number the observing peer has actually RECEIVED.
               Gossipsub publication gives the publisher no delivery receipt
               (primary/src/network/mod.rs:448-451 just hands the encoded blob
               to [self.handle.publish]), so this is the family's hidden fact;
    - [exec]   the persisted execution tip;
    - [phase]  {!Running}, {!Replaying}, {!Live};
    - [closed] the on-chain epoch was concluded, i.e. a block carrying
               [ctx.close_epoch] ran [concludeEpoch]
               (tn-reth/src/evm/block.rs:787-822).

    {2 Scoping assumptions, stated so they can be attacked}

    - ONE crash. {!crash_restart_step} is the only [Running -> Replaying] edge
      and {!Live} has none back, so the model admits exactly one crash/restart.
      A crash loop is a real liveness hazard but an orthogonal one; admitting it
      would make every recovery statement false for a reason that has nothing to
      do with the gates under test.
    - The crash and the restart are ONE transition: the down interval has no
      observable content here (nothing in the model advances while the process
      is dead except gossip delivery, which {!deliver_step} allows in every
      phase anyway).
    - No NEW consensus output is produced after the restart. The modelled
      window is the epoch boundary, where the replay runs before
      [create_consensus] (run_epoch.rs:220-258) and the next output would be
      numbered above the pack tip - so it could never fill the gap. Keeping the
      tips honest prefixes is worth more than the extra states.

    {2 Role mapping}

    - [V0] is [v], the active CVV: signer, pack writer and executor. Its view is
      [(saved, pubd, exec, phase, closed)] - it knows what it persisted, what it
      signed, what it executed, whether it is replaying and whether the registry
      epoch closed. It does NOT see [rcvd]. Everything else in the model is its
      own local state, so [v] has perfect information about it and a positive
      [K_V0] over those components would be a projection of its own view: the
      family therefore only ever asserts [K_V0] NEGATIVELY, about the one thing
      it cannot see (whether the peer received the gossip).
    - [V1] is [w], the observing peer - the family's positive knowledge agent.
      Its view is [rcvd] and nothing else: the [ConsensusResult] messages it
      received. It sees no pack, no engine queue, no execution tip and no phase.
    - [V2] .. [V9] are idle: constant blank view, never under [K]. *)

(** A monotone prefix tip over the two modelled consensus numbers: [T0] is
    "neither", [T1] is "up to and including N1", [T2] is "up to and including
    N2", where [N2] is the output whose commit timestamp has reached the epoch
    boundary. Prefix order is sound because the subscriber handles outputs in
    order ([FuturesOrdered], subscriber.rs:335-341) and the engine executes one
    at a time (engine/src/lib.rs:223-230). *)
type tip = T0 | T1 | T2

(** Total order index for {!tip}: consensus-number order. *)
let tip_index = function T0 -> 0 | T1 -> 1 | T2 -> 2

(** Total order on {!tip}. *)
let tip_compare a b = Int.compare (tip_index a) (tip_index b)

(** [true] iff [a] is strictly below [b] in consensus-number order. *)
let tip_lt a b = Int.compare (tip_index a) (tip_index b) < 0

(** [true] iff [a] is at or above [b] in consensus-number order. *)
let tip_ge a b = Bool.not (tip_lt a b)

(** [true] iff the two tips are the same number. *)
let tip_equal a b = Int.equal 0 (tip_compare a b)

(** The next number, saturating at [T2]. Every use is guarded by
    [tip_lt _ T2], so the saturating arm is never the one taken. *)
let tip_next = function T0 -> T1 | T1 -> T2 | T2 -> T2

(** Where the node's process is in the crash/recovery cycle.

    - [Running] the live process: the subscriber is saving, signing and
      broadcasting, and [wait_for_epoch_boundary] is forwarding
      (run_epoch.rs:561-619);
    - [Replaying] the process restarted and [replay_missed_consensus] is
      re-forwarding the committed-but-unexecuted gap (start_epoch.rs:71-107),
      which happens BEFORE live consensus is created (run_epoch.rs:220-258);
    - [Live] the replay window is over. This covers both exits of
      run_epoch.rs:220-238 - resuming live consensus, and the
      replay-hit-the-boundary early return at :225-231 - because in this
      model's window they agree: no further output of the modelled epoch can
      reach the engine. *)
type phase = Running | Replaying | Live

(** Total order index for {!phase}: the order the process moves through. *)
let phase_index = function Running -> 0 | Replaying -> 1 | Live -> 2

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** [true] iff the live process is up. *)
let phase_is_running = function Running -> true | Replaying | Live -> false

(** [true] iff the restarted process is inside the replay scan. *)
let phase_is_replaying = function
  | Replaying -> true
  | Running | Live -> false

(** [true] iff the process died and came back, i.e. the replay window has been
    entered (whether or not it has been left). *)
let phase_is_restarted = function
  | Replaying | Live -> true
  | Running -> false

(** The joint global state.

    - [saved] the pack tip;
    - [pubd] the highest signed+gossiped [ConsensusResult];
    - [rcvd] the highest [ConsensusResult] the observing peer received - the
      hidden component, invisible to [v];
    - [exec] the persisted execution tip;
    - [phase] where the process is in the crash/recovery cycle;
    - [closed] the on-chain epoch was concluded by a closing block. *)
type state = {
  saved : tip;
  pubd : tip;
  rcvd : tip;
  exec : tip;
  phase : phase;
  closed : bool;
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = tip_compare s1.saved s2.saved in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = tip_compare s1.pubd s2.pubd in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = tip_compare s1.rcvd s2.rcvd in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = tip_compare s1.exec s2.exec in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = phase_compare s1.phase s2.phase in
          if Bool.not (Int.equal c4 0) then c4
          else Bool.compare s1.closed s2.closed

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    - [View_node] is [v]'s: its pack tip, what it signed and gossiped, its
      execution tip, its phase and whether the registry epoch closed. It does
      NOT carry [rcvd] - a gossipsub publish returns no delivery receipt
      (primary/src/network/mod.rs:448-451).
    - [View_observer] is [w]'s: ONLY the highest number for which it received a
      signed [ConsensusResult]. It carries no pack tip, no engine-queue
      occupancy, no execution tip, no phase and no epoch state, because the
      wire form has none of them (primary/src/network/mod.rs:440-447).
    - [View_idle] is the constant blank view of the eight non-participants. *)
type view =
  | View_node of tip * tip * tip * phase * bool
  | View_observer of tip
  | View_idle

(** Total order on the node view's five components. *)
let view_node_compare (sa, pa, ea, pha, ca) (sb, pb, eb, phb, cb) =
  let c = tip_compare sa sb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = tip_compare pa pb in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = tip_compare ea eb in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = phase_compare pha phb in
        if Bool.not (Int.equal c3 0) then c3 else Bool.compare ca cb

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_node _ | View_observer _) -> -1
  | (View_node _ | View_observer _), View_idle -> 1
  | View_observer x, View_observer y -> tip_compare x y
  | View_observer _, View_node _ -> -1
  | View_node _, View_observer _ -> 1
  | View_node (sa, pa, ea, pha, ca), View_node (sb, pb, eb, phb, cb) ->
      view_node_compare (sa, pa, ea, pha, ca) (sb, pb, eb, phb, cb)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** [V0] is the active CVV [v]: signer, pack writer and executor. *)
let signer = Validator.V0

(** [V1] is the observing peer [w]: the family's positive knowledge agent. *)
let observer = Validator.V1

(** View projection. [V0] and [V1] are the two agents; [V2] .. [V9] are idle
    non-agents with the constant blank view and never appear under [K]. *)
let view v s =
  match v with
  | Validator.V0 -> View_node (s.saved, s.pubd, s.exec, s.phase, s.closed)
  | Validator.V1 -> View_observer s.rcvd
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_save_before_publish
      (** delete [save_consensus(output.clone(), consensus_chain).await?;] from
          [handle_consensus_output] (subscriber.rs:286) while leaving the
          signature and the [publish_consensus] call (:299-313) in place. The
          pack tip then never advances on the active-CVV path, while signed
          [ConsensusResult]s keep going out, so {!publish_step} loses its
          [pubd < saved] gate. NO SIBLING REPAIRS IT: the shutdown drain's
          [save_consensus] (:394-397) is a different call site but only fires
          for outputs still in [waiting], i.e. ones that never reached
          [handle_consensus_output] and were therefore never published; the
          follow-path writer [handle_sync_output] (:154) is unreachable for an
          active CVV ([NodeMode::CvvActive => {}], state-sync/src/lib.rs:67-71);
          and restart does not retro-fill, because [get_missing_consensus]
          (state-sync/src/lib.rs:148-182) reads the pack, so an output that was
          never written is simply absent from it. *)
  | No_replay_scan
      (** delete the [if last_db_block.number > last_executed_block.number
          { ... }] gap scan at state-sync/src/lib.rs:169-178, so
          [get_missing_consensus] always returns an empty vector and
          {!replay_step} never fires. NO SIBLING REPAIRS IT ACROSS A RESTART:
          the one genuine second scanner,
          [send_leftover_consensus_output_to_engine] Phase 2
          (close_epoch.rs:133-159), keys off the in-memory
          [self.last_forwarded_consensus_number] and runs only on a
          same-process non-boundary exit (run_epoch.rs:408-423), which a hard
          crash destroys; and the live forwarder cannot revisit the gap because
          its watermark is primed from the PACK tip at startup
          (node.rs:824-833) so those numbers classify [Stale] and are skipped
          (run_epoch.rs:566-583, :866-891), while Bullshark reads its restored
          last-committed rounds from that same pack
          (storage/src/consensus_pack.rs:1196-1213). The one remaining candidate
          repair is the state-sync FOLLOW loop, which really would re-fetch the
          hole: [spawn_stream_consensus_headers] starts from
          [consensus_bus.last_consensus_block] (state-sync/src/lib.rs:195-197),
          which is the EXECUTION tip
          (primary/src/consensus_bus.rs:693-703), not the pack tip. But it is
          spawned only for [CvvInactive]/[Observer]
          (state-sync/src/lib.rs:67-71), and the sole demotion of a live active
          CVV is [behind_consensus] (primary/src/network/handler.rs:137-213),
          whose triggers are a ROUND outside the GC window (:175) or an epoch
          mismatch (:179-191). A skipped number is a HOLE, not a lag: the node
          keeps executing every later output, so its
          [exec_round]/[committed_round] stay level with consensus (:149-163)
          and the demotion never fires. *)
  | No_boundary_recompute
      (** delete [if output.committed_at() >= self.epoch_boundary {
          output.set_epoch_close(); }] from [process_output]
          (run_epoch.rs:536-539), so an output forwarded through that function
          reaches the engine with [close_epoch = false] and its block never
          runs [concludeEpoch] (tn-reth/src/payload.rs:88-91,
          tn-reth/src/evm/block.rs:794). A deserialized output cannot supply the
          flag itself: [Deserialize] hard-codes [close_epoch: false]
          (types/src/primary/output.rs:94-104) and the replay path loads from
          the pack ([get_consensus_output_current],
          storage/src/consensus.rs:730-736); the engine cannot infer it either
          (engine/src/payload_builder.rs:84-97 consults only
          [output.close_epoch()]). THE LIVE PATH IS GENUINELY REPAIRED and the
          model says so: [wait_for_epoch_boundary] calls [set_epoch_close()]
          itself at run_epoch.rs:603-604 before [process_output], so
          {!exec_live_step} still concludes the epoch under this mutation. What
          is NOT repaired is the replay path (start_epoch.rs:89-96 hands the
          deserialized output straight to [process_output]) and the leftover
          drain (close_epoch.rs:127, :148), both of which rely on the deleted
          recompute. The second-derivation site
          ([context_for_block] recovers [close_epoch] from a block's 32-byte
          [extra_data], tn-reth/src/evm/config.rs:150-178) is not a repair
          either: it is the RE-execution path for a closing block that was
          already produced, and under this mutation no such block is ever
          produced - block production reads [payload.close_epoch] instead
          (:180-193). *)

(** [subscriber.rs:286] fires for the next output. The subscriber handles one
    completed output at a time, and within [handle_consensus_output] the save
    strictly precedes the publish, so a new save cannot start until the
    previous output's publish has happened - hence the [pubd = saved] guard.
    {!No_save_before_publish} deletes the call, so this step disappears. *)
let save_step mut s =
  match mut with
  | Pristine | No_replay_scan | No_boundary_recompute ->
      if
        phase_is_running s.phase
        && tip_equal s.pubd s.saved
        && tip_lt s.saved T2
      then [ { s with saved = tip_next s.saved } ]
      else []
  | No_save_before_publish -> []

(** [subscriber.rs:299-313] signs the [ConsensusResult] and gossips it. On the
    pristine path this can only ever run for an output the save at :286 already
    persisted, which is the [pubd < saved] gate. Under
    {!No_save_before_publish} the save is gone but the publish is not, so the
    gate degrades to "an output the subscriber has in hand". *)
let publish_step mut s =
  if Bool.not (phase_is_running s.phase) then []
  else
    match mut with
    | Pristine | No_replay_scan | No_boundary_recompute ->
        if tip_lt s.pubd s.saved then [ { s with pubd = tip_next s.pubd } ]
        else []
    | No_save_before_publish ->
        if tip_lt s.pubd T2 then [ { s with pubd = tip_next s.pubd } ] else []

(** Gossip delivery of an already-published [ConsensusResult] to the observing
    peer. Independent of [v]'s phase - the message is on the network the moment
    [publish_consensus] hands it to [self.handle.publish]
    (primary/src/network/mod.rs:448-451) - and never acknowledged back to [v],
    which is what makes [rcvd] invisible in {!View_node}. *)
let deliver_step s =
  if tip_lt s.rcvd s.pubd then [ { s with rcvd = tip_next s.rcvd } ] else []

(** Execution on the LIVE path: the output broadcast at subscriber.rs:317 is
    picked up by [wait_for_epoch_boundary], forwarded through [process_output]
    and executed. The bound is [exec < pubd] because an output is broadcast for
    execution only after it has been signed and published, and the gap
    [pubd - exec] is the engine's bounded backlog (engine/src/lib.rs:31-38,
    :223-230, :245).

    This step concludes the epoch under EVERY mutation when it executes [N2].
    That is the modelled sibling of {!No_boundary_recompute}:
    [wait_for_epoch_boundary] stamps the flag itself at run_epoch.rs:603-604,
    one frame above the deleted recompute, so live boundary detection survives
    the deletion intact. *)
let exec_live_step s =
  if phase_is_running s.phase && tip_lt s.exec s.pubd then
    let e = tip_next s.exec in
    [ { s with exec = e; closed = s.closed || tip_ge e T2 } ]
  else []

(** The hard crash and the restart, as one transition. The engine queue and
    [last_forwarded_consensus_number] are lost; [saved], [exec] and [closed] are
    durable, and [rcvd] is the peer's state, so none of them move. Enabled from
    any [Running] state: which states have a save/execute gap is what the
    statements' antecedents decide, not what the transition relation is allowed
    to produce. *)
let crash_restart_step s =
  if phase_is_running s.phase then [ { s with phase = Replaying } ] else []

(** Is there still a missing output for the replay to forward? Pristine, this
    is exactly the [last_db_block.number > last_executed_block.number] gate of
    [get_missing_consensus] (state-sync/src/lib.rs:169-178) driving
    [replay_missed_consensus]'s loop (start_epoch.rs:79-105). Under
    {!No_replay_scan} the returned vector is always empty, so the loop body
    never runs. *)
let replay_enabled mut s =
  match mut with
  | Pristine | No_save_before_publish | No_boundary_recompute ->
      phase_is_replaying s.phase && tip_lt s.exec s.saved
  | No_replay_scan -> false

(** [true] iff forwarding through [process_output] still stamps the boundary
    flag, i.e. run_epoch.rs:536-539 is present. *)
let recompute_stamps_close = function
  | Pristine | No_save_before_publish | No_replay_scan -> true
  | No_boundary_recompute -> false

(** One replayed output: [get_consensus_output_current] loads it from the pack
    (start_epoch.rs:89-90, storage/src/consensus.rs:730-736), so it arrives with
    [close_epoch = false] (types/src/primary/output.rs:94-104), and
    [process_output] is the only thing that can stamp it
    (run_epoch.rs:530-539) before the engine executes it. *)
let replay_step mut s =
  if replay_enabled mut s then
    let e = tip_next s.exec in
    [
      {
        s with
        exec = e;
        closed = s.closed || (recompute_stamps_close mut && tip_ge e T2);
      };
    ]
  else []

(** The replay loop ran out of missing outputs, so the node leaves the replay
    window (run_epoch.rs:220-238: either it waits for the last replayed output
    and creates live consensus at :258, or the replay hit the boundary and it
    closes the epoch and returns at :225-231). Deriving the guard as "the replay
    step is not enabled" keeps the two mutation cases in one place: pristine it
    fires at [exec = saved], under {!No_replay_scan} it fires immediately with
    the gap still open. *)
let go_live_step mut s =
  if phase_is_replaying s.phase && Bool.not (replay_enabled mut s) then
    [ { s with phase = Live } ]
  else []

(** The transition relation: one component advances per step. [Live] has no
    execution transition on purpose - the live forwarder's watermark is primed
    from the pack tip (node.rs:824-833) so a skipped number classifies [Stale]
    (run_epoch.rs:566-583, :866-891) and Bullshark will not re-sequence it
    (storage/src/consensus_pack.rs:1196-1213). Only {!deliver_step} survives
    there, and it is bounded, so every path terminates. *)
let next_with mut s =
  List.concat
    [
      save_step mut s;
      publish_step mut s;
      deliver_step s;
      exec_live_step s;
      crash_restart_step s;
      replay_step mut s;
      go_live_step mut s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The single initial state: nothing saved, nothing signed, nothing received,
    nothing executed, the process up and the epoch open. *)
let initial =
  { saved = T0; pubd = T0; rcvd = T0; exec = T0; phase = Running; closed = false }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Saved_1
      (** [N1] is in the consensus pack (subscriber.rs:286 ->
          state-sync/src/lib.rs:105-114) *)
  | Saved_2  (** the epoch-closing output [N2] is in the consensus pack *)
  | Published_1
      (** [v] signed and gossiped a [ConsensusResult] for [N1]
          (subscriber.rs:299-313) *)
  | Published_2  (** [v] signed and gossiped a [ConsensusResult] for [N2] *)
  | Received_1
      (** the observing peer actually received [v]'s signed [ConsensusResult]
          for [N1] *)
  | Received_2  (** the observing peer received the one for [N2] *)
  | Executed_1  (** [v]'s persisted execution tip has reached [N1] *)
  | Executed_2  (** [v]'s persisted execution tip has reached [N2] *)
  | Restarted
      (** [v]'s process died and came back: it is inside or past the
          [replay_missed_consensus] window (start_epoch.rs:71-107) *)
  | Epoch_concluded
      (** a block carrying [ctx.close_epoch] ran the [concludeEpoch] system
          call (tn-reth/src/evm/block.rs:787-822, :390-399) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Saved_1 -> tip_ge s.saved T1
  | Saved_2 -> tip_ge s.saved T2
  | Published_1 -> tip_ge s.pubd T1
  | Published_2 -> tip_ge s.pubd T2
  | Received_1 -> tip_ge s.rcvd T1
  | Received_2 -> tip_ge s.rcvd T2
  | Executed_1 -> tip_ge s.exec T1
  | Executed_2 -> tip_ge s.exec T2
  | Restarted -> phase_is_restarted s.phase
  | Epoch_concluded -> s.closed

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Saved_1 -> "packed(n1)"
  | Saved_2 -> "packed(n2)"
  | Published_1 -> "signed_result(n1)"
  | Published_2 -> "signed_result(n2)"
  | Received_1 -> "observed_result(n1)"
  | Received_2 -> "observed_result(n2)"
  | Executed_1 -> "executed(n1)"
  | Executed_2 -> "executed(n2)"
  | Restarted -> "restarted"
  | Epoch_concluded -> "epoch_concluded"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every reachable
    world by test/t_pack_replay_topos.ml. Every transition strictly advances one
    of (saved, pubd, rcvd, exec, phase) or flips [closed] false-to-true, so
    reachability is expected to be antisymmetric - but that is settled by
    RUNNING the gate, not by this comment. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state,
    mutation-parameterized transitions, the two-agent view, the atom
    valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
