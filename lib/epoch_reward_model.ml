(** Finite interpreted system for the EPOCH_REWARD family: how telcoin-network
    maintains the in-memory per-leader reward counter across the engine's
    empty-output fast path and across a crash-and-rebuild restart, and what one
    node can know about a peer's counter. File citations refer to
    Telcoin-Association/telcoin-network (HEAD 0c59c15b).

    THE MODELLED MECHANISM. One epoch at TWO committee nodes over a FIXED
    committed sequence of three consensus outputs whose leaders are three
    distinct authorities:
    - [O1] carries no batches and is NOT the epoch close. [execute_consensus_output]
      credits its leader at payload_builder.rs:30 - the FIRST statement of the
      function - and then takes the batch-less non-closing early return at
      payload_builder.rs:84-97, producing NO execution block at all and only
      pushing [(leader_round, consensus_num_hash, None)] onto the engine-update
      channel. [RecentBlocks::push_latest] with [None] pushes no executed block
      (recent_blocks.rs:36-60) and [last_executed_consensus_block] reads the
      parent_beacon_block_root of [latest_execution_block()]
      (consensus_bus.rs:669-688), so the executed-block watermark does NOT move
      across a skipped round.
    - [O2] carries batches, so exactly one execution block is produced; that
      block IS the executed watermark.
    - [O3] carries no batches but IS the epoch boundary. The skip is gated on
      [if !output.close_epoch()] (payload_builder.rs:85), so the boundary output
      falls through to payload_builder.rs:99-136, which builds ONE synthetic
      empty [TNPayload] from the parent's [base_fee_per_gas] / [gas_limit] with
      the leader's execution address as beneficiary. Executing it fires
      [apply_consensus_block_rewards] + [apply_closing_epoch_contract_call]
      (block.rs:794-835) and stamps [rewards_counter.generate_withdrawals()] and
      its root into the header (block.rs:969-978). That is the SEAL.
      [close_epoch_for_last_batch] answers [Some(true)] for an empty
      batch_digests list (output.rs:240-244).

    THE RESTART REBUILD. A node that crashes mid-epoch loses the counter (it is
    purely in-memory, gas_accumulator.rs:20-21 / :90-96) and rebuilds it from two
    halves that PARTITION the epoch's committed rounds:
    - CATCHUP: [catchup_accumulator] reads [last_executed_round] out of the
      pinned finalized header's nonce (node.rs:231-232) and calls
      [count_leaders] only when that round is > 0 and in this epoch
      (node.rs:262-268). [count_leaders] walks CONSENSUS headers and skips every
      one with [leader_round > last_executed_round] (consensus_pack.rs:1284-1291).
    - REPLAY: [get_missing_consensus] collects exactly consensus numbers
      [last_executed_block.number + 1 ..= last_db_block.number]
      (state-sync/lib.rs:148-182) and [replay_missed_consensus] forwards them
      through the NORMAL engine path, stopping at the epoch close
      (start_epoch.rs:71-107), so each replayed output is credited by the very
      same [inc_leader_count] call the live path uses.
    Because a blockless round never advances the executed watermark, it always
    falls on the REPLAY side and never on both - that is the whole reason the
    partition is exact. [inc_leader_count] itself is a bare [+= 1] with no
    per-round key and no dedup (gas_accumulator.rs:98-107), so the partition is
    the ONLY thing preventing a double credit. [RewardsCounter::clear] runs only
    at the boundary (gas_accumulator.rs:109-113 from run_epoch.rs:658).

    COMPONENTS. Per node: how far its engine has consumed the sequence (a
    {!phase}), its in-memory per-leader ledger (three saturating {!count}s, one
    per committed output since the three leaders are distinct), and whether it
    has executed the epoch-closing block. Globally: whether the PEER crashed and
    rebuilt this epoch. The consensus DB is modelled as already holding all three
    outputs while the ENGINE lags (every output is saved before it is broadcast,
    run_epoch.rs:568-573) - the adversarial interleaving that keeps the
    committed-but-unexecuted replay window non-empty at every phase below P3,
    which is exactly the seam the catchup/replay partition has to get right.

    ORDERING IS LOAD-BEARING. The blockless output must come BEFORE a
    block-producing one. With the alternative ordering [batched, blockless,
    boundary] every crash point rebuilds the same ledger even when the credit is
    moved below the skip, i.e. the {!Credit_after_skip} mutation would be
    silently repaired and the fairness statement would prove under its own pin.

    ROLE MAPPING. [V1] is the reference node: it never crashes and is the ONLY
    knowledge agent used under [K]. Its view is its own phase, its own ledger and
    its own sealed flag - all of it process-local state. [V2] is the peer that
    carries the hidden crash-and-rebuild branch; it is a real node and so gets a
    real view (its own projection plus its own crash flag - a node knows it
    restarted), but it never appears under [K]. [V0] and [V3] are idle
    non-agents with the constant blank view and never appear under [K].

    THE SEAL ACKNOWLEDGEMENT (the epoch record vote). Sealing is a local
    execution act, but it is NOT unacknowledged. Once the boundary output is
    identified, [close_epoch] awaits [wait_for_consensus_execution(target_hash)]
    (run_epoch.rs:653) and only then does [write_epoch_record] read
    [self.consensus_bus.latest_execution_block_num_hash()] into
    [EpochRecord.final_state] alongside [final_consensus =
    (last_consensus_header.number, target_hash)] (close_epoch.rs:231-245).
    [latest_execution_block_num_hash] is the num/hash of the last EXECUTED block
    (recent_blocks.rs:67-74), so past the await it is exactly the epoch's closing
    block: the record DIGEST is a commitment to having sealed. The record is
    saved and published on [epoch_record_watch] (close_epoch.rs:247-248);
    [spawn_epoch_vote_collector] wakes on that watch (epoch_votes.rs:302-342) and
    [manage_epoch_votes] signs the record and gossips the vote
    (epoch_votes.rs:59-73); a peer counts an inbound vote only when
    [vote.epoch_hash == epoch_hash && committee_keys.contains(&vote.public_key)]
    (epoch_votes.rs:88-111). So a matched peer vote - standalone gossip
    ([PrimaryGossip::EpochVote], message.rs:18-31) or the same signature inside
    an aggregated [EpochCertificate] - tells the receiver that that peer computed
    the identical closing execution state, i.e. that it sealed. This model
    carries that acknowledgement explicitly as {!state.v1_saw_peer_vote}, so no
    statement about the seal's invisibility is true merely by omitting it.

    WHAT V1 CANNOT SEE, AND WHY THAT IS FAITHFUL. (a) the peer's consumption
    progress: no protocol message reports how far a peer's ENGINE has executed,
    the engine's only outward signal being [engine_update_tx] into its OWN
    consensus bus (payload_builder.rs:92, node.rs:1305-1322), while the one
    gossiped progress record, [PrimaryGossip::Consensus] of a [ConsensusResult],
    is published by the CONSENSUS subscriber and carries only the consensus
    header's epoch/round/number/hash (subscriber.rs:288-316, block.rs:116-133);
    (b) the peer's reward counters: the counter is process-local and in-memory,
    never gossiped, and becomes chain-visible only when a node executes the
    CLOSING block and stamps [generate_withdrawals()] into it (block.rs:969-978);
    (c) whether the peer crashed: [catchup_accumulator] (node.rs:189-268) and
    [replay_missed_consensus] (start_epoch.rs:71-107) are startup-local recovery
    with no wire trace at all; (d) whether the peer has executed the closing
    block - but ONLY until the peer's epoch vote arrives, which is precisely the
    acknowledgement described above and is modelled, not omitted.

    DECLARED MODELLING ASSUMPTIONS (so no statement is true only by omission):
    - V1 never crashes - it is the reference node; only the peer carries the
      hidden crash branch, which is precisely what the knower cannot see.
    - At most one crash per epoch, and none after the close: past the close the
      accumulator is cleared (run_epoch.rs:658) and recovery re-enters at the
      NEXT epoch.
    - Only V1's receipt of the peer's epoch vote is tracked, not V2's symmetric
      receipt of V1's: V2 never appears under [K], so a second flag would only
      duplicate states without changing any statement's truth value.
    - No idle self-loop: a node with unconsumed committed output always has an
      enabled step, i.e. the liveness conjunct is conditional on the engine
      continuing to drain the to_engine channel (run_epoch.rs:548). Every move
      strictly increases (phase v1 + phase v2 + restart-used + vote-seen), so the
      graph is a finite DAG whose terminals the kernel stutter-closes: [Af] is
      honest and the {!Skip_batchless_close} refutation is a genuine gate removal
      (the terminal is reached with [sealed = false]), never a manufactured
      stall. *)

(** How far a node's engine has consumed the epoch's fixed committed sequence
    [O1] (blockless, non-closing), [O2] (batched), [O3] (blockless boundary). *)
type phase =
  | P0  (** nothing consumed: the epoch has just opened *)
  | P1  (** [O1] consumed - credited, but skipped, so no block and no watermark *)
  | P2  (** [O2] consumed - one execution block, the executed watermark *)
  | P3  (** [O3] consumed - the epoch's sequence is exhausted *)

(** Total order index for {!phase}. *)
let phase_index = function P0 -> 0 | P1 -> 1 | P2 -> 2 | P3 -> 3

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** [true] iff the engine has processed the batch-less non-closing output [O1]
    (payload_builder.rs:84-97). *)
let phase_consumed_blockless = function
  | P0 -> false
  | P1 | P2 | P3 -> true

(** [true] iff no execution block of this epoch has been produced yet, so the
    last-executed-consensus watermark has not moved (recent_blocks.rs:36-60,
    consensus_bus.rs:669-688). [O1] produced no block, hence [P1] too. *)
let phase_watermark_zero = function
  | P0 | P1 -> true
  | P2 | P3 -> false

(** [true] iff the batch-less BOUNDARY output [O3] is the node's next output. *)
let phase_at_boundary = function
  | P0 | P1 -> false
  | P2 -> true
  | P3 -> false

(** A saturating per-leader credit counter. [Two] is the absorbing "already
    wrong" value: two credits for one committed round already refutes
    exactly-once, so the counter never needs to climb higher (the real increment
    is unbounded and un-deduplicated, gas_accumulator.rs:98-107). *)
type count =
  | Zero  (** the round's leader has not been credited *)
  | One  (** the round's leader has been credited exactly once *)
  | Two  (** the round's leader has been credited twice or more: already wrong *)

(** Total order index for {!count}. *)
let count_index = function Zero -> 0 | One -> 1 | Two -> 2

(** Total order on {!count}. *)
let count_compare a b = Int.compare (count_index a) (count_index b)

(** Equality on {!count} without polymorphic compare. *)
let count_equal a b = Int.equal (count_index a) (count_index b)

(** [true] iff the counter stands at exactly one. *)
let count_is_one = function Zero -> false | One -> true | Two -> false

(** [true] iff the counter has already recorded a second credit for one
    committed round. *)
let count_is_double = function Zero -> false | One -> false | Two -> true

(** Saturating increment: the real [inc_leader_count] is [*v += 1] with no cap
    and no per-round key (gas_accumulator.rs:100-107); the model saturates at
    {!Two} because the statements only ever ask "more than once?". *)
let count_inc = function Zero -> One | One -> Two | Two -> Two

(** One node's in-memory reward ledger for the epoch: one counter per committed
    output, each output having a distinct leader
    ([RewardsCounter::leader_counts], gas_accumulator.rs:90-96). *)
type ledger = { l1 : count; l2 : count; l3 : count }

(** Total deterministic order over ALL ledger fields. *)
let ledger_compare la lb =
  let c = count_compare la.l1 lb.l1 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = count_compare la.l2 lb.l2 in
    if Bool.not (Int.equal c1 0) then c1 else count_compare la.l3 lb.l3

(** Componentwise equality: two nodes holding equal ledgers would seal identical
    withdrawals (block.rs:969-978). *)
let ledger_equal la lb =
  count_equal la.l1 lb.l1 && count_equal la.l2 lb.l2 && count_equal la.l3 lb.l3

(** [true] iff some committed round of this ledger was credited twice. *)
let ledger_has_double l =
  count_is_double l.l1 || count_is_double l.l2 || count_is_double l.l3

(** The empty ledger a fresh (or freshly restarted) node starts the epoch with:
    [RewardsCounter::clear] ran at the previous boundary
    (gas_accumulator.rs:109-113 from run_epoch.rs:658). *)
let ledger_zero = { l1 = Zero; l2 = Zero; l3 = Zero }

(** One node's engine state: how far it has consumed, what its counter holds,
    and whether it has executed the epoch-closing block. *)
type node = { prog : phase; led : ledger; sealed : bool }

(** Total order index for [bool] - no polymorphic compare. *)
let bool_index = function false -> 0 | true -> 1

(** Total order on [bool]. *)
let bool_compare a b = Int.compare (bool_index a) (bool_index b)

(** Total deterministic order over ALL node fields. *)
let node_compare na nb =
  let c = phase_compare na.prog nb.prog in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = ledger_compare na.led nb.led in
    if Bool.not (Int.equal c1 0) then c1 else bool_compare na.sealed nb.sealed

(** The joint global state. [v1] is the reference node (never crashes) and the
    single knowledge agent; [v2] is the peer that carries the hidden
    crash-and-rebuild branch; [v2_restarted] records that the peer's in-memory
    counter was lost and rebuilt through catchup+replay this epoch
    (node.rs:189-268, start_epoch.rs:71-107); [v1_saw_peer_vote] records that V1
    has received and MATCHED the peer's epoch-record vote, the one wire artefact
    that commits to a peer's closing EXECUTION state (epoch_votes.rs:59-73,
    :88-111 over [EpochRecord.final_state], close_epoch.rs:231-248). *)
type state = { v1 : node; v2 : node; v2_restarted : bool; v1_saw_peer_vote : bool }

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = node_compare s1.v1 s2.v1 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = node_compare s1.v2 s2.v2 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = bool_compare s1.v2_restarted s2.v2_restarted in
      if Bool.not (Int.equal c2 0) then c2
      else bool_compare s1.v1_saw_peer_vote s2.v1_saw_peer_vote

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. [View_v1] is the knowledge agent V1's projection -
    its OWN phase, its OWN reward ledger, its OWN sealed flag and the ONE inbound
    wire fact it can hold about the peer's execution, namely a matched peer epoch
    vote (epoch_votes.rs:88-111). It still sees no peer phase, no peer ledger, no
    peer counter and above all no peer crash flag. [View_v2] is the peer's
    symmetric projection plus its own crash flag (a node knows it restarted); V2
    is a real node, not an idle party, so it gets a real view, but only V1 ever
    appears under [K]. [View_idle] is the constant blank view of the non-agents
    V0 and V3. *)
type view =
  | View_v1 of phase * ledger * bool * bool
      (** V1's own consumption progress, ledger, sealed flag, and whether it has
          matched the peer's epoch-record vote *)
  | View_v2 of phase * ledger * bool * bool
      (** V2's own consumption progress, ledger, sealed flag and crash flag *)
  | View_idle  (** the constant blank view of the non-agents V0, V3 *)

(** Total deterministic order over ALL fields of V1's view. *)
let view_v1_compare (pa, la, sa, wa) (pb, lb, sb, wb) =
  let c = phase_compare pa pb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = ledger_compare la lb in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = bool_compare sa sb in
      if Bool.not (Int.equal c2 0) then c2 else bool_compare wa wb

(** Total deterministic order over ALL fields of V2's view. *)
let view_v2_compare (pa, la, sa, ra) (pb, lb, sb, rb) =
  let c = phase_compare pa pb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = ledger_compare la lb in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = bool_compare sa sb in
      if Bool.not (Int.equal c2 0) then c2 else bool_compare ra rb

(** Total order on views: [View_idle] < [View_v1] < [View_v2], with the
    field-wise order within each constructor. Every constructor is spelled: no
    wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_v1 _ | View_v2 _) -> -1
  | (View_v1 _ | View_v2 _), View_idle -> 1
  | View_v1 (pa, la, sa, wa), View_v1 (pb, lb, sb, wb) ->
      view_v1_compare (pa, la, sa, wa) (pb, lb, sb, wb)
  | View_v1 _, View_v2 _ -> -1
  | View_v2 _, View_v1 _ -> 1
  | View_v2 (pa, la, sa, ra), View_v2 (pb, lb, sb, rb) ->
      view_v2_compare (pa, la, sa, ra) (pb, lb, sb, rb)

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 is the ONLY knowledge agent used under [K]: it sees its
    own consumption progress, its own three reward counters, whether it has
    executed the closing block - all purely node-local state - and whether the
    peer's epoch-record vote has arrived and matched its own record digest, which
    is the only inbound message in this scope that says anything about a peer's
    execution (epoch_votes.rs:88-111). V2 is a real node with a real view (its
    own projection plus its own crash flag) but never appears under [K]; V0 and
    V3 are idle non-agents with the constant blank view. *)
let view v s =
  match v with
  | Validator.V1 ->
      View_v1 (s.v1.prog, s.v1.led, s.v1.sealed, s.v1_saw_peer_vote)
  | Validator.V2 -> View_v2 (s.v2.prog, s.v2.led, s.v2.sealed, s.v2_restarted)
  | Validator.V0 | Validator.V3 -> View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine  (** the code as written at HEAD 0c59c15b *)
  | Credit_after_skip
      (** delete the PLACEMENT gate at crates/engine/src/payload_builder.rs:30 -
          [gas_accumulator.rewards_counter().inc_leader_count(output.leader().author())]
          is the FIRST statement of [execute_consensus_output], ABOVE the
          batch-less non-closing early return at :84-97. Moving it below that
          return credits only outputs that actually reach execution, so the live
          [O1] step no longer sets [l1], i.e. the transition P0 -> P1 leaves the
          ledger untouched. NO SIBLING PATH REPAIRS IT: [rg inc_leader_count
          crates] returns exactly three sites - payload_builder.rs:30 (live),
          consensus_pack.rs:1291 inside [count_leaders] (restart catchup) and a
          unit test. The catchup writer does not repair the deletion, it
          CONTRADICTS it: [count_leaders] walks CONSENSUS headers
          (consensus_pack.rs:1267-1294), not executed blocks, so on a restarted
          peer it still credits the blockless round; [try_restore_state]
          (node.rs:1272-1293) reseeds only from EXECUTED blocks and cannot supply
          the blockless round either. There is no caller-side filter, no
          re-derivation of counts from the chain and no content-addressed dedup
          (the counter is a bare [HashMap] increment, gas_accumulator.rs:98-107),
          so live and rebuilt ledgers diverge instead of being repaired. *)
  | No_catchup_watermark
      (** delete [if leader_round > last_executed_round { continue; }] at
          crates/storage/src/consensus_pack.rs:1287-1289, the guard confining the
          catchup half of the restart rebuild to rounds at or below the
          executed-block watermark. The catchup then credits the
          committed-but-unexecuted [O3] that [replay_missed_consensus] is about
          to re-forward, so the restart-from-P2 transition lands at ledger
          [(One,One,Two)]. NO SIBLING PATH REPAIRS IT: [inc_leader_count] is a
          bare increment with no per-round key and no set
          (gas_accumulator.rs:98-107); [RewardsCounter::clear] runs only at the
          epoch boundary (gas_accumulator.rs:109-113 from run_epoch.rs:658, i.e.
          AFTER the closing block has already sealed the totals); replay
          re-executes and never subtracts (start_epoch.rs:71-107); the other half
          of catchup rebuilds gas stats by walking executed blocks but leader
          counts come ONLY from the consensus DB (node.rs:253-268); and
          [get_missing_consensus] has no overlap filter beyond the same watermark
          comparison, taken on CONSENSUS numbers (state-sync/lib.rs:169-178), so
          it cannot see the catchup's over-count. *)
  | Skip_batchless_close
      (** delete the [if !output.close_epoch()] condition at
          crates/engine/src/payload_builder.rs:85, which confines the
          empty-output skip to NON-closing outputs. Every batch-less output then
          skips execution, so the P2 -> P3 step (and the [O3] leg of every
          replay) stops setting [sealed]: no synthetic closing block is built
          (payload_builder.rs:99-136 is unreachable), no
          applyIncentives/concludeEpoch fires (block.rs:794-835) and no reward
          withdrawals are stamped (block.rs:969-978). NO SIBLING PATH REPAIRS IT,
          three candidates checked: (i) a LATER output closing instead -
          [process_output] flags every output past the boundary
          (run_epoch.rs:530-539) but [wait_for_epoch_boundary] RETURNS at the
          first such output (run_epoch.rs:595-612) and the leftover drain
          likewise returns at the first boundary output
          (close_epoch.rs:114-162), so no second closing output is forwarded in
          that epoch; (ii) RE-EXECUTION supplying the close - [context_for_block]
          re-derives close_epoch from a block's 32-byte extra_data
          (config.rs:150-178), but that is content-addressed on a closing block
          some payload path must first have BUILT, and with the gate deleted
          fleet-wide no such block exists to import; (iii) the close HANGING and
          forcing a retry - it does not, because [contains_consensus] also tracks
          SKIPPED rounds via [recent_consensus_num_hashes]
          (recent_blocks.rs:36-60, :91-104), so
          [wait_for_consensus_execution] (consensus_bus.rs:650-667) resolves on
          the skipped boundary output and the node proceeds into the next epoch
          with no closing block at all. Ledgers are untouched (the credit at :30
          is above the return), keeping the refutation attributable to the
          liveness conjunct alone. *)

(** The [O1] credit. Under {!Credit_after_skip} the increment sits BELOW the
    batch-less non-closing early return, so the skipped output earns nothing.
    Every mutation arm is spelled. *)
let credit_o1 mut led =
  match mut with
  | Pristine | No_catchup_watermark | Skip_batchless_close ->
      { led with l1 = count_inc led.l1 }
  | Credit_after_skip -> led

(** The [O2] credit: [O2] carries batches, so it never takes the batch-less
    early return and payload_builder.rs:30 fires for it under every mutation. *)
let credit_o2 led = { led with l2 = count_inc led.l2 }

(** The [O3] credit: [O3] is the epoch close, so it never takes the batch-less
    NON-CLOSING early return and payload_builder.rs:30 fires for it under every
    mutation - including {!Skip_batchless_close}, which removes only the
    execution (and hence the seal), not the credit above the return. *)
let credit_o3 led = { led with l3 = count_inc led.l3 }

(** Does executing [O3] seal the epoch? Under {!Skip_batchless_close} the
    [!output.close_epoch()] condition is gone, so the batch-less BOUNDARY output
    also takes the skip: no synthetic block, hence no applyIncentives /
    concludeEpoch and no withdrawals. *)
let seals_o3 = function
  | Pristine | Credit_after_skip | No_catchup_watermark -> true
  | Skip_batchless_close -> false

(** One node consumes the next committed output live. Returns [[]] at [P3] (the
    epoch's sequence is exhausted); a list, never an option. *)
let consume mut n =
  match n.prog with
  | P0 -> [ { prog = P1; led = credit_o1 mut n.led; sealed = n.sealed } ]
  | P1 -> [ { prog = P2; led = credit_o2 n.led; sealed = n.sealed } ]
  | P2 -> [ { prog = P3; led = credit_o3 n.led; sealed = seals_o3 mut } ]
  | P3 -> []

(** Catchup half of the restart, from a ZERO ledger (the in-memory counter is
    lost). The executed-block watermark is 0 at [P0]/[P1] - [O1] produced no
    block, so [last_executed_consensus_block] still points below it - and
    node.rs:264's [last_executed_round > 0] guard then skips [count_leaders]
    entirely. At [P2] the pristine guard (consensus_pack.rs:1287-1289) admits
    only [leader_round <= 2], i.e. [O1] and [O2]; {!No_catchup_watermark} deletes
    it and admits the whole pack, [O3] included. [P3] is unreachable here
    (restart is disabled past the close) and is mapped to the zero ledger. *)
let catchup mut prog =
  match prog with
  | P0 | P1 -> ledger_zero
  | P2 -> (
      match mut with
      | Pristine | Credit_after_skip | Skip_batchless_close ->
          { l1 = One; l2 = One; l3 = Zero }
      | No_catchup_watermark -> { l1 = One; l2 = One; l3 = One })
  | P3 -> ledger_zero

(** Replay half of the restart: [get_missing_consensus] forwards exactly the
    outputs numbered ABOVE the last EXECUTED consensus block
    (state-sync/lib.rs:148-182), and they flow through the normal
    [payload_builder] path, so each is credited by the same [credit_*] functions
    the live path uses. A node at [P0] or [P1] has executed no block, so its
    watermark is 0 and all three outputs are replayed; a node at [P2] replays
    only [O3]. *)
let replay mut prog led =
  match prog with
  | P0 | P1 -> credit_o3 (credit_o2 (credit_o1 mut led))
  | P2 -> credit_o3 led
  | P3 -> led

(** Crash + restart + catchup + replay, as ONE atomic transition (the node is
    down in between and nothing about it is observable). Replay stops at the
    epoch close (start_epoch.rs:99-104), which is [O3], so the recovered node
    lands at [P3]. Disabled at [P3]: past the close the accumulator is cleared
    (run_epoch.rs:658) and recovery re-enters at the NEXT epoch. *)
let restart mut n =
  match n.prog with
  | P3 -> []
  | P0 | P1 | P2 ->
      [
        {
          prog = P3;
          led = replay mut n.prog (catchup mut n.prog);
          sealed = seals_o3 mut;
        };
      ]

(** V1 receives and matches the peer's epoch-record vote - the seal
    acknowledgement. Enabled exactly when BOTH nodes have executed the
    epoch-closing block and V1 has not already matched the vote.

    Both preconditions are the real ones. The peer only signs and gossips a vote
    after its own [write_epoch_record] has published a record on
    [epoch_record_watch] (close_epoch.rs:247-248 into epoch_votes.rs:302-342,
    :59-73), and that record is written only after [close_epoch] awaited
    [wait_for_consensus_execution] and read [latest_execution_block_num_hash]
    into [final_state] (run_epoch.rs:653, close_epoch.rs:236-245,
    recent_blocks.rs:67-74) - so the vote exists only once the PEER has sealed.
    The receiver counts it only when [vote.epoch_hash == epoch_hash], compared
    against the digest of its OWN record (epoch_votes.rs:88-96) - so V1 must have
    sealed too.

    Under {!Skip_batchless_close} no node executes a closing block at all, so no
    record commits to a closing state and there is no seal to acknowledge: the
    flag correctly stays false rather than being disabled by fiat. The step
    therefore does not branch on the mutation - the [sealed] guard already
    carries the mutation's effect. *)
let see_peer_vote s =
  if s.v1.sealed && s.v2.sealed && Bool.not s.v1_saw_peer_vote then
    [ { s with v1_saw_peer_vote = true } ]
  else []

(** The transition relation: either node consumes one committed output, or the
    PEER crashes and recovers (at most once - V1 is the never-crashing reference
    node), or V1 matches the peer's epoch vote. Every move strictly increases
    (phase v1 + phase v2 + restart-used + vote-seen), so the graph is a finite
    DAG and its terminals are stutter-closed by the kernel: [Af] is honest and no
    idle self-loop is added. *)
let next_with mut s =
  List.concat
    [
      List.map (fun n -> { s with v1 = n }) (consume mut s.v1);
      List.map (fun n -> { s with v2 = n }) (consume mut s.v2);
      (if s.v2_restarted then []
       else
         List.map
           (fun n -> { s with v2 = n; v2_restarted = true })
           (restart mut s.v2));
      see_peer_vote s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: the epoch has just opened, both engines have consumed
    nothing, both [RewardsCounter]s are empty ([clear] ran at the previous
    boundary, gas_accumulator.rs:109-113 from run_epoch.rs:658), and the peer has
    not crashed, and no epoch-record vote has been exchanged (no record exists
    until the boundary, close_epoch.rs:231-248). *)
let initial =
  let fresh = { prog = P0; led = ledger_zero; sealed = false } in
  { v1 = fresh; v2 = fresh; v2_restarted = false; v1_saw_peer_vote = false }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | V1_consumed_blockless
      (** [v1.prog] is P1/P2/P3: V1's engine has processed [O1], the batch-less
          non-closing output (payload_builder.rs:84-97) *)
  | V1_watermark_zero
      (** [v1.prog] is P0/P1: V1 has executed no block of this epoch, so its
          last-executed-consensus watermark has not moved
          (recent_blocks.rs:36-60, consensus_bus.rs:669-688) *)
  | V1_credited_blockless
      (** [v1.led.l1 = One]: V1's counter for the blockless round's leader stands
          at exactly one *)
  | V1_sealed
      (** [v1.sealed]: V1 has executed the epoch-closing block - applyIncentives
          + concludeEpoch (block.rs:794-835) with the reward withdrawals stamped
          in (block.rs:969-978) *)
  | V1_at_boundary
      (** [v1.prog = P2]: the batch-less boundary output [O3] is V1's next
          output *)
  | V2_sealed  (** [v2.sealed]: the peer has executed the epoch-closing block *)
  | V1_saw_peer_vote
      (** [v1_saw_peer_vote]: V1 has received the peer's epoch-record vote and
          matched it against its OWN record digest
          ([vote.epoch_hash == epoch_hash] plus committee membership,
          epoch_votes.rs:88-111) - a signed commitment by the peer to the
          identical closing execution state (close_epoch.rs:236-245) *)
  | V2_restarted
      (** [v2_restarted]: the peer crashed and rebuilt its counter through
          catchup+replay this epoch (node.rs:189-268, start_epoch.rs:71-107) *)
  | V2_double_credit
      (** some counter of [v2.led] is [Two]: the peer credited one committed
          round twice *)
  | Credit_blockless_agrees
      (** [v1.led.l1 = v2.led.l1]: the two nodes hold the same count for the
          blockless round's leader *)
  | Ledgers_equal
      (** [v1.led = v2.led] componentwise: the two nodes hold identical
          per-leader counts, i.e. they would seal identical withdrawals
          (block.rs:969-978) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | V1_consumed_blockless -> phase_consumed_blockless s.v1.prog
  | V1_watermark_zero -> phase_watermark_zero s.v1.prog
  | V1_credited_blockless -> count_is_one s.v1.led.l1
  | V1_sealed -> s.v1.sealed
  | V1_at_boundary -> phase_at_boundary s.v1.prog
  | V2_sealed -> s.v2.sealed
  | V1_saw_peer_vote -> s.v1_saw_peer_vote
  | V2_restarted -> s.v2_restarted
  | V2_double_credit -> ledger_has_double s.v2.led
  | Credit_blockless_agrees -> count_equal s.v1.led.l1 s.v2.led.l1
  | Ledgers_equal -> ledger_equal s.v1.led s.v2.led

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | V1_consumed_blockless -> "v1_consumed_blockless"
  | V1_watermark_zero -> "v1_watermark_zero"
  | V1_credited_blockless -> "v1_credited_blockless"
  | V1_sealed -> "v1_sealed"
  | V1_at_boundary -> "v1_at_boundary"
  | V2_sealed -> "v2_sealed"
  | V1_saw_peer_vote -> "v1_saw_peer_vote"
  | V2_restarted -> "v2_restarted"
  | V2_double_credit -> "v2_double_credit"
  | Credit_blockless_agrees -> "credit_blockless_agrees"
  | Ledgers_equal -> "ledgers_equal"

(** The exact CTLK checker over this family's ordered state and view. *)
module Checker = System.Make (State) (View)

(** The checker spec under a mutation: single initial state,
    mutation-parameterized transitions, the two-node view, the atom
    valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
