(** Finite interpreted system for the BATCH_VERDICT family: the worker's
    batch-seal quorum wait for ONE sealed batch, authored by V0. File citations
    refer to Telcoin-Association/telcoin-network (git HEAD 0c59c15b).

    The modeled mechanism. After [Worker::seal] spawns [verify_batch]
    (worker.rs:287-291), the quorum waiter broadcasts the sealed batch to the
    other committee members and folds their answers
    (quorum_waiter.rs:130-170, 184-244):
    - the committee has 4 authorities of unit voting power
      ([EQUAL_VOTING_POWER] = 1, committee.rs:25, :508; [total_voting_power] =
      [authorities.len()], committee.rs:261-263), so
      [quorum_threshold] = 2*4/3 + 1 = 3 (committee.rs:247-252);
    - the author seeds [total_stake] with its OWN power 1
      (quorum_waiter.rs:167) and [available_stake] with 3, one per peer
      (:148-150);
    - hence [max_rejected_stake] = (3 + 1) - 3 = 1 (:170): a SECOND permanent
      rejection is what breaks [QuorumRejected] at :236-239;
    - each peer answer arrives through [QuorumWaiter::waiter]
      (quorum_waiter.rs:84-116) as exactly one of [Ok(stake)],
      [WaiterError::Rejected(stake)] (a [NetworkError::RPCError], returned with
      NO retry at :94-100) or [WaiterError::Network(stake)] (all
      [MAX_BATCH_REPORT_ATTEMPTS] = 3 attempts exhausted, :91, :115).

    The peer side of one report leg (handler.rs:231-263, called from
    mod.rs:487-503): the responder checks committee membership (:237-239, a
    permanent [NonCommitteeBatch]), runs [validate_batch] (:244-246), writes
    the [NodeBatchesCache] row (:252-254), tells its own primary (:257-260) and
    only THEN returns [Ok] (:262) which mod.rs:490-491 turns into
    [WorkerResponse::ReportBatch]. Failures are classified by
    [WorkerResponse::into_error_ref] (message.rs:125-155): every transient
    responder-side condition ([Internal], [Timeout], [Network], [StreamClosed],
    [DBInsert], [DBCommit], [DBRead], [StdIo]) becomes
    [WorkerResponse::RecoverableError] and every deliberate rejection becomes
    [WorkerResponse::Error]. [WorkerNetworkHandle::report_batch]
    (handle.rs:169-190) then maps [Error] to [NetworkError::RPCError] (:185)
    and [RecoverableError] to [NetworkError::RPCRetryable] (:186-188).

    Components. Three: [leg1] = peer V1's report leg, [leg2] = peer V2's report
    leg, [verdict] = the value the quorum wait returns.

    SCHEDULE RESTRICTION (load-bearing, documented deliberately). The THIRD
    committee peer never answers within the seal timeout: its stake stays in
    [available_stake] and is never decremented, and a wait that could still
    reach quorum ends at the outer [tokio::time::timeout]
    (quorum_waiter.rs:133, 245-250). Pre-resolving that peer would drop
    [available_stake] to 2 and make the anti-quorum check at :241-243 fire on
    the FIRST rejection, rendering [QuorumRejected] unreachable and the
    rejection statement vacuous. A consequence of the restriction is that the
    :220-223 ran-out-of-peers [AntiQuorum] branch never fires here; every
    [AntiQuorum] in this model arises from the :241 stake check.

    Scope cuts, each conservative for every asserted conjunct AND under every
    gate deletion this family pins:
    - [leg2] omits the [Rej_unknown] value (one collapsing pair on [leg1]
      already witnesses the verdict opacity; a second copy would double the
      rejected block without adding a witness);
    - the TWO real causes of a possession-free [WaiterError::Network] are split
      across the two legs instead of being duplicated on both, which keeps the
      reachable set at 47 (R6). [leg1] carries [Exh_transport] - the report
      never reached the peer, or its answer never came back - and [leg2] carries
      [Exh_nopossess] - the peer's own [NodeBatchesCache] insert failed. The
      split is load-bearing, not cosmetic: [Exh_transport] never passes through
      the [RecoverableError] arm of [report_batch] at all, because
      handle.rs:175-176 propagates the [send_request] and response-channel
      errors with [?] BEFORE the [WorkerResponse] match at :177-189 is reached,
      so a dial failure, a dropped connection or an outbound timeout surfaces as
      a NON-[RPCError] [NetworkError] ([Dial], [Outbound], [Timeout],
      [Disconnected], [AckChannelClosed]; error.rs:18-136), lands in the
      catch-all retry arm at quorum_waiter.rs:101-112 and, after
      [MAX_BATCH_REPORT_ATTEMPTS], becomes [WaiterError::Network] at :115 -
      precisely what the doc comment at :72-83 states. [leg1] therefore keeps a
      possession-free exhaustion value under BOTH mutations below.
      (Provenance: an earlier revision of this model folded the transport-loss
      cause out entirely and claimed the fold was conservative. The 2026-07
      adversarial review CONFIRMED it was not: what refuted S1's first conjunct
      under {!No_recoverable_class} was the fold, not the deleted arm. Restoring
      [Exh_transport] on [leg1] is that repair, and S1 is now a negative control
      for {!No_recoverable_class} rather than a pin of it.)

    Role mapping. V0 is the batch AUTHOR and the only knowledge agent: it is the
    sole validator that ever appears under [K]. V1 and V2 are the two modeled
    committee peers and V3 is the third, non-answering peer; all three are idle
    non-agents carrying the constant blank {!View_idle} and never appear under
    [K] - they occur only as SUBJECTS of atoms, because their hidden local state
    is exactly what V0 cannot see.

    What V0's view holds is precisely what the fold at quorum_waiter.rs:186-219
    receives: per modeled peer the waiter-level outcome only, plus the verdict
    the loop broke with. What it CRUCIALLY omits:
    - whether an exhausted leg's peer actually wrote its [NodeBatchesCache] row:
      [WaiterError::Network(deliver)] carries only the stake
      (quorum_waiter.rs:115) and :216-218 discards the error, so
      [Exh_possess], [Exh_nopossess] and [Exh_transport] all project to
      [Saw_exhausted];
    - whether a rejecting leg's peer ran its own [validate_batch] or merely
      failed to identify the requester: [WaiterError::Rejected(deliver)] drops
      the error string at :94-100 and the fold at :212-215 keeps only the stake,
      so [Rej_verdict], [Rej_unknown] (and, under mutation, [Rej_transient]) all
      project to [Saw_reject];
    - whether an accepting peer's row is durable: [Ack_possess] and
      [Ack_nopossess] both project to [Saw_accept], which is exactly why the
      {!No_peer_store_before_ack} mutation is invisible to V0.
    There is no remote-possession oracle either: [get_batch_local_cache] reads
    the LOCAL [NodeBatchesCache] only (batch_fetcher.rs:58-68) and the
    consensus-chain fallback at :52 needs a committed certificate, impossible
    for a batch that never reached quorum. Nothing in the view clocks the retry
    counter or the timeout. *)

(** One committee peer's report leg: the peer's HIDDEN local outcome together
    with the waiter-level outcome the author folds for it. *)
type leg =
  | Pending
      (** no response folded yet: the [qw-peer-i] task
          (quorum_waiter.rs:155-159) is still running *)
  | Ack_possess
      (** handler.rs:244-262 ran to completion - [validate_batch] ok, the
          [NodeBatchesCache] row written (:252-254), the peer's own primary
          told (:257-260) - so [WorkerResponse::ReportBatch] (mod.rs:490-491)
          became [Ok(())] (handle.rs:177-178) and then [Ok(stake)]
          (quorum_waiter.rs:93) *)
  | Ack_nopossess
      (** MUTANT-ONLY ({!No_peer_store_before_ack}): the peer validated and
          acked, but no row exists because the durable write was deleted *)
  | Rej_verdict
      (** the peer ran its OWN committee check (handler.rs:237-239) or
          [validate_batch] (:244-246) and rejected, giving a permanent
          [WorkerResponse::Error] (message.rs:141-153) ->
          [NetworkError::RPCError] (handle.rs:185) -> [WaiterError::Rejected]
          with no retry (quorum_waiter.rs:94-100) *)
  | Rej_unknown
      (** the responding node's network layer could not map the requesting
          [PeerId] to a BLS key (consensus.rs:1149, 1174-1177), so
          [NetworkEvent::Error] became a permanent [WorkerResponse::Error]
          (mod.rs:455-456) -> [RPCError] -> [Rejected]: permanent CLASS, but NO
          batch verdict was ever computed by that peer *)
  | Rej_transient
      (** MUTANT-ONLY ({!No_recoverable_class}): a transient responder-side
          condition answered as permanent and therefore folded as [Rejected] *)
  | Exh_possess
      (** the peer completed handler.rs:244-262 (row written) but every ack was
          lost in transport: three attempts, then [WaiterError::Network]
          (quorum_waiter.rs:91, 101-115) *)
  | Exh_nopossess
      (** the peer's own [store.insert] failed (handler.rs:252-254 ->
          [WorkerNetworkError::Internal]) -> [RecoverableError]
          (message.rs:128-137) -> [RPCRetryable] (handle.rs:186-188) -> retried
          three times -> [WaiterError::Network]; no row exists. Carried by
          [leg2] (see the scope-cut note in the header). *)
  | Exh_transport
      (** the report never got a response out of the peer: [send_request] or the
          response channel failed, so handle.rs:175-176 propagated a
          NON-[RPCError] [NetworkError] ([Dial], [Outbound], [Timeout],
          [Disconnected], [AckChannelClosed]; error.rs:18-136) with [?] before
          the [WorkerResponse] match at :177-189 was ever reached. That error
          lands in the catch-all retry arm (quorum_waiter.rs:101-112) and after
          [MAX_BATCH_REPORT_ATTEMPTS] becomes [WaiterError::Network] (:115). The
          responder never ran handler.rs:252-254, so no row exists. Carried by
          [leg1]; this is the exhaustion value that survives BOTH mutations,
          because neither gate sits on this path. *)

(** Total order index for {!leg}. *)
let leg_index = function
  | Pending -> 0
  | Ack_possess -> 1
  | Ack_nopossess -> 2
  | Rej_verdict -> 3
  | Rej_unknown -> 4
  | Rej_transient -> 5
  | Exh_possess -> 6
  | Exh_nopossess -> 7
  | Exh_transport -> 8

(** Total order on {!leg}. *)
let leg_compare a b = Int.compare (leg_index a) (leg_index b)

(** The author's local record of one leg - ALL the fold at
    quorum_waiter.rs:186-219 retains of a peer answer. *)
type obs =
  | Unseen  (** the per-peer receiver has not yielded yet *)
  | Saw_accept  (** [Ok(stake)] folded at quorum_waiter.rs:187-190 *)
  | Saw_reject  (** [WaiterError::Rejected(stake)] folded at :212-215 *)
  | Saw_exhausted  (** [WaiterError::Network(stake)] folded at :216-218 *)

(** Total order index for {!obs}. *)
let obs_index = function
  | Unseen -> 0
  | Saw_accept -> 1
  | Saw_reject -> 2
  | Saw_exhausted -> 3

(** Total order on {!obs}. *)
let obs_compare a b = Int.compare (obs_index a) (obs_index b)

(** The waiter-level outcome the author folds for a leg: the ONLY thing that
    crosses the network boundary into V0's state. *)
let obs_of_leg = function
  | Pending -> Unseen
  | Ack_possess | Ack_nopossess -> Saw_accept
  | Rej_verdict | Rej_unknown | Rej_transient -> Saw_reject
  | Exh_possess | Exh_nopossess | Exh_transport -> Saw_exhausted

(** [true] iff the author has folded something for this leg, i.e. the peer's
    stake has left [available_stake] (quorum_waiter.rs:189, :214, :217). *)
let obs_is_resolved = function
  | Unseen -> false
  | Saw_accept | Saw_reject | Saw_exhausted -> true

(** [true] iff the fold added the peer's stake to [total_stake] (:188). *)
let obs_is_accept = function
  | Saw_accept -> true
  | Unseen | Saw_reject | Saw_exhausted -> false

(** [true] iff the fold added the peer's stake to [rejected_stake] (:213). *)
let obs_is_reject = function
  | Saw_reject -> true
  | Unseen | Saw_accept | Saw_exhausted -> false

(** The value the quorum wait returns (quorum_waiter.rs:209, :222, :239, :242,
    :250). *)
type verdict =
  | Waiting  (** the loop at :184 has not broken yet *)
  | Quorum  (** [Ok(())] - [total_stake >= threshold] (:190, :209) *)
  | Rejected
      (** [QuorumWaiterError::QuorumRejected] -
          [rejected_stake > max_rejected_stake] (:236-239) *)
  | Anti
      (** [QuorumWaiterError::AntiQuorum] -
          [total_stake + available_stake < threshold] (:241-243) *)
  | Timeout
      (** [QuorumWaiterError::Timeout] - the outer [tokio::time::timeout]
          elapsed (:133, :245-250) *)

(** Total order index for {!verdict}. *)
let verdict_index = function
  | Waiting -> 0
  | Quorum -> 1
  | Rejected -> 2
  | Anti -> 3
  | Timeout -> 4

(** Total order on {!verdict}. *)
let verdict_compare a b = Int.compare (verdict_index a) (verdict_index b)

(** Structural equality on {!verdict}, derived from {!verdict_compare} so no
    polymorphic comparison is used. *)
let verdict_equal a b = Int.equal 0 (verdict_compare a b)

(** The joint global state: the two modeled peer legs and the seal verdict. *)
type state = { leg1 : leg; leg2 : leg; verdict : verdict }

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = leg_compare s1.leg1 s2.leg1 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = leg_compare s1.leg2 s2.leg2 in
    if Bool.not (Int.equal c1 0) then c1 else verdict_compare s1.verdict s2.verdict

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. [View_author] is V0's projection: the
    waiter-level outcome it folded for each of the two modeled peers, plus the
    verdict its seal path returned. [View_idle] is the constant blank view of
    the non-agents V1, V2 and V3. *)
type view = View_author of obs * obs * verdict | View_idle

(** Total deterministic order over ALL fields of the author's view. *)
let view_author_compare (o1, o2, v) (o1', o2', v') =
  let c = obs_compare o1 o1' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = obs_compare o2 o2' in
    if Bool.not (Int.equal c1 0) then c1 else verdict_compare v v'

(** Total order on views: [View_idle] < [View_author], field-wise within the
    constructor. Every cross-constructor arm is spelled: no wildcard on the
    finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_author (_, _, _) -> -1
  | View_author (_, _, _), View_idle -> 1
  | View_author (o1, o2, v), View_author (o1', o2', v') ->
      view_author_compare (o1, o2, v) (o1', o2', v')

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 is the batch author and the ONLY knowledge agent; V1,
    V2 and V3 are idle non-agents with the constant blank view and never appear
    under [K]. *)
let view v s =
  match v with
  | Validator.V0 -> View_author (obs_of_leg s.leg1, obs_of_leg s.leg2, s.verdict)
  | Validator.V1
  | Validator.V2
  | Validator.V3
  | Validator.V4
  | Validator.V5
  | Validator.V6
  | Validator.V7
  | Validator.V8
  | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_peer_store_before_ack
      (** delete the durable write [store.insert::<NodeBatchesCache>(&digest,
          &batch)] at handler.rs:252-254 - the write that precedes the primary
          report (:257-260) and the [Ok] ack (:262). The peer still validates
          and still acks, it merely never takes possession, so every
          [Pending -> Ack_possess] becomes [Pending -> Ack_nopossess] and the
          [Pending -> Exh_possess] resolution disappears; the surviving
          exhaustion values are the possession-free ones ([Exh_transport] on
          [leg1], [Exh_nopossess] on [leg2]), since deleting a write cannot
          create possession anywhere. R4 sibling hunt: a repo-wide
          sweep for [insert::<NodeBatchesCache>] finds exactly four write
          sites, and each of the three siblings is closed on a batch that never
          reached quorum - handler.rs:202-208 is the gossip prefetch, reachable
          only from [WorkerGossip::Batch], and the author publishes that gossip
          at worker.rs:320 which sits INSIDE the quorum-success arm only;
          batch_fetcher.rs:190-196 can only serve a batch some node already
          stored and is itself driven by that same prefetch or by a primary
          sync need; network/primary.rs:104-129 writes only digests the node's
          OWN primary asked it to synchronize ([synchronize], primary.rs:29-62,
          with the write gated on [requested.contains(&digest)] at :114) and
          only batches it FETCHED from a peer that already held them, so it
          cannot create possession that did not already exist somewhere;
          and worker.rs:359 is the AUTHOR's own post-quorum write of its own
          batch, not a peer's. The read side cannot manufacture possession
          either ([get_batch_local_cache] reads [NodeBatchesCache] only,
          batch_fetcher.rs:58-68; the consensus-chain fallback at :52 needs a
          certificate). handler.rs:252 is therefore the SOLE route to peer
          possession on the report path, so nothing repairs the deletion. *)
  | No_recoverable_class
      (** delete the [WorkerResponse::RecoverableError(WorkerRPCError(s)) =>
          Err(NetworkError::RPCRetryable(s))] arm of [report_batch]
          (handle.rs:186-188), folding recoverable responses into the permanent
          [RPCError] arm at :185. A peer's momentary [NodeBatchesCache] write
          failure (handler.rs:252-254 -> [Internal] -> [RecoverableError] at
          message.rs:128-137) then reaches the author as an explicit rejection,
          so every [Pending -> Exh_nopossess] becomes
          [Pending -> Rej_transient], which the fold books as
          [rejected_stake] with no retry (quorum_waiter.rs:94-100, 212-215).
          SCOPE OF THE DELETION - this is the part an earlier revision got
          wrong. The arm sits inside the [WorkerResponse] match at
          handle.rs:177-189, which is reached only when a response actually came
          back: [send_request] and the response channel are unwrapped with [?]
          at :175-176, so every transport failure (dial, dropped connection,
          outbound timeout) bypasses the match altogether and still exhausts
          through the catch-all retry arm at quorum_waiter.rs:101-115. The
          deletion therefore removes ONLY the responder-side store-failure
          cause of a possession-free exhaustion; [Exh_possess] AND
          [Exh_transport] both remain, so an exhausted [leg1] is still
          possession-opaque under this gate. Consequently this mutation does not
          and must not refute S1 - S1 is a negative control for it. R4 sibling
          hunt for what it DOES refute (S3), five routes, none repairs it:
          (a) the retry loop at quorum_waiter.rs:91 with its backoff at
          :108-111 cannot help, because the [RPCError] arm returns at :99
          before any retry; (b) [report_batch] (handle.rs:169) has exactly ONE
          call site in the tree, quorum_waiter.rs:92, so no second reporting
          route re-derives permanence; (c) the responder side is not a repair -
          [into_error_ref] (message.rs:125-155) still labels the condition
          [RecoverableError] and mod.rs:496 still sends it, but with the arm
          gone nothing downstream of handle.rs consults that label; (d) the
          caller side only renames - worker.rs:327-342 maps [QuorumWaiterError]
          to [BlockSealError] and batch-builder lib.rs:199-210 collapses all
          six non-fatal variants into the same empty result; (e) handle.rs
          carries the same [Error]/[RecoverableError] split on the
          batch-request-stream path, which never feeds [rejected_stake]. *)

(** Committee size: 4 authorities, each of unit voting power
    ([EQUAL_VOTING_POWER] = 1, committee.rs:25, :508;
    [total_voting_power] = [authorities.len()], committee.rs:261-263). *)
let committee_size = 4

(** This authority's own stake, the seed of [total_stake]
    (quorum_waiter.rs:167). *)
let own_stake = 1

(** [quorum_threshold] = 2 * N / 3 + 1 = 3 (committee.rs:247-252). *)
let quorum_threshold = ((2 * committee_size) / 3) + 1

(** The stake broadcast to peers, i.e. [available_stake] before any fold
    (quorum_waiter.rs:148-150): every committee member but the author. *)
let broadcast_stake = committee_size - own_stake

(** [max_rejected_stake] = ([available_stake] + [total_stake]) - [threshold]
    = (3 + 1) - 3 = 1 (quorum_waiter.rs:170). *)
let max_rejected_stake = broadcast_stake + own_stake - quorum_threshold

(** [true] iff [a] is strictly below [b]; int-monomorphic, no polymorphic
    comparison. *)
let int_lt a b = Int.compare a b < 0

(** [true] iff [a] is at least [b]; int-monomorphic. *)
let int_ge a b = Bool.not (int_lt a b)

(** [true] iff [a] is strictly above [b]; int-monomorphic. *)
let int_gt a b = int_lt b a

(** Count how many of the two modeled legs' observations satisfy [p]. *)
let tally p o1 o2 = (if p o1 then 1 else 0) + if p o2 then 1 else 0

(** The verdict the wait would break with given the two folded legs, computed
    exactly as the loop at quorum_waiter.rs:187-243 does with the third peer
    still outstanding: [total_stake] = own seed + accepted stake (:167, :188),
    [available_stake] = broadcast stake minus every resolved leg (:148-150,
    :189, :214, :217), then the quorum test (:190, :209), the rejection test
    (:236-239) and the anti-quorum test (:241-243) in the code's own order.
    The quorum test legitimately precedes the rejection test even though the
    code's quorum break sits inside the [Ok] arm at :190: reaching the
    threshold needs both modeled legs accepted, which forces zero rejections. *)
let verdict_of l1 l2 =
  let o1 = obs_of_leg l1 in
  let o2 = obs_of_leg l2 in
  let resolved = tally obs_is_resolved o1 o2 in
  let accepts = tally obs_is_accept o1 o2 in
  let rejects = tally obs_is_reject o1 o2 in
  let total = own_stake + accepts in
  let available = broadcast_stake - resolved in
  if int_ge total quorum_threshold then Quorum
  else if int_gt rejects max_rejected_stake then Rejected
  else if int_lt (total + available) quorum_threshold then Anti
  else Waiting

(** The values V1's leg can resolve to under a mutation. [leg1] is the leg that
    carries the TRANSPORT cause of exhaustion (see the header's scope-cut note):
    pristine it can accept-with-possession, reject on its own verdict, reject
    because its network layer could not identify the requester, exhaust after a
    successful store, or exhaust because the report never got through.
    {!No_peer_store_before_ack} deletes handler.rs:252-254, so the accept loses
    possession and [Exh_possess] disappears - but [Exh_transport] SURVIVES,
    because a report that never reached the peer never depended on the deleted
    write. {!No_recoverable_class} deletes handle.rs:186-188, which no [leg1]
    value passes through: [Exh_transport] is produced by the [?] at
    handle.rs:175-176, upstream of the [WorkerResponse] match entirely, so this
    leg is UNCHANGED under that gate. That invariance is deliberate - it is what
    keeps S1's first conjunct pinned on the real system rather than on the
    abstraction. *)
let leg1_resolutions mut =
  match mut with
  | Pristine -> [ Ack_possess; Rej_verdict; Rej_unknown; Exh_possess; Exh_transport ]
  | No_peer_store_before_ack -> [ Ack_nopossess; Rej_verdict; Rej_unknown; Exh_transport ]
  | No_recoverable_class -> [ Ack_possess; Rej_verdict; Rej_unknown; Exh_possess; Exh_transport ]

(** The values V2's leg can resolve to under a mutation. [leg2] carries the
    RESPONDER-STORE-FAILURE cause of exhaustion and omits [Rej_unknown] (both
    documented scope cuts: one collapsing rejection pair on [leg1] already
    witnesses the verdict opacity). {!No_peer_store_before_ack} strips
    possession from the accept and removes [Exh_possess];
    {!No_recoverable_class} turns the responder-side store failure into an
    explicit, no-retry rejection ([Exh_nopossess] -> [Rej_transient]), which is
    the reclassification S3 is pinned on: one such leg alongside a genuine
    permanent rejection already reaches [rejected_stake] = 2 >
    [max_rejected_stake] = 1 (quorum_waiter.rs:170, 236-239). *)
let leg2_resolutions mut =
  match mut with
  | Pristine -> [ Ack_possess; Rej_verdict; Exh_possess; Exh_nopossess ]
  | No_peer_store_before_ack -> [ Ack_nopossess; Rej_verdict; Exh_nopossess ]
  | No_recoverable_class -> [ Ack_possess; Rej_verdict; Exh_possess; Rej_transient ]

(** V1's leg resolving: one [qw-peer] receiver yields (quorum_waiter.rs:185)
    and the fold recomputes the verdict. A leg already folded has no move -
    each per-peer receiver yields exactly once. *)
let resolve_leg1 mut s =
  match s.leg1 with
  | Pending ->
      List.map
        (fun l -> { leg1 = l; leg2 = s.leg2; verdict = verdict_of l s.leg2 })
        (leg1_resolutions mut)
  | Ack_possess | Ack_nopossess | Rej_verdict | Rej_unknown | Rej_transient
  | Exh_possess | Exh_nopossess | Exh_transport ->
      []

(** V2's leg resolving, symmetric to {!resolve_leg1}. *)
let resolve_leg2 mut s =
  match s.leg2 with
  | Pending ->
      List.map
        (fun l -> { leg1 = s.leg1; leg2 = l; verdict = verdict_of s.leg1 l })
        (leg2_resolutions mut)
  | Ack_possess | Ack_nopossess | Rej_verdict | Rej_unknown | Rej_transient
  | Exh_possess | Exh_nopossess | Exh_transport ->
      []

(** The transition relation. While the wait is [Waiting], either outstanding
    leg may resolve, and the outer [tokio::time::timeout]
    (quorum_waiter.rs:133, 245-250) may fire - that last move is enabled at
    EVERY [Waiting] state, so no [Waiting] state is terminal and the third,
    never-answering peer's stake simply stays in [available_stake]. Once the
    seal path has returned (worker.rs:302-352) nothing more happens and the
    kernel stutter-closes the terminal. *)
let next_with mut s =
  match s.verdict with
  | Quorum | Rejected | Anti | Timeout -> []
  | Waiting ->
      List.concat
        [
          resolve_leg1 mut s;
          resolve_leg2 mut s;
          [ { leg1 = s.leg1; leg2 = s.leg2; verdict = Timeout } ];
        ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: [verify_batch] has been spawned and the per-peer report
    tasks are in flight (quorum_waiter.rs:130, 148-161), the author has folded
    nothing, and the loop at :184 has not broken. Single initial state. *)
let initial = { leg1 = Pending; leg2 = Pending; verdict = Waiting }

(** [true] iff the peer holds a [NodeBatchesCache] row for this digest, i.e.
    handler.rs:252-254 completed on that node. *)
let leg_holds_batch = function
  | Ack_possess | Exh_possess -> true
  | Pending | Ack_nopossess | Rej_verdict | Rej_unknown | Rej_transient
  | Exh_nopossess | Exh_transport ->
      false

(** [true] iff the author folded [Ok(stake)] for this leg
    (quorum_waiter.rs:93, :187). *)
let leg_is_accept = function
  | Ack_possess | Ack_nopossess -> true
  | Pending | Rej_verdict | Rej_unknown | Rej_transient | Exh_possess
  | Exh_nopossess | Exh_transport ->
      false

(** [true] iff the author folded [WaiterError::Network] for this leg after
    [MAX_BATCH_REPORT_ATTEMPTS] (quorum_waiter.rs:91, :115, :216-218). *)
let leg_is_exhausted = function
  | Exh_possess | Exh_nopossess | Exh_transport -> true
  | Pending | Ack_possess | Ack_nopossess | Rej_verdict | Rej_unknown
  | Rej_transient ->
      false

(** [true] iff the peer's answer really was a permanent application-level
    error - a [WorkerResponse::Error] (message.rs:141-153 or mod.rs:455-456)
    mapped to [NetworkError::RPCError] at handle.rs:185. [Rej_transient] is
    excluded: under {!No_recoverable_class} the condition behind it is
    transient and only the deleted arm made it look permanent. *)
let leg_is_permanent_reject = function
  | Rej_verdict | Rej_unknown -> true
  | Pending | Ack_possess | Ack_nopossess | Rej_transient | Exh_possess
  | Exh_nopossess | Exh_transport ->
      false

(** [true] iff the peer itself computed a batch verdict and rejected - its own
    committee check (handler.rs:237-239) or [validate_batch] (:244-246,
    validator.rs). *)
let leg_is_local_verdict = function
  | Rej_verdict -> true
  | Pending | Ack_possess | Ack_nopossess | Rej_unknown | Rej_transient
  | Exh_possess | Exh_nopossess | Exh_transport ->
      false

(** [true] iff the peer's permanent error came from its network layer failing
    to map the requester to a BLS key (consensus.rs:1149, 1174-1177 ->
    mod.rs:455-456), so no batch verdict was computed at all. *)
let leg_is_unknown_requester = function
  | Rej_unknown -> true
  | Pending | Ack_possess | Ack_nopossess | Rej_verdict | Rej_transient
  | Exh_possess | Exh_nopossess | Exh_transport ->
      false

(** The atom vocabulary this family's statements quantify over. Author-side
    atoms ([Verdict_*], [Accepted_v1], [Exhausted_v1]) are components of V0's
    view; peer-side atoms ([Holds_*], [Permanent_reject_*], [Local_verdict_v1],
    [Unknown_requester_v1]) are hidden remote state and are exactly the ones
    that appear under [K]. *)
type atom =
  | Verdict_quorum
      (** the quorum wait returned [Ok(())] (quorum_waiter.rs:190, :209) *)
  | Verdict_rejected
      (** [QuorumWaiterError::QuorumRejected] (quorum_waiter.rs:236-239) *)
  | Verdict_anti  (** [QuorumWaiterError::AntiQuorum] (quorum_waiter.rs:241-243) *)
  | Accepted_v1
      (** the author folded [Ok(stake)] for V1 (quorum_waiter.rs:93, :187) *)
  | Exhausted_v1
      (** the author folded [WaiterError::Network] for V1 after
          [MAX_BATCH_REPORT_ATTEMPTS] (quorum_waiter.rs:91, :115, :216-218) *)
  | Holds_v1
      (** V1 has a [NodeBatchesCache] row for this digest
          (handler.rs:252-254) *)
  | Holds_v2  (** likewise for V2 *)
  | Permanent_reject_v1
      (** V1's response was a permanent application-level error
          ([WorkerResponse::Error] -> [NetworkError::RPCError],
          message.rs:141-153, mod.rs:455-456, handle.rs:185) *)
  | Permanent_reject_v2  (** likewise for V2 *)
  | Local_verdict_v1
      (** V1 actually ran its own committee check / [validate_batch] and
          rejected (handler.rs:237-246) *)
  | Unknown_requester_v1
      (** V1's permanent error came from its network layer failing to map the
          requester, so no batch verdict was computed (consensus.rs:1174-1177,
          mod.rs:455-456) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Verdict_quorum -> verdict_equal s.verdict Quorum
  | Verdict_rejected -> verdict_equal s.verdict Rejected
  | Verdict_anti -> verdict_equal s.verdict Anti
  | Accepted_v1 -> leg_is_accept s.leg1
  | Exhausted_v1 -> leg_is_exhausted s.leg1
  | Holds_v1 -> leg_holds_batch s.leg1
  | Holds_v2 -> leg_holds_batch s.leg2
  | Permanent_reject_v1 -> leg_is_permanent_reject s.leg1
  | Permanent_reject_v2 -> leg_is_permanent_reject s.leg2
  | Local_verdict_v1 -> leg_is_local_verdict s.leg1
  | Unknown_requester_v1 -> leg_is_unknown_requester s.leg1

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Verdict_quorum -> "verdict=quorum"
  | Verdict_rejected -> "verdict=quorum_rejected"
  | Verdict_anti -> "verdict=anti_quorum"
  | Accepted_v1 -> "accepted(V1)"
  | Exhausted_v1 -> "exhausted(V1)"
  | Holds_v1 -> "holds(V1)"
  | Holds_v2 -> "holds(V2)"
  | Permanent_reject_v1 -> "permanent_reject(V1)"
  | Permanent_reject_v2 -> "permanent_reject(V2)"
  | Local_verdict_v1 -> "local_verdict(V1)"
  | Unknown_requester_v1 -> "unknown_requester(V1)"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: single initial state, mutation-
    parameterized transitions, the author-only view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
