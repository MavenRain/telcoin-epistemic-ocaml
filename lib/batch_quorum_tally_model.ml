(** The BATCH_QUORUM_TALLY family: ONE [QuorumWaiter::verify_batch] attempt by a
    batch author over the 4-member committee of {!Validator} (f = 1, quorum
    threshold 2f+1 = 3, every identity worth exactly one unit of voting power).

    Mechanism, all citations opened in telcoin-network at git 0c59c15b:

    - the broadcast fan-out. [crates/consensus/worker/src/quorum_waiter.rs:136-137]
      takes [inner.committee.others_keys_except(inner.authority.protocol_key())]
      - by [crates/types/src/committee.rs:561-573] every authority whose protocol
        key differs from the author, so exactly n-1 = 3 distinct keys - and
      [quorum_waiter.rs:148-161] spawns one independent report task per peer,
      accumulating [available_stake] as it goes (:150). There is NO [.await]
      anywhere between :148 and :161, so the enclosing
      [tokio::time::timeout] (:133) cannot interrupt the loop: dispatch either
      does not start or completes in full. That is why the model's dispatch
      prefix is a straight-line chain and [Af whole_committee_offered] is an
      honest inevitability rather than a scheduling assumption.
    - the per-peer classification. A responder's momentary batch-store write
      failure becomes [WorkerNetworkError::Internal]
      ([network/handler.rs:252-254]); [WorkerResponse::into_error_ref]
      ([network/message.rs:125-155]) routes it, with [Timeout], [Network],
      [StreamClosed], [DBInsert], [DBCommit], [DBRead] and [StdIo], to
      [RecoverableError] (:128-137), while [Bcs], [BatchValidation],
      [NonCommitteeBatch], [InvalidRequest], [InvalidTopic], [TooManyBatches],
      [UnexpectedBatch], [DuplicateBatch], [UnknownStreamRequest],
      [RequestHashMismatch] and [BatchEpochMismatch] stay a permanent [Error]
      (:138-153). The requester maps the two apart at
      [network/handle.rs:185-188]: permanent -> [NetworkError::RPCError],
      recoverable -> [NetworkError::RPCRetryable].
    - the per-peer retry. [quorum_waiter.rs:91-116] retries up to
      [MAX_BATCH_REPORT_ATTEMPTS] = 3 (:16) with backoff on EVERY error except
      [RPCError], which returns [WaiterError::Rejected] immediately (:94-100);
      exhausted retries return [WaiterError::Network] (:115).
    - the tally. [quorum_waiter.rs:166-170] sets [threshold =
      committee.quorum_threshold()] (= 3, committee.rs:243/:247-252),
      [total_stake = authority.voting_power()] (the author's own vote, = 1 by
      [Authority::voting_power] at committee.rs:170-172) and
      [max_rejected_stake = (available_stake + total_stake) - threshold] =
      (3 + 1) - 3 = 1. The wait loop (:184-244)
      credits an ack (:187-190), charges a rejection (:212-215) and only
      decrements availability on a network outcome (:216-218), then breaks
      [Ok] at :190, [QuorumRejected] at :236-240 and [AntiQuorum] at :241-243
      (or at :220-223 when the peer stream is exhausted).

    Components: [offered] (how far the fan-out loop has got), the reply [tally]
    of the six resolutions one peer task can have, and the two running totals
    [total_stake] / [rejected_stake] the loop carries, collapsed into the
    [outcome] the loop breaks with.

    WHY A MULTISET AND NOT PER-IDENTITY LEGS. Voting power is equal for every
    committee member ([EQUAL_VOTING_POWER = 1], committee.rs:25, returned for
    any member by committee.rs:507-509) and the loop's decision function reads
    ONLY the three stake sums, so peer identity is not an input to any decision
    the mechanism makes. The state is therefore the multiset of resolutions, and
    the equal-weight fact that licenses the abstraction is itself conjunct (B)
    of S3. This keeps the model at 54 reachable states instead of 178.

    ROLE MAPPING. V0 is the batch author and the only knowledge agent. Its view
    is what the wait loop actually holds: how many peers it dispatched to, and
    the per-class counts of the [Result<VotingPower, WaiterError>] values it has
    consumed - acks, permanent rejections, unavailabilities - plus its own
    [outcome]. It is exactly this coarse because [Self::waiter]
    (quorum_waiter.rs:84-116) collapses every non-[RPCError] outcome into
    [WaiterError::Network] before the loop ever sees it: a peer that answered
    [RecoverableError] three times and a peer that was simply unreachable are
    the same value at :216. HIDDEN from V0: whether a rejection was an honest
    validation/committee-view refusal or a Byzantine one, whether an
    unavailability was a real store fault or a Byzantine peer fabricating the
    same recoverable reply, and whether an ack cost the peer a retry. V1, V2 and
    V3 are the recipients; because the model is a multiset over their identities
    they carry the constant blank view {!View_idle} and never appear under [K].

    DISCLOSED, NOT CLAIMED. Downstream, [QuorumRejected] and [AntiQuorum] are
    treated identically: crates/batch-builder/src/lib.rs:194-211 collapses
    [QuorumRejected | AntiQuorum | Timeout | NotValidator | FailedToReport |
    FailedQuorum] into an empty mined set, leaving the transactions in the pool
    for a later batch. Every statement here is therefore about the verdict of
    ONE attempt and the author's knowledge at it, never about transaction loss.
    The [Timeout] arm (:133, :250) is likewise outside the model: it produces
    [QuorumWaiterError::Timeout], never [QuorumRejected], so it cannot witness
    against any conjunct below. *)

(** The committee's quorum threshold 2f+1. [Committee::quorum_threshold]
    (crates/types/src/committee.rs:516-518) returns the value
    [calculate_quorum_threshold] fixed at :243, [2 * total_votes / 3 + 1]
    (:247-252) - with the free twin [quorum_threshold(committee_members)] at
    :684-688 - which is [2 * 4 / 3 + 1 = 3] for a 4-member committee of
    equal-power authorities. *)
let threshold = 3

(** The size of the pristine broadcast set: every committee member except the
    author, [n - 1 = 3] (quorum_waiter.rs:136-137 through
    [Committee::others_keys_except], committee.rs:561-573). *)
let full_fanout = 3

(** What one dispatched peer's report task finally resolved to. Each value is a
    complete run of [Self::waiter] (quorum_waiter.rs:84-116) for that peer. *)
type cause =
  | Ack
      (** the peer validated and stored the batch on the first attempt
          (handler.rs:231-262) and answered [WorkerResponse::ReportBatch], so
          the waiter returns [Ok(deliver)] (quorum_waiter.rs:93). *)
  | Store_fault_then_ack
      (** the peer's [store.insert::<NodeBatchesCache>] failed on the first
          attempt (handler.rs:252-254 -> [Internal] -> [RecoverableError],
          message.rs:128-137), the requester turned it into
          [NetworkError::RPCRetryable] (handle.rs:186-188), the waiter's retry
          arm (:101-113) slept and re-sent, and the second attempt succeeded.
          Indistinguishable from {!Ack} at the tally: both are [Ok(deliver)]. *)
  | Reject_honest
      (** an honest peer permanently refused: its committee view does not
          contain the author (handler.rs:237-239, [NonCommitteeBatch]), its
          [validate_batch] failed (:244-246), or the epoch did not match
          (message.rs:151, [BatchEpochMismatch]). All are permanent [Error] ->
          [RPCError] -> [WaiterError::Rejected] with no retry (:94-100). Honest
          peers can disagree here: the committee/epoch view is per-peer. *)
  | Reject_byzantine
      (** a corrupt peer sends the same permanent refusal for no honest reason.
          Byte-identical to {!Reject_honest} on the wire. *)
  | Stall_store_fault
      (** an honest peer's store write kept failing: [RecoverableError] on all
          [MAX_BATCH_REPORT_ATTEMPTS] = 3 attempts (quorum_waiter.rs:16, :91),
          so the waiter falls out of the loop with [WaiterError::Network]
          (:115), which only decrements availability (:216-218). *)
  | Stall_byzantine
      (** a corrupt peer fabricates the same recoverable reply on every
          attempt: it withholds its ack while staying out of the rejecters set,
          and its store never failed because it never stored anything. *)

(** The author's running reply tally: how many of the dispatched peer tasks have
    resolved each way. This is the multiset the loop's stake sums read. *)
type tally = {
  acked : int;  (** {!Ack} resolutions *)
  acked_after_retry : int;  (** {!Store_fault_then_ack} resolutions *)
  rejected_honest : int;  (** {!Reject_honest} resolutions *)
  rejected_byzantine : int;  (** {!Reject_byzantine} resolutions *)
  stalled_store_fault : int;  (** {!Stall_store_fault} resolutions *)
  stalled_byzantine : int;  (** {!Stall_byzantine} resolutions *)
}

(** Total deterministic comparison over ALL tally fields. *)
let tally_compare t1 t2 =
  let ca = Int.compare t1.acked t2.acked in
  if Bool.not (Int.equal ca 0) then ca
  else
    let cb = Int.compare t1.acked_after_retry t2.acked_after_retry in
    if Bool.not (Int.equal cb 0) then cb
    else
      let cc = Int.compare t1.rejected_honest t2.rejected_honest in
      if Bool.not (Int.equal cc 0) then cc
      else
        let cd = Int.compare t1.rejected_byzantine t2.rejected_byzantine in
        if Bool.not (Int.equal cd 0) then cd
        else
          let ce = Int.compare t1.stalled_store_fault t2.stalled_store_fault in
          if Bool.not (Int.equal ce 0) then ce
          else Int.compare t1.stalled_byzantine t2.stalled_byzantine

(** The empty tally: no peer task has resolved yet. *)
let no_replies =
  {
    acked = 0;
    acked_after_retry = 0;
    rejected_honest = 0;
    rejected_byzantine = 0;
    stalled_store_fault = 0;
    stalled_byzantine = 0;
  }

(** How many dispatched peer tasks have resolved. *)
let resolved t =
  t.acked + t.acked_after_retry + t.rejected_honest + t.rejected_byzantine
  + t.stalled_store_fault + t.stalled_byzantine

(** Acks the author has consumed: [Ok(deliver)] at quorum_waiter.rs:187. *)
let ack_replies t = t.acked + t.acked_after_retry

(** Permanent-error replies: [WaiterError::Rejected] at quorum_waiter.rs:212. *)
let rejection_replies t = t.rejected_honest + t.rejected_byzantine

(** Unavailability outcomes: [WaiterError::Network] at quorum_waiter.rs:216. *)
let unavailable_replies t = t.stalled_store_fault + t.stalled_byzantine

(** Peer resolutions that only a corrupt identity can produce. Capped at one by
    {!admissible_causes}: f = 1, so at most one committee member deviates. A
    corrupt peer that behaves honestly is folded into the honest causes, which
    is sound because it is observationally identical. *)
let byzantine_acts t = t.rejected_byzantine + t.stalled_byzantine

(** The value the wait loop (quorum_waiter.rs:184-244) breaks with. *)
type verdict =
  | Undecided  (** the loop is still awaiting responses *)
  | Reached_quorum  (** [break Ok(())] at :209, guarded by :190 *)
  | Rejected_by_quorum  (** [QuorumWaiterError::QuorumRejected] at :236-240 *)
  | Anti_quorum  (** [QuorumWaiterError::AntiQuorum] at :220-223 or :241-243 *)

(** Total order index for {!verdict}. *)
let verdict_index = function
  | Undecided -> 0
  | Reached_quorum -> 1
  | Rejected_by_quorum -> 2
  | Anti_quorum -> 3

(** Total order on {!verdict}. *)
let verdict_compare a b = Int.compare (verdict_index a) (verdict_index b)

(** Equality on {!verdict}, via its total order. *)
let verdict_equal a b = Int.equal 0 (verdict_compare a b)

(** The joint global state of one seal attempt. [available_stake] is NOT stored:
    it is exactly [offered - resolved replies] at every reachable state, because
    :150 raises it once per dispatch and each of :189, :214 and :217 lowers it
    once per resolution. *)
type state = {
  offered : int;
      (** how many peers the fan-out loop (:148-161) has spawned a task for *)
  replies : tally;  (** the resolutions consumed so far *)
  total_stake : int;
      (** the loop's [total_stake], seeded with the author's own voting power
          at :167 and raised at :188 *)
  rejected_stake : int;  (** the loop's [rejected_stake], raised at :213 *)
  outcome : verdict;  (** the value the loop has broken with, if any *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let ca = Int.compare s1.offered s2.offered in
  if Bool.not (Int.equal ca 0) then ca
  else
    let cb = tally_compare s1.replies s2.replies in
    if Bool.not (Int.equal cb 0) then cb
    else
      let cc = Int.compare s1.total_stake s2.total_stake in
      if Bool.not (Int.equal cc 0) then cc
      else
        let cd = Int.compare s1.rejected_stake s2.rejected_stake in
        if Bool.not (Int.equal cd 0) then cd
        else verdict_compare s1.outcome s2.outcome

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** The loop's [available_stake]: the stake of the peers still outstanding, and
    equally the number of dispatched tasks that have not resolved. *)
let available_stake s = s.offered - resolved s.replies

(** A validator's local view.

    [View_author] is V0's: the size of its own broadcast set and the per-class
    counts it has consumed - acks, permanent rejections, unavailabilities -
    together with its own [outcome]. It does NOT carry the honest/Byzantine
    split of a rejection, the store-fault/fabrication split of an
    unavailability, or the retry cost of an ack: {!cause} values that differ
    only in those respects produce the same view.

    [View_idle] is the constant blank view of the three recipients: the model is
    a multiset over their identities, so they hold no distinguishing local
    state here and never appear under [K]. *)
type view =
  | View_author of int * int * int * int * verdict
      (** the author's view: [(offered, acks, permanent rejections,
          unavailabilities, own verdict)] *)
  | View_idle  (** the constant blank view of the non-agents V1..V9 *)

(** Total order on the author's view tuple. *)
let author_view_compare (o1, a1, r1, u1, v1) (o2, a2, r2, u2, v2) =
  let ca = Int.compare o1 o2 in
  if Bool.not (Int.equal ca 0) then ca
  else
    let cb = Int.compare a1 a2 in
    if Bool.not (Int.equal cb 0) then cb
    else
      let cc = Int.compare r1 r2 in
      if Bool.not (Int.equal cc 0) then cc
      else
        let cd = Int.compare u1 u2 in
        if Bool.not (Int.equal cd 0) then cd else verdict_compare v1 v2

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_author _ -> -1
  | View_author _, View_idle -> 1
  | View_author (o1, a1, r1, u1, v1), View_author (o2, a2, r2, u2, v2) ->
      author_view_compare (o1, a1, r1, u1, v1) (o2, a2, r2, u2, v2)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 is the batch author and the only knowledge agent; V1, V2
    and V3 are the three recipients of the fan-out and are idle non-agents with
    the constant blank view. {!Validator} carries ten identities because
    {!Tn_model} runs a ten-member committee; the committee this family abstracts
    has four members, so V4..V9 are outside it and idle as well. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_author
        ( s.offered,
          ack_replies s.replies,
          rejection_replies s.replies,
          unavailable_replies s.replies,
          s.outcome )
  | Validator.V1 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the mechanism as written *)
  | No_author_self_credit
      (** delete the author's own vote from the rejection budget at
          crates/consensus/worker/src/quorum_waiter.rs:170, i.e. replace
          [let max_rejected_stake = (available_stake + total_stake) - threshold]
          with [available_stake - threshold]. The budget falls from 1 to 0, so
          the FIRST permanent rejection satisfies [rejected_stake >
          max_rejected_stake] at :236 and the attempt breaks [QuorumRejected]:
          the transition [one rejection -> Rejected_by_quorum] is added. No
          sibling path re-imposes "two rejections": the exhausted-peer exit
          (:220-223) is a failure exit that needs every task resolved, the
          availability exit (:241-243) is not tripped by a single rejection
          (1 + 2 >= 3), and the success test at :190 can only pre-empt when two
          acks are scheduled first, which is schedule-dependence rather than a
          repair. [total_stake]'s own seed at :167 is untouched, so quorum still
          works and the deletion is surgical. *)
  | No_recoverable_class
      (** delete the [Self::RecoverableError(...)] arm at
          crates/consensus/worker/src/network/message.rs:135-137 so the
          transient responder-side conditions fall through to [Self::Error].
          A momentary batch-store write failure (handler.rs:252-254) then
          arrives as [NetworkError::RPCError] (handle.rs:185) and hits the
          no-retry rejection arm at quorum_waiter.rs:94-100, so
          {!Store_fault_then_ack}, {!Stall_store_fault} and {!Stall_byzantine}
          all charge [rejected_stake] instead of merely lowering availability.
          THE RETRY LOOP DOES NOT REPAIR IT: :101-113 retries every error EXCEPT
          [RPCError], which is precisely the arm the deletion routes into - that
          is why {!Store_fault_then_ack}, the resolution the retry rescues in
          the pristine model, becomes a rejection here too. Nor is there a
          second producer of the class: [WorkerResponse::into_error_ref]
          (message.rs:125-155) is the only worker-side classifier, called from
          network/mod.rs:496 and :602 and nowhere else. *)
  | Truncated_fanout
      (** truncate the broadcast set at
          crates/consensus/worker/src/quorum_waiter.rs:136-137 to the first
          [threshold - 1] = 2 peers. Because [others_keys_except]
          (committee.rs:561-573) walks a keyed map in a deterministic order the
          SAME identity is dropped on every attempt, so the dispatch chain stops
          at [offered = 2] and [whole_committee_offered] is never reached. The
          one real sibling repairs POSSESSION, not ack-eligibility: after quorum
          the author gossips the digest (worker.rs:316-320) and a peer missing
          the batch prefetches it (network/handler.rs:167-192), which the model
          grants in its most generous form as
          {!Gossip_holder_without_ack_eligibility}; but only an inbound
          [ReportBatch] produces the [WorkerResponse::ReportBatch] the waiter
          counts (handle.rs:169-190, whose single caller is quorum_waiter.rs:92),
          so a prefetching peer can never contribute stake. *)

(** The broadcast set size under a mutation. *)
let fanout_size mut =
  match mut with
  | Pristine | No_author_self_credit | No_recoverable_class -> full_fanout
  | Truncated_fanout -> threshold - 1

(** The rejection budget of quorum_waiter.rs:170, computed once from the
    post-dispatch [available_stake] - which is [offered], since {!decide} only
    ever runs after the fan-out loop has finished. *)
let max_rejected_stake mut s =
  match mut with
  | Pristine | No_recoverable_class | Truncated_fanout ->
      s.offered + 1 - threshold
  | No_author_self_credit -> s.offered - threshold

(** Does this resolution credit [total_stake] (quorum_waiter.rs:188)? *)
let credits_total mut c =
  match c with
  | Ack -> true
  | Store_fault_then_ack -> (
      match mut with
      | Pristine | No_author_self_credit | Truncated_fanout -> true
      | No_recoverable_class -> false)
  | Reject_honest | Reject_byzantine | Stall_store_fault | Stall_byzantine ->
      false

(** Does this resolution charge [rejected_stake] (quorum_waiter.rs:213)? *)
let charges_rejection mut c =
  match c with
  | Ack -> false
  | Reject_honest | Reject_byzantine -> true
  | Store_fault_then_ack | Stall_store_fault | Stall_byzantine -> (
      match mut with
      | Pristine | No_author_self_credit | Truncated_fanout -> false
      | No_recoverable_class -> true)

(** Record one resolved peer task in the tally. *)
let bump c t =
  match c with
  | Ack -> { t with acked = t.acked + 1 }
  | Store_fault_then_ack ->
      { t with acked_after_retry = t.acked_after_retry + 1 }
  | Reject_honest -> { t with rejected_honest = t.rejected_honest + 1 }
  | Reject_byzantine ->
      { t with rejected_byzantine = t.rejected_byzantine + 1 }
  | Stall_store_fault ->
      { t with stalled_store_fault = t.stalled_store_fault + 1 }
  | Stall_byzantine -> { t with stalled_byzantine = t.stalled_byzantine + 1 }

(** The decision the loop takes after consuming one response, in the order the
    code takes it: the quorum test at :190 (which lives in the [Ok] arm, but
    [total_stake] can only rise there, so testing it after every response is
    equivalent), then the rejection-budget test at :236-240, then the
    availability test at :241-243, then the exhausted-peer exit at :220-223.
    That last arm is provably dead for a 4-member committee - with
    [available_stake = 0] the availability test has already fired unless two
    acks landed, and two acks break [Ok] - and is kept only for faithfulness. *)
let decide mut s =
  if threshold <= s.total_stake then Reached_quorum
  else if max_rejected_stake mut s < s.rejected_stake then Rejected_by_quorum
  else if s.total_stake + available_stake s < threshold then Anti_quorum
  else if Int.equal 0 (available_stake s) then Anti_quorum
  else Undecided

(** The resolutions one more peer task may take. The two Byzantine causes are
    offered only while no Byzantine act has happened yet: f = 1, so at most one
    committee member deviates from honest behaviour. *)
let admissible_causes s =
  let honest = [ Ack; Store_fault_then_ack; Reject_honest; Stall_store_fault ] in
  if Int.equal 0 (byzantine_acts s.replies) then
    honest @ [ Reject_byzantine; Stall_byzantine ]
  else honest

(** Consume one peer response: move the running totals and re-decide. *)
let resolve mut s c =
  let stepped =
    {
      s with
      replies = bump c s.replies;
      total_stake =
        (if credits_total mut c then s.total_stake + 1 else s.total_stake);
      rejected_stake =
        (if charges_rejection mut c then s.rejected_stake + 1
         else s.rejected_stake);
    }
  in
  { stepped with outcome = decide mut stepped }

(** Spawn the report task for one more peer (quorum_waiter.rs:148-161). *)
let dispatch s = { s with offered = s.offered + 1 }

(** The transition relation: the fan-out loop runs to completion first - it
    contains no [.await], so nothing can interleave with it - and then the wait
    loop consumes one response at a time in any order ([FuturesUnordered]
    completion order, :140-142, :185). A decided loop has broken and stutters. *)
let next_with mut s =
  if Bool.not (verdict_equal Undecided s.outcome) then []
  else if s.offered < fanout_size mut then [ dispatch s ]
  else if 0 < available_stake s then List.map (resolve mut s) (admissible_causes s)
  else []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: nothing dispatched, nothing consumed, and [total_stake]
    already seeded with the author's own voting power (quorum_waiter.rs:167,
    [Authority::voting_power] at committee.rs:170-172, which is
    [EQUAL_VOTING_POWER = 1] at committee.rs:25). The seed is assigned after the
    fan-out loop in the real code, but nothing reads it before, so seeding it at
    the initial state is equivalent. *)
let initial =
  {
    offered = 0;
    replies = no_replies;
    total_stake = 1;
    rejected_stake = 0;
    outcome = Undecided;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Quorum_reached  (** verdict(b) = Ok: [break Ok(())] at :190/:209 *)
  | Permanently_rejected  (** verdict(b) = QuorumRejected (:236-240) *)
  | Anti_quorum_reached  (** verdict(b) = AntiQuorum (:220-223, :241-243) *)
  | Two_rejecting_peers
      (** |rejecters(b)| >= 2: at least two peers answered a permanent error *)
  | Honest_rejecter
      (** some rejecter rejected for an honest reason (committee view, batch
          validation, epoch) - hidden from the author *)
  | Byzantine_rejecter
      (** some rejecter is the corrupt identity - hidden from the author *)
  | Store_write_failed
      (** some peer's [store.insert::<NodeBatchesCache>] really failed
          (handler.rs:252-254), whether or not a retry later rescued it *)
  | Non_rejection_charged
      (** [rejected_stake] exceeds the number of permanent-error replies: some
          resolution that was not an explicit rejection has been charged to the
          rejection budget *)
  | No_peer_rejected  (** no peer answered a permanent error at all *)
  | Whole_committee_offered
      (** the fan-out reached all n-1 = 3 committee peers (:136-137) *)
  | Two_peer_acks  (** at least two peers contributed their unit of stake *)
  | One_unavailable_peer
      (** exactly one peer resolved to [WaiterError::Network] (:216-218) *)
  | Gossip_holder_without_ack_eligibility
      (** the batch reached quorum while some committee peer was never offered
          it: the post-quorum gossip (worker.rs:316-320) plus prefetch
          (network/handler.rs:167-192) hands that peer the batch, yet it
          contributed no stake. The modelled form of the ONE real sibling repair
          of {!Truncated_fanout}, granted in its most generous form
          (unconditional) so that a statement cannot be true by ignoring it. *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Quorum_reached -> verdict_equal Reached_quorum s.outcome
  | Permanently_rejected -> verdict_equal Rejected_by_quorum s.outcome
  | Anti_quorum_reached -> verdict_equal Anti_quorum s.outcome
  | Two_rejecting_peers -> 2 <= rejection_replies s.replies
  | Honest_rejecter -> 1 <= s.replies.rejected_honest
  | Byzantine_rejecter -> 1 <= s.replies.rejected_byzantine
  | Store_write_failed ->
      1 <= s.replies.stalled_store_fault + s.replies.acked_after_retry
  | Non_rejection_charged -> rejection_replies s.replies < s.rejected_stake
  | No_peer_rejected -> Int.equal 0 (rejection_replies s.replies)
  | Whole_committee_offered -> Int.equal full_fanout s.offered
  | Two_peer_acks -> 2 <= ack_replies s.replies
  | One_unavailable_peer -> Int.equal 1 (unavailable_replies s.replies)
  | Gossip_holder_without_ack_eligibility ->
      verdict_equal Reached_quorum s.outcome && s.offered < full_fanout

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Quorum_reached -> "verdict(b) = Ok"
  | Permanently_rejected -> "verdict(b) = QuorumRejected"
  | Anti_quorum_reached -> "verdict(b) = AntiQuorum"
  | Two_rejecting_peers -> "|rejecters(b)| >= 2"
  | Honest_rejecter -> "exists honest w in rejecters(b)"
  | Byzantine_rejecter -> "exists byzantine w in rejecters(b)"
  | Store_write_failed -> "store_write_failed(b)"
  | Non_rejection_charged -> "rejected_stake > |rejecters(b)|"
  | No_peer_rejected -> "rejecters(b) = {}"
  | Whole_committee_offered -> "offered(b) = committee \\ {author}"
  | Two_peer_acks -> "|ackers(b)| >= 2"
  | One_unavailable_peer -> "|unavailable(b)| = 1"
  | Gossip_holder_without_ack_eligibility -> "gossip_holder_not_offered(b)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} by
    test/t_batch_quorum_tally_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
