(** Finite interpreted system for the ROUND_WEIGHT_CAP family: the per-origin
    voting-power cap inside telcoin-network's round-parent aggregator, the
    2f+1 threshold gate that reads the capped weight, and the remote
    re-derivation of both that the header voters run one round later. File
    citations refer to Telcoin-Association/telcoin-network at the working tree
    of git HEAD 0c59c15b; every one of them was opened in this checkout.

    THE MODELLED MECHANISM. One round [r], one node's aggregator. Certificates
    for round [r] land in [CertificatesAggregatorManager::append_certificate]
    (aggregators/certificates.rs:24-44), which routes each into the round's
    [CertificatesAggregator] (:52-63) and, on a [Some(parents)] return, sends
    the whole parent batch to the proposer over the consensus bus (:39-41).
    [CertificatesAggregator::append] (:75-102) is three steps in a fixed order:

    - :80  [let origin = certificate.origin().clone();]
    - :82-85 THE DISTINCTNESS GUARD -
      [if !self.authorities_seen.insert(origin.clone()) { return None; }].
      A second certificate carrying an origin already in [authorities_seen] is
      discarded here. The discard is a bare [return None]: no log, no metric,
      no error, no fault attribution. Contrast the sibling vote aggregator,
      which raises [DagError::AuthorityReuse] on the same condition
      (aggregators/votes.rs:42-45) - the certificate route deliberately does
      not.
    - :87-89 [self.certificates.push(certificate); self.weight +=
      committee.voting_power_by_id(&origin);]. The per-identity unit is fixed
      at one: [EQUAL_VOTING_POWER: VotingPower = 1] (types/src/committee.rs:25)
      and [voting_power_by_id] returns it for any committee member and [0]
      otherwise (:511-513).
    - :91-99 THE THRESHOLD GATE -
      [if self.weight >= committee.quorum_threshold() { ... return
      Some(self.certificates.drain(..).collect()); }]. [quorum_threshold]
      (:516-518) is precomputed by [calculate_quorum_threshold] (:247-252) as
      [2 * total_votes / 3 + 1] over [total_voting_power] =
      [self.authorities.len()] (:261-263), i.e. exactly 3 for the four
      equal-power validators of this family. The weight is deliberately NOT
      reset on emission (:94-97).

    WHY THE DISTINCTNESS GUARD IS LOAD-BEARING, i.e. how a duplicate reaches
    [append] at all. Two independent routes, one of which needs no Byzantine
    behaviour whatsoever:

    - RE-FETCH (honest). The single-certificate ingress dedups by digest -
      [process_certificate] returns early on
      [self.config.node_storage().contains(&digest)?]
      (state_sync/cert_validator.rs:93-98) - but the catch-up ingress does
      not. [process_fetched_certificates_in_parallel] (:235-243) runs
      [verify_collection] (:246-268) and then
      [forward_verified_certs] (:133) directly; neither [verify_collection]
      nor [classify_certificates_for_verification] (:272-296) consults the
      certificate store at all. Downstream,
      [CertificateManager::process_verified_certificates]
      (state_sync/cert_manager.rs:74-135) checks [is_verified] (:90-93),
      pending status (:96-101) and missing parents (:103-118) - never
      [(round, origin)] uniqueness - and hands the batch to
      [accept_verified_certificates] (:189-220), which writes storage (:196)
      and calls [append_certificate] again (:205-211). So a certificate the
      node already accepted, re-delivered inside a fetch response, arrives at
      [append] a second time with the SAME origin.
    - EQUIVOCATION (Byzantine). Two distinct round-[r] headers from one author
      are two distinct digests, so the :93-98 dedup cannot see them either.
      The vote-once rule at network/handler.rs:787-847 permits a voter to vote
      again for a different header at the same round precisely when no
      certificate has yet been stored for that [(author, round)]
      (the [cert_exists] test at :824-839), so a second certificate for the
      same author and round is constructible.

    TWO SCOPE NOTES, so the abstraction is not mistaken for a stronger claim
    than the code supports. First, [voting_power_by_id] returns [0] for a
    non-member (types/src/committee.rs:511-513) while [authorities_seen] takes
    any origin, so the exact invariant is
    [weight = |authorities_seen INTERSECT committee|]; a non-member certificate
    never reaches [append] anyway (the committee check is inside
    [validate_and_verify] far upstream), and the model's [origins] IS the
    committee-intersected count. Second, [garbage_collect]
    (certificates.rs:46-49) drops whole round aggregators with
    [self.aggregators.retain(|k, _| k > gc_round)], and a later certificate for
    that round re-creates one through [or_insert_with] (:32-36) with
    [weight = 0] and an empty [authorities_seen] (:67-69) - counters that reset
    TOGETHER, so a gc cycle cannot inflate weight relative to distinct origins.
    This model covers exactly one aggregator lifetime.

    WHAT DOES NOT REPAIR THE GUARD. [save_cert]
    (storage/src/stores/certificate_store.rs:128-147) silently OVERWRITES the
    [CertificateDigestByRound] entry keyed [(round, origin)] (:137-138) rather
    than flagging a conflict; [append_certificate] has no error path except
    the channel send (certificates.rs:40); and on the emitting node the
    proposer never re-derives the round quorum - [process_parents]
    (proposer.rs:384-467) only warns on a round mismatch (:385-390), extends
    [last_parents] (:447) and sets [advance_round = self.ready()] (:463);
    [ready] (:374-379) dispatches to [update_leader] (:319-327) or
    [enough_votes] (:338-365), and [enough_votes] tallies
    [voting_power_by_id(certificate.origin())] over [last_parents] with NO
    distinctness filter (:351-358); the propose gate itself is the bare
    [let enough_parents = !self.last_parents.is_empty();] (:751).

    WHAT DOES REPAIR IT, ONE ROUND LATER AND ON SOMEBODY ELSE'S MACHINE. When
    the round-[r+1] header built on that parent set is sent for voting, each
    remote voter re-derives both properties from scratch inside
    [PrimaryNetworkHandler::process_request]'s header path: it inserts every
    parent author into a [BTreeSet] and fails with
    [HeaderError::DuplicateParents] on a repeat (handler.rs:700, :725-728),
    and it re-sums [committee.voting_power_by_id(parent.origin())] and fails
    with [CertificateError::Inquorate] below [quorum_threshold()]
    (:730, :733-738). This model carries that repair explicitly ([header]),
    it stays LIVE under both mutations, and it is exactly why this family's
    claims are anchored on the LOCAL emission event rather than on what the
    network ends up accepting (R5).

    COMPONENTS. Eight fields, one round, one aggregator:
    - [kind]: FROZEN by the two initial states - is the duplicate that reaches
      [append] a re-fetched copy of a certificate the node already holds
      (cert_validator.rs:235-243 bypassing the :93-98 dedup) or a SECOND,
      distinct round-[r] header from a Byzantine V3 (handler.rs:824-839)? This
      is the family's hidden global bit.
    - [certified]: has a supermajority - 2f+1 = 3 distinct committee members -
      had a round-[r] header certified anywhere in the system? Monotone,
      environment-driven, and a strict precondition for the THIRD distinct
      append (a node cannot append a certificate that does not exist). The
      first two distinct appends are unconstrained, since two appended origins
      witness only two certified members.
    - [origins]: [|authorities_seen|] for round [r] on the local aggregator,
      0..3 (certificates.rs:62, :83).
    - [weight]: [self.weight] for round [r], 0..4 (certificates.rs:58, :89).
      Pristine this always equals [origins]; that equality IS the cap.
    - [emitted]: has [append] returned [Some(parents)] and the manager pushed
      them to the proposer (certificates.rs:98, :39-41)? Latching, because the
      weight is never reset (:94-97). It is a stored field rather than a
      derived predicate precisely because the threshold-gate mutation changes
      WHEN it fires, and the atom valuation may not read the mutation.
    - [dup]: has the duplicate round-[r] certificate for an already-counted
      origin been offered to [append] yet? Enabled once [origins >= 1], i.e.
      once the origin in question is in [authorities_seen]; the mirror-image
      arrival order is symmetric, since whichever of the two arrives first is
      the one counted.
    - [peer]: the peer primary's OWN round-[r] aggregator - has it reached its
      own 2f+1 and fired? Requires [certified], for the same reason the third
      local append does.
    - [header]: the remote voters' verdict on the round-[r+1] header built
      from the emitted parent set (handler.rs:725-728, :733-738).
      [H_rejected] is unreachable pristine and is the visible signature of the
      repair firing.

    ROLE MAPPING (a knowledge agent needs a real, non-constant view; a
    blank-view party may never appear under [K]):
    - V0 = the local primary running the round-[r] [CertificatesAggregator]
      and the knowledge agent of S2 and S3 conjunct (B). Its view is
      [(origins, weight, emitted, observation, header)]: its own
      [authorities_seen] cardinality and [weight], whether its own [append]
      fired, WHICH duplicate it personally received (it holds both digests, so
      a re-fetched copy and a second distinct header are distinguishable to
      it), and the fate of its own proposed header. It does NOT see
      [certified] - nothing on this route reports how many committee members
      are certified system-wide - and it does NOT see [peer]: each node's
      aggregator fires on its own local arrival order and no message carries a
      peer's aggregator weight.
    - V1 = a peer primary and the knowledge agent of S3 conjunct (C). Its view
      is [(peer, header)]: its own round-[r] aggregator status, plus the
      verdict it itself computed on V0's round-[r+1] header (it is one of the
      voters of handler.rs:700-738). It sees nothing of V0's
      [authorities_seen], nothing of V0's [weight], and - this is the point of
      S3 - no trace of the duplicate V0 dropped, because the drop is a bare
      [return None] (certificates.rs:83-85) that emits nothing to the network.
    - V3 = the possibly-equivocating origin. It is modelled only through its
      acts ([kind]); it is NOT a knowledge agent and never appears under [K].
    - V2 = idle. V2 and V3 both carry the constant blank view [View_idle]. *)

(** The committee size of this family: four equal-power validators, f = 1
    (types/src/committee.rs:261-263 counts [self.authorities.len()]). *)
let committee_size = 4

(** The 2f+1 parent quorum [append] compares its accumulated weight against:
    [2 * total_votes / 3 + 1] (types/src/committee.rs:247-252), precomputed
    into [quorum_threshold()] (:516-518). For [committee_size = 4] this is 3. *)
let quorum_threshold = (2 * committee_size / 3) + 1

(** What the duplicate round-[r] certificate that reaches [append] a second
    time actually is. FROZEN by the initial state: this is the family's hidden
    global fact. *)
type dup_kind =
  | Refetched_copy
      (** the very certificate the node already accepted, re-delivered inside
          a fetch response - [process_fetched_certificates_in_parallel]
          (cert_validator.rs:235-243) never consults the certificate store, so
          the digest dedup at :93-98 is bypassed. No Byzantine behaviour is
          involved. *)
  | Second_header
      (** a SECOND, distinct round-[r] header from the Byzantine origin V3,
          certified separately. Two distinct digests, so the :93-98 dedup
          cannot see them; constructible because the vote-once rule re-permits
          a vote for a different header at the same round while no certificate
          is yet stored for that author and round (handler.rs:824-839). *)

(** Total order index for {!dup_kind}. *)
let dup_kind_index = function Refetched_copy -> 0 | Second_header -> 1

(** Total order on {!dup_kind}. *)
let dup_kind_compare a b = Int.compare (dup_kind_index a) (dup_kind_index b)

(** Whether a supermajority of DISTINCT committee members has had a round-[r]
    header certified anywhere in the system. The global fact S2 is about. *)
type cert_quorum =
  | C_below  (** fewer than 2f+1 = 3 distinct members are certified at [r] *)
  | C_reached
      (** at least [quorum_threshold] distinct members are certified at [r] -
          each of them collected 2f+1 votes on its own header, so this is a
          fact about that many REMOTE completed proposal rounds *)

(** Total order index for {!cert_quorum}. *)
let cert_quorum_index = function C_below -> 0 | C_reached -> 1

(** Total order on {!cert_quorum}. *)
let cert_quorum_compare a b =
  Int.compare (cert_quorum_index a) (cert_quorum_index b)

(** Whether the duplicate certificate has been offered to the local
    aggregator's [append] yet. *)
type dup_site =
  | D_none  (** it has not been delivered *)
  | D_at_v0
      (** it reached V0's [append] with an origin already in
          [authorities_seen] (certificates.rs:83) *)

(** Total order index for {!dup_site}. *)
let dup_site_index = function D_none -> 0 | D_at_v0 -> 1

(** Total order on {!dup_site}. *)
let dup_site_compare a b = Int.compare (dup_site_index a) (dup_site_index b)

(** The local aggregator's emission latch: has [append] returned
    [Some(parents)] for round [r] (certificates.rs:98) and has the manager
    forwarded them to the proposer (:39-41)? *)
type emission =
  | Em_pending  (** every [append] so far returned [None] *)
  | Em_fired  (** the parent batch for [r] has gone to the proposer *)

(** Total order index for {!emission}. *)
let emission_index = function Em_pending -> 0 | Em_fired -> 1

(** Total order on {!emission}. *)
let emission_compare a b = Int.compare (emission_index a) (emission_index b)

(** The peer primary's own round-[r] aggregator. *)
type peer_agg =
  | P_idle  (** the peer's round-[r] aggregator has not reached 2f+1 *)
  | P_quorum
      (** the peer's own [append] fired for round [r]; requires
          [C_reached] for the same reason the third local append does *)

(** Total order index for {!peer_agg}. *)
let peer_agg_index = function P_idle -> 0 | P_quorum -> 1

(** Total order on {!peer_agg}. *)
let peer_agg_compare a b = Int.compare (peer_agg_index a) (peer_agg_index b)

(** The remote voters' verdict on the round-[r+1] header built from the
    emitted parent set (handler.rs:700-738). *)
type hdr_verdict =
  | H_none  (** no header has been proposed on this parent set yet *)
  | H_accepted
      (** the voters' [BTreeSet] of parent authors accepted every parent
          (handler.rs:725-728) and the re-summed stake cleared
          [quorum_threshold()] (:733-738) *)
  | H_rejected
      (** [HeaderError::DuplicateParents] (handler.rs:725-728) or
          [CertificateError::Inquorate] (:733-738): the downstream repair
          fired. Unreachable on the pristine model - that is the point *)

(** Total order index for {!hdr_verdict}. *)
let hdr_verdict_index = function
  | H_none -> 0
  | H_accepted -> 1
  | H_rejected -> 2

(** Total order on {!hdr_verdict}. *)
let hdr_verdict_compare a b =
  Int.compare (hdr_verdict_index a) (hdr_verdict_index b)

(** The joint global state: the frozen duplicate kind, the global
    certification progress, the local aggregator's two counters and its
    emission latch, the duplicate's delivery, the peer's aggregator, and the
    remote header verdict. *)
type state = {
  kind : dup_kind;
  certified : cert_quorum;
  origins : int;
  weight : int;
  emitted : emission;
  dup : dup_site;
  peer : peer_agg;
  header : hdr_verdict;
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let ca = dup_kind_compare s1.kind s2.kind in
  if Bool.not (Int.equal ca 0) then ca
  else
    let cb = cert_quorum_compare s1.certified s2.certified in
    if Bool.not (Int.equal cb 0) then cb
    else
      let cc = Int.compare s1.origins s2.origins in
      if Bool.not (Int.equal cc 0) then cc
      else
        let cd = Int.compare s1.weight s2.weight in
        if Bool.not (Int.equal cd 0) then cd
        else
          let ce = emission_compare s1.emitted s2.emitted in
          if Bool.not (Int.equal ce 0) then ce
          else
            let cf = dup_site_compare s1.dup s2.dup in
            if Bool.not (Int.equal cf 0) then cf
            else
              let cg = peer_agg_compare s1.peer s2.peer in
              if Bool.not (Int.equal cg 0) then cg
              else hdr_verdict_compare s1.header s2.header

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** What the local primary can tell about the duplicate it received. It holds
    both digests, so a re-delivered copy of a certificate it already accepted
    and a second, distinct header from the same author at the same round are
    different observations to it - and only the second one attributes
    equivocation. *)
type dup_obs =
  | Obs_none  (** no duplicate has reached this node's [append] *)
  | Obs_refetch  (** the duplicate was a re-delivered copy of a known digest *)
  | Obs_second  (** the duplicate was a distinct header from a counted author *)

(** Total order index for {!dup_obs}. *)
let dup_obs_index = function
  | Obs_none -> 0
  | Obs_refetch -> 1
  | Obs_second -> 2

(** Total order on {!dup_obs}. *)
let dup_obs_compare a b = Int.compare (dup_obs_index a) (dup_obs_index b)

(** A validator's local view.

    [View_local] is V0, the node running the round-[r] aggregator: its own
    [|authorities_seen|] and [weight], its own emission latch, which duplicate
    it personally received, and the fate of its own round-[r+1] header. It
    does NOT carry [certified] (no message on this route reports how many
    committee members are certified system-wide) and does NOT carry [peer]
    (no message carries a peer's aggregator weight).

    [View_peer] is V1, a peer primary: its own round-[r] aggregator status and
    the verdict it itself computed as a voter on V0's header
    (handler.rs:700-738). It carries no component of V0's aggregator, and in
    particular no trace of the duplicate V0 dropped - the drop is a bare
    [return None] (certificates.rs:83-85).

    [View_idle] is the constant blank view of V2 and of the origin V3; neither
    ever appears under [K]. *)
type view =
  | View_local of int * int * emission * dup_obs * hdr_verdict
  | View_peer of peer_agg * hdr_verdict
  | View_idle

(** Total order on the {!View_local} payload, every component spelled. *)
let view_local_compare (o1, w1, e1, d1, h1) (o2, w2, e2, d2, h2) =
  let ca = Int.compare o1 o2 in
  if Bool.not (Int.equal ca 0) then ca
  else
    let cb = Int.compare w1 w2 in
    if Bool.not (Int.equal cb 0) then cb
    else
      let cc = emission_compare e1 e2 in
      if Bool.not (Int.equal cc 0) then cc
      else
        let cd = dup_obs_compare d1 d2 in
        if Bool.not (Int.equal cd 0) then cd else hdr_verdict_compare h1 h2

(** Total order on the {!View_peer} payload, every component spelled. *)
let view_peer_compare (p1, h1) (p2, h2) =
  let ca = peer_agg_compare p1 p2 in
  if Bool.not (Int.equal ca 0) then ca else hdr_verdict_compare h1 h2

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_local _ | View_peer _) -> -1
  | (View_local _ | View_peer _), View_idle -> 1
  | View_local (o1, w1, e1, d1, h1), View_local (o2, w2, e2, d2, h2) ->
      view_local_compare (o1, w1, e1, d1, h1) (o2, w2, e2, d2, h2)
  | View_local _, View_peer _ -> -1
  | View_peer _, View_local _ -> 1
  | View_peer (p1, h1), View_peer (p2, h2) ->
      view_peer_compare (p1, h1) (p2, h2)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** What the local primary observes about the duplicate it received: nothing
    at all until one arrives, and afterwards which of the two hazards it was. *)
let observation s =
  match s.dup with
  | D_none -> Obs_none
  | D_at_v0 -> (
      match s.kind with
      | Refetched_copy -> Obs_refetch
      | Second_header -> Obs_second)

(** View projection. V0 and V1 are the knowledge agents; V2 and the origin V3
    are idle non-agents with the constant blank view and never appear under
    [K]. This family keeps the four-member committee semantics its mechanism
    is stated over ({!Validator} carries the ten-member roster of
    {!Tn_model}), so V4..V9 are outside the modelled committee and are idle
    too. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_local (s.origins, s.weight, s.emitted, observation s, s.header)
  | Validator.V1 -> View_peer (s.peer, s.header)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_distinct_origin_guard
      (** delete the distinctness guard at
          crates/consensus/primary/src/aggregators/certificates.rs:83-85
          ([if !self.authorities_seen.insert(origin.clone()) { return None; }]),
          so a duplicate certificate for an already-counted origin falls
          through to :88-89 and adds a second unit of voting power. In the
          model the [deliver_duplicate] transition stops being a pure
          bookkeeping step and increments [weight] (and may therefore trip the
          :92 threshold), producing states with [weight > origins].

          NO SIBLING PATH REPAIRS IT on the emitting node. The digest dedup at
          cert_validator.rs:93-98 sees only exact retransmissions and is
          bypassed entirely by the fetch route (:235-243 -> :133, with
          :246-268 and :272-296 never touching storage); two equivocating
          headers are two distinct digests, so it could not see them anyway.
          cert_manager.rs:74-135 checks verification, pending and missing
          parents but never [(round, origin)] uniqueness. [save_cert]
          (certificate_store.rs:128-147) OVERWRITES the [(round, origin)]
          index at :137-138 instead of flagging a conflict.
          [append_certificate] (certificates.rs:24-44) has no error arm but
          the channel send. The proposer never re-derives distinctness
          (proposer.rs:384-467, :338-365, :751). The [DagError::AuthorityReuse]
          arm exists only in the VOTE aggregator (votes.rs:42-45) and is not
          consulted here. The one genuine repair is remote and one round later
          (handler.rs:725-728, :733-738); it is MODELLED as [header] and stays
          live under this mutation, which is why it refutes only the
          local-emission claims. *)
  | No_quorum_threshold_gate
      (** delete the threshold comparison at
          crates/consensus/primary/src/aggregators/certificates.rs:91-92
          ([if self.weight >= committee.quorum_threshold()]), so every
          successful append returns [Some(parents)] and the manager forwards a
          one-certificate parent batch to the proposer (:39-41). In the model
          [emitted] latches on the FIRST append instead of the third.

          NO SIBLING PATH REPAIRS IT on the emitting node: [process_parents]
          (proposer.rs:384-467) only warns on a round mismatch (:385-390) and
          extends [last_parents] (:447); [ready] (:374-379) delegates to
          [update_leader] (:319-327) or [enough_votes] (:338-365), which
          tallies stake over [last_parents] without any quorum re-derivation
          for the round itself; and the propose gate is the bare
          [!self.last_parents.is_empty()] (:751). The remote voters DO catch
          it (Inquorate, handler.rs:733-738), and that repair is modelled and
          stays live - so this mutation too refutes only local-emission
          claims. *)

(** Does the post-append weight fire the round-quorum gate at
    certificates.rs:91-92? Under {!No_quorum_threshold_gate} the comparison is
    gone, so every successful append emits. *)
let fires mut w =
  match mut with
  | Pristine | No_distinct_origin_guard -> quorum_threshold <= w
  | No_quorum_threshold_gate -> true

(** Latch the emission flag: the weight is never reset (certificates.rs:94-97),
    so once the batch has gone to the proposer it stays gone. *)
let latch em fired =
  match em with
  | Em_fired -> Em_fired
  | Em_pending -> if fired then Em_fired else Em_pending

(** The transition relation: the environment certifies the supermajority, the
    local aggregator appends a new distinct origin or is offered the
    duplicate, the peer's own aggregator fires, and the round-[r+1] header
    built on the emitted parent set collects the remote voters' verdict. One
    component advances per step; every step is monotone. *)
let next_with mut s =
  let certify =
    match s.certified with
    | C_below -> [ { s with certified = C_reached } ]
    | C_reached -> []
  in
  let append_new =
    let allowed =
      match s.certified with
      | C_below -> s.origins < quorum_threshold - 1
      | C_reached -> s.origins < quorum_threshold
    in
    if allowed then
      let w = s.weight + 1 in
      [
        {
          s with
          origins = s.origins + 1;
          weight = w;
          emitted = latch s.emitted (fires mut w);
        };
      ]
    else []
  in
  let deliver_duplicate =
    match s.dup with
    | D_at_v0 -> []
    | D_none ->
        if s.origins < 1 then []
        else (
          match mut with
          | Pristine | No_quorum_threshold_gate -> [ { s with dup = D_at_v0 } ]
          | No_distinct_origin_guard ->
              let w = s.weight + 1 in
              [
                {
                  s with
                  dup = D_at_v0;
                  weight = w;
                  emitted = latch s.emitted (fires mut w);
                };
              ])
  in
  let peer_step =
    match (s.certified, s.peer) with
    | C_reached, P_idle -> [ { s with peer = P_quorum } ]
    | C_reached, P_quorum -> []
    | C_below, (P_idle | P_quorum) -> []
  in
  let propose =
    match (s.emitted, s.header) with
    | Em_fired, H_none ->
        [
          {
            s with
            header =
              (if quorum_threshold <= s.origins then H_accepted else H_rejected);
          };
        ]
    | Em_fired, (H_accepted | H_rejected) -> []
    | Em_pending, (H_none | H_accepted | H_rejected) -> []
  in
  certify @ append_new @ deliver_duplicate @ peer_step @ propose

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state of the all-honest world: the duplicate that will reach
    [append] is a re-delivered copy of a certificate the node already holds
    (cert_validator.rs:235-243). Nothing is certified, nothing appended. *)
let initial =
  {
    kind = Refetched_copy;
    certified = C_below;
    origins = 0;
    weight = 0;
    emitted = Em_pending;
    dup = D_none;
    peer = P_idle;
    header = H_none;
  }

(** The sibling initial state in which the duplicate is a SECOND, distinct
    round-[r] header from the Byzantine origin V3 (handler.rs:824-839). The
    two initial states differ only in this frozen hidden bit, which is exactly
    the branch a node that never received the duplicate can never resolve. *)
let initial_equivocating = { initial with kind = Second_header }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Emitted_round_quorum
      (** emitted = Em_fired : the round-[r] aggregator returned
          [Some(parents)] and the manager pushed the batch to the proposer
          (certificates.rs:98, :39-41) *)
  | Distinct_quorum_appended
      (** origins >= quorum_threshold : [|authorities_seen|] for round [r] has
          reached 2f+1 DISTINCT committee members (certificates.rs:83) *)
  | Weight_exceeds_origins
      (** weight > origins : some identity moved the round toward its parent
          quorum by more than one unit - the state the cap forbids
          (certificates.rs:83-89 with EQUAL_VOTING_POWER = 1,
          committee.rs:25) *)
  | Duplicate_appended
      (** dup = D_at_v0 : a duplicate round-[r] certificate for an
          already-counted origin has been offered to [append]
          (certificates.rs:83) *)
  | Origin_equivocated
      (** kind = Second_header : the origin V3 really did get two distinct
          round-[r] headers certified. A global fact about V3's acts *)
  | Remote_quorum_certified
      (** certified = C_reached : at least 2f+1 DISTINCT committee members
          have had a round-[r] header certified, i.e. that many remote nodes
          each completed a proposal round *)
  | Peer_reached_quorum
      (** peer = P_quorum : the peer primary's OWN round-[r] aggregator fired *)
  | Header_accepted
      (** header = H_accepted : a remote voter accepted the round-[r+1] header
          built on the emitted parent set (handler.rs:725-728, :733-738) *)
  | Header_rejected
      (** header = H_rejected : a remote voter rejected it with
          [DuplicateParents] or [Inquorate] - the downstream repair firing *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Emitted_round_quorum -> (
      match s.emitted with Em_fired -> true | Em_pending -> false)
  | Distinct_quorum_appended -> quorum_threshold <= s.origins
  | Weight_exceeds_origins -> s.origins < s.weight
  | Duplicate_appended -> (
      match s.dup with D_at_v0 -> true | D_none -> false)
  | Origin_equivocated -> (
      match s.kind with Second_header -> true | Refetched_copy -> false)
  | Remote_quorum_certified -> (
      match s.certified with C_reached -> true | C_below -> false)
  | Peer_reached_quorum -> (
      match s.peer with P_quorum -> true | P_idle -> false)
  | Header_accepted -> (
      match s.header with
      | H_accepted -> true
      | H_none | H_rejected -> false)
  | Header_rejected -> (
      match s.header with
      | H_rejected -> true
      | H_none | H_accepted -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Emitted_round_quorum -> "emitted_0(r)"
  | Distinct_quorum_appended -> "distinct_0(r) >= 2f+1"
  | Weight_exceeds_origins -> "weight_0(r) > |authorities_seen_0(r)|"
  | Duplicate_appended -> "duplicate_offered_0(r)"
  | Origin_equivocated -> "equivocated(V3,r)"
  | Remote_quorum_certified -> "certified(r) >= 2f+1"
  | Peer_reached_quorum -> "emitted_1(r)"
  | Header_accepted -> "header_accepted_0(r+1)"
  | Header_rejected -> "header_rejected_0(r+1)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every
    reachable world by test/t_round_weight_cap_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the two initial states (the frozen
    duplicate-kind branch), mutation-parameterized transitions, the
    four-role view projection, the atom valuation. *)
let spec_of mut =
  {
    Checker.init = [ initial; initial_equivocating ];
    next = next_with mut;
    view;
    label;
  }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
