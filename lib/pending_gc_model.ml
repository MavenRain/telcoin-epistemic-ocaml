(** Finite interpreted system for the PENDING_GC family: telcoin-network's
    parked-certificate ("pending") mechanism and its garbage-collection release,
    plus the vote round that reads the same pending map. File citations refer to
    Telcoin-Association/telcoin-network at the working tree of git HEAD
    0c59c15b.

    THE MODELED MECHANISM. A verified certificate [c] at round [r] arrives at
    the local primary [v]. [v] admits it only in causal order: the missing-parent
    check at cert_manager.rs:103-118 runs ONLY when [cert.round() > gc_round + 1]
    (cert_manager.rs:108), and when it fires and a parent is absent from storage
    (get_missing_parents, cert_manager.rs:139-180) the certificate is parked in
    the PendingCertificateManager (insert_pending, cert_manager.rs:111) and a
    [CertificateFetcherCommand::Ancestors] is dispatched (cert_manager.rs:173-176).
    Otherwise [v] runs update_pending + accept_verified_certificates
    (cert_manager.rs:120-124), which writes to the certificate store, appends to
    the parent aggregator and forwards to consensus (cert_manager.rs:189-220)
    with NO parent precondition of its own.

    A parked certificate has exactly two release routes:
    - the CASCADE: the missing parent [d] is itself accepted, so update_pending
      (pending_cert_manager.rs:85-131) removes [d] from
      [missing_parent_digests], and the now-unlocked child is pushed into
      accept_verified_certificates (cert_manager.rs:121-124). The parent ends up
      stored.
    - the GC RELEASE: the local gc horizon advances past [d]'s round, so
      process_gc_round runs its drain loop (cert_manager.rs:235-238) -
      [next_for_gc_round] selects the lowest collected missing-parent key,
      [update_pending] (pending_cert_manager.rs:85-131) drops that key from
      [missing_for_pending] and returns every child whose
      [missing_parent_digests] thereby emptied, and
      [accept_verified_certificates] takes them - so the child is accepted with
      [d] STILL ABSENT. The loop plus update_pending IS the release;
      next_for_gc_round (pending_cert_manager.rs:137-156) only selects, and its
      [if round > gc_round { return None }] is the loop's termination test (see
      the ANCHOR NOTE on {!No_gc_release}). The horizon is driven per node by
      the GarbageCollector's own committed-round watch (gc.rs:66-92) over
      [gc_round = committed_round - gc_depth] (consensus/utils.rs:59-62).

    Above the horizon [d] can still be fetched; below it, it cannot: the fetcher
    sets its request bound from [gc_round] (certificate_fetcher.rs:258-286) and
    reads written rounds via [origins_after_round(gc_round + 1)]
    (certificate_fetcher.rs:350-379), and the direct-verification path rejects
    [d] as [TooOld] (cert_validator.rs:114-125). The window is not hermetic - a
    peer-volunteered batch in which [d] is a parent of another certificate gets
    [mark_verified_indirectly] and skips the TooOld check
    (cert_validator.rs:288-324) - so this model deliberately does NOT gate
    [deliver_d] on the horizon, and instead carries an explicit [D_lost] value
    for the honest "the parent simply never arrives" branch.

    WHAT [c] ITSELF TELLS [v]. A certificate carries the roaring bitmap of the
    authorities that signed it (certificate.rs:349-354) and [v] cannot accept
    [c] without reading that bitmap: validate_and_verify sums its weight and
    rejects anything below [committee.quorum_threshold()]
    (certificate.rs:225-251 via signed_by, :177-199), which for the four
    equal-weight validators of this family is [(2 * 4) / 3 + 1 = 3]
    (committee.rs:684-688). An HONEST signer cannot have voted for [c]'s header
    without holding every one of that header's parents, [d] among them: the
    vote path blocks on notify_read_parent_certificates (handler.rs:688-693),
    which maps [notify_read] over [header.parents()]
    (header_validator.rs:39-67) and returns only once each parent has been
    written by accept_verified_certificates (cert_manager.rs:196). That
    possession is CURRENT and not merely historical at the operative state: a
    certificate store trims only below [round - ROUNDS_TO_KEEP] with
    [ROUNDS_TO_KEEP = 64] (storage/src/lib.rs:46, certificate_store.rs:149-172)
    while the horizon sits [gc_depth <= MAX_GC_DEPTH = 50] rounds back
    (types/src/primary/mod.rs:45, config/src/node.rs:300-305,
    consensus/utils.rs:59-62), so [d] is still inside every peer's retention
    window when [v]'s horizon passes it.

    So [v] does NOT reason in the dark about [d]. At the operative state
    (accepted [c], never held [d]) it knows a QUORUM signed [c], hence that at
    least [3 - f = 2] of the signers held [d]. What it cannot do is put a NAME
    to one of them. [v] itself is not among [c]'s signers there - it never held
    [d], its own vote would have blocked on [notify_read] for [d], and the same
    64-vs-50 retention margin rules out "it held [d] then GC'd it" - so the
    three signers are exactly the other three committee members and [w] is
    necessarily one of them. With [f = 1], one of those three may be faulty,
    and a faulty signer's vote is only a BLS signature over the header digest:
    nothing in validate_and_verify ties a signer's key to its store contents.
    [v] can therefore neither confirm nor rule out that this particular [w] is
    a holder rather than the tolerated faulty signer. That unresolvable fault
    branch - NOT an absence of channels - is what [peer_d] encodes, and it is
    the only thing S1 conjunct B claims [v] does not know.

    In parallel, the header author [a] has an outstanding vote request for a
    header [h] at round [r+1] that lists [c] among its parents. The voter's
    reply is governed by two gates: identify_unkown_parents
    (header_validator.rs:195-229) does multi_contains against storage and then
    round-trips the residue through [FilterUnkownDigests]
    (cert_manager.rs:298-301) into filter_unknown_digests, whose
    [unknown.retain(|digest| !self.pending.contains_key(digest))]
    (pending_cert_manager.rs:171-173) drops any digest already parked; only what
    survives becomes [PrimaryResponse::MissingParents] (handler.rs:653-669). And
    before a vote is produced, handler.rs:688-693 BLOCKS on
    notify_read_parent_certificates, which maps
    [certificate_store.notify_read] over every parent
    (header_validator.rs:39-67); notify_read returns only once the certificate
    is actually written, which happens exactly in accept_verified_certificates
    (cert_manager.rs:196). Only then are the parents quorum-checked
    (handler.rs:700-738) and the vote created and stored (handler.rs:860-872).

    Both of those are the gates on the response the voter COMPUTES. A response
    it has already computed is CACHED per author (handler.rs:510-516) and
    replayed: a repeat request for the same header digest carrying an empty
    parents list returns the cached [MissingParents] set verbatim
    (handler.rs:519-534) - before any storage read, before
    identify_unkown_parents and before the [FilterUnkownDigests] round trip -
    and its own comment names the trigger (the proposer's certifier restarting
    and losing the missing-parent hint; certifier.rs:140-205 also clears the
    hint on any non-RPC network error). A digest that was genuinely unknown
    when the set was computed is therefore named again by that replay even if
    it has since been parked. This model represents ONE computed response per
    header - [req] leaves [R_open] exactly once - and the family's claims are
    scoped accordingly: S3 conjunct A is about the response the voter computes,
    never about a verbatim replay of an earlier one.

    COMPONENTS. One certificate chain and one vote round:
    - [local_c]: [v]'s state for [c] - unknown / parked in the pending map /
      accepted (i.e. written by accept_verified_certificates);
    - [local_d]: [v]'s possession of [c]'s parent [d] - absent / stored / lost
      (the acquisition window closed and it never came);
    - [horizon]: [v]'s gc horizon relative to [d]'s round - below / past;
    - [req]: the single vote round for [h] as seen through [v]'s per-author
      vote cache (handler.rs:510-516) - no response computed yet / a computed
      MissingParents / a computed Vote;
    - [peer_d]: whether the peer [w] - one of [c]'s three signers, see above -
      actually POSSESSES [d]. FROZEN: fixed by the two initial states and
      touched by no transition. [W_holds_parent] is the branch in which [w] is
      one of the honest signers, which held [d] before it voted
      (handler.rs:688-693, header_validator.rs:39-67) and still holds it;
      [W_without_parent] is the branch in which [w] is the single faulty signer
      tolerated by [f = 1], whose signature attests nothing about its store.
      Nothing [v] can observe separates the two. The faulty branch's other
      possible misbehaviours are out of scope: no transition reads [peer_d], so
      the abstraction only ever weakens what [v] is credited with knowing.

    ROLE MAPPING (a knowledge agent must have a real, non-constant view; a
    blank-view party may never appear under [K]):
    - V1 = the local primary [v], the accepting/voting node, and the knowledge
      agent of S1. Its view is [(local_c, local_d, horizon, req)]: its own
      pending map and certificate store, its own gc_round, and the vote round it
      is serving. It does NOT see [peer_d]: what [c] hands [v] is a quorum of
      signatures (certificate.rs:225-251), and with [f = 1] one of those may be
      the faulty one, so no view [v] can build resolves whether THIS peer holds
      [d]. The horizon does not create that ignorance - it makes it terminal,
      because past the horizon [v]'s own acquisition route closes
      (certificate_fetcher.rs:258-286, :350-379, cert_validator.rs:114-125) and
      first-hand possession can no longer settle the question.
    - V0 = the header author [a], the knowledge agent of S3 conjunct B. Its view
      is ONLY [req]: whether the voter has yet computed a response for [h] and,
      if so, which one. It sees no component of [v]'s store, pending map or
      horizon - the certifier only ever re-sends the parents the voter named and
      volunteers nothing (certifier.rs:121-198).
    - V2 = the peer [w], one of [c]'s signers: honest in one initial branch, the
      tolerated faulty signer in the other. It sees ONLY its own [peer_d]. It is
      a possession-holder, never a knower: V2 NEVER appears under [K].
    - V3 is idle: the constant blank view [View_idle], never under [K]. *)

(** [v]'s state for the arriving certificate [c]. [C_pending] is "parked in the
    PendingCertificateManager map" (insert_pending, cert_manager.rs:111);
    [C_accepted] is "written by accept_verified_certificates"
    (cert_manager.rs:189-220). *)
type cert_state = C_unknown | C_pending | C_accepted

(** Total order index for {!cert_state}. *)
let cert_state_index = function C_unknown -> 0 | C_pending -> 1 | C_accepted -> 2

(** Total order on {!cert_state}. *)
let cert_state_compare a b =
  Int.compare (cert_state_index a) (cert_state_index b)

(** [v]'s possession of [c]'s parent [d]. [D_lost] means the acquisition window
    closed with [d] never delivered - the honest branch that the fetcher's
    [gc_round] bound (certificate_fetcher.rs:258-286, :350-379) and the
    [TooOld] rejection (cert_validator.rs:114-125) make permanent. *)
type dep_state = D_absent | D_stored | D_lost

(** Total order index for {!dep_state}. *)
let dep_state_index = function D_absent -> 0 | D_stored -> 1 | D_lost -> 2

(** Total order on {!dep_state}. *)
let dep_state_compare a b = Int.compare (dep_state_index a) (dep_state_index b)

(** [v]'s gc horizon relative to [d]'s round. [H_past] abstracts
    [gc_round >= d.round], the point at which BOTH the cert_manager.rs:108 round
    guard stops protecting [c] AND [d] becomes [TooOld] on the direct
    verification path (cert_validator.rs:114-125). *)
type horizon = H_below | H_past

(** Total order index for {!horizon}. *)
let horizon_index = function H_below -> 0 | H_past -> 1

(** Total order on {!horizon}. *)
let horizon_compare a b = Int.compare (horizon_index a) (horizon_index b)

(** The single vote round for the author's header [h], as recorded in [v]'s
    per-author vote cache (handler.rs:510-516). [R_open]: [v] has COMPUTED no
    response for [h] yet, so whatever it emits next comes off the live gates.
    [R_missing]: [v] computed a [PrimaryResponse::MissingParents]
    (handler.rs:653-669). [R_voted]: [v] computed a [Vote]
    (handler.rs:860-872). The two answered values are terminal because a repeat
    request for the same digest is served from the cache (handler.rs:517-534,
    :564), which REPLAYS an answer instead of computing one. *)
type vote_round = R_open | R_missing | R_voted

(** Total order index for {!vote_round}. *)
let vote_round_index = function R_open -> 0 | R_missing -> 1 | R_voted -> 2

(** Total order on {!vote_round}. *)
let vote_round_compare a b =
  Int.compare (vote_round_index a) (vote_round_index b)

(** Peer [w]'s possession of [d], where [w] is one of [c]'s three signers (see
    the header). [W_holds_parent]: [w] is an honest signer, so it held [d]
    before it voted (handler.rs:688-693, header_validator.rs:39-67) and still
    holds it ([ROUNDS_TO_KEEP = 64] > [gc_depth <= 50], storage/src/lib.rs:46,
    types/src/primary/mod.rs:45). [W_without_parent]: [w] is the one faulty
    signer tolerated by [f = 1], whose signature attests nothing about its
    store - validate_and_verify (certificate.rs:225-251) checks bitmap weight
    and the aggregate signature, never possession. The frozen hidden bit [v] can
    neither observe nor change. *)
type peer_dep = W_without_parent | W_holds_parent

(** Total order index for {!peer_dep}. *)
let peer_dep_index = function W_without_parent -> 0 | W_holds_parent -> 1

(** Total order on {!peer_dep}. *)
let peer_dep_compare a b = Int.compare (peer_dep_index a) (peer_dep_index b)

(** The joint global state: [v]'s three certificate-chain components, the single
    vote round, and the frozen hidden peer bit. *)
type state = {
  local_c : cert_state;
  local_d : dep_state;
  horizon : horizon;
  req : vote_round;
  peer_d : peer_dep;
}

(** Total deterministic comparison over ALL five state fields. *)
let state_compare s1 s2 =
  let c = cert_state_compare s1.local_c s2.local_c in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = dep_state_compare s1.local_d s2.local_d in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = horizon_compare s1.horizon s2.horizon in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = vote_round_compare s1.req s2.req in
        if Bool.not (Int.equal c3 0) then c3
        else peer_dep_compare s1.peer_d s2.peer_d

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. [View_local] is V1's projection - the local
    primary [v] sees its own certificate state, its own possession of the
    parent, its own gc horizon and the vote round it is serving, and NO peer
    component. [View_author] is V0's projection - the header author sees only
    the outcome of its own vote request. [View_peer] is V2's projection - the
    signer [w] sees only its own possession of [d]; V2 never appears under
    [K]. [View_idle] is the constant blank view of the non-agent V3. *)
type view =
  | View_local of cert_state * dep_state * horizon * vote_round
  | View_author of vote_round
  | View_peer of peer_dep
  | View_idle

(** Total deterministic order over ALL fields of V1's view. *)
let view_local_compare (ca, da, ha, ra) (cb, db, hb, rb) =
  let c = cert_state_compare ca cb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = dep_state_compare da db in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = horizon_compare ha hb in
      if Bool.not (Int.equal c2 0) then c2 else vote_round_compare ra rb

(** Total order on views: [View_idle] < [View_author] < [View_local] <
    [View_peer], with the field-wise order within each constructor. Every
    constructor pair is spelled: no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_author _ | View_local _ | View_peer _) -> -1
  | (View_author _ | View_local _ | View_peer _), View_idle -> 1
  | View_author ra, View_author rb -> vote_round_compare ra rb
  | View_author _, (View_local _ | View_peer _) -> -1
  | (View_local _ | View_peer _), View_author _ -> 1
  | View_local (ca, da, ha, ra), View_local (cb, db, hb, rb) ->
      view_local_compare (ca, da, ha, ra) (cb, db, hb, rb)
  | View_local _, View_peer _ -> -1
  | View_peer _, View_local _ -> 1
  | View_peer pa, View_peer pb -> peer_dep_compare pa pb

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 (the local primary) and V0 (the header author) are the
    knowledge agents; V2 (the peer [w], one of [c]'s signers) carries a real
    view but is a possession-holder that never appears under [K]; V3 is idle
    with the constant blank view. *)
let view v s =
  match v with
  | Validator.V1 -> View_local (s.local_c, s.local_d, s.horizon, s.req)
  | Validator.V0 -> View_author s.req
  | Validator.V2 -> View_peer s.peer_d
  | Validator.V3 -> View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | No_gc_release
      (** delete the garbage-collection release route: BOTH the drain loop of
          process_gc_round (cert_manager.rs:235-238 -
          [while let Some((round, digest)) = self.pending.next_for_gc_round(
          gc_round)] taking [update_pending]'s unlocked deque into
          [accept_verified_certificates]) together with the effect that loop
          relies on (pending_cert_manager.rs:97-131: [update_pending] removes
          the collected [(round, digest)] key from [missing_for_pending] and
          returns every child whose [missing_parent_digests] thereby emptied)
          AND its sibling cert_manager.rs:108 (the
          [if cert.round() > self.gc_round() + 1] horizon skip). A parked
          certificate must then wait for its literal parent forever.

          ANCHOR NOTE - an earlier revision of this doc anchored the release on
          next_for_gc_round's [if round > gc_round { return None }] bound plus
          its [pending.missing_parent_digests.clear()]
          (pending_cert_manager.rs:143-153); a review corrected that and the
          anchor above is the repaired one. Neither of those is the release.
          (i) The bound is the drain loop's TERMINATION test: deleting it makes
          next_for_gc_round return the first key unconditionally, so the loop
          would release parked certificates at ANY gc round - more eager, not
          absent. (ii) The [clear()] is unreachable: [pending] is keyed by
          PARKED-CERTIFICATE digests (pending_cert_manager.rs:41, inserted
          :63-73) while [missing_for_pending] is keyed by
          [(parent_round, parent_digest)] (:46, :76-78), and a certificate [Y]
          that is still parked always still has a missing-parent key at
          [round(Y) - 1], which sorts strictly before [(round(Y), Y)] in the
          same BTreeMap - so the [first_key_value] digest fed to
          [self.pending.get_mut(&digest)] at :151 is never a parked
          certificate. next_for_gc_round only SELECTS the lowest collected
          parent. The model's semantics were right all along ({!gc_release}
          deletes the release wholesale); only the file:line was wrong. REMOVES
          the
          release side effect of [gc_tick] and the horizon branch of
          [deliver_c], making (C_pending, D_absent, H_past) and hence the
          terminal (C_pending, D_lost, H_past) reachable, and making
          accepted-without-parent unreachable. The sibling hunt found FOUR
          candidate repairs and none survives: (1) the :108 horizon skip is the
          obvious one and is deleted by this same constructor; (2) re-delivery
          of [c] cannot re-open it - process_verified_certificates returns
          [Pending] on the [is_pending] early return before doing anything
          (cert_manager.rs:96-101), so a gossip or fetcher copy is dropped, which
          is why [deliver_c] is disabled once [local_c] leaves [C_unknown];
          (3) the [CertificateFetcherCommand::Ancestors] fired when the parent
          was first found missing (cert_manager.rs:169-177) cannot retrieve [d]
          after the horizon, because set_bounds uses [gc_round]
          (certificate_fetcher.rs:258-286) and get_written_rounds uses
          [origins_after_round (gc_round + 1)]
          (certificate_fetcher.rs:350-379), so every fetch target is strictly
          above [gc_round], and validate_and_verify additionally rejects [d] as
          [TooOld] (cert_validator.rs:114-125); the one residual hole - a
          peer-volunteered batch where [d] is a parent of another certificate
          gets [mark_verified_indirectly] and skips TooOld
          (cert_validator.rs:288-324) - is MODELED rather than omitted, since
          [deliver_d] stays enabled at [H_past], and the pin survives it because
          the [lose_d] branch supplies a path on which [d] simply never arrives;
          (4) recover_state re-appends only the last two rounds of STORED
          certificates, never pending ones (cert_manager.rs:244-258). *)
  | No_parent_check
      (** delete the missing-parent precondition on acceptance:
          cert_manager.rs:109-117, i.e. the get_missing_parents call and the
          [if !missing_parents.is_empty() { insert_pending(...); Pending }]
          branch. ADDS (C_unknown, *, H_below) -> (C_accepted, *, H_below) to
          [deliver_c]: the certificate is accepted immediately even above the
          horizon with the parent absent, so (C_accepted, D_absent, H_below)
          becomes reachable and causal order is broken below the horizon. The
          sibling hunt looked for a second parent-presence check anywhere on the
          acceptance funnel and found NONE: cert_validator.rs:88-130
          process_certificate only dedups against storage, runs
          validate_and_verify (TooOld plus signature) and forwards;
          forward_verified_certs (cert_validator.rs:133-226) only syncs batches
          and triggers a fetch when the certificate is too far ahead; the
          fetched-certificate path funnels into the same
          [ProcessVerifiedCertificates] command (cert_validator.rs:235-243); and
          accept_verified_certificates itself (cert_manager.rs:189-220) writes,
          appends and forwards with no parent precondition. Side effect worth
          naming: [C_pending] becomes unreachable, so S2 and S3 degrade to a
          vacuous antecedent under this mutation rather than being refuted by
          it - they are pinned elsewhere. *)
  | No_pending_filter
      (** delete the pending filter on the vote reply:
          pending_cert_manager.rs:171-173,
          [unknown.retain(|digest| !self.pending.contains_key(digest))] in
          filter_unknown_digests, reached through the [FilterUnkownDigests]
          command (cert_manager.rs:298-301) from identify_unkown_parents
          (header_validator.rs:195-229). ADDS
          (C_pending, *, *, R_open) -> (C_pending, *, *, R_missing) to
          [report_missing]: a parent held in the pending map is now named in the
          [MissingParents] response (handler.rs:653-669). The reachable SET is
          unchanged - only the edge relation differs, which is exactly why S3
          conjunct A is an [Ax] and not a state implication. The sibling hunt
          cleared two repairs: check_for_missing_parents also drops digests
          already present in [requested_parents] (handler.rs:875-924), but the
          entry is keyed [(header.round() - 1, digest)] and is Vacant on the
          FIRST request for that key, so it cannot re-hide the pending parent in
          this family's single vote round - and the model keeps the
          corresponding freedom (see {!report_missing_step}: [req] may stay
          [R_open] while [local_c] is [C_unknown]) so the statement survives
          that filter rather than ignoring it; and the storage pre-filter cannot
          hide it either, because a pending certificate is NOT in the certificate
          store - write_all happens only in accept_verified_certificates
          (cert_manager.rs:196) - so multi_contains
          (header_validator.rs:212-219) reports it as unknown. The retain is
          therefore the sole pending filter. *)
  | No_parent_wait
      (** delete the blocking parent wait before voting: handler.rs:688-693,
          [self.state_sync.notify_read_parent_certificates(&header).await?]
          (header_validator.rs:39-67 mapping certificate_store.rs:250-269
          notify_read over every parent), replaced by a non-blocking read of
          whatever is already in storage. ADDS
          (C_pending, *, *, R_open) -> (C_pending, *, *, R_voted) to
          [issue_vote]: the voter votes while the parent is still parked, so
          V0's [R_voted] view class gains a state whose [local_c] is
          [C_pending] and [K (V0, accepted_v(c))] fails. Only the pending case is
          added - when the parent is genuinely unknown the code still returns
          [MissingParents] at handler.rs:659-669 before ever reaching line 693.
          The sibling hunt examined the obvious repair, the parent quorum check
          at handler.rs:700-738: a non-blocking substitute drops the pending
          parent and could in principle fail [stake >= threshold]. It does NOT
          repair the deletion in general - handler.rs:632-637 admits up to
          [committee.size()] parents and a proposer normally lists every parent
          it holds, so with four validators a header carrying all four round-r
          parents still musters the 2f+1 threshold from the three stored ones and
          the vote is issued without [c]. This family's header [h] is scoped to
          exactly that shape ([c] plus three already-stored siblings, a constant
          background), so the quorum sibling is disabled by construction. Also
          checked: check_for_missing_parents would not have named [c] (it is
          pending, hence filtered at pending_cert_manager.rs:171-173), so nothing
          re-adds it, and the author volunteers only the parents it was
          explicitly asked for (certifier.rs:121-198). *)

(** The cascade a parent's acceptance performs on a parked child: update_pending
    removes the parent from [missing_parent_digests] and the unlocked child goes
    straight into accept_verified_certificates (pending_cert_manager.rs:85-131,
    cert_manager.rs:121-124), atomically within the one call. *)
let cascade = function
  | C_pending -> C_accepted
  | C_unknown -> C_unknown
  | C_accepted -> C_accepted

(** The garbage-collection release a horizon advance performs on a parked
    certificate: the process_gc_round drain loop (cert_manager.rs:235-238),
    whose [update_pending] call (pending_cert_manager.rs:97-131) drops the
    collected parent key and hands back the children it unlocked, which
    [accept_verified_certificates] then writes (cert_manager.rs:189-220).
    Deleted wholesale by {!No_gc_release}; every other mutation spells its own
    arm. *)
let gc_release mut c =
  match mut with
  | No_gc_release -> c
  | Pristine | No_parent_check | No_pending_filter | No_parent_wait -> cascade c

(** Where a freshly delivered certificate lands. Pristine it is accepted when
    the horizon has already passed its parent's round (the cert_manager.rs:108
    guard is skipped, so cert_manager.rs:120-124 runs unconditionally) or when
    the parent is in storage (get_missing_parents returns empty,
    cert_manager.rs:139-180); otherwise it is parked (cert_manager.rs:111).
    {!No_parent_check} accepts unconditionally; {!No_gc_release} has lost the
    horizon skip, so only a stored parent lets it through. *)
let park mut s =
  match mut with
  | No_parent_check -> C_accepted
  | No_gc_release -> (
      match s.local_d with
      | D_stored -> C_accepted
      | D_absent | D_lost -> C_pending)
  | Pristine | No_pending_filter | No_parent_wait -> (
      match s.horizon with
      | H_past -> C_accepted
      | H_below -> (
          match s.local_d with
          | D_stored -> C_accepted
          | D_absent | D_lost -> C_pending))

(** Whether the voter would name [c] in a [MissingParents] reply. Pristine only
    a genuinely unknown certificate is named: a parked one is dropped by the
    retain at pending_cert_manager.rs:171-173, and an accepted one is in storage
    so multi_contains already excludes it (header_validator.rs:212-219).
    {!No_pending_filter} deletes the retain, so the parked case is named too. *)
let report_enabled mut c =
  match c with
  | C_unknown -> true
  | C_pending -> (
      match mut with
      | No_pending_filter -> true
      | Pristine | No_gc_release | No_parent_check | No_parent_wait -> false)
  | C_accepted -> false

(** Whether the voter can produce a [Vote] for [h]. Pristine it must first have
    [c] in the certificate store, because handler.rs:693 blocks on notify_read
    until accept_verified_certificates has written it (cert_manager.rs:196,
    certificate_store.rs:250-269). {!No_parent_wait} deletes that block, so a
    still-parked [c] no longer stops the vote. *)
let vote_enabled mut c =
  match c with
  | C_accepted -> true
  | C_pending -> (
      match mut with
      | No_parent_wait -> true
      | Pristine | No_gc_release | No_parent_check | No_pending_filter -> false)
  | C_unknown -> false

(** DELIVER_D: the missing parent [d] arrives and is accepted, cascading into
    any child parked on it. Deliberately NOT gated on the horizon: the
    indirect-verification bypass (a peer-volunteered batch in which [d] is a
    parent of another certificate gets [mark_verified_indirectly] and skips the
    TooOld check, cert_validator.rs:288-324) keeps a narrow post-horizon
    delivery path open, and modeling it is what makes {!No_gc_release} an honest
    pin rather than one that leans on an omission. *)
let deliver_d_step s =
  match s.local_d with
  | D_absent -> [ { s with local_d = D_stored; local_c = cascade s.local_c } ]
  | D_stored | D_lost -> []

(** LOSE_D: the honest "[d] never arrives" branch, enabled only once the horizon
    has passed - below the horizon the fetcher still targets [d]
    (certificate_fetcher.rs:258-286, :350-379); past it every fetch target is
    strictly above [gc_round] and direct verification rejects [d] as [TooOld]
    (cert_validator.rs:114-125). *)
let lose_d_step s =
  match (s.local_d, s.horizon) with
  | D_absent, H_past -> [ { s with local_d = D_lost } ]
  | D_absent, H_below -> []
  | (D_stored | D_lost), (H_past | H_below) -> []

(** GC_TICK: this node's committed-round watch fires (gc.rs:66-92), the horizon
    advances past [d]'s round ([gc_round = committed_round - gc_depth],
    consensus/utils.rs:59-62), and process_gc_round releases anything parked on
    a collected parent (cert_manager.rs:227-241). *)
let gc_tick_step mut s =
  match s.horizon with
  | H_below ->
      [ { s with horizon = H_past; local_c = gc_release mut s.local_c } ]
  | H_past -> []

(** DELIVER_C: the verified certificate [c] reaches process_verified_certificates
    and is either accepted or parked ({!park}). Disabled once [local_c] has left
    [C_unknown] because a re-delivered copy hits the [is_pending] early return
    (cert_manager.rs:96-101) or the storage dedup (cert_validator.rs:88-130) and
    changes nothing. *)
let deliver_c_step mut s =
  match s.local_c with
  | C_unknown -> [ { s with local_c = park mut s } ]
  | C_pending | C_accepted -> []

(** REPORT_MISSING: the voter COMPUTES a [PrimaryResponse::MissingParents]
    (handler.rs:653-669) off the live gates. There is NO forced move - [req] may
    legitimately stay [R_open] while [local_c] is [C_unknown], which models the
    [requested_parents] filter (handler.rs:875-924) emptying the missing set on
    a repeat request. Fires only from [R_open]: once a response is cached, a
    repeat request is served by the cache (handler.rs:517-534, :564), which
    replays rather than computes, and this family claims nothing about a
    replay (see {!vote_round}). *)
let report_missing_step mut s =
  match s.req with
  | R_open ->
      if report_enabled mut s.local_c then [ { s with req = R_missing } ] else []
  | R_missing | R_voted -> []

(** ISSUE_VOTE: the voter COMPUTES a [Vote] (handler.rs:860-872), having
    cleared the quorum check on the parents that notify_read returned
    (handler.rs:700-738). Fires only from [R_open], for the same cache reason
    as {!report_missing_step}. *)
let issue_vote_step mut s =
  match s.req with
  | R_open ->
      if vote_enabled mut s.local_c then [ { s with req = R_voted } ] else []
  | R_missing | R_voted -> []

(** The transition relation: the six single-step rules, each contributing the
    empty list when disabled. Nothing reads or writes [peer_d]. Every component
    is monotone, so the reachable graph is a finite DAG whose only stuttering
    states are fully advanced ones - which is what makes S2's [Af] honest and
    what makes the {!No_gc_release} pin bite (it creates a stuttering state that
    still has a parked certificate). *)
let next_with mut s =
  List.concat
    [
      deliver_d_step s;
      lose_d_step s;
      gc_tick_step mut s;
      deliver_c_step mut s;
      report_missing_step mut s;
      issue_vote_step mut s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state of the world in which [w] is the faulty signer and does
    NOT hold [d]: the author's vote request for [h] has reached [v], [v] has
    computed no response yet, [c] is not yet delivered, [d] is not yet held, and
    [v]'s horizon is still below [d]'s round. *)
let initial =
  {
    local_c = C_unknown;
    local_d = D_absent;
    horizon = H_below;
    req = R_open;
    peer_d = W_without_parent;
  }

(** The sibling initial state of the all-honest world, in which [w] is an
    honest signer of [c] and therefore DOES hold [d]. The two initial states
    differ only in the frozen hidden peer bit - i.e. in whether the [f = 1]
    fault budget is spent on [w] - which is exactly the branch [v] can never
    resolve, since both worlds produce the same quorum bitmap on [c]. *)
let initial_peer_holds = { initial with peer_d = W_holds_parent }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Cert_pending
      (** local_c = C_pending : [c] is parked in [v]'s pending map
          (pending_v(c)) *)
  | Cert_accepted
      (** local_c = C_accepted : [c] has been written to [v]'s certificate store
          by accept_verified_certificates (accepted_v(c)) *)
  | Parent_stored
      (** local_d = D_stored : [v] holds [c]'s parent [d] (stored_v(d)) *)
  | Horizon_past
      (** horizon = H_past : [v]'s gc horizon has passed [d]'s round
          (gc_past_v(d)) *)
  | Peer_holds_parent
      (** peer_d = W_holds_parent : the signer [w] actually holds [d]
          (holds_w(d)) - i.e. [w] is one of [c]'s honest signers rather than
          the tolerated faulty one. The hidden fault branch V1 can never
          resolve *)
  | Vote_unanswered
      (** req = R_open : [v] has COMPUTED no response for [h] yet - its
          per-author vote cache holds no entry for this header digest
          (handler.rs:510-516) - so the next response it emits is one it
          computes (unanswered_v(h)) *)
  | Missing_reported
      (** req = R_missing : [v] computed a [MissingParents] response naming [c]
          (handler.rs:653-669) (missing_computed(v->a,c)) *)
  | Vote_issued
      (** req = R_voted : [v] computed a [Vote] on [h] (handler.rs:860-872)
          (vote_issued(v->a)) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Cert_pending -> (
      match s.local_c with
      | C_pending -> true
      | C_unknown | C_accepted -> false)
  | Cert_accepted -> (
      match s.local_c with
      | C_accepted -> true
      | C_unknown | C_pending -> false)
  | Parent_stored -> (
      match s.local_d with D_stored -> true | D_absent | D_lost -> false)
  | Horizon_past -> (
      match s.horizon with H_past -> true | H_below -> false)
  | Peer_holds_parent -> (
      match s.peer_d with
      | W_holds_parent -> true
      | W_without_parent -> false)
  | Vote_unanswered -> (
      match s.req with R_open -> true | R_missing | R_voted -> false)
  | Missing_reported -> (
      match s.req with R_missing -> true | R_open | R_voted -> false)
  | Vote_issued -> (
      match s.req with R_voted -> true | R_open | R_missing -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Cert_pending -> "pending_v(c)"
  | Cert_accepted -> "accepted_v(c)"
  | Parent_stored -> "stored_v(d)"
  | Horizon_past -> "gc_past_v(d)"
  | Peer_holds_parent -> "holds_w(d)"
  | Vote_unanswered -> "unanswered_v(h)"
  | Missing_reported -> "missing_computed(v->a,c)"
  | Vote_issued -> "vote_issued(v->a)"

(** The exact CTLK checker over this family's ordered state and view. *)
module Checker = System.Make (State) (View)

(** The checker spec under a mutation: the two initial states (the frozen peer
    branch), mutation-parameterized transitions, the four-role view projection,
    the atom valuation. *)
let spec_of mut =
  {
    Checker.init = [ initial; initial_peer_holds ];
    next = next_with mut;
    view;
    label;
  }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
