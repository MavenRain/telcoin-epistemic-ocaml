(** Finite interpreted system for the PARENT_CLAIM_BINDING family: the
    two-sided binding of ONE missing parent certificate to exactly ONE
    proposer, on telcoin-network's vote path. File citations refer to
    Telcoin-Association/telcoin-network at git HEAD [0c59c15b] and every one of
    them was opened in that checkout while writing this module.

    {1 The mechanism}

    A primary [j] that is asked to vote on a peer header whose parents it does
    not have runs three gates, and the proposer that answers runs a fourth:

    - {b the first-come slot claim} (voter). [check_for_missing_parents]
      (handler.rs:879-924) asks [identify_unkown_parents]
      (state_sync/header_validator.rs:198-229) which declared parents are
      neither in storage nor pending, then claims each one for THIS header's
      author under an [Entry::Vacant] guard, handler.rs:910-921:
      {v
      unknown_certs.retain(|digest| {
          let key = (header.round().saturating_sub(1), *digest);
          if let Entry::Vacant(e) = current_requests.entry(key) {
              e.insert(header.author().clone()); true
          } else { false }
      });
      v}
      The [else { false }] silently removes the digest from a LATER author's
      missing list. The slot is released only by age pruning as the round
      advances (handler.rs:902-908).
    - {b the empty-missing fall-through} (voter). handler.rs:659-669 returns
      [PrimaryResponse::MissingParents(missing)] only when [missing] is
      non-empty; with the digest filtered out, [missing] can be empty and the
      flow falls through to handler.rs:688-693
      ([notify_read_parent_certificates], "NOTE: this check is necessary for
      correctness"), which awaits [notify_read] per parent
      (state_sync/header_validator.rs:56-63). [notify_read]
      (storage/src/stores/certificate_store.rs:250-269) is a bare
      [receiver.await] with NO internal timeout.
    - {b the requester binding} (voter). Certificates that ride along with a
      vote request are sanitized BEFORE any signature work,
      handler.rs:936-946:
      {v
      let requested_parents = self.requested_parents.lock();
      parents.retain(|cert| {
          let req = (cert.round(), cert.digest());
          if let Some(authority) = requested_parents.get(&req) {
              authority == header.author()
          } else { false }
      });
      v}
      and only the survivors are handed to
      [self.state_sync.process_peer_certificate(parent)]
      (handler.rs:948-951), i.e. only the survivors ever reach
      [validate_and_verify] (state_sync/cert_validator.rs:100-104, 111-130 ->
      types/src/primary/certificate.rs:225-251). The dropped bytes were marked
      [SignatureVerificationState::Unverified] at handler.rs:672-682 and were
      never verified, which is exactly why dropping one teaches [j] nothing.
    - {b the author's disclosure filter} (proposer). certifier.rs:143-168
      answers a [MissingParents(M)] reply by reading [M] from its own store
      but first intersecting it with its own declared parents
      (certifier.rs:150-151, [.filter(|parent| header.parents().contains(parent))])
      and then requiring the read to have returned exactly as many
      certificates as were asked for (certifier.rs:157-165). [read_all]
      (storage/src/stores/certificate_store.rs:243-248) returns
      [Vec<Option<Certificate>>] and the [.flatten()] at certifier.rs:154 drops
      the [None]s, so the count check is load-bearing and is modeled here.

    {1 Components and the two scenarios}

    The voter-side gates and the author-side filter are enforced by DIFFERENT
    nodes on DIFFERENT messages and do not interact, so composing them would be
    a pure product with no shared transition. This model therefore carries them
    as two DISJOINT scenario components of one state type, selected by the
    initial state list (six initial states, four voter worlds and two author
    stores). Nothing is hidden by the split: within the voter scenario the
    author's own filter is on the path when [a] supplies [d] (the digest IS
    declared in [h_a], so certifier.rs:151 passes), and within the author
    scenario the voter-side table is irrelevant because the misbehaving voter
    is the one naming a digest.

    Voter scenario. Authors [a] and [b] both propose headers whose parent set
    contains one digest [d] that [j] lacks. [j] sees [h_a] first, claims
    [(r-1,d)] for [a], and answers [MissingParents([d])]; then [j] sees [h_b],
    whose copy of [d] is filtered off by the [Vacant] guard, so [j] falls
    through into the blocking [notify_read]. The hidden component is
    {!world} - what actually exists out in the network - and [j]'s view never
    contains it.

    Author scenario. Proposer [a]'s header [h_a] declares exactly one parent
    [p1]; [a]'s store holds [p1], and (depending on the initial state) also an
    UNdeclared certificate [p2]. A voter answers with [MissingParents] naming
    either the declared [p1] or the undeclared [p2].

    {1 Role mapping}

    - [V1] is the voter [j] and is the family's ONLY knowledge agent: its view
      is its whole local evaluation state (which author owns the slot, whether
      [d] is in its store, what it received and what it dropped, whether it
      voted or was torn down) and NOTHING of {!world}.
    - [V2] is the proposer [a]; in the author scenario its view is its own
      certificate store plus its own request state. It is a real,
      non-constant view but NO statement asserts [K (V2, _)] - there is
      nothing hidden from [a] in that scenario.
    - [b], the second proposer, the third honest holder [c] and the
      misbehaving voter are phantom parties folded into {!world} and the
      author-scenario branching; they are never a {!Validator.t} and never
      appear under [K].
    - [V0] and [V3] .. [V9] are idle: constant blank view, never under [K].

    Each agent's view is [View_idle] on the scenario it does not participate
    in, so the two components' view classes never mix. *)

(** What is actually out in the network in the voter scenario. HIDDEN from
    [j]: no constructor of {!view} mentions it. [b] offers a certificate
    claiming [(r-1,d)] in exactly the two worlds where it has bytes to send;
    the bytes are genuine in {!W_b_holds} and forged in {!W_bogus}, and [j]
    cannot tell those apart at the moment it drops them because
    handler.rs:936-946 runs before handler.rs:948-951. *)
type world =
  | W_none
      (** [d] was never built: author [a] is Byzantine and the digest names a
          header nobody made. [b] holds nothing and offers nothing. *)
  | W_bogus
      (** [d] was never built, and [b] is Byzantine: it hands [j] unverified
          bytes claiming [(r-1,d)] inside a vote request. *)
  | W_b_holds
      (** [d] genuinely exists (author [a] built and certified it) and [b]
          holds a copy, which it offers inside a vote request. *)
  | W_c_holds
      (** [d] genuinely exists and a third honest peer [c] holds a copy, but
          [c] has no reason to push it and [b] holds nothing. *)

(** Total order index for {!world}. *)
let world_index = function
  | W_none -> 0
  | W_bogus -> 1
  | W_b_holds -> 2
  | W_c_holds -> 3

(** Total order on {!world}. *)
let world_compare a b = Int.compare (world_index a) (world_index b)

(** [true] iff a genuine certificate for [d] exists somewhere in the network.
    This is the family's hidden global-possession fact. *)
let world_d_exists = function
  | W_b_holds | W_c_holds -> true
  | W_none | W_bogus -> false

(** [true] iff [b] hands [j] a vote request carrying bytes that claim
    [(r-1,d)] - genuine in {!W_b_holds}, forged in {!W_bogus}. *)
let world_b_offers = function
  | W_bogus | W_b_holds -> true
  | W_none | W_c_holds -> false

(** [true] iff [b]'s offered bytes are the genuine certificate, i.e. iff they
    would survive [Certificate::validate_and_verify]
    (types/src/primary/certificate.rs:225-251). *)
let world_b_holds_genuine = function
  | W_b_holds -> true
  | W_none | W_bogus | W_c_holds -> false

(** The voter [j]'s local evaluation state in the voter scenario. This IS
    [j]'s view: every constructor is something [j] can read off its own
    [requested_parents] table, its own certificate store and the requests it
    has served. *)
type vphase
  = Ph_start
      (** nothing received yet; the [(r-1,d)] slot is vacant *)
  | Ph_a_hinted
      (** [j] served [h_a] with empty parents, [check_for_missing_parents]
          claimed [(r-1,d)] for [a] (handler.rs:910-921) and [j] replied
          [MissingParents([d])] (handler.rs:659-669) *)
  | Ph_b_filtered
      (** [j] served [h_b] with empty parents; the [Entry::Vacant] guard was
          occupied so [d] was dropped from [b]'s missing list
          (handler.rs:915-920), [missing] came back empty, and [j] fell
          through into the blocking [notify_read_parent_certificates]
          (handler.rs:688-693) *)
  | Ph_b_hinted
      (** [j] told [b] that [d] is missing, rebinding the slot to [b]. Only
          reachable under {!No_vacant_claim} *)
  | Ph_b_offer_dropped
      (** [b] handed [j] a vote request carrying bytes claiming [(r-1,d)];
          [try_accept_unknown_certs]'s [retain] dropped them because the slot
          names [a] (handler.rs:936-946). [j] is still parked in
          [notify_read] *)
  | Ph_b_offer_taken
      (** the same bytes survived [retain] and were handed to
          [process_peer_certificate] (handler.rs:948-951). Only reachable
          under {!No_requester_binding}. [j] is still parked in
          [notify_read] *)
  | Ph_stored
      (** the genuine certificate for [d] is in [j]'s certificate store and
          [notify_read] has woken *)
  | Ph_b_voted
      (** [j] finished evaluating [h_b] and issued its vote
          (handler.rs:860-872) *)
  | Ph_b_timedout
      (** the evaluation of [h_b] was torn down by a wall-clock deadline
          without ever obtaining [d] *)

(** Total order index for {!vphase}. *)
let vphase_index = function
  | Ph_start -> 0
  | Ph_a_hinted -> 1
  | Ph_b_filtered -> 2
  | Ph_b_hinted -> 3
  | Ph_b_offer_dropped -> 4
  | Ph_b_offer_taken -> 5
  | Ph_stored -> 6
  | Ph_b_voted -> 7
  | Ph_b_timedout -> 8

(** Total order on {!vphase}. *)
let vphase_compare a b = Int.compare (vphase_index a) (vphase_index b)

(** What proposer [a]'s certificate store holds in the author scenario. [p1]
    is the ONE parent [h_a] declares; [p2] is a certificate [a] happens to
    have but did not declare. Constant along every run: a store only grows,
    and nothing in this scenario writes to it. *)
type astore =
  | As_only_p1  (** [a] holds the declared parent [p1] and nothing else *)
  | As_p1_and_p2
      (** [a] also holds the UNdeclared certificate [p2], so
          [read_all] would return [Some p2] for it
          (storage/src/stores/certificate_store.rs:243-248) *)

(** Total order index for {!astore}. *)
let astore_index = function As_only_p1 -> 0 | As_p1_and_p2 -> 1

(** Total order on {!astore}. *)
let astore_compare a b = Int.compare (astore_index a) (astore_index b)

(** Proposer [a]'s own state while answering a [MissingParents] reply
    (certifier.rs:138-219). *)
type aphase =
  | Ph_auth_start  (** [a] has sent [h_a] and is waiting on vote responses *)
  | Ph_auth_asked_declared
      (** a voter answered [MissingParents([p1])]: the digest IS declared in
          [h_a] *)
  | Ph_auth_asked_undeclared
      (** a misbehaving voter answered [MissingParents([p2])]: the digest is
          NOT declared in [h_a] *)
  | Ph_auth_served_declared
      (** [a] read [p1] and re-sent the vote request carrying it
          (certifier.rs:146-155, 171-172) *)
  | Ph_auth_served_undeclared
      (** [a] served the undeclared [p2]. Only reachable under
          {!No_author_parent_filter} *)
  | Ph_auth_abort
      (** the count check failed and [a] returned
          [DagError::ProposedHeaderMissingCertificates] (certifier.rs:157-165),
          ending that peer's vote task; the collector records the failure at
          certifier.rs:350-357 and keeps waiting on the other peers *)

(** Total order index for {!aphase}. *)
let aphase_index = function
  | Ph_auth_start -> 0
  | Ph_auth_asked_declared -> 1
  | Ph_auth_asked_undeclared -> 2
  | Ph_auth_served_declared -> 3
  | Ph_auth_served_undeclared -> 4
  | Ph_auth_abort -> 5

(** Total order on {!aphase}. *)
let aphase_compare a b = Int.compare (aphase_index a) (aphase_index b)

(** The joint global state: one of the two disjoint scenario components. *)
type state =
  | Voter of world * vphase
      (** the voter [j] evaluating [h_a] then [h_b] against the hidden
          {!world} *)
  | Author of astore * aphase
      (** the proposer [a] answering a [MissingParents] reply out of the
          store it happens to hold *)

(** Total deterministic comparison over ALL state fields, with the
    cross-constructor arms spelled out. *)
let state_compare s1 s2 =
  match (s1, s2) with
  | Voter (w1, p1), Voter (w2, p2) ->
      let c = world_compare w1 w2 in
      if Bool.not (Int.equal c 0) then c else vphase_compare p1 p2
  | Voter (_, _), Author (_, _) -> -1
  | Author (_, _), Voter (_, _) -> 1
  | Author (t1, q1), Author (t2, q2) ->
      let c = astore_compare t1 t2 in
      if Bool.not (Int.equal c 0) then c else aphase_compare q1 q2

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    [Vj] is the voter [j] = [V1]: its whole local evaluation state and
    NOTHING of {!world} - [j]'s [requested_parents] table records only WHOM it
    asked, never who HOLDS, and the bytes it drops at handler.rs:936-946 were
    never verified.

    [Va] is the proposer [a] = [V2]: its own certificate store and its own
    request state. Nothing in the author scenario is hidden from [a], so no
    statement asserts [K (V2, _)].

    [View_idle] is the constant blank view of [V0] and [V3] .. [V9], and also
    the view each of [V1]/[V2] has on the scenario it does not participate in,
    which keeps the two components' view classes disjoint. *)
type view =
  | Vj of vphase  (** the voter [j] = [V1] inside the voter scenario *)
  | Va of astore * aphase
      (** the proposer [a] = [V2] inside the author scenario *)
  | View_idle  (** the constant blank view: idle validators and off-scenario *)

(** Total deterministic order over ALL fields of [a]'s view. *)
let va_compare (t1, q1) (t2, q2) =
  let c = astore_compare t1 t2 in
  if Bool.not (Int.equal c 0) then c else aphase_compare q1 q2

(** Total order on views: [View_idle] < [Vj] < [Va]. Every constructor pair is
    spelled: no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (Vj _ | Va _) -> -1
  | (Vj _ | Va _), View_idle -> 1
  | Vj p1, Vj p2 -> vphase_compare p1 p2
  | Vj _, Va _ -> -1
  | Va _, Vj _ -> 1
  | Va (t1, q1), Va (t2, q2) -> va_compare (t1, q1) (t2, q2)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. [V1] is the voter [j], the family's only knowledge agent;
    [V2] is the proposer [a], with a real but never-[K]'d view; every other
    validator is idle with the constant blank view and never appears under
    [K]. *)
let view v s =
  match v with
  | Validator.V1 -> (
      match s with Voter (_, ph) -> Vj ph | Author (_, _) -> View_idle)
  | Validator.V2 -> (
      match s with
      | Voter (_, _) -> View_idle
      | Author (st, aph) -> Va (st, aph))
  | Validator.V0 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at [0c59c15b] *)
  | No_requester_binding
      (** delete the [authority == header.author()] comparison at
          handler.rs:940-944, making the [retain] closure
          [requested_parents.get(&req).is_some()]. This ADDS the transition
          [Ph_b_filtered -> Ph_b_offer_taken]: bytes offered by [b] survive
          sanitization and reach [process_peer_certificate] even though the
          slot names [a].

          Sibling-repair hunt: [process_peer_certificate] ->
          [process_certificate(_, external = true)] ->
          [validate_and_verify] (state_sync/cert_validator.rs:100-104,
          111-130) -> [Certificate::validate_and_verify]
          (types/src/primary/certificate.rs:225-251) checks the epoch, the
          header, quorum weight and the BLS aggregate, so FORGERY is fully
          repaired - and that repair IS modeled: {!W_bogus} has no
          [Ph_b_offer_taken -> Ph_stored] edge. That is precisely why the
          pinned statement is a request-BINDING invariant and not an
          unforgeability one: the binding itself has no second enforcer, and
          the admission of a valid-but-unrequested certificate into [j]'s
          pending/fetcher machinery survives every downstream check. *)
  | No_vacant_claim
      (** replace the [Entry::Vacant] claim at handler.rs:915-920 with an
          unconditional [insert]-and-keep, so a later author's copy of the
          digest is kept on its missing list and the slot is rebound to it.
          This REPLACES [Ph_a_hinted -> Ph_b_filtered] with
          [Ph_a_hinted -> Ph_b_hinted]: [b] IS told [d] is missing, so
          [reply(j,h_b) = MissingParents([d])] becomes reachable.

          Sibling-repair hunt: no other route re-establishes the exclusivity.
          [try_accept_unknown_certs] (handler.rs:930-954) reads the SAME
          table, so rebinding it hands [b] the admission too rather than
          repairing anything (the two gates are mutually reinforcing, not
          mutually repairing) - which is why the rebound slot then DROPS [a]'s
          own later supply, modeled as the loss of the [Ph_stored] edge in
          {!W_c_holds}. [identify_unkown_parents]'s pending suppression
          (state_sync/header_validator.rs:221-228 ->
          state_sync/pending_cert_manager.rs:171-173,
          [unknown.retain(|digest| !self.pending.contains_key(digest))])
          covers only locally PENDING digests, and [d] is not pending in this
          run. The certificate fetcher is not a repair either: [Ancestors] is
          fired only from state_sync/cert_manager.rs:169-177 (a processed
          CERTIFICATE with missing parents) and state_sync/cert_validator.rs
          :201-204 (a TooNew certificate), and here [j] has seen only a
          HEADER naming [d]. *)
  | No_author_parent_filter
      (** delete the [.filter(|parent| header.parents().contains(parent))] at
          certifier.rs:150-151. This ADDS the transition
          [Ph_auth_asked_undeclared -> Ph_auth_served_undeclared], but ONLY
          from {!As_p1_and_p2}.

          Sibling-repair hunt: the count check at certifier.rs:157-165 IS a
          sibling and it IS modeled - with the filter deleted and the store at
          {!As_only_p1}, [read_all] returns [[None]], the [.flatten()] at
          certifier.rs:154 drops it, [parents.len() = 0 <> 1 = expected_count]
          and [a] still aborts. The deletion therefore bites only when [a]
          actually holds the undeclared certificate, which is exactly the
          case the filter exists for. On the voter's side there is no repair:
          in this scenario the voter DID name the digest in its own [missing]
          list, so handler.rs:537-548's [parents.len() == missing.len()] and
          [missing.contains(&parent)] checks pass too. *)
  | No_evaluation_deadline
      (** delete EVERY wall-clock bound on a blocked vote evaluation: both
          [tokio::time::timeout(max_header_delay, self.vote_inner(header,
          parents))] at handler.rs:582-586 AND the
          [_ = cancel => ()] arm of the [tokio::select!] that drives the
          spawned vote task at network/mod.rs:1531-1551. This REMOVES every
          [_ -> Ph_b_timedout] transition, so a blocked evaluation that never
          obtains [d] becomes a terminal state and the kernel stutters it
          forever.

          Sibling-repair hunt: BOTH sites must go, and that is why this
          constructor deletes both. Deleting only handler.rs:582-586 is
          silently repaired by the network layer's [cancel] arm, which drops
          the [request_handler.vote(..)] future outright; deleting only the
          [cancel] arm is repaired by the [max_header_delay] timeout. Nothing
          else bounds the wait: [notify_read]
          (storage/src/stores/certificate_store.rs:250-269) is a bare
          [receiver.await] with no internal timeout, and
          [notify_read_parent_certificates]
          (state_sync/header_validator.rs:56-63) just drains a
          [FuturesOrdered] of them. *)

(** The wall-clock teardown of a blocked evaluation of [h_b]: present under
    every mutation except {!No_evaluation_deadline}, which deletes both of its
    real-code sites at once. *)
let deadline_step mut w =
  match mut with
  | Pristine | No_requester_binding | No_vacant_claim | No_author_parent_filter
    ->
      [ Voter (w, Ph_b_timedout) ]
  | No_evaluation_deadline -> []

(** [b]'s vote request carrying bytes that claim [(r-1,d)], as sanitized by
    [try_accept_unknown_certs] (handler.rs:930-954): dropped while the slot
    names [a], admitted once the binding comparison is gone. *)
let offer_step mut w =
  if world_b_offers w then
    match mut with
    | Pristine | No_vacant_claim | No_author_parent_filter
    | No_evaluation_deadline ->
        [ Voter (w, Ph_b_offer_dropped) ]
    | No_requester_binding -> [ Voter (w, Ph_b_offer_taken) ]
  else []

(** The bound author [a] answering the [MissingParents([d])] hint it received
    at {!Ph_a_hinted} with the genuine certificate; [retain] admits it because
    the slot names [a], and [process_peer_certificate] stores it. Available in
    exactly the worlds where the certificate exists. *)
let supply_step w =
  if world_d_exists w then [ Voter (w, Ph_stored) ] else []

(** The voter scenario's transition relation under a mutation. *)
let voter_next mut w ph =
  match ph with
  | Ph_start -> [ Voter (w, Ph_a_hinted) ]
  | Ph_a_hinted -> (
      match mut with
      | Pristine | No_requester_binding | No_author_parent_filter
      | No_evaluation_deadline ->
          [ Voter (w, Ph_b_filtered) ]
      | No_vacant_claim -> [ Voter (w, Ph_b_hinted) ])
  | Ph_b_filtered ->
      List.concat [ offer_step mut w; supply_step w; deadline_step mut w ]
  | Ph_b_hinted ->
      (* the rebound slot now names [b], so [b]'s copy is admitted - and [a]'s
         own later supply is dropped by the very same [retain], which is why
         only [W_b_holds] resolves here and [W_c_holds] no longer does. *)
      List.concat
        [
          (if world_b_holds_genuine w then [ Voter (w, Ph_stored) ] else []);
          deadline_step mut w;
        ]
  | Ph_b_offer_dropped ->
      (* the drop leaves [j] exactly where it was: still parked in
         [notify_read], still waiting on the bound author. *)
      List.concat [ supply_step w; deadline_step mut w ]
  | Ph_b_offer_taken ->
      (* admitted onto the vote path; forged bytes are then rejected by
         [Certificate::validate_and_verify] and nothing is stored. *)
      List.concat
        [
          (if world_b_holds_genuine w then [ Voter (w, Ph_stored) ] else []);
          deadline_step mut w;
        ]
  | Ph_stored -> [ Voter (w, Ph_b_voted) ]
  | Ph_b_voted -> []
  | Ph_b_timedout -> []

(** The author scenario's transition relation under a mutation. *)
let author_next mut st aph =
  match aph with
  | Ph_auth_start ->
      [
        Author (st, Ph_auth_asked_declared);
        Author (st, Ph_auth_asked_undeclared);
      ]
  | Ph_auth_asked_declared -> [ Author (st, Ph_auth_served_declared) ]
  | Ph_auth_asked_undeclared -> (
      match mut with
      | Pristine | No_requester_binding | No_vacant_claim
      | No_evaluation_deadline ->
          [ Author (st, Ph_auth_abort) ]
      | No_author_parent_filter -> (
          match st with
          | As_only_p1 ->
              (* the count check still fires: read_all -> [None] -> flatten ->
                 [] -> 0 <> 1 (certifier.rs:154, 157-165). *)
              [ Author (st, Ph_auth_abort) ]
          | As_p1_and_p2 -> [ Author (st, Ph_auth_served_undeclared) ]))
  | Ph_auth_served_declared -> []
  | Ph_auth_served_undeclared -> []
  | Ph_auth_abort -> []

(** The transition relation: each state advances inside its own scenario
    component, so the two components stay disjoint. Terminal states are
    stutter-closed by the kernel, which is what makes
    {!No_evaluation_deadline} refute the until-conjunct. *)
let next_with mut s =
  match s with
  | Voter (w, ph) -> voter_next mut w ph
  | Author (st, aph) -> author_next mut st aph

(** The pristine transition relation. *)
let next = next_with Pristine

(** Voter scenario, [d] never built and [b] silent. *)
let initial = Voter (W_none, Ph_start)

(** Voter scenario, [d] never built and [b] Byzantine: it offers forged bytes
    claiming [(r-1,d)]. *)
let initial_bogus = Voter (W_bogus, Ph_start)

(** Voter scenario, [d] genuinely exists and [b] holds and offers a copy. *)
let initial_b_holds = Voter (W_b_holds, Ph_start)

(** Voter scenario, [d] genuinely exists at a third honest peer [c] that never
    volunteers it. *)
let initial_c_holds = Voter (W_c_holds, Ph_start)

(** Author scenario, [a] holding only its one declared parent. *)
let initial_author_lean = Author (As_only_p1, Ph_auth_start)

(** Author scenario, [a] also holding an undeclared certificate - the only
    configuration in which deleting certifier.rs:150-151 changes anything. *)
let initial_author_rich = Author (As_p1_and_p2, Ph_auth_start)

(** Every initial state: the four hidden voter worlds and the two author
    stores. *)
let inits =
  [
    initial;
    initial_bogus;
    initial_b_holds;
    initial_c_holds;
    initial_author_lean;
    initial_author_rich;
  ]

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Bound_a
      (** the [(r-1,d)] slot of [j]'s [requested_parents] is owned by author
          [a] and the evaluation of [h_b] has not yet resolved
          (handler.rs:910-921; the slot is released by the age pruning at
          handler.rs:902-908 as the round advances) *)
  | Bound_b  (** the same slot is owned by author [b] instead *)
  | Hb_told_missing
      (** [j]'s reply to [b] names [d], i.e.
          [reply(j,h_b) = MissingParents([d])] (handler.rs:662-668) *)
  | Hb_blocked
      (** [j]'s evaluation of [h_b] is parked in
          [notify_read_parent_certificates] (handler.rs:688-693) *)
  | Hb_timedout
      (** that evaluation was torn down by a wall-clock deadline without
          obtaining [d] *)
  | Offer_seen
      (** [b] handed [j] a vote request carrying bytes claiming [(r-1,d)] *)
  | Offer_admitted
      (** those bytes survived the [retain] of handler.rs:936-946 and were
          handed to [process_peer_certificate] (handler.rs:948-951) *)
  | Stored  (** the genuine certificate for [d] is in [j]'s store *)
  | D_exists
      (** HIDDEN: a genuine certificate for [d] exists somewhere in the
          network *)
  | B_holds_d
      (** HIDDEN: [b] is specifically the peer holding it - used only as the
          R2 non-singleton probe for the family's one positive [K] *)
  | A_asked_undeclared
      (** a voter answered [a] with [MissingParents] naming a digest [h_a]
          does not declare *)
  | A_served_undeclared  (** [a] served that undeclared certificate *)
  | A_aborted
      (** [a] returned [DagError::ProposedHeaderMissingCertificates] and tore
          that peer's vote request down (certifier.rs:157-165) *)

(** Atom valuation inside the voter scenario. *)
let voter_label a w ph =
  match a with
  | Bound_a -> (
      match ph with
      | Ph_a_hinted | Ph_b_filtered | Ph_b_offer_dropped | Ph_b_offer_taken ->
          true
      | Ph_start | Ph_b_hinted | Ph_stored | Ph_b_voted | Ph_b_timedout -> false)
  | Bound_b -> (
      match ph with
      | Ph_b_hinted -> true
      | Ph_start | Ph_a_hinted | Ph_b_filtered | Ph_b_offer_dropped
      | Ph_b_offer_taken | Ph_stored | Ph_b_voted | Ph_b_timedout ->
          false)
  | Hb_told_missing -> (
      match ph with
      | Ph_b_hinted -> true
      | Ph_start | Ph_a_hinted | Ph_b_filtered | Ph_b_offer_dropped
      | Ph_b_offer_taken | Ph_stored | Ph_b_voted | Ph_b_timedout ->
          false)
  | Hb_blocked -> (
      match ph with
      | Ph_b_filtered | Ph_b_offer_dropped | Ph_b_offer_taken -> true
      | Ph_start | Ph_a_hinted | Ph_b_hinted | Ph_stored | Ph_b_voted
      | Ph_b_timedout ->
          false)
  | Hb_timedout -> (
      match ph with
      | Ph_b_timedout -> true
      | Ph_start | Ph_a_hinted | Ph_b_filtered | Ph_b_hinted
      | Ph_b_offer_dropped | Ph_b_offer_taken | Ph_stored | Ph_b_voted ->
          false)
  | Offer_seen -> (
      match ph with
      | Ph_b_offer_dropped | Ph_b_offer_taken -> true
      | Ph_start | Ph_a_hinted | Ph_b_filtered | Ph_b_hinted | Ph_stored
      | Ph_b_voted | Ph_b_timedout ->
          false)
  | Offer_admitted -> (
      match ph with
      | Ph_b_offer_taken -> true
      | Ph_start | Ph_a_hinted | Ph_b_filtered | Ph_b_hinted
      | Ph_b_offer_dropped | Ph_stored | Ph_b_voted | Ph_b_timedout ->
          false)
  | Stored -> (
      match ph with
      | Ph_stored | Ph_b_voted -> true
      | Ph_start | Ph_a_hinted | Ph_b_filtered | Ph_b_hinted
      | Ph_b_offer_dropped | Ph_b_offer_taken | Ph_b_timedout ->
          false)
  | D_exists -> world_d_exists w
  | B_holds_d -> world_b_holds_genuine w
  | A_asked_undeclared -> false
  | A_served_undeclared -> false
  | A_aborted -> false

(** Atom valuation inside the author scenario. The voter-scenario atoms are
    all false here: the two components describe different runs. *)
let author_label a aph =
  match a with
  | Bound_a | Bound_b | Hb_told_missing | Hb_blocked | Hb_timedout | Offer_seen
  | Offer_admitted | Stored | D_exists | B_holds_d ->
      false
  | A_asked_undeclared -> (
      match aph with
      | Ph_auth_asked_undeclared -> true
      | Ph_auth_start | Ph_auth_asked_declared | Ph_auth_served_declared
      | Ph_auth_served_undeclared | Ph_auth_abort ->
          false)
  | A_served_undeclared -> (
      match aph with
      | Ph_auth_served_undeclared -> true
      | Ph_auth_start | Ph_auth_asked_declared | Ph_auth_asked_undeclared
      | Ph_auth_served_declared | Ph_auth_abort ->
          false)
  | A_aborted -> (
      match aph with
      | Ph_auth_abort -> true
      | Ph_auth_start | Ph_auth_asked_declared | Ph_auth_asked_undeclared
      | Ph_auth_served_declared | Ph_auth_served_undeclared ->
          false)

(** Atom valuation over the global state. *)
let label a s =
  match s with
  | Voter (w, ph) -> voter_label a w ph
  | Author (_, aph) -> author_label a aph

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Bound_a -> "bound(j,(r-1,d))=a"
  | Bound_b -> "bound(j,(r-1,d))=b"
  | Hb_told_missing -> "reply(j,h_b)=MissingParents([d])"
  | Hb_blocked -> "blocked(j,h_b)"
  | Hb_timedout -> "timeout(j,h_b)"
  | Offer_seen -> "offered(b,d)"
  | Offer_admitted -> "admitted(j,d,from=b)"
  | Stored -> "stored(j,d)"
  | D_exists -> "exists(d)"
  | B_holds_d -> "holds(b,d)"
  | A_asked_undeclared -> "named_undeclared(v,a)"
  | A_served_undeclared -> "served_undeclared(a)"
  | A_aborted -> "aborted(a,v)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation ({!Denote}, lib/internal/DESIGN.md), pinned to
    agree with {!System} at every reachable world by
    test/t_parent_claim_binding_topos.ml.

    Every transition of this model strictly advances a phase index, so the
    reachability relation is antisymmetric and the frame is a genuine finite
    POSET (run, not guessed: the [poset] group of the topos gate is green on
    the pristine model and on all four mutants). *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the six initial states (four hidden
    voter worlds, two author stores - the same list as {!inits}, spelled out
    here so the integrator can read it off [spec_of] verbatim), the
    mutation-parameterized transitions, the two-agent view and the atom
    valuation. *)
let spec_of mut =
  {
    Checker.init =
      [
        initial;
        initial_bogus;
        initial_b_holds;
        initial_c_holds;
        initial_author_lean;
        initial_author_rich;
      ];
    next = next_with mut;
    view;
    label;
  }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
