(** Finite interpreted system for the CAUSAL_HANDOFF family: the primary's
    state-sync repair loop as one object - the pending-certificate map, the
    ordered release of unblocked dependents into the consensus DAG, the
    garbage-collection drain of blocked-parent keys, and the certificate
    fetcher's gc floor on its catch-up targets. File citations refer to
    Telcoin-Association/telcoin-network at 0c59c15b and every one of them was
    opened in this checkout.

    {2 The modelled mechanism}

    One causal chain of three certificates on one authority's lineage:

    - [Cert_p] at round [r0] - the MISSING parent. It is not in the local
      certificate store; it is what the fetcher is chasing.
    - [Cert_a] at round [r0 + 1] - arrived, parked because [Cert_p] is missing
      (crates/consensus/primary/src/state_sync/cert_manager.rs:108-118: a
      certificate above [gc_round + 1] whose parents are absent is handed to
      [insert_pending]).
    - [Cert_b] at round [r0 + 2] - arrived, parked because [Cert_a] is itself
      pending, hence absent from storage.

    The blocked-parent index is
    [missing_for_pending: BTreeMap<(Round, HeaderDigest), HashSet<HeaderDigest>>]
    (pending_cert_manager.rs:42-46, keyed by the PARENT's round - the verbatim
    comment there is [/// The keys are (round, digest) to enable garbage
    collection by round]). Insertion uses the parent's round,
    [let parent_round = certificate.round() - 1] (pending_cert_manager.rs:64,
    :76-78), so the two keys here are [(r0, p)] holding {a} and [(r0+1, a)]
    holding {b}.

    Two release paths write the same handoff queue:

    - ARRIVAL. [Cert_p] shows up, has no missing parents, and unlocks the
      cascade: [let mut unlocked = self.pending.update_pending(cert.round(),
      digest)?; unlocked.push_front(cert); self.accept_verified_certificates
      (unlocked).await?;] (cert_manager.rs:121-124). [update_pending]
      (pending_cert_manager.rs:85-131) is itself causal - a certificate is moved
      to [ready_certificates] only once its LAST missing parent is removed
      (:114-126), and its own key is enqueued for the worklist at :122 only
      after it has been pushed onto the ready queue at :125 - so the unlocked
      deque is already [a; b] and the [push_front] at :123 is the single line
      that puts the unblocking parent AHEAD of them. The requirement is stated
      verbatim at cert_manager.rs:106-107: [// NOTE: this also ensures
      certificates are accepted in causal order // which is a strict requirement
      for consensus to build the DAG correctly].
    - GC DRAIN. The horizon moves past the missing parent and the blocked keys
      are drained lowest-first, under the verbatim comment [// iterate one round
      at a time to preserver causal order]:
      [while let Some((round, digest)) = self.pending.next_for_gc_round(gc_round)
      { let unlocked = self.pending.update_pending(round, digest)?;
      self.accept_verified_certificates(unlocked).await?; }]
      (cert_manager.rs:234-238). [next_for_gc_round]
      (pending_cert_manager.rs:137-156) takes [first_key_value()] (:140) and
      STOPS when that smallest key is above the horizon (:144-146).

    Handoff itself is cert_manager.rs:189-220: the whole batch is committed to
    storage first ([write_all], :196) and only then, per certificate IN QUEUE
    ORDER, [self.consensus_bus.new_certificates().send(cert).await] (:214).

    The consumer is the Bullshark DAG. [ConsensusState::try_insert] runs
    [try_insert_in_dag] with [check_parents = true] (state.rs:114-122) and that
    function has TWO horizon escapes which this model reproduces exactly,
    because omitting either would make a false statement look true:

    - [if certificate.round() <= gc_round { return Ok(false); }]
      (state.rs:132-138) - a certificate at or below the horizon is silently
      DROPPED, never inserted, and no error is returned to the sender;
    - [if round <= gc_round + 1 { return Ok(()); }] (state.rs:193-197) - parents
      are not checked one round above the horizon.

    Above both, a missing parent is [ConsensusError::MissingParent] /
    [MissingParentRound] (state.rs:198-212), which propagates with [?] out of
    [Bullshark::process_certificate] (bullshark.rs:116) and out of
    [ConsensusState::run] (state.rs:372-376), killing a task spawned with
    [spawn_critical_task] (state.rs:347-349). That is a full node shutdown, so
    it is modelled as an ABSORBING [fatal] state with no successors.

    The fetcher leg. When [Cert_a] was found to have missing parents the manager
    sent [CertificateFetcherCommand::Ancestors] (cert_manager.rs:168-177) and
    the fetcher recorded [self.targets.insert(header.author().clone(),
    header.round())] (certificate_fetcher.rs:212) - a target for [Cert_a]'s
    author at round [r0 + 1]. Before every attempt the targets are re-filtered
    (certificate_fetcher.rs:332-348):
    [let last_written_round = written_rounds.get(origin).and_then(|rounds|
    rounds.last()).copied().unwrap_or(gc_round); ... last_written_round <
    *target_round], with the verbatim comments [// This applies GC to targets as
    well.] and [// NOTE: even if the store actually does not have target_round
    for the origin, // it is ok to stop fetching without this certificate.]
    [written_rounds] comes from [origins_after_round(gc_round + 1)]
    (certificate_fetcher.rs:365, store semantics certificate_store.rs:329-351,
    whose own NOTE is [caller assumes this is inclusive]), so it can only ever
    report rounds at or above [gc_round + 1]. Both routes out of the target map
    are therefore modelled: the STORE route (the certificate really was
    obtained, and its round is still inside the [>= gc_round + 1] window) and
    the FLOOR route (the [unwrap_or(gc_round)] default). The gc round itself is
    [gc_round(committed_round, gc_depth) = commit_round.saturating_sub(gc_depth)]
    (cert_manager.rs:63-68, certificate_fetcher.rs:376-379, utils.rs:59-62).

    {2 Components and the round arithmetic}

    [gc] ranges over three horizons, [G0 = r0 - 1], [G1 = r0], [G2 = r0 + 1],
    and only ever advances: it is [commit_round.saturating_sub(gc_depth)]
    (utils.rs:59-62), and commits do not need this lineage - Bullshark elects
    and commits on leader support from a threshold of OTHER authorities, so a
    node lagging on one author's chain still sees its horizon move. The three
    values are all load-bearing and none is decorative:

    - at [G0] the consumer checks [Cert_a]'s parents ([r0+1 > (r0-1)+1]);
    - at [G1] the drain is armed (key [(r0, p)] satisfies [round <= gc_round])
      and [Cert_b] is still parent-checked;
    - at [G2] the fetcher's floor default [gc_round = r0+1] finally reaches the
      target round, and the second blocked key [(r0+1, a)] becomes drainable.

    [Cert_p] can only ARRIVE while [gc = G0]. That is not a convenience: the
    fetch request carries [self.exclusive_lower_bound = gc_round]
    (message.rs:204-228, called at certificate_fetcher.rs:278-279), so once the
    horizon reaches [r0] a round-[r0] certificate is no longer requestable.

    {2 Role mapping}

    - [V0] is the local primary - the knowledge agent that runs
      [CertificateManager] and [CertificateFetcher]. Its view is its own gc
      horizon, its own handoff sequence, its own release queue, whether it has
      garbage-collected the blocked key, whether its fetch target is still
      armed, and whether its consensus task died. It does NOT see [peer]: the
      fetcher gets no signal distinguishing "nobody has this certificate any
      more" from "this attempt did not reach a holder", which is exactly what
      certificate_fetcher.rs:342-346 says out loud.
    - [V1] is the responder peer - the second knowledge agent. Its view is its
      OWN possession of [Cert_p] and whether a request is outstanding (the
      fetcher issues attempts only while [targets] is non-empty:
      [start_fetch_task] returns early on [self.targets.is_empty()],
      certificate_fetcher.rs:269-273, and [handle_fetch_completion] restarts
      only [if !self.targets.is_empty()], :251-253). It sees NOTHING of V0's
      store, queue or horizon.
    - [V2] .. [V9] are idle: constant blank view, never under [K].

    The model scopes the responder set to the single peer [V1], so "obtainable"
    and "V1 holds it" coincide. Widening the set replaces [Peer_holds] by a
    disjunction over responders and turns the V1 knowledge conjunct into a claim
    about the set that has collectively lost it; nothing else changes. *)

(** One certificate of the modelled causal chain. [Cert_p] is at round [r0] and
    is the missing parent; [Cert_a] at [r0 + 1] is parked on [Cert_p];
    [Cert_b] at [r0 + 2] is parked on [Cert_a]
    (cert_manager.rs:108-118, pending_cert_manager.rs:58-81). *)
type cert = Cert_p | Cert_a | Cert_b

(** Total order index for {!cert}: the chain order, which is also round order. *)
let cert_index = function Cert_p -> 0 | Cert_a -> 1 | Cert_b -> 2

(** Total order on {!cert}. *)
let cert_compare a b = Int.compare (cert_index a) (cert_index b)

(** [true] iff the two certificates are the same one. *)
let cert_equal a b = Int.equal 0 (cert_compare a b)

(** Total deterministic order on certificate sequences (handoff order and
    release-queue order are both sequences, and the whole family is about the
    order, so the comparator must be order-sensitive). *)
let rec cert_list_compare xs ys =
  match (xs, ys) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs', y :: ys' ->
      let c = cert_compare x y in
      if Bool.not (Int.equal c 0) then c else cert_list_compare xs' ys'

(** The garbage-collection horizon [gc_round(committed_round, gc_depth)]
    (utils.rs:59-62). [G0 = r0 - 1], [G1 = r0], [G2 = r0 + 1]; it only ever
    advances. *)
type gcr = G0 | G1 | G2

(** Total order index for {!gcr}. *)
let gcr_index = function G0 -> 0 | G1 -> 1 | G2 -> 2

(** Total order on {!gcr}. *)
let gcr_compare a b = Int.compare (gcr_index a) (gcr_index b)

(** The hidden network fact: whether the responder peer [V1] still holds
    [Cert_p]. [Lost] is the case certificate_fetcher.rs:342-346 explicitly
    tolerates ("even if the store actually does not have target_round for the
    origin, it is ok to stop fetching without this certificate"). *)
type holding = Holds | Lost

(** Total order index for {!holding}. *)
let holding_index = function Holds -> 0 | Lost -> 1

(** Total order on {!holding}. *)
let holding_compare a b = Int.compare (holding_index a) (holding_index b)

(** [true] iff the responder still possesses the missing parent. *)
let peer_possesses = function Holds -> true | Lost -> false

(** The joint global state.

    - [gc] the local horizon;
    - [peer] the hidden possession bit of the responder;
    - [handed] the certificates already sent to [new_certificates]
      (cert_manager.rs:214), oldest first - this IS the order the DAG sees;
    - [queue] certificates released but not yet sent, in the order the release
      path produced them;
    - [discarded] the drain removed the blocked key [(r0, p)], i.e. [Cert_p] was
      garbage-collected rather than obtained (pending_cert_manager.rs:137-156);
    - [target] the fetcher still holds a catch-up target for [Cert_a]'s author
      at round [r0 + 1] (certificate_fetcher.rs:212, :332-348);
    - [fatal] the consensus task returned [MissingParent] / [MissingParentRound]
      and the critical task died (state.rs:198-212, :372-376). *)
type state = {
  gc : gcr;
  peer : holding;
  handed : cert list;
  queue : cert list;
  discarded : bool;
  target : bool;
  fatal : bool;
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = gcr_compare s1.gc s2.gc in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = holding_compare s1.peer s2.peer in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = cert_list_compare s1.handed s2.handed in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = cert_list_compare s1.queue s2.queue in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.discarded s2.discarded in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Bool.compare s1.target s2.target in
            if Bool.not (Int.equal c5 0) then c5
            else Bool.compare s1.fatal s2.fatal

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    [View_local] is V0's projection: its horizon, handoff sequence, release
    queue, gc bookkeeping, fetch target and shutdown flag - everything the local
    primary owns, and NOTHING about the responder's possession.

    [View_peer] is V1's projection: its own possession of [Cert_p] and whether a
    fetch attempt is outstanding, which it observes by receiving the request.
    It carries no component of V0's store, queue or horizon.

    [View_idle] is the constant blank view of the non-agents V2..V9. *)
type view =
  | View_local of gcr * cert list * cert list * bool * bool * bool
  | View_peer of holding * bool
  | View_idle

(** Total deterministic order over ALL fields of V0's view. *)
let view_local_compare (g, h, q, d, t, f) (g', h', q', d', t', f') =
  let c = gcr_compare g g' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = cert_list_compare h h' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = cert_list_compare q q' in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare d d' in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare t t' in
          if Bool.not (Int.equal c4 0) then c4 else Bool.compare f f'

(** Total deterministic order over ALL fields of V1's view. *)
let view_peer_compare (p, t) (p', t') =
  let c = holding_compare p p' in
  if Bool.not (Int.equal c 0) then c else Bool.compare t t'

(** Total order on views: [View_idle] < [View_local] < [View_peer]. Every
    constructor pairing is spelled out; there is no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_local _ | View_peer _) -> -1
  | (View_local _ | View_peer _), View_idle -> 1
  | View_local (g, h, q, d, t, f), View_local (g', h', q', d', t', f') ->
      view_local_compare (g, h, q, d, t, f) (g', h', q', d', t', f')
  | View_local _, View_peer _ -> -1
  | View_peer _, View_local _ -> 1
  | View_peer (p, t), View_peer (p', t') -> view_peer_compare (p, t) (p', t')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 (the local primary) and V1 (the responder peer) are the
    knowledge agents with real, non-constant views; V2..V9 are idle non-agents
    with the constant blank view and never appear under [K]. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_local (s.gc, s.handed, s.queue, s.discarded, s.target, s.fatal)
  | Validator.V1 -> View_peer (s.peer, s.target)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | Handoff_push_back
      (** change [unlocked.push_front(cert)] to [unlocked.push_back(cert)] at
          cert_manager.rs:123, so the ARRIVAL path enqueues [a; b; p] instead of
          [p; a; b]: the dependents released by [Cert_p] are sent to
          [new_certificates] before [Cert_p] itself. At [gc = G0] this hands
          [Cert_a] (round [r0+1 > gc_round+1 = r0]) to a DAG that has no
          [Cert_p], adding the transition into the absorbing [fatal] state. No
          sibling path repairs it: the consumer does not re-sort - [check_parents]
          (state.rs:187-214) returns [MissingParent]/[MissingParentRound], the
          error rides [?] out of [Bullshark::process_certificate]
          (bullshark.rs:116) and out of [ConsensusState::run] (state.rs:372-376),
          killing a [spawn_critical_task] task (state.rs:347-349); [write_all]
          (cert_manager.rs:196) has already committed the whole batch to storage
          BEFORE any handoff, so the store is order-insensitive and cannot
          repair DAG order; and [update_pending]'s own worklist [pop_front]
          (pending_cert_manager.rs:95) is not a second ordering gate, because a
          key is enqueued at :122 only after its certificate is already on the
          ready queue at :125. The only genuine repair is a RESTART, where
          [construct_dag_from_cert_store] rebuilds with [check_parents = false]
          (state.rs:88-110), which is outside a running system. *)
  | Release_highest_first
      (** replace [first_key_value()] with [last_key_value()] at
          pending_cert_manager.rs:140, so the GC DRAIN reads the HIGHEST blocked
          key instead of the lowest. Two consequences, both modelled. (i) The
          stop test [if round > gc_round { return None; }] (:144-146) now reads
          the largest key, so at [gc = G1] the drain returns [None] even though
          key [(r0, p)] is eligible - the release is delayed to [G2]. (ii) At
          [gc = G2] the drain processes key [(r0+1, a)] FIRST: :151-153 clears
          the pending [Cert_a]'s own missing set without releasing it, while
          [update_pending] releases its child [Cert_b]; only the next iteration,
          on key [(r0, p)], releases [Cert_a]. The queue is therefore [b; a] -
          a dependent handed to consensus before the certificate it was blocked
          on. No sibling path repairs the order: [update_pending]
          (pending_cert_manager.rs:85-131) only orders certificates WITHIN one
          release, and [cert_manager]'s own [cert.round() > self.gc_round() + 1]
          guard (cert_manager.rs:108) governs the arrival path, not the drain.
          Honest scope: this inversion is NOT consumer-observable, because the
          drain's own precondition [round <= gc_round] forces the inverted
          parent to or below the horizon, where state.rs:132-138 drops it and
          state.rs:193-197 exempts its child - so this deletion does NOT reach
          the [fatal] state, and the statement it pins is the causal-order
          contract the code states for itself (cert_manager.rs:106-107, :234),
          not a shutdown. *)
  | Target_retain_default_zero
      (** change [.unwrap_or(gc_round)] to [.unwrap_or(0)] in the fetch-target
          retain at certificate_fetcher.rs:337, deleting the garbage-collection
          FLOOR on catch-up targets while leaving the store-satisfaction route
          intact. A target for an authority with nothing in the
          [origins_after_round(gc_round + 1)] window then satisfies
          [0 < target_round] forever. No sibling path removes it: the only other
          write to [self.targets] is the insert at :212, gated by
          [should_fetch_certificate] (:223-239) which admits strictly HIGHER
          rounds only; [CertificateFetcherCommand::Kick] (:181-190) reads
          [self.targets.is_empty()] but never clears it; there is no periodic
          sweep and no epoch-boundary clear (the epoch guard at :195-204 only
          skips ADDING out-of-epoch targets); and [handle_fetch_completion]
          (:241-256) drives the loop rather than cleaning it. The store route is
          modelled and is genuinely NOT a repair: [written_rounds] is built from
          [origins_after_round(gc_round + 1)] (:365, certificate_store.rs:329-351),
          so once the horizon passes the target round the certificate can never
          appear there again, and the floor was the only remaining exit. *)

(** [true] iff the certificate has already been sent to consensus. *)
let handed_off s c = List.exists (fun x -> cert_equal x c) s.handed

(** [true] iff the certificate is already in the release queue. *)
let queued s c = List.exists (fun x -> cert_equal x c) s.queue

(** [true] iff the local primary has the certificate at all - released and
    handed off, or released and still queued. *)
let received s c = handed_off s c || queued s c

(** The order the ARRIVAL path puts on the batch. Pristine and both unrelated
    mutations keep [push_front] (cert_manager.rs:123), so the unblocking parent
    leads; [Handoff_push_back] appends it instead. *)
let arrival_release mut =
  match mut with
  | Pristine | Release_highest_first | Target_retain_default_zero ->
      [ Cert_p; Cert_a; Cert_b ]
  | Handoff_push_back -> [ Cert_a; Cert_b; Cert_p ]

(** The order the GC DRAIN puts on the batch, and at which horizons it is armed.
    Pristine (and both unrelated mutations) take the LOWEST blocked key first,
    so key [(r0, p)] fires as soon as [gc_round >= r0] and its cascade yields
    [a; b]. [Release_highest_first] reads the highest key, which is above the
    horizon at [G1] (so nothing drains) and at [G2] releases [b] before [a]. *)
let drain_release mut gc =
  match (mut, gc) with
  | (Pristine | Handoff_push_back | Target_retain_default_zero), G0 -> []
  | (Pristine | Handoff_push_back | Target_retain_default_zero), (G1 | G2) ->
      [ [ Cert_a; Cert_b ] ]
  | Release_highest_first, (G0 | G1) -> []
  | Release_highest_first, G2 -> [ [ Cert_b; Cert_a ] ]

(** Does the consumer check this certificate's parents at this horizon?
    [try_insert_in_dag] drops it outright below the horizon (state.rs:132-138)
    and [check_parents] exempts one round above it (state.rs:193-197), so with
    [Cert_p] at [r0], [Cert_a] at [r0+1], [Cert_b] at [r0+2] and
    [gc_round(G0,G1,G2) = r0-1, r0, r0+1] the check fires exactly here. Every
    pair is spelled out. *)
let consensus_checks_parents gc c =
  match (c, gc) with
  | Cert_p, (G0 | G1 | G2) -> false
  | Cert_a, G0 -> true
  | Cert_a, (G1 | G2) -> false
  | Cert_b, (G0 | G1) -> true
  | Cert_b, G2 -> false

(** [true] iff the parent this certificate is checked against is already in the
    DAG. Whenever the check fires, the parent's round is strictly above the
    horizon (it is exactly one below a round that is more than one above the
    horizon), so "in the DAG" reduces to "already handed off". [Cert_p]'s own
    parents are at [r0 - 1 <= gc_round] and are never checked. *)
let parent_in_dag s c =
  match c with
  | Cert_p -> true
  | Cert_a -> handed_off s Cert_p
  | Cert_b -> handed_off s Cert_a

(** [true] iff handing this certificate over now raises
    [ConsensusError::MissingParent] / [MissingParentRound] (state.rs:198-212). *)
let missing_parent_error s c =
  consensus_checks_parents s.gc c && Bool.not (parent_in_dag s c)

(** The horizon advances by one, driven by commits the rest of the committee
    makes without this lineage. Monotone. *)
let gc_step s =
  match s.gc with
  | G0 -> [ { s with gc = G1 } ]
  | G1 -> [ { s with gc = G2 } ]
  | G2 -> []

(** The ARRIVAL path: the missing parent is fetched and unlocks the cascade
    (cert_manager.rs:121-124). Armed only at [G0], because the request carries
    [exclusive_lower_bound = gc_round] (message.rs:209, set at
    certificate_fetcher.rs:278-279) so a round-[r0] certificate stops being
    requestable once the horizon reaches [r0]; and only while the responder
    still holds it, the release queue is empty, the key has not been garbage
    collected and the dependents are still parked. *)
let arrival_step mut s =
  let armed =
    peer_possesses s.peer
    && (match s.gc with G0 -> true | G1 | G2 -> false)
    && (match s.queue with [] -> true | _ :: _ -> false)
    && Bool.not s.discarded
    && Bool.not (received s Cert_p)
    && Bool.not (handed_off s Cert_a)
  in
  if armed then [ { s with queue = arrival_release mut } ] else []

(** The GC DRAIN path: the horizon passes the blocked key and the parked
    dependents are released (cert_manager.rs:234-238,
    pending_cert_manager.rs:137-156). Armed while the release queue is empty and
    the dependents are still parked. Setting [discarded] records that the
    missing parent was garbage-collected rather than obtained. *)
let drain_step mut s =
  let armed =
    (match s.queue with [] -> true | _ :: _ -> false)
    && Bool.not s.discarded
    && Bool.not (handed_off s Cert_a)
    && Bool.not (received s Cert_p)
  in
  if armed then
    List.map
      (fun release -> { s with discarded = true; queue = release })
      (drain_release mut s.gc)
  else []

(** One handoff: the head of the release queue is sent to [new_certificates]
    (cert_manager.rs:214) and the DAG either accepts it or raises a missing
    parent. *)
let handoff_step s =
  match s.queue with
  | [] -> []
  | c :: rest ->
      [
        {
          s with
          queue = rest;
          handed = s.handed @ [ c ];
          fatal = s.fatal || missing_parent_error s c;
        };
      ]

(** The store route out of the target map: the certificate really was written,
    and its round [r0 + 1] is still inside the [>= gc_round + 1] window that
    [origins_after_round] reports (certificate_fetcher.rs:365,
    certificate_store.rs:329-351). That window closes once the horizon reaches
    [G2], where [gc_round + 1 = r0 + 2 > r0 + 1]. *)
let target_satisfied_by_store s =
  handed_off s Cert_a && match s.gc with G0 | G1 -> true | G2 -> false

(** The floor route out of the target map: the [unwrap_or(gc_round)] default at
    certificate_fetcher.rs:337, which drops the target once the horizon reaches
    the target round [r0 + 1], i.e. at [G2]. [Target_retain_default_zero]
    replaces the default with [0], which never reaches a positive target round,
    so this route disappears entirely. *)
let target_satisfied_by_floor mut s =
  match mut with
  | Pristine | Handoff_push_back | Release_highest_first -> (
      match s.gc with G0 | G1 -> false | G2 -> true)
  | Target_retain_default_zero -> false

(** [update_targets] (certificate_fetcher.rs:327-349) runs before every attempt
    and drops a target satisfied by either route. *)
let target_step mut s =
  if s.target && (target_satisfied_by_store s || target_satisfied_by_floor mut s)
  then [ { s with target = false } ]
  else []

(** The transition relation: one component advances per step. A [fatal] state
    has NO successors - the consensus task was spawned with
    [spawn_critical_task] (state.rs:347-349) and its error kills the node - so
    the kernel stutter-closes it. *)
let next_with mut s =
  if s.fatal then []
  else
    List.concat
      [
        gc_step s;
        arrival_step mut s;
        drain_step mut s;
        handoff_step s;
        target_step mut s;
      ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state on the hidden branch where the responder has LOST the
    missing parent: horizon at [r0 - 1], both dependents parked, nothing handed
    off, the fetch target armed. *)
let initial =
  {
    gc = G0;
    peer = Lost;
    handed = [];
    queue = [];
    discarded = false;
    target = true;
    fatal = false;
  }

(** The initial state on the hidden branch where the responder still HOLDS the
    missing parent. Identical in every component V0 can see - that is what makes
    the possession bit unknowable to the fetcher. *)
let initial_peer_holds = { initial with peer = Holds }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Handed_p
      (** the missing parent has been sent to consensus
          (cert_manager.rs:214) *)
  | Handed_a  (** the round-[r0+1] dependent has been sent to consensus *)
  | Handed_b  (** the round-[r0+2] dependent has been sent to consensus *)
  | P_received
      (** the local primary holds the missing parent at all - released and
          handed off, or released and still queued *)
  | Discarded
      (** the drain removed the blocked key [(r0, p)]: the missing parent was
          garbage-collected rather than obtained
          (pending_cert_manager.rs:137-156) *)
  | Target_active
      (** the fetcher still holds a catch-up target for the round-[r0+1]
          author (certificate_fetcher.rs:212, :332-348) *)
  | Fatal
      (** consensus raised [MissingParent] / [MissingParentRound] and the
          critical task died (state.rs:198-212, :372-376) *)
  | Peer_holds
      (** the hidden network fact: the responder peer still possesses the
          missing parent *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Handed_p -> handed_off s Cert_p
  | Handed_a -> handed_off s Cert_a
  | Handed_b -> handed_off s Cert_b
  | P_received -> received s Cert_p
  | Discarded -> s.discarded
  | Target_active -> s.target
  | Fatal -> s.fatal
  | Peer_holds -> peer_possesses s.peer

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Handed_p -> "handoff(p)"
  | Handed_a -> "handoff(a)"
  | Handed_b -> "handoff(b)"
  | P_received -> "received(p)"
  | Discarded -> "gc_discarded(p)"
  | Target_active -> "target(a_author,r0+1)"
  | Fatal -> "missing_parent_shutdown"
  | Peer_holds -> "peer_holds(p)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every reachable
    world by test/t_causal_handoff_topos.ml. Every transition strictly increases
    one of (horizon, released count, handed count, target dropped, fatal), so
    the reachability relation is expected to be antisymmetric - but that is
    settled by RUNNING the gate, not by this comment. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the two hidden-branch initial states,
    mutation-parameterized transitions, the two-agent view, the atom
    valuation. *)
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
