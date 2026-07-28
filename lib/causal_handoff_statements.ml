(** The CAUSAL_HANDOFF statement family, encoded over the
    {!Causal_handoff_model} interpreted system. Three statements mined from the
    primary's state-sync repair loop: the ordering contract on the store-to-DAG
    handoff (two release paths, two different lines of code) and the
    garbage-collection floor on the certificate fetcher's catch-up targets.
    File citations refer to Telcoin-Association/telcoin-network at 0c59c15b.

    {2 Reading guide for the K operands}

    There are exactly three epistemic operands in the family and none of them is
    a projection of its own knower's view or rigid over the reachable set.

    - [~K_V0(peer_holds(p))] and [~K_V0(~peer_holds(p))] (S3 conjunct B, and the
      second half in S2 conjunct B). [peer_holds(p)] is ANOTHER NODE'S
      POSSESSION and appears in no component of V0's view. V0's view is its own
      horizon, handoff sequence, release queue, gc bookkeeping, fetch target and
      shutdown flag; the two hidden branches of the model differ ONLY in that
      bit and in whether the arrival transition is available, so every reachable
      state in which V0 has not actually received the certificate has a twin in
      the other branch with an identical V0 view. That is the ignorance witness,
      and it is exactly what certificate_fetcher.rs:342-346 states in prose:
      "even if the store actually does not have target_round for the origin, it
      is ok to stop fetching without this certificate". The guard
      [~received(p)] is load-bearing and honest: once the certificate really
      arrives, V0 does know a peer had it, and the statement does not pretend
      otherwise.

    - [K_V1(~received(p))] (S3 conjunct C) is the one POSITIVE knowledge claim.
      Its operand is a fact about the OTHER node's store, of which V1's view -
      its own possession plus whether a request is outstanding - contains no
      component. It is not rigid: [received(p)] is true at reachable states (the
      whole arrival path). The V1-view class at the operative state is not a
      singleton either: it holds every reachable state with [peer_holds] false
      and the target still armed, which ranges over all three horizons, both
      release configurations and both values of [gc_discarded(p)] - the
      contingency suite proves that by exhibiting a same-view state that
      disagrees on [gc_discarded(p)].

    {2 Honest scope}

    S2's ordering conjunct is pinned by a real gate, but the inversion it
    forbids is NOT visible to the consumer: the drain's own precondition
    ([round <= gc_round], pending_cert_manager.rs:144-146) forces the inverted
    parent to or below the horizon, where [try_insert_in_dag] drops it outright
    (state.rs:132-138) and [check_parents] exempts its child
    (state.rs:193-197). The statement therefore asserts the causal-order
    contract the code states for ITSELF (cert_manager.rs:106-107 and :234) and
    the model does NOT set [missing_parent_shutdown] on that path. S1's
    inversion, on the arrival path, is a different matter: there the inverted
    parent is above the horizon and the shutdown is real. *)

open Causal_handoff_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a false antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - unlocked-parent-precedes-its-dependents-into-consensus [safety].

    When an arriving certificate unblocks a chain of parked dependents, it is
    pushed to the FRONT of the release deque before the batch is handed to
    consensus, so the sequence offered to the DAG is topologically sorted.

    (A) No missing-parent shutdown: AG( ~missing_parent_shutdown ). The handoff
    loop sends each certificate in queue order to [new_certificates]
    (cert_manager.rs:214) and the consumer checks parents for every certificate
    more than one round above the horizon ([check_parents], state.rs:187-214,
    with the exemptions at state.rs:132-138 and :193-197 both modelled). At
    [gc = G0] the round-[r0+1] dependent IS checked, so its parent must already
    be in the DAG. Pristine that is guaranteed by [unlocked.push_front(cert)]
    (cert_manager.rs:123) on the arrival path, and by the horizon exemptions on
    the drain path (the drain is armed only from [G1], where the round-[r0+1]
    certificate is exempt).

    (B) The dependent never overtakes what unblocked it:
    AG( handoff(a) -> handoff(p) \\/ gc_discarded(p) ). A parked certificate is
    released only when its LAST missing parent digest is removed
    (pending_cert_manager.rs:114-126), and the digest is removed either because
    the parent arrived and led the batch (cert_manager.rs:121-124) or because
    the drain garbage-collected the key (pending_cert_manager.rs:137-156). There
    is no third route, so a released dependent always carries one of the two
    witnesses.

    Mutation pin: {!Causal_handoff_model.Handoff_push_back} turns
    [unlocked.push_front(cert)] into [push_back] at cert_manager.rs:123, so the
    arrival batch leaves as [a; b; p]. Conjunct B fails at every horizon, and at
    [gc = G0] conjunct A fails as well because the round-[r0+1] dependent meets
    a DAG with no round-[r0] parent and consensus returns
    [ConsensusError::MissingParentRound]. Sibling-repair hunt: none exists in a
    running node - the consumer does not re-sort but dies ([?] out of
    bullshark.rs:116 and state.rs:372-376, on a [spawn_critical_task] task,
    state.rs:347-349); [write_all] (cert_manager.rs:196) has already stored the
    whole batch before any handoff, so the store cannot repair DAG order; and
    [update_pending]'s worklist [pop_front] (pending_cert_manager.rs:95) is not
    a second ordering gate, since a key is enqueued at :122 only after its
    certificate has been pushed onto the ready queue at :125. The only repair is
    a restart, where [construct_dag_from_cert_store] rebuilds with
    [check_parents = false] (state.rs:88-110). *)
let s1 =
  let no_missing_parent_shutdown = Formula.Ag (Formula.Not (atom Fatal)) in
  let dependent_never_overtakes_parent =
    Formula.Ag
      (Formula.Implies
         (atom Handed_a, Formula.Or (atom Handed_p, atom Discarded)))
  in
  {
    name = "unlocked-parent-precedes-its-dependents-into-consensus";
    bucket = Statements.Safety;
    formula =
      Formula.And (no_missing_parent_shutdown, dependent_never_overtakes_parent);
    antecedent = atom Handed_a;
  }

(** S2 - gc-release-drains-the-lowest-blocked-round-first [safety].

    When the garbage-collection horizon advances past blocked parents, the
    pending manager drains the blocked-parent index from its SMALLEST key, so
    the cascade of released dependents stays topologically sorted even though
    the unblocking event is garbage collection rather than an arrival.

    (A) The drain never presents a dependent before the certificate it was
    blocked on: AG( handoff(b) -> handoff(a) ). The index is
    [BTreeMap<(Round, HeaderDigest), _>] keyed by the PARENT's round
    (pending_cert_manager.rs:42-46, :64, :76-78) and [next_for_gc_round] takes
    [first_key_value()] (:140), stopping at the first key above the horizon
    (:144-146); the caller drains in a [while let] loop under the verbatim
    comment [// iterate one round at a time to preserver causal order]
    (cert_manager.rs:234-238). Lowest-first matters precisely because :151-153
    force-clears the missing set of a blocked parent that is ITSELF pending
    without releasing it - so if the higher key were taken first, that parent's
    child would be released while the parent stayed parked.

    (B) Garbage-collecting the missing parent teaches the node nothing about the
    network: AG( gc_discarded(p) /\\ ~handoff(p) -> ~K_V0(~peer_holds(p)) ).
    Dropping the key is a local horizon decision, not evidence of absence; the
    fetcher says so itself at certificate_fetcher.rs:342-346. V0's view has no
    component of the responder's possession, so every discarded state has a twin
    in the other hidden branch with an identical V0 view.

    Mutation pin: {!Causal_handoff_model.Release_highest_first} replaces
    [first_key_value()] with [last_key_value()] at
    pending_cert_manager.rs:140. At [G2] the drain then takes key
    [(r0+1, a)] first, force-clears the parked round-[r0+1] certificate at
    :151-153 and releases its round-[r0+2] child, leaving the parent for the
    next iteration on key [(r0, p)]: the queue is [b; a] and conjunct A fails.
    (The same edit also turns the stop test at :144-146 into a read of the
    HIGHEST key, so at [G1] the drain returns [None] and the release is delayed
    - modelled, and a second independent consequence of the same line.)
    Sibling-repair hunt: [update_pending] (pending_cert_manager.rs:85-131)
    orders certificates only WITHIN one release and cannot repair the order
    across two [next_for_gc_round] iterations; [cert_manager]'s own
    [cert.round() > self.gc_round() + 1] guard (cert_manager.rs:108) governs the
    arrival path, not the drain; and there is no re-sort at the consumer. What
    the consumer DOES have is the pair of horizon escapes (state.rs:132-138 and
    :193-197), and because the drain only fires on keys at or below the horizon
    the inverted parent is always inside them - so this deletion is refuted by
    the ordering contract itself and NOT by a shutdown, which is why conjunct A
    is stated over the handoff sequence and the model leaves
    [missing_parent_shutdown] false on this path. *)
let s2 =
  let dependent_after_its_blocker =
    Formula.Ag (Formula.Implies (atom Handed_b, atom Handed_a))
  in
  let discard_is_not_evidence_of_absence =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Discarded, Formula.Not (atom Handed_p)),
           Formula.Not
             (Formula.K (Validator.V0, Formula.Not (atom Peer_holds))) ))
  in
  {
    name = "gc-release-drains-the-lowest-blocked-round-first";
    bucket = Statements.Safety;
    formula =
      Formula.And (dependent_after_its_blocker, discard_is_not_evidence_of_absence);
    antecedent = atom Handed_b;
  }

(** S3 - every-fetch-target-is-eventually-dropped-by-the-gc-floor [liveness].

    No catch-up target survives forever, not even one that can never be
    satisfied, because the target filter defaults an authority with nothing in
    the reported window to the garbage-collection round itself.

    (A) AG( target -> AF( ~target \\/ missing_parent_shutdown ) ). Before every
    attempt [update_targets] (certificate_fetcher.rs:327-349) recomputes
    [last_written_round = written_rounds.get(origin).and_then(|rounds|
    rounds.last()).copied().unwrap_or(gc_round)] and keeps the target only while
    [last_written_round < *target_round]. Two exits are modelled: the STORE exit
    (the certificate really was written and its round is still inside the
    [origins_after_round(gc_round + 1)] window, certificate_fetcher.rs:365 and
    certificate_store.rs:329-351) and the FLOOR exit (the [unwrap_or(gc_round)]
    default at :337). The disjunct [missing_parent_shutdown] is not slack: a
    node whose critical consensus task has died stops running the fetcher too,
    and pretending otherwise would be the manufactured half of a liveness
    claim. That the fetch loop would otherwise never end is
    certificate_fetcher.rs:269-273 and :241-256 - [start_fetch_task] returns
    early only on an empty target map, and [handle_fetch_completion] restarts a
    fetch after every completion while it is non-empty.

    (B) The fetcher cannot tell whether what it is chasing still exists:
    AG( target /\\ ~received(p) -> ~K_V0(peer_holds(p)) /\\
    ~K_V0(~peer_holds(p)) ). This is the ignorance the [NOTE] at
    certificate_fetcher.rs:342-346 is written around.

    (C) The responder that lost it knows the requester will not get it:
    AG( target /\\ ~peer_holds(p) -> K_V1(~received(p)) ). V1 observes its own
    store and, because attempts are issued only while the target map is
    non-empty (certificate_fetcher.rs:269-273, :251-253), that a request is
    outstanding; within the modelled responder set that is enough to settle a
    fact about V0's store which V0 itself cannot settle.

    Mutation pin: {!Causal_handoff_model.Target_retain_default_zero} changes
    [.unwrap_or(gc_round)] to [.unwrap_or(0)] at certificate_fetcher.rs:337,
    deleting the floor exit and leaving the store exit intact. On the run where
    the horizon reaches [G2] before the certificate is released, the store exit
    is already dead - [origins_after_round(gc_round + 1)] can no longer report
    the round-[r0+1] certificate at all - so the target is retained forever and
    conjunct A is refuted at a terminal state with no shutdown. Sibling-repair
    hunt: the only other write to [self.targets] is the insert at :212, gated by
    [should_fetch_certificate] (:223-239) which admits strictly HIGHER rounds
    only; [Kick] (:181-190) reads [is_empty] but never clears; there is no
    periodic sweep and no epoch-boundary clear (the epoch guard at :195-204 only
    skips ADDING out-of-epoch targets); [handle_fetch_completion] (:241-256)
    drives the loop rather than cleaning it. R8: the deleted default is a real
    garbage-collection floor, not a sibling path the code would have taken
    anyway - the store exit is modelled explicitly and is exercised on the runs
    where the certificate is released before the horizon passes it. *)
let s3 =
  let target_eventually_dropped =
    Formula.Ag
      (Formula.Implies
         ( atom Target_active,
           Formula.Af (Formula.Or (Formula.Not (atom Target_active), atom Fatal))
         ))
  in
  let chase_is_blind =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Target_active, Formula.Not (atom P_received)),
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom Peer_holds)),
               Formula.Not
                 (Formula.K (Validator.V0, Formula.Not (atom Peer_holds))) ) ))
  in
  let responder_knows_the_requester_is_empty_handed =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Target_active, Formula.Not (atom Peer_holds)),
           Formula.K (Validator.V1, Formula.Not (atom P_received)) ))
  in
  {
    name = "every-fetch-target-is-eventually-dropped-by-the-gc-floor";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        ( target_eventually_dropped,
          Formula.And (chase_is_blind, responder_knows_the_requester_is_empty_handed)
        );
    antecedent = Formula.And (atom Target_active, Formula.Not (atom Peer_holds));
  }

(** The family's statements: two safety ordering contracts on the two release
    paths, and the fetcher's liveness floor. *)
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
