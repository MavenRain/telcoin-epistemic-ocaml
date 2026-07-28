(** The DAG_RETENTION statement family, encoded over the {!Dag_retention_model}
    interpreted system. The three statements were mined from telcoin-network and
    re-grounded line by line against the working tree at git HEAD 0c59c15b; every
    citation below was opened in that checkout. They share one model because they
    are three different gates over the SAME three fields of one
    [ConsensusState] - [dag], [last_committed] and [last_round.committed_round] -
    and because the dag's deliberate RETENTION of committed certificates
    (state.rs:43-45, :182-183) is simultaneously what makes the two dedup gates
    load-bearing and what makes S3's straggler insertable at all.

    Reading guide for the [K] operands. There are exactly two, both in S3, and
    both target authority A's POSSESSION of D's round-2 certificate - another
    node's possession, not a projection of V0's own view:

    - [K (Validator.V0, holds_A(D2))] (S3 conjunct C) is asserted at the states
      where A3 is resident AND names D2 among its parents. V0's inference is
      the ordinary one the code itself relies on: a header's parents are
      certificates its author held, and V0 reads that list off the certificate
      in its dag ([certificate.header().parents()], state.rs:201-202). The
      operand is NOT rigid - [holds_A(D2)] is false at every reachable state of
      the two {!Dag_retention_model.initial} / [initial_peer_c_holds] worlds -
      and the operative view class is NOT a singleton: it contains the
      [peer_c = C_holds_parent] twin and the [peer_c = C_without_parent] twin,
      which disagree on [holds_C(D2)]. So at the very state where V0 learns
      that A held D2 it still cannot tell whether C does, and the [K] is a real
      quantification over two worlds. Both facts are discharged by
      satisfiability tests in t_dag_retention.ml.

    - [~K (Validator.V0, holds_A(D2))] (S3 conjunct D) is asserted at the
      states where A DID hold D2, D2 is resident in V0's dag, and A3 has not
      arrived yet. The ignorance witness is the colliding pair
      W1 = (A_names_parent, *, Ph_leader4, S_resident, Ch_inflight) and
      W2 = (A_omits_parent, *, Ph_leader4, S_resident, Ch_inflight): both
      reachable, identical under [View_consensus] - the child is not in the dag
      in either, so nothing V0 holds mentions D2's re-use - and disagreeing on
      [holds_A(D2)]. This is the epistemic content of the always-insert
      comment at state.rs:143-144: the node retains a below-commit certificate
      "to allow verifying parent existence" precisely because at insert time it
      cannot know whether anyone built on it.

    S1 and S2 carry no [K]: they are single-node temporal properties over V0's
    own sequence, and the interesting thing about them is that each rests on
    ONE comparison over a dag that still physically contains everything the
    comparison is protecting. *)

open Dag_retention_model

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

(** S1 - causal-closure-certificate-sequenced-exactly-once-across-subdags
    [safety]. A certificate that a committed sub-dag has carried is never
    carried by a second one, even though it is still physically in the dag when
    the next leader's walk runs over it.

    (A) EXACTLY-ONCE:
    AG( sequenced(c1) -> AG ~resequenced(c1) ). [order_dag] is a DFS from the
    leader (utils.rs:10-57). It filters PARENTS with
    [let mut skip = already_ordered.contains(&digest);] then
    [skip |= state.last_committed.get(certificate.origin())
             .map_or_else(|| false, |r| &certificate.round() <= r);]
    (utils.rs:36-40). [already_ordered] is allocated fresh on every call
    (utils.rs:16), so it dedups only WITHIN one walk; the [last_committed]
    disjunct is the only cross-walk guard, and [state.update] advances
    [last_committed] per sequenced certificate (state.rs:164-168) immediately
    after each walk (bullshark.rs:224-233). The premise the guard is defending
    against is retention: [update] purges only with
    [self.dag.retain(|r, _| *r > self.last_round.gc_round)] (state.rs:182-183),
    and with the default [gc_depth = MAX_GC_DEPTH = 50] (node.rs:302-305,
    types/src/primary/mod.rs:45) [gc_round] saturates to 0 in this window, so
    L2 and its parents are all still there when L4's walk descends through D3
    into A2 = L2. The field's own doc comment names the job:
    "This map is used to clean up the dag and ensure we don't commit twice the
    same certificate" (state.rs:37-38).

    (B) THE SECOND WALK IS REAL:
    AG( leapfrogged(D2) -> sequenced(c1) ). By the time the round-4 leader has
    been committed, [c1] has already been carried once. This is the anti-vacuity
    conjunct: it forbids the degenerate reading in which conjunct A holds
    because [c1] is never sequenced at all, and it pins that the two walks are
    ordered as claimed.

    Mutation pin: {!Dag_retention_model.No_last_committed_skip} deletes the
    [last_committed] disjunct at utils.rs:37-40, so L4's walk descends past
    A2 = L2 into its round-1 parents and delivers [c1] a second time -
    conjunct A flips. Sibling hunt: [already_ordered] (utils.rs:16, :36) is
    per-walk; [dag.retain] (state.rs:182-183) removes nothing here;
    try_insert's below-commit return (state.rs:159-160, bullshark.rs:116-119)
    only suppresses elections for arriving certificates and never touches a
    walk; and [save_consensus] (state-sync/src/lib.rs:105-114) persists the
    output with no uniqueness check. Nothing re-establishes the effect. *)
let s1 =
  let exactly_once =
    Formula.Ag
      (Formula.Implies
         (atom C1_sequenced, Formula.Ag (Formula.Not (atom C1_resequenced))))
  in
  let second_walk_is_real =
    Formula.Ag (Formula.Implies (atom Leapfrogged, atom C1_sequenced))
  in
  {
    name = "causal-closure-certificate-sequenced-exactly-once-across-subdags";
    bucket = Statements.Safety;
    formula = Formula.And (exactly_once, second_walk_is_real);
    antecedent = Formula.And (atom C1_sequenced, atom Leapfrogged);
  }

(** S2 - committed-leader-round-never-reanchored-for-double-execution [safety].
    A leader round that has been committed is never committed again, although
    every ingredient for re-committing it is still available at the moment the
    late certificate arrives.

    (A) NO SECOND ANCHOR:
    AG( committed_leader(L2) -> AG ~reanchored(L2) ). The whole shield is
    [if leader_round <= state.last_round.committed_round { return
    Ok((Outcome::LeaderBelowCommitRound, Vec::new())) }] (bullshark.rs:135-138).
    Everything downstream of it would succeed. A3 is at round 3, so
    [r = 2] is even and [>= 2] (bullshark.rs:126-131), and A3 is ABOVE its own
    origin's committed round ([3 > last_committed[A] = 2]) so try_insert
    returns true and bullshark.rs:116-119 does not stop it. L2 is still in the
    dag (state.rs:182-183). The support recount at bullshark.rs:192-206 sums
    the same round-3 certificates and still clears
    [validity_threshold = ceil(4/3) = 2] (committee.rs:254-259).
    [order_leaders]' range [committed_round + 2 ..= leader_round - 2] is
    [4 ..= 2] and therefore empty (bullshark.rs:290), so [to_commit = [L2]].
    And [order_dag] pushes whatever it pops into [ordered] with no skip check
    at all (utils.rs:15-21) - the certificate-level dedup of S1 explicitly does
    NOT protect the walk root - so a second [CommittedSubDag] carrying L2's own
    nonce (bullshark.rs:218, :240-246) reaches the sequence channel
    (state.rs:456-460).

    (B) THE TRIGGER STAYS INSERTABLE:
    AG( leapfrogged(D2) -> EF resident(A3) ). Safety here is not bought by
    refusing the late certificate: from every leapfrogged state A3 can still be
    inserted. That is the anti-vacuity conjunct, and it is exactly what
    {!Dag_retention_model.Insert_gated_on_last_committed} destroys - a variant
    that stops the re-anchor by killing the node instead of by refusing the
    commit.

    Mutation pin: {!Dag_retention_model.No_below_commit_shortcircuit} deletes
    bullshark.rs:136-138, so A3's arrival at or after the round-2 commit
    re-elects L2 and emits a second sub-dag - conjunct A flips. Sibling hunt:
    try_insert's below-commit return does not apply to A3 (it is above
    [last_committed[A]]); [wait_for_execution] (state.rs:421-434) passes,
    because the re-committed leader's [latest_execution_block] is old and
    execution is already past it, so the "bogus sub dag" branch is not taken;
    the [assert_eq!(self.state.last_round.committed_round, leader_commit_round)]
    at state.rs:470 still holds, since both are 2; and [save_consensus]
    (state-sync/src/lib.rs:105-114) has no sub-dag-digest uniqueness check.
    Nothing repairs the deletion. *)
let s2 =
  let no_second_anchor =
    Formula.Ag
      (Formula.Implies
         (atom Leader2_committed, Formula.Ag (Formula.Not (atom Leader2_reanchored))))
  in
  let trigger_stays_insertable =
    Formula.Ag
      (Formula.Implies (atom Leapfrogged, Formula.Ef (atom Child_resident)))
  in
  {
    name = "committed-leader-round-never-reanchored-for-double-execution";
    bucket = Statements.Safety;
    formula = Formula.And (no_second_anchor, trigger_stays_insertable);
    antecedent = Formula.And (atom Leapfrogged, atom Child_resident);
  }

(** S3 - below-commit-certificate-retained-so-children-stay-insertable
    [liveness]. A certificate whose origin's round was already leapfrogged by
    commit triggers no election, but it is STILL inserted; because of that a
    later certificate naming it as a parent passes the parent-existence check
    and consensus keeps running. And the reason the insert cannot be conditional
    is epistemic: at insert time the node does not know whether any peer built
    on it.

    (A) THE LATE CHILD STILL LANDS:
    AG( leapfrogged(D2) -> AF resident(A3) ). state.rs:143-148 inserts
    unconditionally - "Always insert the certificate even if it is below last
    committed round of its origin, to allow verifying parent existence" - and
    carries the below-commit information in the RETURN VALUE instead
    ([Ok(certificate.round() > last_committed.get(origin).cloned()
    .unwrap_or_default())], state.rs:159-160), which bullshark.rs:116-119 turns
    into [Outcome::CertificateBelowCommitRound]. So D2 lands in [dag[2]] and
    A3's [check_parents] (state.rs:198-208) finds it.

    (B) THE CONSENSUS TASK SURVIVES:
    AG ~dead(consensus). [ConsensusError::MissingParent] (consensus/mod.rs:35,
    constructed at state.rs:203-206) is fatal: [new_certificate] propagates it
    with [?] (state.rs:373-375) out of [run], which is a
    [spawn_critical_task] (state.rs:347-349). The digest is matched NOWHERE in
    the tree, so there is no catch and no retry.

    (C) THE CITATION IS PROOF OF POSSESSION:
    AG( cites(A3,D2) -> K_v0( holds_A(D2) ) ). A header's parents are
    certificates its author held, and V0 reads that list straight off the
    certificate in its dag (state.rs:201-202 iterates
    [certificate.header().parents()]). The operand is a fact about ANOTHER
    node's possession, false at every reachable state of the two worlds in
    which A did not wait for D2, and the operative view class contains two
    worlds that disagree on [holds_C(D2)] - so V0 learns that A held D2 while
    remaining unable to say whether C does.

    (D) BEFORE THAT, NOTHING:
    AG( (resident(D2) /\\ holds_A(D2) /\\ ~resident(A3)) ->
        ~K_v0( holds_A(D2) ) ). At the moment V0 must decide whether to keep a
    below-commit certificate, no channel has told it that anyone built on the
    thing. The colliding pair is W1 = (A_names_parent, Ph_leader4, S_resident,
    Ch_inflight) and W2 = (A_omits_parent, Ph_leader4, S_resident,
    Ch_inflight): both reachable, identical under [View_consensus], disagreeing
    on [holds_A(D2)]. Conjuncts C and D together are the epistemic reading of
    the always-insert comment: the retention is unconditional because the
    knowledge that would justify a condition arrives strictly later.

    Mutation pin: {!Dag_retention_model.Insert_gated_on_last_committed} guards
    the insertion with [round > last_committed[origin]], deleting
    state.rs:143-148. D2 is then dropped at [Ph_leader4], A3's
    [check_parents] returns [MissingParent] and the critical task exits -
    conjuncts A and B both flip. Sibling hunt: the horizon exemption in
    [check_parents] covers only [round <= gc_round + 1 = 1] (state.rs:195-197)
    and A3 is at round 3; [order_dag]'s tolerant [None] arm (utils.rs:46)
    never runs, because the insert-time check errors first; the crash-recovery
    path calls the very function being mutated
    ([construct_dag_from_cert_store] -> [try_insert_in_dag], state.rs:102), so
    a restart inherits the drop; and upstream causal delivery
    (cert_manager.rs:103-124, its own comment at :106-107, modeled as
    {!Dag_retention_model.child_upstream_ready}) reads the certificate STORE
    rather than the consensus dag, so it still forwards A3 into the failure.
    That last one is the repair path the model deliberately CARRIES rather than
    omits. *)
let s3 =
  let late_child_still_lands =
    Formula.leads_to (atom Leapfrogged) (atom Child_resident)
  in
  let consensus_survives = Formula.Ag (Formula.Not (atom Consensus_dead)) in
  let citation_is_proof_of_possession =
    Formula.Ag
      (Formula.Implies
         ( atom Child_cites_straggler,
           Formula.K (Validator.V0, atom Peer_a_holds_straggler) ))
  in
  let ignorance_at_insert_time =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             ( atom Straggler_resident,
               Formula.And
                 (atom Peer_a_holds_straggler, Formula.Not (atom Child_resident))
             ),
           Formula.Not (Formula.K (Validator.V0, atom Peer_a_holds_straggler)) ))
  in
  {
    name = "below-commit-certificate-retained-so-children-stay-insertable";
    bucket = Statements.Liveness;
    formula =
      Formula.conj
        [
          late_child_still_lands;
          consensus_survives;
          citation_is_proof_of_possession;
          ignorance_at_insert_time;
        ];
    antecedent = Formula.And (atom Leapfrogged, atom Straggler_resident);
  }

(** The family's statements: the certificate-level exactly-once guard, the
    leader-level no-re-anchor guard, and the retention liveness backbone with
    its epistemic justification. *)
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
