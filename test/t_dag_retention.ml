(** The DAG_RETENTION family proves on the pristine {!Dag_retention_model}
    through [prove_nonvacuous] (so every antecedent is also checked reachable),
    the reachable graph stays in its justified band, the three gates the family
    depends on genuinely forbid the states they claim to forbid, and the
    epistemic layer is genuinely partial-information.

    The contingency group is where R2 and R3 are discharged. The family has one
    POSITIVE knowledge conjunct, [K (V0, holds_A(D2))] in S3 conjunct C. It gets
    a contingency test (the knowledge is not collapsed: it fails somewhere
    reachable), an operand-contingency test (the operand itself is false
    somewhere reachable, so it is not rigid) and a NON-SINGLETON VIEW CLASS
    test: at the very state where V0 learns that A held D2 it still cannot rule
    out that C holds it too, which is only possible if another reachable world
    shares that view. The family has one NEGATIVE knowledge conjunct,
    [~K (V0, holds_A(D2))] in S3 conjunct D, which gets its ignorance witness
    naming the colliding pair - the world in which A waited for D2 and the world
    in which it did not - with the operand pinned TRUE at the witnessing state
    so the [~K] cannot pass for the trivial reason that the operand is false
    there.

    Three faithfulness guards sit in the sanity group rather than the
    contingency group. [straggler-can-land-before-the-leapfrog] pins that D2 has
    a reachable EARLY arrival in which its round is still above its origin's
    committed round, which is why
    {!Dag_retention_model.Insert_gated_on_last_committed} is phase-scoped
    instead of blanket - a blanket drop would not be the real gate.
    [child-can-land-before-the-straggler] pins that the modeled upstream
    causal-order gate (cert_manager.rs:103-124) is a real per-parent condition
    and not a blanket serialization of the two deliveries.
    [leapfrogged-below-commit-state-is-reached] pins that the below-commit case
    S3 is about is actually visited, so the always-insert really is exercised. *)

open Telcoin_epistemic
open Dag_retention_model

(** Build the pristine system or fail the test on an impossible [Empty_init]. *)
let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Checker.Empty_init -> Alcotest.fail "make: empty init")
    (make ())

(** Render a proof error for the assertion message. *)
let error_to_string = function
  | Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Checker.Vacuous_antecedent -> "vacuous antecedent"

(** One proof case: the statement proves on the pristine model. *)
let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Dag_retention_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Dag_retention_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Dag_retention_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 2 peer_a x 2 peer_c x 3 phases x 3 straggler states x 3
   child states x 3 sequencing counts x 3 anchor counts = 972. The pristine
   reachable set is exactly 42: [c1] and [anchor] are functions of the phase
   when no gate is deleted, [S_refused] and [Ch_fatal] are unreachable, and the
   surviving (straggler, child) pairs are 4 for the [A_omits_parent] worlds and
   3 for the [A_names_parent] ones (there the child cannot land before its
   parent), so (4 + 3) x 3 phases x 2 peer_c = 42. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 972))

(* The exact pristine reachable count, pinned so a silent transition-relation
   drift shows up as a failing test rather than as a quietly different model. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "exact pristine reachable count" 42
        (Checker.reachable_count sys))

(* S1's gate, stated as unreachability: no committed sub-dag ever carries [c1] a
   second time. This is exactly what the [last_committed] disjunct of the walk
   skip (utils.rs:37-40) enforces over a dag that still holds every committed
   certificate (state.rs:182-183), and exactly what No_last_committed_skip
   removes. *)
let resequencing_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF resequenced(c1)" false
        (Checker.satisfiable sys (f C1_resequenced)))

(* S2's gate, stated as unreachability: no second sub-dag is ever anchored on
   the round-2 leader. This is the single comparison at bullshark.rs:136-138,
   and exactly what No_below_commit_shortcircuit removes. *)
let reanchoring_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF reanchored(L2)" false
        (Checker.satisfiable sys (f Leader2_reanchored)))

(* S3's gate, stated as unreachability: the critical consensus task never exits
   on ConsensusError::MissingParent (state.rs:203-206, :373-375, :347-349).
   This is what the always-insert of state.rs:143-148 buys, and exactly what
   Insert_gated_on_last_committed removes. *)
let consensus_death_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF dead(consensus)" false
        (Checker.satisfiable sys (f Consensus_dead)))

(* Faithfulness guard: the below-commit state S3 is about is genuinely visited -
   the round-4 leader has been committed, [last_committed[D] = 3] has passed
   D2's round, and D2 is nevertheless resident in the dag. Without this the
   always-insert would never be exercised and S3 would be about nothing. *)
let leapfrogged_below_commit_state_is_reached () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (leapfrogged(D2) /\\ resident(D2))" true
        (Checker.satisfiable sys
           (Formula.And (f Leapfrogged, f Straggler_resident))))

(* Faithfulness guard for the SCOPE of Insert_gated_on_last_committed: D2 also
   has a reachable EARLY arrival, at which [2 > last_committed[D]] and every
   variant inserts it. The real guard is a comparison, not a blanket refusal, so
   a mutation that dropped D2 unconditionally would not be the real gate; this
   pins that the model keeps the comparison. *)
let straggler_can_land_before_the_leapfrog () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (resident(D2) /\\ ~leapfrogged(D2))" true
        (Checker.satisfiable sys
           (Formula.And (f Straggler_resident, Formula.Not (f Leapfrogged)))))

(* Faithfulness guard for the modeled upstream repair path: the certificate
   manager's causal-order gate (cert_manager.rs:103-124) is a PER-PARENT
   condition, so in the worlds where A3 does not name D2 it lands with D2 still
   absent. If this were false the model would be serializing both deliveries and
   the S3 pin would be measuring the wrong thing. *)
let child_can_land_before_the_straggler () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (resident(A3) /\\ ~resident(D2))" true
        (Checker.satisfiable sys
           (Formula.And (f Child_resident, Formula.Not (f Straggler_resident)))))

(* R2, first half - the positive knowledge of S3 conjunct C is CONTINGENT: there
   are reachable states at which V0 does not know that A held D2. A knowledge
   conjunct that held everywhere would be epistemically empty. *)
let possession_knowledge_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v0 holds_A(D2)" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f Peer_a_holds_straggler)))))

(* R2, second half - the OPERAND is contingent too, so the [K] is not knowledge
   of something rigid: [holds_A(D2)] is false at every reachable state of the
   two worlds in which A did not wait for D2. *)
let possession_operand_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~holds_A(D2) and EF holds_A(D2)" true
        (Checker.satisfiable sys (Formula.Not (f Peer_a_holds_straggler))
        && Checker.satisfiable sys (f Peer_a_holds_straggler)))

(* R2, the non-singleton view class test for S3 conjunct C. At the operative
   state - A3 resident and naming D2 - pick [holds_C(D2)], which is FALSE
   there, and check that V0 does not know it is false. That is only possible if
   another reachable world shares V0's view at that state, i.e. the class is not
   a singleton and the [K] of conjunct C is a real quantification over two
   worlds rather than a lookup. The colliding world is the
   [C_holds_parent] twin: C's round-3 certificate was certified and delivered
   before D2 finished assembling, so C's possession leaves no trace in V0's
   ConsensusState. *)
let citing_child_view_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (cites(A3,D2) /\\ ~K_v0 ~holds_C(D2))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Child_cites_straggler,
                Formula.Not
                  (Formula.K
                     (Validator.V0, Formula.Not (f Peer_c_holds_straggler))) ))))

(* R3 ignorance witness for S3 conjunct D. The operand is pinned TRUE at the
   witnessing state, so the [~K] cannot pass for the trivial reason that the
   operand is simply false there: at a state where A DOES hold D2, D2 is
   resident in V0's dag and A3 has not arrived yet, V0 still cannot conclude it,
   because nothing it holds mentions D2's re-use. Colliding pair, both reachable
   and identical under [View_consensus]:
   W1 = (A_names_parent, Ph_leader4, S_resident, Ch_inflight) and
   W2 = (A_omits_parent, Ph_leader4, S_resident, Ch_inflight). *)
let ignorance_before_the_citation () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (resident(D2) /\\ holds_A(D2) /\\ ~resident(A3) /\\ ~K_v0 holds_A(D2))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Straggler_resident, f Peer_a_holds_straggler),
                Formula.And
                  ( Formula.Not (f Child_resident),
                    Formula.Not
                      (Formula.K (Validator.V0, f Peer_a_holds_straggler)) ) ))))

(* The other half of the R3 pair: the colliding world itself is reachable with
   the same visible configuration and the operand FALSE, which is what makes the
   ignorance above genuine rather than an artefact of an unreachable twin. *)
let ignorance_colliding_world_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (resident(D2) /\\ ~holds_A(D2) /\\ ~resident(A3) /\\ leapfrogged(D2))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And
                  (f Straggler_resident, Formula.Not (f Peer_a_holds_straggler)),
                Formula.And (Formula.Not (f Child_resident), f Leapfrogged) ))))

(* And the positive side actually happens: there is a reachable state at which
   the resident A3 names D2 AND V0 knows that A held it. Without this, conjunct
   C of S3 would be vacuously true over an empty operative set. *)
let citation_knowledge_is_attained () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (cites(A3,D2) /\\ K_v0 holds_A(D2))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Child_cites_straggler,
                Formula.K (Validator.V0, f Peer_a_holds_straggler) ))))

let () =
  Alcotest.run "dag_retention"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Dag_retention_statements.name `Quick
              (prove_one st))
          Dag_retention_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "resequencing-unreachable" `Quick
            resequencing_unreachable;
          Alcotest.test_case "reanchoring-unreachable" `Quick
            reanchoring_unreachable;
          Alcotest.test_case "consensus-death-unreachable" `Quick
            consensus_death_unreachable;
          Alcotest.test_case "leapfrogged-below-commit-state-is-reached" `Quick
            leapfrogged_below_commit_state_is_reached;
          Alcotest.test_case "straggler-can-land-before-the-leapfrog" `Quick
            straggler_can_land_before_the_leapfrog;
          Alcotest.test_case "child-can-land-before-the-straggler" `Quick
            child_can_land_before_the_straggler;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "possession-knowledge-is-contingent" `Quick
            possession_knowledge_is_contingent;
          Alcotest.test_case "possession-operand-is-contingent" `Quick
            possession_operand_is_contingent;
          Alcotest.test_case "citing-child-view-class-is-not-a-singleton" `Quick
            citing_child_view_class_is_not_a_singleton;
          Alcotest.test_case "ignorance-before-the-citation" `Quick
            ignorance_before_the_citation;
          Alcotest.test_case "ignorance-colliding-world-is-reachable" `Quick
            ignorance_colliding_world_is_reachable;
          Alcotest.test_case "citation-knowledge-is-attained" `Quick
            citation_knowledge_is_attained;
        ] );
    ]
