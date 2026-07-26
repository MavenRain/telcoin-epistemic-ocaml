(** The UNRESOLVED-AUTHOR family (DESIGN CONSENSUS-EXT #3) proves on the
    pristine {!Unres_model}, its reachable graph is the expected tiny 3-way
    branching structure, and the epistemic layer is genuinely
    partial-information: at a flagged state the honest-author lag run and the
    Byzantine-junk run collide in V2's view, so each [~K_V2] conjunct holds
    non-trivially - the operand is TRUE at the flagged state yet knowledge
    still fails, exactly the card's false witness (consensus.rs:1499-1513, the
    attribute-free reject flag). *)

open Telcoin_epistemic
open Unres_model

(** Build the pristine system or fail the test on an impossible [Empty_init]. *)
let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Checker.Empty_init -> Alcotest.fail "make: empty init")
    (make ())

(** Render a proof error for the assertion message; both constructors spelled. *)
let error_to_string = function
  | Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Checker.Vacuous_antecedent -> "vacuous antecedent"

(** One proof case: the statement proves on the pristine model. *)
let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Unres_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Unres_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Unres_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The reachable set is exactly the 4-phase run with one 3-way hidden branch
    resolved at the first step: 1 initial + 3 x (Deliver_r0, Vote_r1, Done) =
    10 states; 16 = 4 phases x 4 [unres] values is the crude product bound and
    leaves slack with no hiding blow-up (V2's local is phase/branch-determined,
    so it adds no independent factor). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 16))

(** Every path reaches the terminal phase - liveness survives the reject via
    the fetch-on-vote recovery (handler.rs:225-230). *)
let terminal_reached () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF done" true
        (Checker.valid sys (Formula.Af (f At_done))))

(** The pristine Skip is unconditional: the author_resolved guard
    (consensus.rs:2094-2095) keeps V2's ban set and penalty latch empty at
    every reachable state, so nobody is ever charged for an unresolved-author
    reject. *)
let skip_holds_pristine () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G (banned_2 = {} /\\ ~penalized_by_2)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.And
                 (Unres_statements.no_ban_by_2, Formula.Not (f Penalized_by_2))))))

(** The honest-author K operator did not collapse to universal truth: some
    reachable state fails [K_V2(unres_author_honest)]. *)
let k_honest_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v2(unres-author-honest)" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V2, f Unres_author_honest)))))

(** The Byzantine-author K operator did not collapse either. *)
let k_byz_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v2(unres-author-byz)" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V2, f Unres_author_byz)))))

(** wcheck run A (lag branch): a flagged state where the rejected author WAS
    honest V1 - [unres_author_honest] is TRUE - yet V2 does not know it,
    because the view-identical junk state makes it false. The operand-true
    side proves the [~K] conjunct is epistemic teeth, not a trivial
    operand-false pass. *)
let false_witness_lag () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (saw-unres /\\ unres-author-honest /\\ ~K_v2 unres-author-honest)"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Saw_unres_2;
                f Unres_author_honest;
                Formula.Not (Formula.K (Validator.V2, f Unres_author_honest));
              ])))

(** wcheck run B (junk-drop branch): the colliding partner - a flagged state
    where the rejected author WAS Byzantine V3 - [unres_author_byz] is TRUE -
    yet V2 does not know it, the view-identical lag state making it false. *)
let false_witness_junk () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (saw-unres /\\ unres-author-byz /\\ ~K_v2 unres-author-byz)" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Saw_unres_2;
                f Unres_author_byz;
                Formula.Not (Formula.K (Validator.V2, f Unres_author_byz));
              ])))

let () =
  Alcotest.run "unres"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Unres_statements.name `Quick (prove_one st))
          Unres_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "terminal-reached" `Quick terminal_reached;
          Alcotest.test_case "skip-holds-pristine" `Quick skip_holds_pristine;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-honest-contingent" `Quick k_honest_contingent;
          Alcotest.test_case "k-byz-contingent" `Quick k_byz_contingent;
          Alcotest.test_case "false-witness-lag" `Quick false_witness_lag;
          Alcotest.test_case "false-witness-junk" `Quick false_witness_junk;
        ] );
    ]
