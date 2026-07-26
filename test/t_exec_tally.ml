(** The EXEC-TALLY statement proves on the pristine model through
    [prove_nonvacuous] (so the antecedent is also checked reachable), the
    reachable graph stays in its justified band, and the epistemic layer is
    genuinely partial-information: the K_V0 operand is contingent, and the
    card's false-witness pair - tally = {V3} before any execution colliding
    with tally = {V3} after execution with honest results in flight - is
    reachable on both sides. *)

open Telcoin_epistemic

let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Exec_tally_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Exec_tally_model.make ())

let error_to_string = function
  | Exec_tally_model.Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Exec_tally_model.Checker.Vacuous_antecedent -> "vacuous antecedent"

let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Exec_tally_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Exec_tally_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Exec_tally_statements.prove sys st)))

(* Crude product bound: 5 phases x 3 fabricate values x 4 reachable tally
   values = 60; the executed flags are phase-determined and [advanced] is
   tally-determined, so they add no factor. The actual reachable set is 9
   states. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Exec_tally_model.Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 64))

let f a = Formula.Atom a

(* The single positive K conjunct of S8 is K_V0(honest-saved), used in
   both halves of the formula: assert its operand is NOT plain truth under
   the view partition, or the statement would be epistemically vacuous. *)
let k_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v0(honest-saved): knowledge did not collapse" true
        (Exec_tally_model.Checker.satisfiable sys
           (Formula.Not
              (Formula.K (Validator.V0, f Exec_tally_model.Honest_saved)))))

let lone_v3_tally =
  Formula.conj
    [
      f (Exec_tally_model.In_tally Validator.V3);
      Formula.Not (f (Exec_tally_model.In_tally Validator.V1));
      Formula.Not (f (Exec_tally_model.In_tally Validator.V2));
    ]

(* wcheck run A: fabricate-result branch pre-[Save_sign] - the observer
   holds exactly V3's fabricated signature and NO honest CVV has saved
   (the operand-false side of the colliding pair). *)
let false_witness_pre_save () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (tally = {v3} /\\ ~honest-saved)" true
        (Exec_tally_model.Checker.satisfiable sys
           (Formula.And
              (lone_v3_tally, Formula.Not (f Exec_tally_model.Honest_saved)))))

(* wcheck run B: same view, other side - honest CVVs saved but their
   signed results are still in flight to the observer (the operand-true
   side), so K_V0 rightly fails at this very state. *)
let false_witness_post_save () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (tally = {v3} /\\ honest-saved /\\ ~K_v0(honest-saved))" true
        (Exec_tally_model.Checker.satisfiable sys
           (Formula.And
              ( lone_v3_tally,
                Formula.And
                  ( f Exec_tally_model.Honest_saved,
                    Formula.Not
                      (Formula.K
                         (Validator.V0, f Exec_tally_model.Honest_saved)) ) ))))

let () =
  Alcotest.run "exec_tally"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Exec_tally_statements.name `Quick
              (prove_one st))
          Exec_tally_statements.all );
      ( "sanity",
        [ Alcotest.test_case "reachable-bounded" `Quick reachable_bounded ] );
      ( "contingency",
        [
          Alcotest.test_case "k-contingent" `Quick k_contingent;
          Alcotest.test_case "false-witness-pre-save" `Quick
            false_witness_pre_save;
          Alcotest.test_case "false-witness-post-save" `Quick
            false_witness_post_save;
        ] );
    ]
