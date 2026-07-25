(** The seven statements prove on the pristine model, each through
    [prove_nonvacuous] (so every antecedent is also checked reachable), and
    every proof hands back a theorem carrying its exact formula. *)

open Telcoin_epistemic

let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Tn_model.Checker.Empty_init -> Alcotest.fail "make: empty init")
    (Tn_model.make ())

let error_to_string = function
  | Tn_model.Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Tn_model.Checker.Vacuous_antecedent -> "vacuous antecedent"

let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Statements.name ^ " [" ^ Statements.bucket_to_string st.Statements.bucket
       ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Statements.prove sys st)))

let theorem_formula_roundtrip () =
  with_sys (fun sys ->
      Alcotest.(check bool) "theorem carries a renderable formula" true
        (Result.fold
           ~ok:(fun thm ->
             0
             < String.length
                 (Formula.pp ~atom:Tn_model.atom_to_string
                    (Tn_model.Checker.Theorem.formula thm)))
           ~error:(fun _ -> false)
           (Statements.prove sys Statements.s1)))

let all_buckets_covered () =
  let has b =
    List.exists
      (fun st ->
        Int.equal 0 (String.compare (Statements.bucket_to_string st.Statements.bucket) b))
      Statements.all
  in
  Alcotest.(check bool) "safety+liveness+fairness+security all present" true
    (has "safety" && has "liveness" && has "fairness" && has "security")

let seven () =
  Alcotest.(check int) "exactly seven statements" 7 (List.length Statements.all)

let () =
  Alcotest.run "statements"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Statements.name `Quick (prove_one st))
          Statements.all );
      ( "meta",
        [
          Alcotest.test_case "theorem-roundtrip" `Quick theorem_formula_roundtrip;
          Alcotest.test_case "buckets" `Quick all_buckets_covered;
          Alcotest.test_case "seven" `Quick seven;
        ] );
    ]
