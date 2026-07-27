(** The ban family (DESIGN BAN #2, #5) proves on the pristine {!Ban_model}
    through [prove_nonvacuous] (so each antecedent is also checked reachable),
    the reachable graph stays in its justified band, and the epistemic layer is
    genuinely partial-information: every positive K conjunct is contingent
    (its ~K is reachable), and both cards' false witnesses - the honest relayer
    holding the bad payload while its innocence is unknowable (#2) and the
    targeted branch where V1 knows byz(V3) but V2 does not (#5) - are
    reachable. *)

open Telcoin_epistemic
open Ban_model

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

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
        (st.Ban_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Ban_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Ban_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The reachable set is the initial state, plus one resolve state per
    strategy at the Forward phase (5), plus one terminal state per strategy at
    Done (5): 11 states. 16 leaves slack without a hiding blow-up. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 16))

(** Every path reaches the terminal phase (the model steps Choose -> Forward
    -> Done and stutter-closes there), so the liveness conjunct AF done is
    honest. *)
let terminal_reached () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF done" true
        (Checker.valid sys (Formula.Af (f At_done))))

(** The positive K conjuncts of S2: [K_i (authored-bad p)] for each honest i
    and each peer p != i. Every one must be contingent - its ~K reachable -
    or the charge-routing implication would hold for the wrong (K-collapsed)
    reason. *)
let s2_k_pairs =
  List.concat_map
    (fun i ->
      List.map
        (fun p -> (i, Authored_bad p))
        (List.filter (fun p -> Bool.not (Validator.equal p i)) roster))
    honest

(** S2 knowledge is not collapsed: for every K conjunct the negation is
    reachable (for the honest-p targets because authored-bad p is never true,
    for the V3 target because a not-yet-delivered invalid branch collides with
    the Cooperate branch on i's view). *)
let s2_k_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "every K_i(authored-bad p) conjunct of S2 has ~K reachable" true
        (List.for_all
           (fun (i, op) ->
             Checker.satisfiable sys (Formula.Not (Formula.K (i, f op))))
           s2_k_pairs))

(** S2 card false witness (wcheck run t): the Invalid_gossip relay branch
    where the bad payload authored by V3 is in flight and V2 has not yet
    received it - authored-bad(V3) is true but V2 cannot know it, so the
    charge-routing K stays contingent. *)
let s2_false_witness () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (authored-bad(v3) /\\ ~evidence(v2) /\\ ~K_v2 authored-bad(v3))"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f (Authored_bad Validator.V3);
                Formula.Not (f (Evidence Validator.V2));
                Formula.Not
                  (Formula.K (Validator.V2, f (Authored_bad Validator.V3)));
              ])))

(** S2 grounded-charge side: when the routed fatal charge does land on V3, the
    charger knows V3 authored the bad payload (every reachable state with that
    local lies downstream of V3's send), so the K in the implication is
    attained, not vacuously false. *)
let s2_charge_grounds_knowledge () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (fatal-charge(v2,v3) /\\ K_v2 authored-bad(v3))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f (Fatal_charge (Validator.V2, Validator.V3)),
                Formula.K (Validator.V2, f (Authored_bad Validator.V3)) ))))

(** S5 knowledge is not collapsed: for every honest i the negation of
    [K_i (byz v3)] is reachable (the initial and Cooperate-branch views, where
    byz(V3) is false, collide with the invalid branches), so the E_honest
    conjunct is genuine. *)
let s5_k_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "every K_i(byz v3) conjunct of S5 has ~K reachable"
        true
        (List.for_all
           (fun i ->
             Checker.satisfiable sys (Formula.Not (Formula.K (i, f Byz_v3))))
           honest))

(** S5 card false witness (wcheck layer i): the targeted branch where only V1
    receives the invalid payload - byz(V3) is true and V1 holds evidence, but
    V2 has none and its view collides with the Cooperate branch, so V2 does
    not know byz(V3). This is the collision that keeps common knowledge from
    forming. *)
let s5_false_witness () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (byz(v3) /\\ evidence(v1) /\\ ~evidence(v2) /\\ ~K_v2 byz(v3))" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Byz_v3;
                f (Evidence Validator.V1);
                Formula.Not (f (Evidence Validator.V2));
                Formula.Not (Formula.K (Validator.V2, f Byz_v3));
              ])))

let () =
  Alcotest.run "ban"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Ban_statements.name `Quick (prove_one st))
          Ban_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "terminal-reached" `Quick terminal_reached;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "s2-k-contingent" `Quick s2_k_contingent;
          Alcotest.test_case "s2-false-witness" `Quick s2_false_witness;
          Alcotest.test_case "s2-charge-grounds-knowledge" `Quick
            s2_charge_grounds_knowledge;
          Alcotest.test_case "s5-k-contingent" `Quick s5_k_contingent;
          Alcotest.test_case "s5-false-witness" `Quick s5_false_witness;
        ] );
    ]
