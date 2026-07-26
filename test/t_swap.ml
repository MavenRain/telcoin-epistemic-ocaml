(** The leader-swap family (DESIGN CONSENSUS-EXT #12) proves on the
    pristine {!Swap_model}, the reachable graph is the expected tiny
    branching structure, and the epistemic layer is genuinely partial-
    information: common knowledge of schedule agreement is contingent
    (it holds at Done but not before), the card's operand-false false
    witness - the Lag_v1 Execute state with swap_installed_v0 but not
    swap_installed_v1 - is reachable, and the No_lag Execute state has the
    operand TRUE while [Everyone] already fails, so the common-knowledge
    conjunct is grounded rather than collapsed. *)

open Telcoin_epistemic
open Swap_model

(** Build the pristine system or fail the test on an impossible
    [Empty_init]. *)
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
        (st.Swap_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Swap_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Swap_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The C-operand of S12: every honest validator's derived next leader for
    the bad slot is [a_good]. *)
let all_leader_good =
  Formula.conj (List.map (fun j -> f (Leader_next_good j)) honest)

(** The install invariant of S12's first conjunct, restated for a direct
    sanity check. *)
let install_invariant =
  Formula.conj
    (List.map
       (fun i ->
         Formula.And
           ( Formula.Implies (f (Swap_installed i), f (Boundary_committed i)),
             Formula.Implies (f (Boundary_committed i), f (Swap_installed i)) ))
       honest)

(** The reachable set is exactly the linear phase run with one 3-way hidden
    lag branch: 2 pre-branch states (Window, Commit_eval) + 3 Execute
    branches + 3 Done branches = 8 states; 16 leaves slack without any
    hiding blow-up. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 16))

(** The schedule always installs: every path eventually reaches an all-
    swapped state (the terminal Done). *)
let install_inevitable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF (all swap-installed)" true
        (Checker.valid sys
           (Formula.Af
              (Formula.conj (List.map (fun i -> f (Swap_installed i)) honest)))))

(** The first conjunct on its own: the install invariant holds at every
    reachable state (bullshark.rs:333-351 gates the table install exactly
    on committing the boundary). *)
let install_invariant_holds () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AG (swap-installed <-> boundary-committed)" true
        (Checker.valid sys (Formula.Ag install_invariant)))

(** The transcribed dispersion gate is the code's: the window's
    accumulated 2/2/2/0 tally arms it, while the multiplicity-1 tally
    1/1/1/0 truncates standard_dev to 0 and is rejected
    (leader_schedule.rs:86-103) - the exact profile split the faithfulness
    review pinned. *)
let dispersion_gate_matches_code () =
  let uniform n =
    List.fold_left
      (fun acc v -> Validator_map.add v n acc)
      Validator_map.empty honest
  in
  Alcotest.(check (pair bool bool))
    "swapped 2/2/2/0, not swapped 1/1/1/0" (true, false)
    (swapped (uniform 2), swapped (uniform 1))

(** Common knowledge did NOT collapse to plain truth: there is a reachable
    state where C_honest(operand) FAILS (this is the [K]-collapse guard the
    task requires - the family's only epistemic operator is [Common], so
    the collapse probe is [Not (Common ...)] rather than [Not (K ...)]). *)
let common_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~C_honest(all leader-next-good): common knowledge did not collapse"
        true
        (Checker.satisfiable sys
           (Formula.Not (Formula.Common (honest, all_leader_good)))))

(** Common knowledge IS attainable: it holds at the Done states where every
    honest validator is committed-and-executed and the shared seed pins
    every table to [a_good], so the [~C] above is contingent, not vacuous. *)
let common_attainable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF C_honest(all leader-next-good)" true
        (Checker.satisfiable sys (Formula.Common (honest, all_leader_good))))

(** The card's operand-false false witness is reachable: the Lag_v1 Execute
    state where V0 has installed its swap table but V1 (the deferred
    committer) has not - swap_installed_v0 /\ ~swap_installed_v1. Its
    honest views collide with the No_lag Execute state, which is exactly
    why knowledge of the operand cannot yet be common. *)
let false_witness_operand_false () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (swap-installed_v0 /\\ ~swap-installed_v1)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f (Swap_installed Validator.V0),
                Formula.Not (f (Swap_installed Validator.V1)) ))))

(** The operand-true / knowledge-absent side: at the No_lag Execute state
    every honest next-leader is [a_good] (operand TRUE) yet [Everyone]
    already fails - V0's committed-but-unexecuted view is bit-identical to
    its view in the Lag_v1 branch where the operand is false - so ~E_honest
    holds where the operand is true, the requested non-trivial pre-state. *)
let operand_true_not_everyone () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (all leader-next-good /\\ ~E_honest(all leader-next-good))" true
        (Checker.satisfiable sys
           (Formula.And
              ( all_leader_good,
                Formula.Not (Formula.Everyone (honest, all_leader_good)) ))))

let () =
  Alcotest.run "swap"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Swap_statements.name `Quick (prove_one st))
          Swap_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "install-inevitable" `Quick install_inevitable;
          Alcotest.test_case "install-invariant-holds" `Quick
            install_invariant_holds;
          Alcotest.test_case "dispersion-gate-matches-code" `Quick
            dispersion_gate_matches_code;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "common-contingent" `Quick common_contingent;
          Alcotest.test_case "common-attainable" `Quick common_attainable;
          Alcotest.test_case "false-witness-operand-false" `Quick
            false_witness_operand_false;
          Alcotest.test_case "operand-true-not-everyone" `Quick
            operand_true_not_everyone;
        ] );
    ]
