(** The ahead-certificate catch-up family (DESIGN CONSENSUS-EXT #13) proves
    on the pristine {!Catchup_model} through [prove_nonvacuous] (so the
    antecedent is also checked reachable) and the reachable graph stays in
    its justified band. The family is pure temporal liveness: the earlier
    K_V2 conjunct was degenerate at the only antecedent-true state
    (singleton V2 view class, operand entailed by V2's own R2 holding) and
    was dropped, so there is no contingency suite - no [K] remains to keep
    honest. *)

open Telcoin_epistemic
open Catchup_model

(** Build the pristine system or fail on an impossible [Empty_init]. *)
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
        (st.Catchup_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Catchup_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Catchup_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** Reachable bound: 12 phases (propose/certify/deliver over R0..R2, plus
    Catch_up, Commit_eval, Done) times 3 lag choices = 36; certificates and
    every local are (phase, lag)-determined - the sole branch point is
    [Deliver R0] - so no extra factor, and the actual reachable set is 21
    states (3 shared-prefix + 9 per branch). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 36))

(** Every path reaches the terminal phase (both branches run to [Done]). *)
let terminal_reached () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF done" true
        (Checker.valid sys (Formula.Af (f At_done))))

(** The unified catch-up antecedent is reachable, so [prove_nonvacuous] does
    not certify S13 on a false hypothesis - the [Lag_v2] [Catch_up] state,
    V2 holding an R2 certificate while still at proposer round R0. *)
let antecedent_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF catch-up antecedent" true
        (Checker.satisfiable sys Catchup_statements.catch_up_antecedent))

let () =
  Alcotest.run "catchup"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Catchup_statements.name `Quick (prove_one st))
          Catchup_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "terminal-reached" `Quick terminal_reached;
          Alcotest.test_case "antecedent-reachable" `Quick antecedent_reachable;
        ] );
    ]
