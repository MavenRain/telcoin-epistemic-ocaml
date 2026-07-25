(** Temporal core of the checker on toy graphs, positive rows paired with
    NEGATIVE rows ([[feedback-confirm-tests-by-mutation]] discipline at the
    semantic level: each negative row is a formula the semantics must refute,
    so a broken fixpoint that over-approximates flips it red).

    Diamond graph: s0 -> {s1, s2}, s1 -> s3, s2 -> s3, s3 terminal (stutter-
    closed by [make]). s2 is labeled Bad, s3 is labeled Goal.

    Livelock graph: s0 -> {s0, s1}, s1 terminal. The s0 self-loop is an
    unfair scheduler; AF must honestly refuse the liveness claim. *)

open Telcoin_epistemic
module Sys = System.Make (Int) (Int)

type atom = Bad | Goal | Start

let diamond_label a s =
  match a with
  | Bad -> Int.equal s 2
  | Goal -> Int.equal s 3
  | Start -> Int.equal s 0

(* Every validator has full observability here: knowledge collapses to truth,
   which t_knowledge tests from the opposite side (hidden state). *)
let full_view (_ : Validator.t) (s : int) = s

let diamond =
  {
    Sys.init = [ 0 ];
    next =
      (fun s ->
        if Int.equal s 0 then [ 1; 2 ]
        else if Int.equal s 1 then [ 3 ]
        else if Int.equal s 2 then [ 3 ]
        else []);
    view = full_view;
    label = diamond_label;
  }

let livelock =
  {
    Sys.init = [ 0 ];
    next = (fun s -> if Int.equal s 0 then [ 0; 1 ] else []);
    view = full_view;
    label =
      (fun a s ->
        match a with
        | Bad -> false
        | Goal -> Int.equal s 1
        | Start -> Int.equal s 0);
  }

let with_sys spec k =
  Result.fold
    ~ok:k
    ~error:(fun Sys.Empty_init -> Alcotest.fail "make: empty init")
    (Sys.make spec)

let reach_count () =
  with_sys diamond (fun sys ->
      Alcotest.(check int) "diamond reachable" 4 (Sys.reachable_count sys))

let af_inevitable () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "AF Goal holds" true
        (Sys.valid sys (Formula.Af (Formula.Atom Goal))))

let af_not_bad () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "AF Bad refuted (s1 path avoids)" false
        (Sys.valid sys (Formula.Af (Formula.Atom Bad))))

let ef_bad () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "EF Bad holds" true
        (Sys.valid sys (Formula.Ef (Formula.Atom Bad))))

let ag_refuted_by_bad () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "AG ~Bad refuted" false
        (Sys.valid sys (Formula.Ag (Formula.Not (Formula.Atom Bad)))))

let au_holds () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "A[~Start-is-false U Goal] via Au" true
        (Sys.valid sys
           (Formula.Au
              ( Formula.Or (Formula.Atom Start, Formula.Not (Formula.Atom Goal)),
                Formula.Atom Goal ))))

let eu_via_bad () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "E[Bad-or-Start U Goal]" true
        (Sys.valid sys
           (Formula.Eu
              ( Formula.Or (Formula.Atom Start, Formula.Atom Bad),
                Formula.Atom Goal ))))

let ax_after_branch () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "AX (AX Goal) holds at s0" true
        (Sys.valid sys (Formula.Ax (Formula.Ax (Formula.Atom Goal)))))

let livelock_refutes_af () =
  with_sys livelock (fun sys ->
      Alcotest.(check bool) "AF Goal refuted under unfair self-loop" false
        (Sys.valid sys (Formula.Af (Formula.Atom Goal))))

let livelock_ef () =
  with_sys livelock (fun sys ->
      Alcotest.(check bool) "EF Goal still holds" true
        (Sys.valid sys (Formula.Ef (Formula.Atom Goal))))

let stutter_terminal_ag () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "AG(Goal -> AX Goal): terminal stutter" true
        (Sys.valid sys
           (Formula.Ag
              (Formula.Implies (Formula.Atom Goal, Formula.Ax (Formula.Atom Goal))))))

(* Proof kernel rows. *)

let prove_ok () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "prove AF Goal = Ok" true
        (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false)
           (Sys.prove sys (Formula.Af (Formula.Atom Goal)))))

let prove_refuted_counts () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "prove AF Bad = Refuted at the 1 init" true
        (Result.fold
           ~ok:(fun _ -> false)
           ~error:(fun e ->
             match e with
             | Sys.Refuted { failing_inits } -> Int.equal failing_inits 1
             | Sys.Vacuous_antecedent -> false)
           (Sys.prove sys (Formula.Af (Formula.Atom Bad)))))

let prove_nonvacuous_guards () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "unreachable antecedent = Vacuous_antecedent" true
        (Result.fold
           ~ok:(fun _ -> false)
           ~error:(fun e ->
             match e with
             | Sys.Refuted _ -> false
             | Sys.Vacuous_antecedent -> true)
           (Sys.prove_nonvacuous sys
              ~antecedent:(Formula.And (Formula.Atom Bad, Formula.Atom Goal))
              (Formula.leads_to
                 (Formula.And (Formula.Atom Bad, Formula.Atom Goal))
                 (Formula.Atom Goal)))))

let prove_nonvacuous_ok () =
  with_sys diamond (fun sys ->
      Alcotest.(check bool) "reachable antecedent passes through" true
        (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false)
           (Sys.prove_nonvacuous sys ~antecedent:(Formula.Atom Bad)
              (Formula.leads_to (Formula.Atom Bad) (Formula.Atom Goal)))))

let theorem_carries_formula () =
  with_sys diamond (fun sys ->
      let goal = Formula.Af (Formula.Atom Goal) in
      Alcotest.(check string) "Theorem.formula round-trips" "F(goal)"
        (Result.fold
           ~ok:(fun thm ->
             Formula.pp
               ~atom:(fun a ->
                 match a with Bad -> "bad" | Goal -> "goal" | Start -> "start")
               (Sys.Theorem.formula thm))
           ~error:(fun _ -> "<refuted>")
           (Sys.prove sys goal)))

let () =
  Alcotest.run "kernel"
    [
      ( "temporal",
        [
          Alcotest.test_case "reach-count" `Quick reach_count;
          Alcotest.test_case "af-inevitable" `Quick af_inevitable;
          Alcotest.test_case "af-not-bad" `Quick af_not_bad;
          Alcotest.test_case "ef-bad" `Quick ef_bad;
          Alcotest.test_case "ag-refuted" `Quick ag_refuted_by_bad;
          Alcotest.test_case "au-holds" `Quick au_holds;
          Alcotest.test_case "eu-via-bad" `Quick eu_via_bad;
          Alcotest.test_case "ax-nested" `Quick ax_after_branch;
          Alcotest.test_case "livelock-refutes-af" `Quick livelock_refutes_af;
          Alcotest.test_case "livelock-ef" `Quick livelock_ef;
          Alcotest.test_case "stutter-terminal" `Quick stutter_terminal_ag;
        ] );
      ( "proof",
        [
          Alcotest.test_case "prove-ok" `Quick prove_ok;
          Alcotest.test_case "prove-refuted" `Quick prove_refuted_counts;
          Alcotest.test_case "vacuity-guard" `Quick prove_nonvacuous_guards;
          Alcotest.test_case "nonvacuous-ok" `Quick prove_nonvacuous_ok;
          Alcotest.test_case "theorem-formula" `Quick theorem_carries_formula;
        ] );
    ]
