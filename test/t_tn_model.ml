(** Sanity of the telcoin abstraction: the reachable graph is the expected
    small branching structure, the runs do what the design says (commit in
    every anchor-bearing branch, no commit in the leader-crash branch, no
    conflicting certificates anywhere), and the epistemic layer is genuinely
    partial-information (a validator that saw only variant A cannot rule
    out equivocation; the delay window makes another validator's anchor
    possession unknowable until re-sync). *)

open Telcoin_epistemic
open Tn_model

let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Checker.Empty_init -> Alcotest.fail "make: empty init")
    (make ())

let f a = Formula.Atom a

let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (64 <= n && n <= 2048))

let terminal_reached () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF done" true
        (Checker.valid sys (Formula.Af (f At_done))))

let no_conflicting_certs () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G ~conflicting-certs" true
        (Checker.valid sys (Formula.Ag (Formula.Not (f Conflicting_certs)))))

let commit_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF committed(v1, anchor)" true
        (Checker.satisfiable sys (f (Committed (Validator.V1, anchor)))))

let crash_branch_never_commits () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "no anchor cert -> no commit: committed implies cert existed" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 (f (Committed (Validator.V1, anchor)), f (Cert_formed anchor))))))

let starved_batch_never_certifies () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "byz cert implies honest holders (contrapositive of starvation)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 ( f (Cert_formed { author = Validator.V3; round = Tn_state.R0; variant = Tn_state.A }),
                   f (Honest_holders_ge { Tn_state.s_author = Validator.V3; s_round = Tn_state.R0 }) )))))

let equivocation_opaque_to_v0 () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (byz-equivocating /\\ ~K_v0 byz-equivocating)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Byz_equivocating,
                Formula.Not (Formula.K (Validator.V0, f Byz_equivocating)) ))))

let delay_window_hides_possession () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (v1 holds anchor unknowably to v0): anchor delivered but K_v0 fails"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f (In_dag (Validator.V1, anchor)),
                Formula.Not
                  (Formula.K (Validator.V0, f (In_dag (Validator.V1, anchor)))) ))))

let eventual_mutual_knowledge () =
  with_sys (fun sys ->
      let all_hold =
        Formula.conj (List.map (fun j -> f (In_dag (j, anchor))) honest)
      in
      Alcotest.(check bool)
        "cert(anchor) ~> E_H(all honest hold anchor)" true
        (Checker.valid sys
           (Formula.leads_to (f (Cert_formed anchor))
              (Formula.Everyone (honest, all_hold)))))

let common_knowledge_of_possession_probe () =
  with_sys (fun sys ->
      let all_hold =
        Formula.conj (List.map (fun j -> f (In_dag (j, anchor))) honest)
      in
      Alcotest.(check bool)
        "cert(anchor) ~> C_H(all honest hold anchor): CK is attained at Done"
        true
        (Checker.valid sys
           (Formula.leads_to (f (Cert_formed anchor))
              (Formula.Common (honest, all_hold)))))

let () =
  Alcotest.run "tn_model"
    [
      ( "structure",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "terminal-reached" `Quick terminal_reached;
          Alcotest.test_case "no-conflicting-certs" `Quick no_conflicting_certs;
          Alcotest.test_case "commit-reachable" `Quick commit_reachable;
          Alcotest.test_case "crash-no-commit" `Quick crash_branch_never_commits;
          Alcotest.test_case "starve-no-cert" `Quick starved_batch_never_certifies;
        ] );
      ( "epistemic",
        [
          Alcotest.test_case "equivocation-opaque" `Quick equivocation_opaque_to_v0;
          Alcotest.test_case "delay-hides-possession" `Quick delay_window_hides_possession;
          Alcotest.test_case "eventual-mutual-knowledge" `Quick eventual_mutual_knowledge;
          Alcotest.test_case "common-knowledge-probe" `Quick common_knowledge_of_possession_probe;
        ] );
    ]
