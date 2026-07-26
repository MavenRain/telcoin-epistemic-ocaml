(** The re-vote family (DESIGN CONSENSUS-EXT #11) proves on the pristine
    {!Revote_model}, the reachable graph is the expected tiny branching
    structure, and the epistemic layer is genuinely partial-information:
    the card's false witness - a re-voting V1 co-existing with a WITHHELD
    certificate it cannot know about - is reachable, its no-certificate
    collision partner is reachable, and certificate knowledge is
    attainable (in the deliver branch), so the ~K in the AG conjunct is
    contingent rather than collapsed. *)

open Telcoin_epistemic
open Revote_model

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
        (st.Revote_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Revote_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Revote_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The reachable set is exactly the linear 4-phase run with one 3-way
    hidden branch at Certify: 2 pre-branch states plus 3 branches times 2
    phases = 8 states; 32 leaves slack without hiding blow-up. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 32))

(** Every path reaches the terminal phase. *)
let terminal_reached () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF done" true
        (Checker.valid sys (Formula.Af (f At_done))))

(** The pristine guard's contract: V1 never re-votes while its own dag
    holds the slot's certificate (handler.rs:824-839) - the deliver
    branch blocks the re-vote. *)
let guard_blocks_under_own_cert () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G (cert-in-v1-dag -> ~revote)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies (f Cert_in_v1_dag, Formula.Not (f Revoted))))))

(** The card's false witness is reachable: a state where V1 has re-voted,
    the certificate EXISTS (withheld in V3's private slot), and V1 does
    not know it - knowledge fails where the operand is true, so the AG
    conjunct's ~K is non-trivial. *)
let false_witness_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (revote /\\ cert-exists /\\ ~K_v1 cert-exists)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Revoted,
                Formula.And
                  ( f Cert_exists,
                    Formula.Not (Formula.K (Validator.V1, f Cert_exists)) ) ))))

(** The collision partner is reachable: the skip-aggregate re-vote state,
    honest-view-identical to the false witness but certificate-free -
    the state that grounds V1's ignorance. *)
let no_cert_collision_partner () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (revote /\\ ~cert-exists)" true
        (Checker.satisfiable sys
           (Formula.And (f Revoted, Formula.Not (f Cert_exists)))))

(** Certificate knowledge is attainable (the deliver branch puts the
    certificate in V1's own dag), so ~K in the AG conjunct is contingent,
    not vacuously true everywhere. *)
let knowledge_attainable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF K_v1 cert-exists" true
        (Checker.satisfiable sys (Formula.K (Validator.V1, f Cert_exists))))

let () =
  Alcotest.run "revote"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Revote_statements.name `Quick (prove_one st))
          Revote_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "terminal-reached" `Quick terminal_reached;
          Alcotest.test_case "guard-blocks-under-own-cert" `Quick
            guard_blocks_under_own_cert;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "false-witness-reachable" `Quick
            false_witness_reachable;
          Alcotest.test_case "no-cert-collision-partner" `Quick
            no_cert_collision_partner;
          Alcotest.test_case "knowledge-attainable" `Quick knowledge_attainable;
        ] );
    ]
