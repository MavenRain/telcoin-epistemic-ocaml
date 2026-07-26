(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    re-vote family: the statement is pinned by deleting exactly the local
    cert-evidence guard it depends on (handler.rs:824-839), and the paired
    row asserts the proof FLIPS to an error on the mutated model - under
    {!Revote_model.No_cert_evidence_guard} V1 re-votes in the deliver
    branch while holding the certificate in its own dag, so
    [K (V1, Cert_exists)] is true at a re-vote state and the AG conjunct
    is refuted. No sibling path repairs the deletion: the model's Revote
    step is already past the [auth_last_vote] cache (the collapsed
    restart premise), so the deleted guard was the sole gate. The
    pristine rows in t_revote are the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Revote_model.Checker.Empty_init -> Alcotest.fail "make: empty init")
    (Revote_model.Checker.make (Revote_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Revote_statements.name name))
    Revote_statements.all

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " flips to refuted under the mutation")
            false
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Revote_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine
    model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Revote_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Revote_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "revote_mutation"
    [
      ( "dropped cert-evidence guard kills revote-under-ignorance",
        pin Revote_model.No_cert_evidence_guard
          "revote-only-under-global-cert-ignorance" );
    ]
