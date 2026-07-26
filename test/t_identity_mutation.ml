(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    identity family: the statement is pinned by
    {!Identity_model.Drop_record_verify}, which deletes exactly the
    [NodeRecord::decode_and_verify] signature gate inside [peer_record_valid]
    (consensus.rs:534-535) the statement depends on, and the mutated row
    asserts the proof FLIPS to an error. Under the mutation the forged record
    binding V1's committee key to p3 (source == advertised, so the admission
    scope at consensus.rs:1912-1944 already passes) validates, an honest node
    confirms [confirmed_0(p3) = V1], and the safety conjunct's
    [K_0 signed_binding(V1, p3)] is false with no provisioning escape -
    refuted. No sibling admission path re-checks the signature (the scope
    disjunct is independently satisfied), so the deletion is a genuine
    refuter, not a no-op silently repaired downstream. The pristine row is
    the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Identity_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Identity_model.Checker.make (Identity_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Identity_statements.name name))
    Identity_statements.all

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
               (Identity_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine
    model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Identity_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Identity_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "identity_mutation"
    [
      ( "dropped signature gate kills confirmed-identity knowledge",
        pin Identity_model.Drop_record_verify
          "confirmed-identity-implies-known-signed-binding" );
    ]
