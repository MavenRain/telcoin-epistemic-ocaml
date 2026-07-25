(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]): every
    statement is pinned by a model mutation that deletes exactly the gate
    the statement depends on, and the paired row asserts the proof FLIPS to
    an error on the mutated model. A statement that stayed green under its
    gate's deletion would be vacuous. The pristine rows in t_statements are
    the matching positive half. *)

open Telcoin_epistemic

let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Tn_model.Checker.Empty_init -> Alcotest.fail "make: empty init")
    (Tn_model.Checker.make (Tn_model.spec_of mut))

let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Statements.name name))
    Statements.all

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
               (Statements.prove sys st)))

let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Tn_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Statements.prove sys st)))

let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "tn_mutation"
    [
      ( "weak-quorum kills cert uniqueness",
        pin Tn_model.Weak_quorum
          "stored-cert-implies-known-quorum-and-slot-uniqueness" );
      ( "dropped batch gate kills vote attestation",
        pin Tn_model.Drop_batch_gate "vote-attests-known-parents-and-payload" );
      ( "dropped vote-once kills the revote discipline",
        pin Tn_model.No_vote_once
          "no-conflicting-revote-and-equivocation-detectability" );
      ( "dropped support check kills commit soundness",
        pin Tn_model.No_support_check "commit-implies-known-support-quorum" );
      ( "unbounded delay kills knowledge propagation",
        pin Tn_model.Unbounded_delay "rounds-advance-under-known-distinct-quorum" );
      ( "leader censorship kills inclusion fairness",
        pin Tn_model.Leader_censors_v2
          "round-robin-leader-common-knowledge-and-slot-fairness" );
      ( "dropped batch gate kills availability",
        pin Tn_model.Drop_batch_gate "quorum-ack-implies-honest-batch-availability" );
    ]
