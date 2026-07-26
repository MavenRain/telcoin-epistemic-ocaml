(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]): the
    EXEC-TALLY statement is pinned by [Weak_sig_threshold], which deletes
    exactly the [sigs >= enough_sigs] advance gate (handler.rs:410) the
    statement depends on, and the mutated row asserts the proof FLIPS to an
    error: the observer's watch advances on V3's lone fabricated signature
    before any honest CVV saved the output. The pristine row is the
    matching positive half. *)

open Telcoin_epistemic

let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Exec_tally_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Exec_tally_model.Checker.make (Exec_tally_model.spec_of mut))

let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Exec_tally_statements.name name))
    Exec_tally_statements.all

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
               (Exec_tally_statements.prove sys st)))

let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Exec_tally_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Exec_tally_statements.prove sys st)))

let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "exec_tally_mutation"
    [
      ( "weak signature threshold kills the tally-grounded knowledge",
        pin Exec_tally_model.Weak_sig_threshold
          "consensus-output-gossip-tally-implies-known-honest-save" );
    ]
