(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    ADMISSION family: BOTH statements are pinned by the single shared gate
    {!Admission_model.No_admission_denial}, which deletes exactly the
    [peer_banned] admission denial (manager.rs:403, behavior.rs:102-105 analog)
    they depend on. Each row asserts the proof FLIPS to an error on the mutated
    model: the deletion adds the (Down,Banned) -> (Up,Banned) retry on every
    pair, so a connection re-forms while the ban is still active. On (V1 -> O)
    that satisfies the inner [Eu] of #4's severance conjunct A (refuting #4); on
    (V2 -> V1) it yields an admitted-while-banned state (refuting #7). The ban=none
    guard is the sole gate on the retry, so no sibling path repairs the deletion,
    and #4's opacity conjunct B is untouched, keeping #4's refutation cleanly
    attributable. The pristine rows are the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Admission_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Admission_model.Checker.make (Admission_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Admission_statements.name name))
    Admission_statements.all

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
               (Admission_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Admission_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Admission_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "admission_mutation"
    [
      ( "dropped admission denial kills local-enforcement opacity",
        pin Admission_model.No_admission_denial
          "ban-is-local-enforcement-and-internode-opaque" );
      ( "dropped admission denial kills known-remote-admission",
        pin Admission_model.No_admission_denial
          "established-connection-implies-known-remote-admission" );
    ]
