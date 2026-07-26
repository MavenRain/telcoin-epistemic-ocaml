(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    ahead-certificate catch-up family: the statement is pinned by
    {!Catchup_model.Drop_catch_up}, which deletes exactly the [Catch_up]
    round jump it depends on (the model analog of removing the
    [minimal_round_for_parents] send, cert_validator.rs:157-158), and the
    mutated row asserts the proof FLIPS to an error - under the mutation the
    terminal [Done] state is reached with [Proposer_round_le (V2, R0)] still
    true while V2 holds an R2 certificate, so the catch-up leads-to - now
    the whole statement - is refuted. No sibling path repairs the deletion:
    [propose] never lists
    the lagging V2 after R0 and never runs again after [Deliver R2] (the real
    system's only other parents sender, the certificate aggregator
    aggregators/certificates.rs:24-44, needs a 2f+1 same-round quorum the
    starved node cannot assemble). The pristine row is the matching positive
    half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail on an impossible [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Catchup_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Catchup_model.Checker.make (Catchup_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Catchup_statements.name name))
    Catchup_statements.all

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
               (Catchup_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Catchup_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Catchup_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "catchup_mutation"
    [
      ( "dropped catch-up step kills the round-catchup leads-to",
        pin Catchup_model.Drop_catch_up
          "ahead-certificate-implies-round-catchup" );
    ]
