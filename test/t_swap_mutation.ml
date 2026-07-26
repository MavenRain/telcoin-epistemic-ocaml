(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    leader-swap family: the statement is pinned by deleting exactly the
    shared draw seed it depends on (leader_schedule.rs:211-213), and the
    paired row asserts the proof FLIPS to an error on the mutated model -
    under {!Swap_model.No_shared_seed} each validator's replacement draw
    becomes an independent hidden choice, so the divergent resolution
    [Draws_split] (V1's table draws V2 where V0/V2 draw [a_good]) reaches
    Done alongside [Draws_shared]. Two Done states then share every honest
    view (all locals committed-and-executed) while their operands disagree,
    so common knowledge of schedule agreement fails and the leads-to
    conjunct is refuted. No sibling path repairs the deletion: Done is
    terminal, so no later step revisits the draw. The pristine rows in
    t_swap are the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Swap_model.Checker.Empty_init -> Alcotest.fail "make: empty init")
    (Swap_model.Checker.make (Swap_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Swap_statements.name name))
    Swap_statements.all

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
               (Swap_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine
    model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Swap_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Swap_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "swap_mutation"
    [
      ( "dropped shared seed kills leader-swap agreement",
        pin Swap_model.No_shared_seed
          "leader-swap-schedule-agreement-from-committed-scores" );
    ]
