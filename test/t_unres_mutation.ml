(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    UNRESOLVED-AUTHOR family: the statement is pinned by deleting exactly the
    author_resolved guard it depends on (consensus.rs:2094-2095), and the
    paired row asserts the proof FLIPS to an error on the mutated model. Under
    {!Unres_model.No_author_resolved_guard} the unresolved-author reject
    unconditionally Fatal-charges its propagation source: in the lag branch
    honest V1 is banned at V2 (peers/all_peers.rs:853-873), so [Banned_2 V1]
    and [Penalized_by_2] fire at a [saw_unres_2] state - an UNJUST charge of a
    peer V2 cannot attribute the frame to - which refutes the statement
    through its no-ban / no-penalty (Skip) conjuncts. Liveness is NOT the
    refuting lever: the vote-time recovery is proposer-sourced (the
    MissingParents flow, handler.rs:653-668), so a ban on the certificate's
    author does not block a third party from supplying it and V2 still
    reassembles the 2f+1 = 3 quorum - [Af done] holds on the mutated system,
    asserted separately by {!mutated_liveness_survives}. So the pin flips for
    the honest reason (the unjust ban/penalty), not a manufactured starvation.
    The pristine rows in t_unres are the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Unres_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Unres_model.Checker.make (Unres_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Unres_statements.name name))
    Unres_statements.all

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
               (Unres_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Unres_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Unres_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** Liveness survives the unjust ban: even under [No_author_resolved_guard],
    the proposer-sourced fetch reassembles the quorum, so [Af done] holds on
    the mutated system - the manufactured-starvation refutation is gone. *)
let mutated_liveness_survives () =
  with_mut Unres_model.No_author_resolved_guard (fun sys ->
      Alcotest.(check bool) "Af done valid on the mutated system" true
        (Unres_model.Checker.valid sys
           (Formula.Af (Formula.Atom Unres_model.At_done))))

let () =
  Alcotest.run "unres_mutation"
    [
      ( "dropped author_resolved guard unjustly bans and penalizes honest V1",
        pin Unres_model.No_author_resolved_guard
          "unresolved-author-reject-skips-penalty-and-liveness-recovers" );
      ( "liveness survives",
        [
          Alcotest.test_case "mutated-liveness-survives" `Quick
            mutated_liveness_survives;
        ] );
    ]
