(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    prefetch family: the statement is pinned by deleting exactly the
    content-addressed keying it depends on - fetched batches keyed by the
    GOSSIPED digest instead of the recomputed one
    (crates/consensus/worker/src/network/handle.rs:509,523) - and the
    paired row asserts the proof FLIPS to an error on the mutated model:
    under {!Prefetch_model.No_content_addressing} V1 stores a Byzantine
    bogus payload under key b in the [Forge_digest] branch and so comes to
    hold b with no real holder, a state view-identical to the Cooperate
    faithful-hold, so [K (V1, Held_by_other)] collapses to false and the
    verified-fetch knowledge conjunct is refuted. No sibling path repairs
    THIS deletion: nothing downstream recomputes the digest, so the
    requested-digests filter (handle.rs:241-244) and the keyed store insert
    (handler.rs:201-202) consume the mutated key unchanged. (Deleting only
    the digest-binding stream abort at handle.rs:512-516 would be silently
    repaired by exactly those two paths.) The pristine rows in t_prefetch
    are the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Prefetch_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Prefetch_model.Checker.make (Prefetch_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Prefetch_statements.name name))
    Prefetch_statements.all

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
               (Prefetch_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine
    model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Prefetch_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Prefetch_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "prefetch_mutation"
    [
      ( "dropped content-addressing kills verified-fetch knowledge",
        pin Prefetch_model.No_content_addressing
          "batch-digest-gossip-prefetch-knowledge-via-verified-fetch" );
    ]
