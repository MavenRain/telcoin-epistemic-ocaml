(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    reqres family: the statement is pinned by [No_digest_gate], which
    deletes exactly the requester-side digest-verification reject
    (state-sync consensus.rs:84-87) the statement depends on, and the
    mutated row asserts the proof FLIPS to an error - a [Fabricate] V3
    payload then caches like a valid one, so [verified-from-v3 /\
    ~held-v3] is reachable and conjuncts 1 and 2 are refuted. No sibling
    path repairs the deletion: the responder-side Deny gate
    (sync_codec.rs:320-347) is the honest responder's self-check, which a
    fabricating V3 never runs, and retrying another peer is a separate run,
    so the refuting cached-bogus state is genuinely reachable under the
    mutation. The holds-and-denies [Withhold] branch cannot repair it
    either: its Denied frame takes the mutation-independent Denied arm of
    [verify], never the gated Bogus arm. The pristine row in t_reqres is
    the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Reqres_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Reqres_model.Checker.make (Reqres_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Reqres_statements.name name))
    Reqres_statements.all

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
               (Reqres_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine
    model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Reqres_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Reqres_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "reqres_mutation"
    [
      ( "dropped digest gate kills verified-response-known-possession",
        pin Reqres_model.No_digest_gate
          "verified-response-implies-known-responder-possession" );
    ]
