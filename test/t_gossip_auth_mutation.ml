(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    GOSSIP-AUTH family: the statement is pinned by
    {!Gossip_auth_model.Drop_publisher_auth}, which deletes exactly the
    authorized-publisher containment arm inside verify_gossip
    (crates/network-libp2p/src/consensus.rs:1504-1508) that the statement
    depends on, and the mutated row asserts the proof FLIPS to an error: the
    outsider's validly-signed [C'] then passes every remaining check and is
    delivered, so [delivered_i(C')] becomes reachable at states where no
    committee member ever published [C'], refuting the outsider-rejection
    conjunct. No sibling path repairs the deletion:
    {!Gossip_auth_model.deliver_c_prime} is the unique writer of the
    [delivered_c_prime] bits, the bits are monotone, and there is no second
    committee-containment check behind the deleted one. The pristine row is
    the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Gossip_auth_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Gossip_auth_model.Checker.make (Gossip_auth_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Gossip_auth_statements.name name))
    Gossip_auth_statements.all

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
               (Gossip_auth_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine
    model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Gossip_auth_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Gossip_auth_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "gossip_auth_mutation"
    [
      ( "dropped authorized-publisher containment kills accepted-gossip \
         knowledge",
        pin Gossip_auth_model.Drop_publisher_auth
          "accepted-gossip-implies-known-committee-publisher" );
    ]
