(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the ban
    family: each statement is pinned by deleting exactly the one code gate it
    depends on, and the paired row asserts the proof FLIPS to an error on the
    mutated model.

    S2 ([content-fault-ban-requires-known-author]) is pinned by
    {!Ban_model.Charge_relayer}, which deletes the is_author_content_fault
    selection (network mod.rs:1803): the fatal charge lands on the honest
    relayer of the invalid gossip instead of its unforgeable author, so a
    reachable state bans honest V1 where authored-bad(V1) is false and both
    conjuncts flip. No sibling path repairs it - the honest relayers are
    modeled non-exempt (committee-slot seeding-lag window), so author routing
    is their sole protection.

    S5 ([committee-exemption-liveness-known-but-unbannable-byzantine]) is
    pinned by {!Ban_model.No_exemption}, which deletes the TrustBasis
    short-circuit (peer.rs:218-231): the Fatal penalty now reaches the ban step
    for the committee member V3, so every evidence-holding honest node bans V3
    in the broadcast branch and conjunct 1 (~banned_i(V3)) is refuted while
    AF done survives on the 3-honest quorum. The pristine rows in t_ban are the
    matching positive halves. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Ban_model.Checker.Empty_init -> Alcotest.fail "make: empty init")
    (Ban_model.Checker.make (Ban_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Ban_statements.name name))
    Ban_statements.all

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
               (Ban_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Ban_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Ban_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "ban_mutation"
    [
      ( "relayer charge kills content-fault-ban-requires-known-author",
        pin Ban_model.Charge_relayer "content-fault-ban-requires-known-author" );
      ( "dropped committee exemption kills the unbannable-byzantine liveness",
        pin Ban_model.No_exemption
          "committee-exemption-liveness-known-but-unbannable-byzantine" );
    ]
