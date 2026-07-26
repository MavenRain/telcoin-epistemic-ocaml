(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    stall family: the statement is pinned by deleting exactly the timeout
    tick arm of [GarbageCollector::ready] it depends on (the arm whose
    handler sends [CertificateFetcherCommand::Kick], gc.rs:51), and the
    paired row asserts the proof FLIPS to an error on the mutated model.
    Under {!Stall_model.No_timeout_fetch} the [Timeout_fetch] micro-step
    copies nothing, so the LAGGED victim reaches [Done] with its pending
    target unserved and an empty dag: the recovery clause's antecedent
    [stalled_v2 /\ cert_quorum(R1) /\ has_fetch_targets_v2] holds at that
    terminal state, [own_quorum(v2,R1)] never does, and so
    AF own_quorum(v2,R1) fails and the conjunction is refuted (not
    vacuous - both EF triggers of the antecedent stay reachable). The
    ignorance clause is untouched by the mutation: the totally starved
    branch never had a pending target, so its Kick was a no-op in the
    pristine model already (certificate_fetcher.rs:184). No sibling path
    repairs the deletion: both starvation flavors suppress [Deliver R1]
    certificate delivery and [Propose R2] header delivery (so
    fetch-on-vote never fires), and direct [Deliver R2] dag delivery to
    the victim - the forward reference sits in the pending buffer, which
    only the timeout fetch serves. The pristine rows in t_stall are the
    matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Stall_model.Checker.Empty_init -> Alcotest.fail "make: empty init")
    (Stall_model.Checker.make (Stall_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Stall_statements.name name))
    Stall_statements.all

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
               (Stall_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine
    model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Stall_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Stall_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "stall_mutation"
    [
      ( "dropped timeout-fetch strands the lagged victim's pending targets",
        pin Stall_model.No_timeout_fetch
          "stalled-commit-timeout-fetch-gated-by-pending-targets" );
    ]
