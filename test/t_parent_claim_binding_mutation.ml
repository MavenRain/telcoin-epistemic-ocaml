(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    PARENT_CLAIM_BINDING family. Each row asserts the statement PROVES on the
    pristine model and FLIPS to an error on the mutated one, so no pin can
    pass on the strength of some other statement having moved.

    The four gate deletions, and the sibling-repair hunt behind each:

    - {!Parent_claim_binding_model.No_requester_binding} deletes the
      [authority == header.author()] comparison of
      [try_accept_unknown_certs] (handler.rs:940-944). S1's binding conjunct
      is refuted at the new [Ph_b_offer_taken] state, where a certificate
      offered by [b] is admitted although the slot names [a]. The BLS/quorum
      check of [Certificate::validate_and_verify]
      (types/src/primary/certificate.rs:225-251) is the obvious sibling and it
      IS in the model - forged bytes still never reach [Ph_stored] - so it
      repairs forgery and not the binding, which is exactly why S1 is stated
      as a request-binding invariant. S1's antecedent stays reachable under
      the mutation, so this is a refutation and not a vacuity flip.
    - {!Parent_claim_binding_model.No_vacant_claim} replaces the
      [Entry::Vacant] claim (handler.rs:915-920) with an unconditional
      insert-and-keep. S2's exclusivity conjunct is refuted because
      [Ph_a_hinted]'s successor becomes [Ph_b_hinted], at which [j]'s reply to
      [b] names [d]. No sibling: [try_accept_unknown_certs] consults the SAME
      table (so the rebound slot hands [b] the admission and starts dropping
      [a]'s own supply), the pending suppression at
      pending_cert_manager.rs:171-173 covers only locally pending digests, and
      the certificate fetcher is fired only by a processed CERTIFICATE
      (cert_manager.rs:169-177) or a TooNew one (cert_validator.rs:201-204),
      never by a header.
    - {!Parent_claim_binding_model.No_evaluation_deadline} deletes BOTH
      wall-clock bounds on a blocked evaluation - the [max_header_delay]
      timeout at handler.rs:582-586 AND the [cancel] arm of the spawned vote
      task at network/mod.rs:1531-1551. S2's until conjunct is then refuted in
      the two worlds where [d] does not exist: [Ph_b_filtered] becomes
      terminal and the kernel stutters it forever. Both sites must go
      together, because either one alone repairs the other; nothing else
      bounds the wait, [notify_read]
      (storage/src/stores/certificate_store.rs:250-269) being a bare
      [receiver.await].
    - {!Parent_claim_binding_model.No_author_parent_filter} deletes the
      [.filter(|parent| header.parents().contains(parent))] at
      certifier.rs:150-151. S3 is refuted at exactly ONE of the six initial
      states, the author holding the undeclared certificate: the count check
      at certifier.rs:157-165 is a real sibling, it is modeled, and it still
      aborts the lean-store run. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Parent_claim_binding_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Parent_claim_binding_model.Checker.make
       (Parent_claim_binding_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Parent_claim_binding_statements.name name))
    Parent_claim_binding_statements.all

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
               (Parent_claim_binding_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Parent_claim_binding_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Parent_claim_binding_statements.prove sys st)))

(** The pin is a REFUTATION and not a vacuity artefact: the statement's
    antecedent is still reachable on the mutated model, so
    [prove_nonvacuous] failed on the formula rather than on the guard. *)
let antecedent_still_reachable mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " antecedent stays reachable under the mutation") true
            (Parent_claim_binding_model.Checker.satisfiable sys
               st.Parent_claim_binding_statements.antecedent))

(** A pristine-proves plus mutated-refutes pair for one statement, with the
    non-vacuity guard that makes the negative half meaningful. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
    Alcotest.test_case (name ^ ":antecedent-live") `Quick
      (antecedent_still_reachable mut name);
  ]

let () =
  Alcotest.run "parent_claim_binding_mutation"
    [
      ( "dropped requester binding admits an unrequested certificate",
        pin Parent_claim_binding_model.No_requester_binding
          "vote-path-certificate-admission-is-bound-to-the-requested-author" );
      ( "dropped Vacant claim tells the second proposer too",
        pin Parent_claim_binding_model.No_vacant_claim
          "a-missing-parent-is-claimed-by-exactly-one-proposer" );
      ( "dropped evaluation deadline unbounds the blocked window",
        pin Parent_claim_binding_model.No_evaluation_deadline
          "a-missing-parent-is-claimed-by-exactly-one-proposer" );
      ( "dropped author parent filter discloses an undeclared certificate",
        pin Parent_claim_binding_model.No_author_parent_filter
          "the-author-serves-only-its-own-declared-parents" );
    ]
