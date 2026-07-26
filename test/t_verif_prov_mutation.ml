(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    VERIF_PROV family: three gates on one catch-up certificate-FETCH ingress,
    each deleted independently, each flipping the statements that actually rest
    on it. Every row asserts the proof FLIPS to an error on the mutated model,
    with the matching pristine row as the positive half.

    {!Verif_prov_model.No_wire_tag_reset} deletes the ingress tag reset inside
    [validate_fetched_certificate] (certificate.rs:465-469, sole call site
    certificate_fetcher.rs:494-505) AND its twin in [validate_received]
    (:295-301), so the gossip ingress cannot be claimed as a repair; a
    peer-asserted [VerifiedDirectly] then short-circuits [verify_signature] at
    certificate.rs:271-274 and a forged batch is stored in full. No sibling
    repairs it: the [signed_by] weight test counts bits of the peer-supplied
    bitmap (:27-38, :243-246), [Header::validate] checks no signature,
    cert_manager's [is_verified] is exactly what [VerifiedDirectly] satisfies
    (:356-364), the genesis short-circuit needs round 0, and nothing downstream
    of the certificate store ever re-verifies. Pins S1 and S2.

    {!Verif_prov_model.No_leaf_direct_verification} deletes the
    [!all_parents.contains(&cert.digest())] disjunct at cert_validator.rs:308, so
    classify stamps BOTH members [VerifiedIndirectly] and the chunk returns
    [Ok(vec![])] without spawning a task - a wholly fabricated batch is stored
    with zero cryptography. Its one genuine sibling, the periodic disjunct at
    :309-311, IS modelled: the default interval is 50 (network.rs:250-268) and
    the batch is scoped to rounds 1 and 2, exactly where the real code leaves it
    inert. Pins S1 and S2.

    {!Verif_prov_model.No_chunk_abort} deletes the collection-wide error
    propagation (`?` at cert_validator.rs:260, `??` at :336-341,
    [validate_and_verify(cert)?] at :356-361), so a failed leaf no longer
    discards the response. Its sibling is real, partial and modelled:
    cert_manager's [if !cert.is_verified()] (:85-93, "NOTE: this is the only time
    this is checked") stops the still-[Unverified] leaf D but NOT the parent C,
    because [VerifiedIndirectly] satisfies [is_verified] (certificate.rs:356-364)
    - which is why the mutated store is [St_c] and not [St_cd]. Pins all three.

    Attribution is clean throughout: the surviving conjuncts of each statement
    (S1's mark-before-evidence window and reset-neutralises witnesses, S2's
    anonymity, S3's stamp-conveys-nothing) were checked to remain valid under
    every mutation, and every statement's antecedent stays reachable under every
    mutation, so no flip here is a masked [Vacuous_antecedent]. S3 in particular
    is deliberately left PROVED by the other two gates - its antecedent is a
    disjunction precisely so that {!Verif_prov_model.No_leaf_direct_verification},
    which makes a failed check unreachable, cannot manufacture a fake refutation. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Verif_prov_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Verif_prov_model.Checker.make (Verif_prov_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Verif_prov_statements.name name))
    Verif_prov_statements.all

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
               (Verif_prov_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Verif_prov_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Verif_prov_statements.prove sys st)))

(** A statement the mutation deliberately leaves alone: it must still PROVE on
    the mutated model. This is the anti-over-claiming half of the pin table - it
    is what stops a mutation from being credited with a refutation it did not
    cause, and it is what proves S3's antecedent disjunction is doing real work
    rather than hiding a [Vacuous_antecedent]. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " still proves under the unrelated mutation")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Verif_prov_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "verif_prov_mutation"
    [
      ( "dropped ingress tag reset kills the storage weak-until",
        pin Verif_prov_model.No_wire_tag_reset
          "fetched-parent-never-stored-before-dependent-signature-check" );
      ( "dropped ingress tag reset kills the inherited quorum",
        pin Verif_prov_model.No_wire_tag_reset
          "indirectly-verified-parent-carries-known-but-anonymous-quorum" );
      ( "dropped leaf direct verification kills the storage weak-until",
        pin Verif_prov_model.No_leaf_direct_verification
          "fetched-parent-never-stored-before-dependent-signature-check" );
      ( "dropped leaf direct verification kills the inherited quorum",
        pin Verif_prov_model.No_leaf_direct_verification
          "indirectly-verified-parent-carries-known-but-anonymous-quorum" );
      ( "dropped chunk abort kills the storage weak-until",
        pin Verif_prov_model.No_chunk_abort
          "fetched-parent-never-stored-before-dependent-signature-check" );
      ( "dropped chunk abort kills the inherited quorum",
        pin Verif_prov_model.No_chunk_abort
          "indirectly-verified-parent-carries-known-but-anonymous-quorum" );
      ( "dropped chunk abort kills the failed-dependent quarantine",
        pin Verif_prov_model.No_chunk_abort
          "failed-dependent-quarantines-the-pre-marked-batch" );
      ( "the quarantine survives the two gates it does not rest on",
        [
          Alcotest.test_case "quarantine:survives-no-wire-tag-reset" `Quick
            (survives_under Verif_prov_model.No_wire_tag_reset
               "failed-dependent-quarantines-the-pre-marked-batch");
          Alcotest.test_case "quarantine:survives-no-leaf-direct-verification"
            `Quick
            (survives_under Verif_prov_model.No_leaf_direct_verification
               "failed-dependent-quarantines-the-pre-marked-batch");
        ] );
    ]
