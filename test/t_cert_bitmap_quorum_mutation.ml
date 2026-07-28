(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    CERT_BITMAP_QUORUM family. Each statement is pinned by its own gate deletion,
    and the [attribution] group records which statements each deletion leaves
    standing, so no pin can pass on the strength of some other statement
    flipping.

    - {!Cert_bitmap_quorum_model.No_weight_threshold} deletes
      [ensure!(weight >= threshold, CertificateError::Inquorate { .. })] at
      crates/types/src/primary/certificate.rs:246 - the [validate_and_verify]
      copy, and only that copy. A certificate crediting ONE member whose single
      signature verifies honestly is then directly verified on the
      certificate-fetcher path, refuting S1's known-distinct-triple conjunct. The
      two candidate repairs are carried by the model and neither closes it:
      [verify_secure]'s [if pks.is_empty() { return false; }]
      (crates/types/src/crypto/bls_signature.rs:274-276) still rejects the
      ZERO-credit offers but says nothing about one key, and [verify_cert]'s
      independent threshold at certificate.rs:261 over the free
      [quorum_threshold(committee.len() as u64)] (committee.rs:686-688) is
      reachable only from the gossip ingress (handler.rs:252), which this
      mutation leaves intact - so the SAME inquorate certificate arriving by
      gossip is still rejected. The deletion is therefore honestly scoped to the
      fetcher path and the model carries both routes as distinct transitions.
    - {!Cert_bitmap_quorum_model.Trust_supplied_signer_set} replaces the
      bitmap-derived key list threaded from [self.signed_by(&committee.bls_keys())]
      (certificate.rs:243, :257) into [self.verify_signature(pks)?]
      (certificate.rs:248, :263) with a caller-supplied signer list, so
      [verify_secure(&to_intent_message(certificate_digest), &pks[..])]
      (certificate.rs:284-286) no longer binds the bitmap to the signature. A
      relayer's padded bitmap then survives verification, refuting S2's
      credited-set-authentic conjunct. No sibling repairs it: [verify_cert]
      routes to the SAME [verify_signature] body, so the deletion applies on both
      gated routes, and [Certificate::signed_authorities()]
      (certificate.rs:352-354) has no consumer outside crates/types that could
      cross-check the set.
    - {!Cert_bitmap_quorum_model.No_genesis_header_equality} deletes the round-0
      shortcut [if self.round() == 0 && Self::genesis(committee).contains(self) {
      return Ok(()); }] at certificate.rs:236-238. A canonical genesis
      certificate offered by a peer then falls through to certificate.rs:241 and
      :246, where its empty bitmap resolves to weight 0 and is rejected as
      [Inquorate], refuting S3's liveness conjunct at a still-reachable
      antecedent. The three candidate repairs are all carried by the model:
      local seeding via [Certificate::genesis] (proposer.rs:145,
      crates/config/src/consensus.rs:144) filters no ingress; a wire-claimed
      [SignatureVerificationState::Genesis] dies at both normalisations
      (certificate.rs:462-471, :295-301, via :329-337) and is modeled as
      {!Cert_bitmap_quorum_model.Genesis_state_claim}; and
      [mark_verified_indirectly] (cert_validator.rs:317-323) is unreachable at
      round 0 because [requires_direct_verification] (cert_validator.rs:303-312)
      forces direct work whenever the round is a multiple of
      [certificate_verification_round_interval] = 50 (network.rs:250, :267).

    One overlap, recorded rather than hidden: S1 also flips under
    {!Cert_bitmap_quorum_model.Trust_supplied_signer_set}, because deleting the
    signature/bitmap binding lets a two-signer certificate be credited with three
    and directly verified. That is a true consequence, not a leak - S1's own pin
    is the threshold deletion, under which S2 and S3 both survive - so the
    [attribution] group asserts every surviving pair and simply does not claim
    the one that is false. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Cert_bitmap_quorum_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Cert_bitmap_quorum_model.Checker.make
       (Cert_bitmap_quorum_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Cert_bitmap_quorum_statements.name name))
    Cert_bitmap_quorum_statements.all

(** Does the statement prove under this mutation? *)
let holds_under mut name k =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          k
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Cert_bitmap_quorum_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  holds_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " flips to refuted under the mutation")
        false proved)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  holds_under Cert_bitmap_quorum_model.Pristine name (fun proved ->
      Alcotest.(check bool) (name ^ " proves on pristine") true proved)

(** Attribution: an unrelated gate deletion leaves this statement standing, so
    the pin is carried by its own gate and not by collateral damage. *)
let survives_under mut name () =
  holds_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " still proves under the unrelated mutation")
        true proved)

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** Atom injection shorthand for the mechanism cases below. *)
let f a = Formula.Atom a

(** The mutation really deletes the fetcher-path threshold and NOTHING else: an
    inquorate certificate becomes directly verifiable, but only on the
    direct-fetch route. [verify_cert]'s own [ensure!] at certificate.rs:261
    still rejects the same certificate arriving by gossip, which is the sibling
    path the model carries so that the deletion is honestly scoped. *)
let threshold_deletion_is_route_scoped () =
  with_mut Cert_bitmap_quorum_model.No_weight_threshold (fun sys ->
      let open Cert_bitmap_quorum_model in
      Alcotest.(check (pair bool bool))
        "inquorate cert verifies on the fetch route only"
        (true, false)
        ( Checker.satisfiable sys
            (Formula.And
               (f Verified_directly, Formula.Not (f Credits_quorum))),
          Checker.satisfiable sys
            (Formula.And
               ( f Verified_directly,
                 Formula.And
                   ( Formula.Not (f Credits_quorum),
                     Formula.Not (f On_direct_fetch) ) )) ))

(** The genesis-shortcut deletion really removes the admission: no state
    reachable under it is admitted by the shortcut, while the offer that would
    have been admitted is still reachable - so S3 flips by refutation, not by its
    antecedent going vacuous. *)
let shortcut_deletion_removes_admission_not_antecedent () =
  with_mut Cert_bitmap_quorum_model.No_genesis_header_equality (fun sys ->
      let open Cert_bitmap_quorum_model in
      Alcotest.(check (pair bool bool))
        "shortcut admission gone, genesis offer still reachable" (false, true)
        ( Checker.satisfiable sys (f Admitted_by_genesis_shortcut),
          Checker.satisfiable sys
            (Formula.And
               ( f Offer_pending,
                 Formula.And
                   ( f Round_zero,
                     Formula.And
                       ( f Canonical_genesis_header,
                         Formula.And
                           ( f On_direct_fetch,
                             Formula.Not (f Wire_claims_genesis_state) ) ) ) ))
        ))

(** S1's name. *)
let s1_name = "direct-verification-implies-known-distinct-triple-signing"

(** S2's name. *)
let s2_name = "verified-bitmap-is-signature-bound-yet-omission-stays-hidden"

(** S3's name. *)
let s3_name = "round-zero-certificate-is-admitted-on-header-equality-alone"

let () =
  Alcotest.run "cert_bitmap_quorum_mutation"
    [
      ( "dropped fetcher threshold kills known distinct triple signing",
        pin Cert_bitmap_quorum_model.No_weight_threshold s1_name );
      ( "unbound signer set kills bitmap authenticity",
        pin Cert_bitmap_quorum_model.Trust_supplied_signer_set s2_name );
      ( "dropped genesis header equality kills round-zero admission",
        pin Cert_bitmap_quorum_model.No_genesis_header_equality s3_name );
      ( "attribution",
        [
          Alcotest.test_case "s1-survives-no-genesis-header-equality" `Quick
            (survives_under Cert_bitmap_quorum_model.No_genesis_header_equality
               s1_name);
          Alcotest.test_case "s2-survives-no-weight-threshold" `Quick
            (survives_under Cert_bitmap_quorum_model.No_weight_threshold s2_name);
          Alcotest.test_case "s2-survives-no-genesis-header-equality" `Quick
            (survives_under Cert_bitmap_quorum_model.No_genesis_header_equality
               s2_name);
          Alcotest.test_case "s3-survives-no-weight-threshold" `Quick
            (survives_under Cert_bitmap_quorum_model.No_weight_threshold s3_name);
          Alcotest.test_case "s3-survives-trust-supplied-signer-set" `Quick
            (survives_under Cert_bitmap_quorum_model.Trust_supplied_signer_set
               s3_name);
        ] );
      ( "mechanism",
        [
          Alcotest.test_case "threshold-deletion-is-route-scoped" `Quick
            threshold_deletion_is_route_scoped;
          Alcotest.test_case
            "shortcut-deletion-removes-admission-not-antecedent" `Quick
            shortcut_deletion_removes_admission_not_antecedent;
        ] );
    ]
