(** The CERT_BITMAP_QUORUM family (S1, S2 security; S3 safety) proves on the
    pristine {!Cert_bitmap_quorum_model} through [prove_nonvacuous] (so every
    antecedent is also checked reachable), the reachable graph stays in its
    justified band, each gate's forbidden state is unreachable, and the epistemic
    layer is genuinely partial-information.

    The [sanity] group also carries this family's R5 discharge. Two of its cases
    are POSITIVE reachability assertions rather than the usual "the gate forbids
    it" negatives:

    - an inquorate certificate really does reach [VerifiedIndirectly] pristine,
      because [mark_verified_indirectly] (cert_validator.rs:317-323) runs no
      check at all on a fetched non-leaf certificate. S1 and S2 are scoped to
      DIRECT verification for exactly that reason, and the counterexample is
      visible in the model rather than omitted from it;
    - a round-0 certificate can never take the indirect route, because
      [requires_direct_verification] (cert_validator.rs:303-312) forces direct
      work whenever the round is a multiple of
      [certificate_verification_round_interval] = 50 (network.rs:250, :267) and 0
      is a multiple of 50. That is what stops the indirect stamp from repairing
      the S3 gate deletion.

    The [contingency] group is where R2 and R3 are discharged: both positive K
    operands are shown contingent and their view classes shown non-singleton, and
    every ignorance conjunct gets a two-directional witness. *)

open Telcoin_epistemic
open Cert_bitmap_quorum_model

(** Build the pristine system or fail the test on an impossible [Empty_init]. *)
let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Checker.Empty_init -> Alcotest.fail "make: empty init")
    (make ())

(** Render a proof error for the assertion message. *)
let error_to_string = function
  | Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Checker.Vacuous_antecedent -> "vacuous antecedent"

(** One proof case: the statement proves on the pristine model. *)
let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Cert_bitmap_quorum_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Cert_bitmap_quorum_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Cert_bitmap_quorum_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The operative state of S1 and S2: the ingress ran the real gate set of
    certificate.rs:243-248 (or its [verify_cert] twin at :257-263) and passed. *)
let verified_directly = f Verified_directly

(** The operative state of S1: a directly verified certificate at a positive
    round. *)
let positive_round_cert_verified =
  Formula.And (verified_directly, Formula.Not (f Round_zero))

(** The operative state of S2: a directly verified, positive-round certificate
    whose bitmap credits a quorum. *)
let quorum_cert_verified =
  Formula.And
    (verified_directly, Formula.And (f Credits_quorum, Formula.Not (f Round_zero)))

(* Loose product bound: one offer life of three stages over 9 offer classes and
   3 ingress routes, minus the round-0 x Fetch_indirect pairs the real
   classifier cannot produce (cert_validator.rs:303-312), so at most
   1 + 22 + 22 states. The pristine reachable count is exactly 45. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 55))

(* S1's gate contract: the bitmap resolves to a set of pairwise distinct
   committee keys (certificate.rs:177-199), that set must reach the threshold
   (certificate.rs:246, or :261 on the gossip path) and the aggregate must
   verify against exactly those keys (certificate.rs:284-286). So a directly
   verified certificate behind which fewer than three distinct members signed is
   UNREACHABLE pristine. No_weight_threshold makes it reachable. *)
let direct_verification_implies_three_signers () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (verified_directly(v,c) /\\ ~exists 3 distinct signers)" false
        (Checker.satisfiable sys
           (Formula.And
              (verified_directly, Formula.Not (f Three_distinct_signers)))))

(* S2's gate contract: the key list handed to verify_secure is DERIVED from the
   bitmap (certificate.rs:243 -> :248 -> :284-286), so a directly verified
   certificate crediting a member that did not sign is UNREACHABLE pristine.
   Trust_supplied_signer_set makes it reachable. *)
let direct_verification_implies_faithful_bitmap () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (verified_directly(v,c) /\\ ~bitmap subset_of signers)" false
        (Checker.satisfiable sys
           (Formula.And
              (verified_directly, Formula.Not (f Bitmap_signature_backed)))))

(* S3's gate contract: the round-0 shortcut fires only on the header equality
   test against the locally rebuilt genesis set (certificate.rs:236-238,
   :46-59), so an admission by shortcut of a non-canonical header is
   UNREACHABLE. No_genesis_header_equality removes the admission entirely. *)
let shortcut_only_admits_canonical_headers () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (admitted_by_genesis_shortcut /\\ ~header in genesis set)" false
        (Checker.satisfiable sys
           (Formula.And
              ( f Admitted_by_genesis_shortcut,
                Formula.Not (f Canonical_genesis_header) ))))

(* The sibling-repair refutation for S3, as a reachability fact: a peer that
   sets the wire signature_verification_state to Genesis
   (certificate.rs:446-448), hoping for the free pass at certificate.rs:272-274,
   is admitted on NO route. Both ingress normalisations
   (validate_fetched_certificate, certificate.rs:462-471; validate_received,
   certificate.rs:295-301) and mark_verified_indirectly
   (cert_validator.rs:319-320) call aggregated_signature(), which returns None
   exactly for that variant (certificate.rs:329-337). *)
let claimed_genesis_state_is_never_admitted () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (wire_state(c)=Genesis /\\ admitted on any route)" false
        (Checker.satisfiable sys
           (Formula.And
              ( f Wire_claims_genesis_state,
                Formula.Or
                  ( verified_directly,
                    Formula.Or
                      (f Admitted_by_genesis_shortcut, f Verified_indirectly) )
              ))))

(* R5, first half. The model does NOT pretend every accepted certificate carries
   a quorum: mark_verified_indirectly (cert_validator.rs:317-323) stamps
   VerifiedIndirectly on a fetched non-leaf certificate with no threshold and no
   signature check, so an inquorate certificate really can end up is_verified().
   This is a POSITIVE assertion - it is why S1 and S2 are scoped to direct
   verification, and it makes the scope a stated limit rather than an
   omission. *)
let indirect_verification_carries_no_quorum () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (verified_indirectly(v,c) /\\ ~exists 3 distinct signers)" true
        (Checker.satisfiable sys
           (Formula.And
              (f Verified_indirectly, Formula.Not (f Three_distinct_signers)))))

(* R5, second half - and the reason the S3 pin is not repaired. A round-0
   certificate can never take the indirect route: requires_direct_verification
   (cert_validator.rs:303-312) short-circuits on
   round().is_multiple_of(certificate_verification_round_interval) with the
   interval 50 (network.rs:250, :267), and 0 is a multiple of 50. *)
let round_zero_never_verified_indirectly () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (round(c)=0 /\\ verified_indirectly)" false
        (Checker.satisfiable sys
           (Formula.And (f Round_zero, f Verified_indirectly))))

(* R2 for S1, first half. The knowledge operand is contingent: somewhere
   reachable V0 does NOT know that three distinct members signed, so the K is
   not collapsed into plain truth under V0's partition. *)
let k_triple_signing_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v0(exists 3 distinct signers): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f Three_distinct_signers)))))

(* R2 for S1 and S2, second half - the NON-SINGLETON VIEW CLASS test, shared by
   both positive K operands because both sit at the same operative state. At a
   directly verified quorum certificate pick [all 4 signed], which is false at
   Quorum_faithful, and assert V0 does not know its negation there. That can
   only hold if a second reachable state shares V0's view - here
   Quorum_dropped_vote, the byte-identical certificate whose fourth vote the
   assembler discarded at aggregators/votes.rs:89. A singleton class would make
   this false and fail the test, which is the point. *)
let k_class_at_verified_quorum_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (verified_directly /\\ quorum bitmap /\\ ~round 0 /\\ \
         ~K_v0(~all 4 signed)): the V0 class is not a singleton"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( quorum_cert_verified,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f All_four_signed))) ))))

(* R2 for S1, second half at S1's OWN operative shape (the test above is stated
   at S2's strictly narrower one). At a directly verified positive-round
   certificate V0 does not know that not all four members signed, so the class
   behind K_v0(exists 3 distinct signers) has at least two members everywhere
   S1 asserts it. *)
let k_class_at_s1_operative_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (verified_directly /\\ ~round 0 /\\ ~K_v0(~all 4 signed)): S1's \
         class is not a singleton"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( positive_round_cert_verified,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f All_four_signed))) ))))

(* R2 for S2, first half. The bitmap-faithfulness operand is contingent too: at
   an offered but not yet dispositioned certificate, V0 cannot tell a padded
   bitmap from a faithful one, because that is precisely what the aggregate
   check at certificate.rs:284-286 has not yet run. *)
let k_faithful_bitmap_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v0(bitmap subset_of signers): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f Bitmap_signature_backed)))))

(* R3 for S2's omission conjunct, direction one: at a directly verified quorum
   certificate whose bitmap really does name every signer, V0 cannot confirm it
   - Quorum_dropped_vote is reachable and view-identical. *)
let ignorance_no_uncredited_signer_holds () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (verified quorum cert /\\ signers subset_of bitmap /\\ \
         ~K_v0(signers subset_of bitmap))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( quorum_cert_verified,
                Formula.And
                  ( f No_uncredited_signer,
                    Formula.Not (Formula.K (Validator.V0, f No_uncredited_signer))
                  ) ))))

(* R3 for S2's omission conjunct, direction two: at a certificate whose fourth
   voter the assembler dropped (aggregators/votes.rs:65-89), V0 cannot detect
   the omission either. *)
let ignorance_no_uncredited_signer_fails () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (verified quorum cert /\\ ~signers subset_of bitmap /\\ \
         ~K_v0(~signers subset_of bitmap))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( quorum_cert_verified,
                Formula.And
                  ( Formula.Not (f No_uncredited_signer),
                    Formula.Not
                      (Formula.K
                         (Validator.V0, Formula.Not (f No_uncredited_signer))) )
              ))))

(* R3 for S3's ignorance conjunct, direction one: a round-0 certificate admitted
   by the shortcut whose attached bitmap IS signature-backed - V0 still cannot
   confirm it, because certificate.rs:236-238 returned Ok before :243-248 ever
   looked at the signature material. *)
let ignorance_shortcut_bitmap_backed () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (admitted_by_genesis_shortcut /\\ bitmap subset_of signers /\\ \
         ~K_v0(bitmap subset_of signers))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Admitted_by_genesis_shortcut,
                Formula.And
                  ( f Bitmap_signature_backed,
                    Formula.Not
                      (Formula.K (Validator.V0, f Bitmap_signature_backed)) ) ))))

(* R3 for S3's ignorance conjunct, direction two: the same header with a
   fabricated bitmap and arbitrary aggregate bytes is admitted identically, and
   V0 cannot detect that either. impl PartialEq for Certificate
   (certificate.rs:495-502) compares neither field. *)
let ignorance_shortcut_bitmap_fabricated () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (admitted_by_genesis_shortcut /\\ ~bitmap subset_of signers /\\ \
         ~K_v0(~bitmap subset_of signers))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Admitted_by_genesis_shortcut,
                Formula.And
                  ( Formula.Not (f Bitmap_signature_backed),
                    Formula.Not
                      (Formula.K
                         (Validator.V0, Formula.Not (f Bitmap_signature_backed)))
                  ) ))))

let () =
  Alcotest.run "cert_bitmap_quorum"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Cert_bitmap_quorum_statements.name `Quick
              (prove_one st))
          Cert_bitmap_quorum_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "direct-verification-implies-three-signers" `Quick
            direct_verification_implies_three_signers;
          Alcotest.test_case "direct-verification-implies-faithful-bitmap" `Quick
            direct_verification_implies_faithful_bitmap;
          Alcotest.test_case "shortcut-only-admits-canonical-headers" `Quick
            shortcut_only_admits_canonical_headers;
          Alcotest.test_case "claimed-genesis-state-is-never-admitted" `Quick
            claimed_genesis_state_is_never_admitted;
          Alcotest.test_case "indirect-verification-carries-no-quorum" `Quick
            indirect_verification_carries_no_quorum;
          Alcotest.test_case "round-zero-never-verified-indirectly" `Quick
            round_zero_never_verified_indirectly;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-triple-signing-contingent" `Quick
            k_triple_signing_contingent;
          Alcotest.test_case "k-class-at-verified-quorum-not-singleton" `Quick
            k_class_at_verified_quorum_not_singleton;
          Alcotest.test_case "k-class-at-s1-operative-not-singleton" `Quick
            k_class_at_s1_operative_not_singleton;
          Alcotest.test_case "k-faithful-bitmap-contingent" `Quick
            k_faithful_bitmap_contingent;
          Alcotest.test_case "ignorance-no-uncredited-signer-holds" `Quick
            ignorance_no_uncredited_signer_holds;
          Alcotest.test_case "ignorance-no-uncredited-signer-fails" `Quick
            ignorance_no_uncredited_signer_fails;
          Alcotest.test_case "ignorance-shortcut-bitmap-backed" `Quick
            ignorance_shortcut_bitmap_backed;
          Alcotest.test_case "ignorance-shortcut-bitmap-fabricated" `Quick
            ignorance_shortcut_bitmap_fabricated;
        ] );
    ]
