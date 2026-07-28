(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    BLS_VERIFY_GATE family. Each of the three statements is pinned by its OWN
    gate deletion, and each gate deletion is checked to leave the other two
    statements proving, so no pin can pass on the strength of some other
    statement flipping.

    - {!Bls_verify_gate_model.Err_on_failed_verify} deletes the two
      [else { return false; }] decode fallbacks at
      crates/tn-reth/src/evm/bls_precompile/mod.rs:145-150 and lets the decoder
      error escape as [PrecompileError::Other]. The undecodable-points class
      then exits [Err] and burns the frame's forwarded gas while a
      wrong-message call still pays the flat 150k, refuting S1's exit and cost
      conjuncts. No sibling repairs it: [dispatch] (mod.rs:102-111) returns the
      handler's result untouched, [bls_precompile] (mod.rs:93-95) only forwards
      [input.data]/[input.gas], and a reverted [STATICCALL] propagates to the
      caller (props :273-321).
    - {!Bls_verify_gate_model.No_length_gate} deletes the 48/96 length pin at
      mod.rs:142-144, so the 96/192 uncompressed serialization of the SAME point
      pair decodes and verifies, refuting S2's canonicity and non-malleability
      conjuncts. The two decoder-level repairs that really exist are modeled and
      survive: a non-serialization length and a flag-clear 96-byte pubkey stay
      rejected because [BlsPublicKey::from_literal_bytes]
      (bls_public_key.rs:99-101) and [BlsSignature::from_bytes]
      (bls_signature.rs:25-29) dispatch on length themselves - mod.rs:135-140
      says precisely which case they do NOT cover.
    - {!Bls_verify_gate_model.No_pk_validation} flips the trailing
      public-key-validation [true] at
      crates/types/src/crypto/bls_signature.rs:195 to [false], so an
      unvalidated / small-subgroup / infinity G2 key with a fabricated signature
      verifies, refuting S3's known-possession conjunct. No sibling repairs it:
      the only caller that validates first
      ([verify_proof_of_possession_bls], bls_signature.rs:171-183 with
      [public_key.validate()] at :176) is the consensus-layer path, and the
      precompile at mod.rs:141-153 never calls it. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Bls_verify_gate_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Bls_verify_gate_model.Checker.make (Bls_verify_gate_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Bls_verify_gate_statements.name name))
    Bls_verify_gate_statements.all

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
               (Bls_verify_gate_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  holds_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " flips to refuted under the mutation")
        false proved)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  holds_under Bls_verify_gate_model.Pristine name (fun proved ->
      Alcotest.(check bool) (name ^ " proves on pristine") true proved)

(** Attribution: an UNRELATED gate deletion leaves this statement standing, so
    each pin is carried by its own gate and not by collateral damage. *)
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

(** S1's name. *)
let s1_name =
  "every-verification-failure-mode-costs-the-same-and-returns-a-value"

(** S2's name. *)
let s2_name = "compressed-encoding-is-the-only-accepted-point-form"

(** S3's name. *)
let s3_name = "accepted-pop-implies-known-key-possession-yet-exclusivity-unknown"

let () =
  Alcotest.run "bls_verify_gate_mutation"
    [
      ( "decode failure escapes as Err kills uniform cost",
        pin Bls_verify_gate_model.Err_on_failed_verify s1_name );
      ( "dropped 48/96 length gate kills compressed-only",
        pin Bls_verify_gate_model.No_length_gate s2_name );
      ( "dropped pk validation kills known key possession",
        pin Bls_verify_gate_model.No_pk_validation s3_name );
      ( "attribution",
        [
          Alcotest.test_case "s1-survives-no-length-gate" `Quick
            (survives_under Bls_verify_gate_model.No_length_gate s1_name);
          Alcotest.test_case "s1-survives-no-pk-validation" `Quick
            (survives_under Bls_verify_gate_model.No_pk_validation s1_name);
          Alcotest.test_case "s2-survives-err-on-failed-verify" `Quick
            (survives_under Bls_verify_gate_model.Err_on_failed_verify s2_name);
          Alcotest.test_case "s2-survives-no-pk-validation" `Quick
            (survives_under Bls_verify_gate_model.No_pk_validation s2_name);
          Alcotest.test_case "s3-survives-err-on-failed-verify" `Quick
            (survives_under Bls_verify_gate_model.Err_on_failed_verify s3_name);
          Alcotest.test_case "s3-survives-no-length-gate" `Quick
            (survives_under Bls_verify_gate_model.No_length_gate s3_name);
        ] );
    ]
