(** Confirm-by-mutation for the BATCH-ADMIT family. Each gate deletion removes
    exactly one guard of the real receive path and the mutated row asserts that
    the statement depending on it FLIPS to an error; the pristine row is the
    matching positive half.

    - [No_gas_ceiling] deletes crates/batch-validator/src/validator.rs:177-182,
      the [if total_possible_gas > max_tx_gas] bound reached from
      [validate_batch] at :77. Nothing else on the receive path re-imposes it:
      [decode_transactions] and [recover_and_validate] (:147-156, :209-215)
      only decode and recover a signer, [validate_batch_size_bytes]
      (:122-141) bounds bytes, [validate_basefee] (:188-195) compares a batch
      field, and [process_report_batch] adds only the committee check
      (crates/consensus/worker/src/network/handler.rs:237-239). The
      builder-side cap (crates/batch-builder/src/batch.rs:73-81) is
      producer-side and does not constrain a Byzantine author. Pins S1.
    - [No_blob_reject] deletes validator.rs:202-204, the [is_eip4844]
      rejection reached from [validate_batch] at :73. The decode that precedes
      it is [reth_recover_raw_transaction::<TransactionSigned>]
      (crates/tn-reth/src/txn_pool.rs:369-373), a plain 2718 decode of the
      consensus envelope, which accepts a blob transaction without a sidecar;
      the byte cap does not bite on a small envelope and the gas ceiling does
      not bite on an ordinary [gas_limit]. Pins S2.
    - [Digest_covers_received_at] deletes the [#[serde(skip)]] on
      [Batch::received_at] (crates/types/src/worker/sealed_batch.rs:86). Every
      seal routes through the one [digest()] helper (:51-53, :149-151,
      :159-162), so no second site re-fixes the key. Pins S3.

    Three extra groups keep the pins honest. The {b targeting} group asserts
    that each deletion leaves the OTHER statements proving, so no pin can pass
    because some unrelated statement collapsed. The {b non-vacuity} group
    asserts that each statement's antecedent is still reachable under the
    mutation that refutes it, so every flip is a value refutation and not a
    [Vacuous_antecedent]. The {b sibling-repair} group shows what each deletion
    does and does not touch: the other content gate keeps working, and the
    digest deletion kills relay out of a stamped copy while leaving a fetch
    served by the author - whose copy is never stamped
    (crates/batch-builder/src/batch.rs:122-123,
    crates/consensus/worker/src/worker.rs:359) - alive. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail on an impossible [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Batch_admit_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Batch_admit_model.Checker.make (Batch_admit_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Batch_admit_statements.name name))
    Batch_admit_statements.all

(** Does the named statement prove under [mut]. *)
let proves_under mut name k =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          k
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Batch_admit_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " flips to refuted under the mutation")
        false proved)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  proves_under Batch_admit_model.Pristine name (fun proved ->
      Alcotest.(check bool) (name ^ " proves on pristine") true proved)

(** A statement untouched by this mutation still proves under it. *)
let survives_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " still proves under an unrelated gate deletion")
        true proved)

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The statement's antecedent is still reachable under the mutation, so the
    refutation above is a value flip and not a vacuity. *)
let antecedent_reachable_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " keeps a reachable antecedent under the mutation")
            true
            (Batch_admit_model.Checker.satisfiable sys
               st.Batch_admit_statements.antecedent))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** One [satisfiable] assertion on the system built under [mut]. *)
let sat_under mut label expected formula () =
  with_mut mut (fun sys ->
      Alcotest.(check bool) label expected
        (Batch_admit_model.Checker.satisfiable sys formula))

(** The name of the gas-ceiling statement. *)
let s1_name = "gas-ceiling-refusal-is-a-committee-verdict-not-a-storage-fact"

(** The name of the blob-rejection statement. *)
let s2_name = "blob-rejection-binds-the-validated-path-only"

(** The name of the digest/receipt-stamp statement. *)
let s3_name =
  "relay-keeps-the-author-digest-while-the-receipt-stamp-stays-private"

(** Some worker admitted the batch through the content-gated path. *)
let some_gated_admission =
  Formula.Or (f Batch_admit_model.Gated_admit_1, f Batch_admit_model.Gated_admit_2)

(** A batch held by the fetch-side worker that did NOT come from the stamping
    relayer, i.e. one served by the author out of its unstamped copy. *)
let held_from_the_author =
  Formula.And
    (f Batch_admit_model.Holds_2, Formula.Not (f Batch_admit_model.Relay_held_2))

let () =
  Alcotest.run "batch_admit_mutation"
    [
      ( "deleting the batch-gas ceiling admits an over-ceiling batch",
        pin Batch_admit_model.No_gas_ceiling s1_name );
      ( "deleting the EIP-4844 rejection admits a blob-carrying batch",
        pin Batch_admit_model.No_blob_reject s2_name );
      ( "putting the receipt stamp back in the digest breaks relay",
        pin Batch_admit_model.Digest_covers_received_at s3_name );
      ( "targeting: each deletion refutes only its own statement",
        [
          Alcotest.test_case "no-gas-ceiling:s2" `Quick
            (survives_under Batch_admit_model.No_gas_ceiling s2_name);
          Alcotest.test_case "no-gas-ceiling:s3" `Quick
            (survives_under Batch_admit_model.No_gas_ceiling s3_name);
          Alcotest.test_case "no-blob-reject:s1" `Quick
            (survives_under Batch_admit_model.No_blob_reject s1_name);
          Alcotest.test_case "no-blob-reject:s3" `Quick
            (survives_under Batch_admit_model.No_blob_reject s3_name);
          Alcotest.test_case "digest-covers-received-at:s1" `Quick
            (survives_under Batch_admit_model.Digest_covers_received_at s1_name);
          Alcotest.test_case "digest-covers-received-at:s2" `Quick
            (survives_under Batch_admit_model.Digest_covers_received_at s2_name);
        ] );
      ( "non-vacuity: every flip is a value refutation",
        [
          Alcotest.test_case "no-gas-ceiling:s1-antecedent" `Quick
            (antecedent_reachable_under Batch_admit_model.No_gas_ceiling s1_name);
          Alcotest.test_case "no-blob-reject:s2-antecedent" `Quick
            (antecedent_reachable_under Batch_admit_model.No_blob_reject s2_name);
          Alcotest.test_case "digest-covers-received-at:s3-antecedent" `Quick
            (antecedent_reachable_under
               Batch_admit_model.Digest_covers_received_at s3_name);
        ] );
      ( "sibling-repair: what each deletion leaves standing",
        [
          (* The two content gates are independent: deleting one does not open
             the other, so neither pin can pass on the other's back. *)
          Alcotest.test_case "no-gas-ceiling-still-rejects-blobs" `Quick
            (sat_under Batch_admit_model.No_gas_ceiling
               "EF (gated-admit /\\ carries-blob) under No_gas_ceiling" false
               (Formula.And
                  (some_gated_admission, f Batch_admit_model.Content_carries_blob)));
          Alcotest.test_case "no-blob-reject-still-holds-the-ceiling" `Quick
            (sat_under Batch_admit_model.No_blob_reject
               "EF (gated-admit /\\ over-ceiling) under No_blob_reject" false
               (Formula.And
                  (some_gated_admission, f Batch_admit_model.Content_over_ceiling)));
          (* The gate deletion is what opens the storage, not the bypass: the
             bypass is already live on pristine, so the S1/S2 flips cannot be
             read as the bypass appearing. *)
          Alcotest.test_case "the-bypass-is-live-on-pristine-too" `Quick
            (sat_under Batch_admit_model.Pristine
               "EF (holds_v2 /\\ carries-blob) on pristine" true
               (Formula.And
                  (f Batch_admit_model.Holds_2,
                   f Batch_admit_model.Content_carries_blob)));
          (* The digest deletion is targeted: relay out of a STAMPED copy dies,
             a fetch served by the author's unstamped copy survives. *)
          Alcotest.test_case "digest-mutation-kills-relay" `Quick
            (sat_under Batch_admit_model.Digest_covers_received_at
               "EF relay-held_v2 under Digest_covers_received_at" false
               (f Batch_admit_model.Relay_held_2));
          Alcotest.test_case "digest-mutation-spares-the-author-fetch" `Quick
            (sat_under Batch_admit_model.Digest_covers_received_at
               "EF (holds_v2 /\\ ~relay-held_v2) under \
                Digest_covers_received_at"
               true held_from_the_author);
          Alcotest.test_case "pristine-keeps-every-copy-content-addressed"
            `Quick
            (sat_under Batch_admit_model.Pristine
               "EF ~(key = digest(stored)) on pristine" false
               (Formula.Not (f Batch_admit_model.Key_matches_digest)));
          Alcotest.test_case "digest-mutation-breaks-content-addressing" `Quick
            (sat_under Batch_admit_model.Digest_covers_received_at
               "EF ~(key = digest(stored)) under Digest_covers_received_at" true
               (Formula.Not (f Batch_admit_model.Key_matches_digest)));
        ] );
    ]
