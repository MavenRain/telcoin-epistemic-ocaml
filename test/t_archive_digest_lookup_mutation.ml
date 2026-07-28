(** Confirm-by-mutation for the ARCHIVE_DIGEST_LOOKUP family: each pin asserts
    the pristine proof AND the flip to refuted under the gate deletion, per
    statement, so a pin can never pass on the strength of some other
    statement's collapse.

    - {!Archive_digest_lookup_model.No_digest_recheck} deletes
      [if batch.digest() != digest { return None; }] from
      [ConsensusPack::Inner::batch] (consensus_pack.rs:1261-1263). It pins S1
      (the substituted record makes the requester reject the WHOLE exchange,
      so the honestly served batch for g never arrives and the [AF] fails) and
      conjunct C of S3 (the archive answers for d while believing it answered
      for d, and no longer knows it holds d's preimage). The two repairs that
      exist for a substituted record - the requester's re-hash of every batch
      it reads (handle.rs:754-761) and the local path's re-keying by
      [b.digest()] (batch_fetcher.rs:229-232) - are MODELLED and are exactly
      what turns the substitution into the loss of the whole exchange; the
      fetch's own [pos >= file_len] early return (:1249-1256) is a different
      gate, is kept, and cannot help because a recycled offset is in range by
      construction.
    - {!Archive_digest_lookup_model.No_bloom_accrue} deletes
      [self.bloom.accrue(key);] from [Index::save]
      (archive/digest_index/index.rs:770). It pins S2: a saved key then has a
      bucket entry the filter rejects, so [load] short-circuits to [NotFound]
      at :777-778. No sibling repairs it - [fetch_position] is private with
      [load] as its only caller, the filter is read back from disk and never
      rebuilt from the buckets (:363-366), and both caller-side de-duplication
      sites run the wrong way (consensus_pack.rs:1034-1037,
      certificate_pack.rs:279-282).
    - {!Archive_digest_lookup_model.No_contains_bounds_check} deletes the
      [pos < self.data.file_len()] comparison from
      [ConsensusPack::Inner::contains_batch] (consensus_pack.rs:1241). It pins
      conjunct A of S3: possession is advertised for a digest whose index
      entry points past the end of the repaired file. Nothing prunes the index
      on repair (:680-684), nothing rebuilds it (pack_validate.rs:183-238) and
      there is no delete API (index.rs:761-797); the fetch path's own gates
      are kept and repair the answer, never the advertisement.

    Reported rather than hidden: {!Archive_digest_lookup_model.No_bloom_accrue}
    ALSO refutes S1, because deleting every bloom bit closes the whole read
    pipeline and nothing is ever served. That row is asserted below so the
    cross-effect is visible rather than latent. It does not refute S3 - it
    makes S3's antecedent unreachable, which [prove_nonvacuous] reports as a
    vacuity rather than a refutation, so S3 is not pinned with it. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Archive_digest_lookup_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Archive_digest_lookup_model.Checker.make
       (Archive_digest_lookup_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0
        (String.compare st.Archive_digest_lookup_statements.name name))
    Archive_digest_lookup_statements.all

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
               (Archive_digest_lookup_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Archive_digest_lookup_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Archive_digest_lookup_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The statement is UNTOUCHED by this mutation: it still proves. This is what
    keeps each pin attributable to its own gate. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " still proves under an unrelated gate deletion")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Archive_digest_lookup_statements.prove sys st)))

let () =
  Alcotest.run "archive_digest_lookup_mutation"
    [
      ( "deleted digest recheck poisons the exchange",
        pin Archive_digest_lookup_model.No_digest_recheck
          "recheck-keeps-a-recycled-offset-from-voiding-the-whole-batch-exchange"
      );
      ( "deleted digest recheck unbinds the answer from the payload",
        pin Archive_digest_lookup_model.No_digest_recheck
          "contains-is-an-index-and-bounds-fact-while-only-the-fetch-binds-the-payload"
      );
      ( "deleted bloom accrue hides a saved key",
        pin Archive_digest_lookup_model.No_bloom_accrue
          "bloom-accrue-is-the-sole-writer-of-the-only-fast-path-negative" );
      ( "deleted bloom accrue also closes the read pipeline",
        [
          Alcotest.test_case "delivery:mutated" `Quick
            (refuted_under Archive_digest_lookup_model.No_bloom_accrue
               "recheck-keeps-a-recycled-offset-from-voiding-the-whole-batch-exchange");
        ] );
      ( "deleted contains bounds check advertises a truncated offset",
        pin Archive_digest_lookup_model.No_contains_bounds_check
          "contains-is-an-index-and-bounds-fact-while-only-the-fetch-binds-the-payload"
      );
      ( "each gate deletion leaves the other statements standing",
        [
          Alcotest.test_case "bloom-statement:under-recheck-deletion" `Quick
            (survives_under Archive_digest_lookup_model.No_digest_recheck
               "bloom-accrue-is-the-sole-writer-of-the-only-fast-path-negative");
          Alcotest.test_case "bloom-statement:under-bounds-deletion" `Quick
            (survives_under Archive_digest_lookup_model.No_contains_bounds_check
               "bloom-accrue-is-the-sole-writer-of-the-only-fast-path-negative");
          Alcotest.test_case "delivery-statement:under-bounds-deletion" `Quick
            (survives_under Archive_digest_lookup_model.No_contains_bounds_check
               "recheck-keeps-a-recycled-offset-from-voiding-the-whole-batch-exchange");
        ] );
    ]
