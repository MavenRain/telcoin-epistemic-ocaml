(** Confirm-by-mutation pins for the ARCHIVE-EPOCH-IMPORT family. Each
    statement is pinned by exactly one gate deletion, and each pin asserts both
    halves: the statement proves on the pristine model and refutes under the
    mutation. Because the verdicts are asserted per statement, a mutation that
    happened to flip some OTHER statement cannot make a pin look real.

    - [final-header-link] deletes the publish-time equality
      [epoch_record.final_consensus.number != last_header.number ||
      epoch_final_hash != last_header.digest() -> InvalidImport]
      (crates/storage/src/consensus.rs:492-497). Nothing else on the publish
      path notices a short pack: the streamed linkage checks
      (consensus_pack.rs:975-986) certify gaplessness only, [files_consistent]
      (:894-902) passes on a truncated-but-cleanly-closed pack, and
      [is_epoch_complete] (consensus.rs:922-930) is a later re-check that never
      un-publishes.
    - [already-held-shortcircuit] deletes the idempotency guard
      (consensus.rs:458-464). The [recent_packs] cache IS a real repair inside
      the remove+rename window and IS modelled, but it is a ten-entry FIFO with
      [pop_front] eviction (:323, :1080-1083), so the eviction path survives
      it; readers take no [pack_install] lock (:1067-1088); [ImportPath::new]
      guards only same-process concurrent imports (:1305-1308); and
      [import_partial_to_staging] diverts only partial sync prefixes (:312-318,
      network/mod.rs:1249-1256), not the full-pack call at :1264-1265.
    - [batch-count-cap] deletes the v1 declared-count check
      (consensus_pack.rs:1466-1468). The legacy v0 counter (:1587-1590) is a
      different function reached only when [stream_iter.version() == 0]
      (:960-974), so it is not a repair - and the [sibling] group below proves
      that in the model: under this mutation the v1 branch overruns and the v0
      branch does not. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Archive_epoch_import_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Archive_epoch_import_model.Checker.make
       (Archive_epoch_import_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Archive_epoch_import_statements.name name))
    Archive_epoch_import_statements.all

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
               (Archive_epoch_import_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Archive_epoch_import_model.Pristine (fun sys ->
          Alcotest.(check bool)
            (name ^ " proves on the pristine model")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Archive_epoch_import_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** Assert satisfiability of a formula under a mutation. *)
let sat_under mut label want g () =
  with_mut mut (fun sys ->
      Alcotest.(check bool) label want
        (Archive_epoch_import_model.Checker.satisfiable sys g))

(** R4 evidence for the batch cap: deleting the v1 check really does leave the
    v1 stream unbounded, and the legacy v0 counter really does NOT cover it -
    only the v1 branch overruns. *)
let v1_overruns =
  sat_under Archive_epoch_import_model.No_batch_count_cap
    "the v1 branch overruns the cap once its own check is deleted" true
    (Formula.And
       ( f Archive_epoch_import_model.Buffer_over_cap,
         f Archive_epoch_import_model.Stream_is_v1 ))

(** ... and its sibling stays bounded, so the v0 counter is a separate gate on
    a separate code path rather than a repair of the deleted one. *)
let legacy_still_bounded =
  sat_under Archive_epoch_import_model.No_batch_count_cap
    "the legacy v0 branch stays bounded under the same deletion" false
    (Formula.And
       ( f Archive_epoch_import_model.Buffer_over_cap,
         Formula.Not (f Archive_epoch_import_model.Stream_is_v1) ))

(** R4 evidence for the install window: the [recent_packs] repair is live in
    the model - a reader IS answered from the cache while the directory entry
    is unlinked... *)
let cache_repair_is_live =
  sat_under Archive_epoch_import_model.No_already_held_shortcircuit
    "a cached reader is still answered inside the unlink window" true
    (Formula.And
       ( f Archive_epoch_import_model.Epoch_dir_absent,
         f Archive_epoch_import_model.Reader_served ))

(** ... and it is still not enough, because the ten-entry FIFO can have evicted
    this epoch by then (consensus.rs:323, :1080-1083). *)
let cache_repair_is_not_enough =
  sat_under Archive_epoch_import_model.No_already_held_shortcircuit
    "an evicted reader errors inside the unlink window" true
    (Formula.And
       ( f Archive_epoch_import_model.Epoch_dir_absent,
         f Archive_epoch_import_model.Reader_failed ))

(** R4 evidence for the final-header equality: deleting it publishes a pack
    whose sender held only a prefix. *)
let short_chain_gets_published =
  sat_under Archive_epoch_import_model.No_final_header_link
    "a short chain is published once the equality is deleted" true
    (Formula.And
       ( f Archive_epoch_import_model.Published,
         Formula.Not (f Archive_epoch_import_model.Peer_holds_full_epoch) ))

let () =
  Alcotest.run "archive_epoch_import_mutation"
    [
      ( "publish-time final-header equality",
        pin Archive_epoch_import_model.No_final_header_link
          "an-epoch-pack-is-published-only-after-its-final-header-matches-the-certified-record"
      );
      ( "already-held short circuit",
        pin Archive_epoch_import_model.No_already_held_shortcircuit
          "an-already-held-epoch-is-never-unlinked-for-a-redundant-import" );
      ( "v1 declared batch-count cap",
        pin Archive_epoch_import_model.No_batch_count_cap
          "a-streamed-output-declares-its-batch-count-before-any-batch-is-buffered"
      );
      ( "sibling",
        [
          Alcotest.test_case "v1-overruns" `Quick v1_overruns;
          Alcotest.test_case "legacy-still-bounded" `Quick legacy_still_bounded;
          Alcotest.test_case "cache-repair-is-live" `Quick cache_repair_is_live;
          Alcotest.test_case "cache-repair-is-not-enough" `Quick
            cache_repair_is_not_enough;
          Alcotest.test_case "short-chain-gets-published" `Quick
            short_chain_gets_published;
        ] );
    ]
