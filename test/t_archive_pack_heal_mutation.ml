(** Confirm-by-mutation for the ARCHIVE-PACK-HEAL family. Each gate deletion
    removes exactly one line of the real pack layer and the mutated row asserts
    that the statement depending on it FLIPS to an error; the pristine row is
    the matching positive half.

    - [No_shrink_clamp] deletes
      crates/storage/src/consensus_pack.rs:716
      ([let new_pack_len = new_pack_len.min(pack_len);]), the only thing
      between the repair's walk-back and [data.truncate] at :717-719.
      [Pack::truncate] is [DataFile::set_len], documented "truncating or
      extending" with no shrink-only assertion (archive/pack.rs:424-427,
      archive/data_file.rs:134-166); the defensive guard on the sibling call
      protects the .pdx file only (position_index/index.rs:227-233);
      [files_consistent] never runs on an append open (:894 is its sole call
      site, :809-814 and :852-857 are the append paths); and the repair's
      epilogue writes the extended length into both digest indexes
      (:721-726), so nothing downstream notices. Pins S1.
    - [No_static_consistency_gate] deletes the
      [if !Self::files_consistent(..) { return Err(PackError::CorruptPack); }]
      block at consensus_pack.rs:894-902. [ConsensusChain::get_static] caches
      the opened pack with no further validation (consensus.rs:1067-1088) and
      is the entry point of a dozen read paths; the per-record CRC
      (archive/pack.rs:346-365) cannot see a record the indexes never learned
      about. Pins S2.
    - [No_write_failure_latch] deletes the
      [AppendError::WriteDataError(_io_err) => self.failed = true] arm at
      archive/pack.rs:269. [run_pack_loop] never rebuilds [inner]
      (consensus_pack.rs:132-193, certificate_pack.rs:53-86) and
      [DataFile::write] has no latch of its own
      (archive/data_file.rs:334-358), so nothing re-establishes it inside a
      process lifetime. Pins S3.

    Two extra groups keep the pins honest. The {b targeting} group asserts
    that each deletion leaves the OTHER two statements proving, so no pin can
    pass because some unrelated statement collapsed. The {b witness} group
    checks that each mutated run fails for the reason claimed - the extended
    heal, the inconsistent read-only open and the vanished latch are each
    asserted reachable (or, for the latch, unreachable) under their own
    mutation, and each statement's antecedent is asserted STILL reachable so
    the flip is a genuine refutation rather than a vacuity report. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail on an impossible [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Archive_pack_heal_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Archive_pack_heal_model.Checker.make
       (Archive_pack_heal_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Archive_pack_heal_statements.name name))
    Archive_pack_heal_statements.all

(** Does the named statement prove under [mut]. *)
let proves_under mut name k =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          k
            (Result.fold ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Archive_pack_heal_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " flips to refuted under the mutation")
        false proved)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  proves_under Archive_pack_heal_model.Pristine name (fun proved ->
      Alcotest.(check bool) (name ^ " proves on pristine") true proved)

(** A statement untouched by this mutation still proves under it. *)
let survives_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " is untouched by this mutation and still proves")
        true proved)

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** One [satisfiable] assertion under a mutation. *)
let sat_under mut label expected formula () =
  with_mut mut (fun sys ->
      Alcotest.(check bool) label expected
        (Archive_pack_heal_model.Checker.satisfiable sys formula))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** S1's name. *)
let n1 = "append-open-repair-never-zero-extends-a-pack-whose-batch-index-survived"

(** S2's name. *)
let n2 = "read-only-open-enforces-the-three-file-agreement-append-open-only-repairs"

(** S3's name. *)
let n3 = "published-pack-error-reveals-the-index-gap-not-whether-the-pack-fail-stopped"

let () =
  Alcotest.run "archive_pack_heal_mutation"
    [
      ("shrink-clamp", pin Archive_pack_heal_model.No_shrink_clamp n1);
      ( "static-consistency-gate",
        pin Archive_pack_heal_model.No_static_consistency_gate n2 );
      ("write-failure-latch", pin Archive_pack_heal_model.No_write_failure_latch n3);
      ( "targeting",
        [
          Alcotest.test_case "shrink-clamp-leaves-s2" `Quick
            (survives_under Archive_pack_heal_model.No_shrink_clamp n2);
          Alcotest.test_case "shrink-clamp-leaves-s3" `Quick
            (survives_under Archive_pack_heal_model.No_shrink_clamp n3);
          Alcotest.test_case "static-gate-leaves-s1" `Quick
            (survives_under Archive_pack_heal_model.No_static_consistency_gate
               n1);
          Alcotest.test_case "static-gate-leaves-s3" `Quick
            (survives_under Archive_pack_heal_model.No_static_consistency_gate
               n3);
          Alcotest.test_case "write-latch-leaves-s1" `Quick
            (survives_under Archive_pack_heal_model.No_write_failure_latch n1);
          Alcotest.test_case "write-latch-leaves-s2" `Quick
            (survives_under Archive_pack_heal_model.No_write_failure_latch n2);
        ] );
      ( "witness",
        [
          (* The clamp deletion refutes S1 by producing exactly the state the
             clamp forbids: a repair that GREW the file even though the batch
             digest index still tracked a real length. *)
          Alcotest.test_case "shrink-clamp-adds-a-guarded-extension" `Quick
            (sat_under Archive_pack_heal_model.No_shrink_clamp
               "EF (heal-ran /\\ batch-index-survived /\\ heal-extended)" true
               (Formula.conj
                  [
                    f Archive_pack_heal_model.Heal_ran;
                    f Archive_pack_heal_model.Batch_index_survived;
                    f Archive_pack_heal_model.Heal_extended;
                  ]));
          (* ...and S1's antecedent is still reachable, so the flip is a
             refutation and not a vacuity report. *)
          Alcotest.test_case "shrink-clamp-keeps-s1-antecedent" `Quick
            (sat_under Archive_pack_heal_model.No_shrink_clamp
               "EF (heal-ran /\\ heal-dropped)" true
               (Formula.And
                  ( f Archive_pack_heal_model.Heal_ran,
                    f Archive_pack_heal_model.Heal_dropped_output )));
          (* The gate deletion refutes S2 by admitting a read-only open of a
             pack whose three files disagree. *)
          Alcotest.test_case "static-gate-admits-a-disagreeing-pack" `Quick
            (sat_under Archive_pack_heal_model.No_static_consistency_gate
               "EF (open-static-ok /\\ ~files-consistent)" true
               (Formula.And
                  ( f Archive_pack_heal_model.Static_open_served,
                    Formula.Not (f Archive_pack_heal_model.Files_agree) )));
          Alcotest.test_case "static-gate-keeps-s2-antecedent" `Quick
            (sat_under Archive_pack_heal_model.No_static_consistency_gate
               "EF open-static-ok" true
               (f Archive_pack_heal_model.Static_open_served));
          (* The latch deletion refutes S3 by making the pack unlatchable, so
             the node's ignorance of the latch collapses into knowledge. *)
          Alcotest.test_case "write-latch-removes-every-latched-state" `Quick
            (sat_under Archive_pack_heal_model.No_write_failure_latch
               "EF pack-latched is unreachable" false
               (f Archive_pack_heal_model.Pack_latched));
          Alcotest.test_case "write-latch-keeps-s3-antecedent" `Quick
            (sat_under Archive_pack_heal_model.No_write_failure_latch
               "EF error-seen" true (f Archive_pack_heal_model.Error_seen));
          (* ...and S3's OTHER conjunct is untouched by that deletion, so the
             refutation is attributable to the latch ignorance alone. *)
          Alcotest.test_case "write-latch-leaves-the-index-gap-knowledge" `Quick
            (sat_under Archive_pack_heal_model.No_write_failure_latch
               "EF (error-seen /\\ K_v0(data-ahead-of-index))" true
               (Formula.And
                  ( f Archive_pack_heal_model.Error_seen,
                    Formula.K
                      ( Validator.V0,
                        f Archive_pack_heal_model.Data_ahead_of_index ) )));
        ] );
    ]
