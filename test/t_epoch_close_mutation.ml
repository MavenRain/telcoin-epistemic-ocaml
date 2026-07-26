(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    EPOCH_CLOSE family. Three gates, three pins, every statement covered:

    - {!Epoch_close_model.No_cert_quorum_count} deletes the [auth_iter <
      super_quorum()] tail of [EpochRecord::verify_with_cert]
      (crates/types/src/primary/epoch.rs:84-88), so a single-signature
      certificate verifies. It adds (Sg_wait, Cd_lone) -> (Sg_open,
      St_far_cert, held = Hd_lone), a state whose V1 view is identical to the
      honest acquisition state, refuting S1's known-endorsement conjunct AND
      S3's acquired-record knowledge conjunct. No sibling repairs it: the
      deletion is at the shared definition all three production callers
      (epoch_votes.rs:156, :200, state-sync/epoch.rs:102) go through, the
      network layer returns peer bytes unvalidated (network/mod.rs:809-829),
      storage only appends (epoch_records.rs:229-243, :597-617), and once the
      poisoned entry is stored the collector skips the epoch outright
      (state-sync/epoch.rs:61-76).
    - {!Epoch_close_model.No_cert_digest_binding} deletes the content-addressing
      of the certificate index in [Inner::save]: the arriving certificate is
      filed under the FETCHED record's digest
      (crates/storage/src/epoch_records.rs:601, :612-614) exactly so that the
      [cert_by_digest(record.digest())] lookup on the STORED record (:374-375)
      cannot resolve it. File it under the epoch slot's own record digest
      instead and (Sg_recover, Cd_sound, Tr_far) -> (Sg_settled, St_own_cert,
      held = Hd_far) appears: the diverged member reports a certificate that a
      super-quorum signed over a DIFFERENT record, refuting S2's
      uncertified-divergence conjunct and S1's known-endorsement conjunct. No
      sibling repairs it: nothing re-verifies the pair on read
      ([get_epoch_by_number] :370-377 just pairs them, and the serving path
      hands the pair straight out, crates/node/src/lib.rs:88-94), the collector
      SKIPS any epoch already holding record + cert
      (state-sync/epoch.rs:61-76) so the bogus attachment disables the one
      background repair, [write_epoch_record] short-circuits unconditionally on
      an existing record (close_epoch.rs:199-205), and [manage_epoch_votes] is
      never re-entered for the same epoch ([get_new_vote_channel] [take()]s the
      receiver once, epoch_votes.rs:236-248). A fetching PEER would reject the
      mismatched pair on [verify_with_cert]'s digest check
      (types/src/primary/epoch.rs:60-63) - a downstream detector, never a
      repair of what this store returns.

      This mutation REPLACES an earlier [No_record_idempotence] pin that
      deleted the already-stored early return
      (crates/storage/src/epoch_records.rs:574-576) and claimed a peer's record
      then displaces V1's. It does not: [idx < len] falls into the out-of-order
      arm (:577-582) whose [Err] [Inner::save] propagates with [?] at :604
      before the cert append, and even without that arm [PositionIndex::save]
      accepts only [key == len] and appends rather than overwrites
      (archive/position_index/index.rs:247-261). Displacement is unreachable by
      any single-gate deletion, which is why S2's stability conjunct is now
      pinned by nothing and says so in its own doc.
    - {!Epoch_close_model.No_committee_predial} deletes the committee pre-dial
      in [open_epoch_pack]'s missing-record branch
      (crates/node/src/manager/node/run_epoch.rs:487-503). It makes the
      zero-peer wait reachable with [Sg_halt] as its only successor, refuting
      S3's EF-opened conjunct. No sibling repairs it: the cross-epoch
      [dial_peer_bls] retries (start_epoch.rs:567-586) are exactly the
      (Sg_entry, Pr_some) start line the model already carries and the
      mutation deliberately leaves intact, while bootstrap registration and
      the per-epoch committee dial live behind
      [spawn_primary_network_for_epoch] (start_epoch.rs:772-787), reached only
      at run_epoch.rs:258-267, strictly AFTER [open_epoch_pack] at :219.

    Each row asserts the proof FLIPS to an error on the mutated model; the
    pristine rows are the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Epoch_close_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Epoch_close_model.Checker.make (Epoch_close_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Epoch_close_statements.name name))
    Epoch_close_statements.all

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
               (Epoch_close_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Epoch_close_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Epoch_close_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The other half of confirm-by-mutation: a gate that this statement does NOT
    rest on must leave it proved, so each refutation is attributable to the
    gate it names rather than to any perturbation of the model. *)
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
               (Epoch_close_statements.prove sys st)))

let () =
  Alcotest.run "epoch_close_mutation"
    [
      ( "dropped super-quorum count kills known endorsement",
        pin Epoch_close_model.No_cert_quorum_count
          "certified-epoch-record-implies-known-supermajority-endorsement" );
      ( "dropped cert digest binding kills uncertified divergence",
        pin Epoch_close_model.No_cert_digest_binding
          "self-closed-epoch-record-is-never-displaced-and-divergence-stays-hidden"
      );
      ( "dropped cert digest binding also kills known endorsement",
        pin Epoch_close_model.No_cert_digest_binding
          "certified-epoch-record-implies-known-supermajority-endorsement" );
      ( "dropped committee pre-dial kills entry acquisition",
        pin Epoch_close_model.No_committee_predial
          "entry-predial-preserves-record-acquisition" );
      ( "dropped super-quorum count also kills acquired-record knowledge",
        pin Epoch_close_model.No_cert_quorum_count
          "entry-predial-preserves-record-acquisition" );
      ( "attribution: unrelated gates leave each statement standing",
        [
          Alcotest.test_case "endorsement survives no-predial" `Quick
            (survives_under Epoch_close_model.No_committee_predial
               "certified-epoch-record-implies-known-supermajority-endorsement");
          Alcotest.test_case "divergence survives no-quorum-count" `Quick
            (survives_under Epoch_close_model.No_cert_quorum_count
               "self-closed-epoch-record-is-never-displaced-and-divergence-stays-hidden");
          Alcotest.test_case "divergence survives no-predial" `Quick
            (survives_under Epoch_close_model.No_committee_predial
               "self-closed-epoch-record-is-never-displaced-and-divergence-stays-hidden");
          Alcotest.test_case "acquisition survives no-cert-digest-binding"
            `Quick
            (survives_under Epoch_close_model.No_cert_digest_binding
               "entry-predial-preserves-record-acquisition");
        ] );
    ]
