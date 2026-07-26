(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    EPOCH_SYNC family. Each statement is pinned by its OWN gate deletion, and
    each deletion refutes exactly that statement while leaving the other two
    proving - so every refutation is cleanly attributable:

    - {!Epoch_sync_model.No_parent_hash_check} deletes [parents_match]
      (crates/state-sync/src/epoch.rs:100, consumed by the guard at :103),
      adding [Pending(R_replay, src) -> Adopted] with the store left at
      [Store_empty] ([save_record]'s idempotent no-op,
      crates/storage/src/epoch_records.rs:570-576) and [marked := true]. That
      refutes S1 conjunct A directly (marked_synced while ~holds_record) and
      conjunct B by factivity. No sibling repairs it: there is no
      [epoch_rec.epoch == epoch] comparison anywhere in epoch.rs:78-137, the
      committee conjunct's [Equal] branch (:28) accepts a replay on a stable
      set, the replayed certificate is genuine, the storage layer reports
      success, and :147's [break] does not fire.
    - {!Epoch_sync_model.No_cert_quorum_check} deletes the super-quorum plus
      aggregate-verify guard inside the SHARED helper
      [EpochRecord::verify_with_cert]
      (crates/types/src/primary/epoch.rs:84-88), adding
      [Pending(R_forged, src) -> Adopted] with [store := Store_forged]. That
      refutes S2 conjunct A (a stored record with no quorum behind it) and
      conjunct B (the four Adopted states collapse into one V1-view class that
      disagrees on the operand). No sibling repairs it: the surviving conjuncts
      compare only PUBLIC values, nothing verifies a record on the way out of
      storage, and the one genuine sibling writer (epoch_votes.rs:200) calls
      the SAME helper and therefore loses the check too.
    - {!Epoch_sync_model.Committee_targeted_fetch} deletes the anonymity of the
      fetch ([send_request_any],
      crates/consensus/primary/src/network/mod.rs:819 with [peer: _] at :821,
      served by the unfiltered rotation at
      crates/network-libp2p/src/consensus.rs:868-881), removing every
      [Wait -> Pending(resp, Src_observer)] transition. The Adopted view class
      collapses to a singleton, so K_V1(source_in_committee) becomes true and
      S3 conjuncts A and B fail, while conjunct C loses its EF target. Nothing
      in the pristine code already leaks the responder identity: it is dropped
      at the single call site, absent from the received bytes, and never named
      by a penalty (state-sync reports none at all).

    The pristine rows are the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Epoch_sync_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Epoch_sync_model.Checker.make (Epoch_sync_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Epoch_sync_statements.name name))
    Epoch_sync_statements.all

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
               (Epoch_sync_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Epoch_sync_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Epoch_sync_statements.prove sys st)))

(** The orthogonality half of a pin: a statement this mutation does NOT target
    still proves on the mutated model, so the refutation above is attributable
    to the targeted gate alone. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " still proves under the untargeted mutation")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Epoch_sync_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The two orthogonality rows of a pin: the other two statements survive. *)
let orthogonal mut names =
  List.map
    (fun name ->
      Alcotest.test_case (name ^ ":survives") `Quick (survives_under mut name))
    names

let () =
  Alcotest.run "epoch_sync_mutation"
    [
      ( "dropped parent-hash conjunct kills the requested-epoch binding",
        pin Epoch_sync_model.No_parent_hash_check
          "adopted-record-answers-the-requested-epoch"
        @ orthogonal Epoch_sync_model.No_parent_hash_check
            [
              "adoption-implies-known-super-quorum-certification";
              "epoch-record-adoption-is-source-blind";
            ] );
      ( "dropped super-quorum guard kills known certification",
        pin Epoch_sync_model.No_cert_quorum_check
          "adoption-implies-known-super-quorum-certification"
        @ orthogonal Epoch_sync_model.No_cert_quorum_check
            [
              "adopted-record-answers-the-requested-epoch";
              "epoch-record-adoption-is-source-blind";
            ] );
      ( "committee-targeted fetch kills source blindness",
        pin Epoch_sync_model.Committee_targeted_fetch
          "epoch-record-adoption-is-source-blind"
        @ orthogonal Epoch_sync_model.Committee_targeted_fetch
            [
              "adopted-record-answers-the-requested-epoch";
              "adoption-implies-known-super-quorum-certification";
            ] );
    ]
