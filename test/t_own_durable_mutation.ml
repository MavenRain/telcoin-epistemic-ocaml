(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    OWN_DURABLE family: three statements, three gate deletions, one pin each -
    every statement is seen to FAIL when the gate it actually depends on is
    removed, so no row is a test that has never been watched fail.

    - {!Own_durable_model.No_disk_write} pins S1
      (own-write-persists-yet-author-cannot-observe-durability). It deletes BOTH
      physical-write routes of the background DB thread - [ins.insert(&db)] in
      the no-open-txn arm (layered_db.rs:220-227) and the
      [if count <= 1 { current_txn.commit() }] branch inside [end_txn]
      (:160-163, reached from :199-208). Both, because a plain
      [Database::insert] takes whichever arm matches the thread's txn state at
      that instant: they are a sibling PAIR and deleting one would be silently
      repaired by the other. Nothing else repairs it either -
      [persist]/[sync_persist] only drain the queue via [DBMessage::CaughtUp]
      and write nothing (:463-495, :247-249), [TxnGuard::drop] routes into the
      same [end_txn] (:60-70), [compact] does not commit, and [Shutdown] breaks
      the loop without ending the txn (:256). The persist transition then leaves
      the physical DB untouched, disk=C1 becomes unreachable, and S1's [Af]
      fails from the crash-free-tail antecedent. S3 is untouched and still
      proves; S2 is deliberately NOT pinned here, because under this mutation
      its disk=C1 antecedent is unreachable and [prove_nonvacuous] returns
      [Vacuous_antecedent] - an honest non-result, not a refutation.
    - {!Own_durable_model.No_proposed_cert_guard} pins S2
      (durable-own-certificate-record-forbids-signature-equivocation). It
      deletes the [get::<ProposedCertificates>] early return in
      [spawn_header_proposal] (certifier.rs:418-430), so the re-certify
      transition fires even when the record IS present: from a state whose write
      already reached disk the node re-runs vote collection, forms a different
      aggregate over the same header digest (the digest excludes the aggregate
      signature, certificate.rs:473-479; the aggregation loop breaks at quorum
      in arrival order, certifier.rs:318-322) and gossips it. No sibling
      repairs it: [proposal_lock] is an in-process mutex that does not survive a
      restart, and the duplicate check in [process_certificate] returns [Ok(())]
      rather than [Err] (cert_validator.rs:93-98), so it does NOT stop
      certifier.rs:454 from publishing the second certificate. S1 and S3 both
      still prove.
    - {!Own_durable_model.No_store_before_publish} pins S3
      (published-own-certificate-implies-known-prior-persist). It deletes the
      [return Err(TaskError::from_message(…))] in the insert-failure arm at
      certifier.rs:443-446, so a failed own-store write falls through to
      [publish_certificate] at :454. A certificate that was never persisted then
      reaches the gossip topic, joins V2's view class, and
      [K_V2(own_cert_stored)] fails throughout it. No sibling repairs it: the
      caller does not retry on [Err], there is no second
      [insert::<ProposedCertificates>] in the tree, and
      [process_own_certificate] writes the [Certificates] table rather than
      re-establishing this one. S1 and S2 both still prove.

    The pristine rows are the matching positive half of each pin. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Own_durable_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Own_durable_model.Checker.make (Own_durable_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Own_durable_statements.name name))
    Own_durable_statements.all

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
               (Own_durable_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Own_durable_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Own_durable_statements.prove sys st)))

(** Attribution half of a pin: a statement this mutation does NOT pin still
    proves under it, so the refutation above is cleanly attributable to the one
    gate rather than to collateral damage across the family. *)
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
               (Own_durable_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "own_durable_mutation"
    [
      ( "dropped physical write kills inevitable own-write persistence",
        pin Own_durable_model.No_disk_write
          "own-write-persists-yet-author-cannot-observe-durability" );
      ( "dropped re-certify guard kills the durable-record equivocation ban",
        pin Own_durable_model.No_proposed_cert_guard
          "durable-own-certificate-record-forbids-signature-equivocation" );
      ( "dropped store-before-publish return kills known-prior-persist",
        pin Own_durable_model.No_store_before_publish
          "published-own-certificate-implies-known-prior-persist" );
      ( "each refutation is attributable to its own gate",
        [
          Alcotest.test_case "no-disk-write leaves S3 proving" `Quick
            (survives_under Own_durable_model.No_disk_write
               "published-own-certificate-implies-known-prior-persist");
          Alcotest.test_case "no-proposed-cert-guard leaves S1 proving" `Quick
            (survives_under Own_durable_model.No_proposed_cert_guard
               "own-write-persists-yet-author-cannot-observe-durability");
          Alcotest.test_case "no-proposed-cert-guard leaves S3 proving" `Quick
            (survives_under Own_durable_model.No_proposed_cert_guard
               "published-own-certificate-implies-known-prior-persist");
          Alcotest.test_case "no-store-before-publish leaves S1 proving" `Quick
            (survives_under Own_durable_model.No_store_before_publish
               "own-write-persists-yet-author-cannot-observe-durability");
          Alcotest.test_case "no-store-before-publish leaves S2 proving" `Quick
            (survives_under Own_durable_model.No_store_before_publish
               "durable-own-certificate-record-forbids-signature-equivocation");
        ] );
    ]
