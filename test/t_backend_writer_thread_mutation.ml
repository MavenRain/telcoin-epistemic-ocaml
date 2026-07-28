(** Confirm-by-mutation for the BACKEND_WRITER_THREAD family: each pin asserts
    the pristine proof AND the flip to refuted under the gate deletion, per
    statement, so a pin can never pass on the strength of some other
    statement's collapse. The two gates are lines 67 and 256 of the same file
    and the last group asserts that each leaves the other's statements
    standing, so neither pin is attributable to the other's deletion.

    - {!Backend_writer_thread_model.No_end_txn_on_drop} deletes
      [let _ = self.tx.send(DBMessage::EndTxn);] from [Drop for TxnGuard]
      (crates/storage/src/layered_db.rs:67, guard at :60-70). It pins S1 (a
      transaction abandoned after writing [w] wedges the overlap count above
      zero forever, so [end_txn]'s [count <= 1] commit at :161-164 is never
      reached again and [w] can no longer reach the backend at all) and S3 (the
      exported [open_txn_count] keeps counting the abandoned transaction, so a
      reading of one no longer entails that any logical transaction is
      outstanding). No sibling repairs it: [DBMessage::CommitTxn] (:199-201) is
      the only other decrement and is sent by exactly one caller behind the
      [AcqRel] swap of [mark_committed] (:52-58, :128-132), which a guard that
      dropped uncommitted never wins (:62); the direct-write route
      [ins.insert(&db)] (:220-227) is the [else] of
      [if let Some((txn, _)) = &mut txn] at :210 and so is unreachable once the
      count is wedged; [persist]/[sync_persist] (:463-495) send
      [DBMessage::CaughtUp], answered with [let _ = tx.send(());] (:247-249)
      without touching [txn]; and [db_run] has no timeout, watchdog or open-txn
      cap anywhere in :178-267.
    - {!Backend_writer_thread_model.No_shutdown_break} deletes the
      [DBMessage::Shutdown => break,] arm (layered_db.rs:256). It pins S2: the
      loop then leaves only when [rx.recv()] fails (:185), i.e. after every
      [Sender] clone has dropped, and a live [LayeredDbTxMut] holds one (:76)
      whose guard sends [EndTxn] on the way out (:67) - so the count drains and
      the physical transaction commits before the loop exits, and the state in
      which an acknowledged write is discarded becomes unreachable. No sibling
      commits the transaction at shutdown in the pristine code: [end_txn] is
      dispatched only from the [CommitTxn] (:199-201) and [EndTxn] (:202-208)
      arms; neither backend transaction wrapper has a [Drop] impl (the
      declaration lists of crates/storage/src/mdbx/database.rs and
      crates/storage/src/redb/database.rs contain [impl DbTxMut for MdbxTxMut]
      at :67-89 and [impl DbTxMut for ReDbTxMut] at :45-69, with [fn commit] at
      :85-88 and :65-68 respectively, and no [impl Drop] at all); and
      [Drop for LayeredDatabase] sends [Shutdown] at :288 and only then joins at
      :293-296.

    HONESTY NOTE. The second mutation is a MODEL device for removing the lossy
    transition, not a patch anyone should apply: without the [break], the real
    [Drop for LayeredDatabase] would deadlock, because it sends [Shutdown] and
    joins (:288-296) while still owning the [Sender] the loop would be waiting
    to see dropped.

    The pins were confirmed CONJUNCT BY CONJUNCT before being written, so no pin
    can be passing because some other conjunct of the same statement collapsed.
    Proving each conjunct alone against each transition relation gives (36
    reachable states pristine, 36 under the first mutation, 27 under the
    second - the second mutation only removes exit states):

    {v
                                          pristine  no_end_txn_on_drop  no_shutdown_break
      S1.A  AG(pending /\ alive -> EF disk)  PROVED      REFUTED             PROVED
      S1.B  AG(quiescent /\ issued -> disk)  PROVED      REFUTED             PROVED
      S2.A  EF(ack /\ b open /\ gone /\ lost) PROVED      PROVED              REFUTED
      S2.B1 AG(ack /\ read 1 -> ~K_V0 both)  PROVED      PROVED              PROVED
      S2.B2 AG(ack /\ gone  -> ~K_V0 both)   PROVED      PROVED              REFUTED
      S2.C  AG(b open /\ read 1 -> ~K_V1 p)  PROVED      PROVED              PROVED
      S3.A  AG(read 1 -> K_V2 some open)     PROVED      REFUTED             PROVED
      S3.B  AG(read 0 -> K_V2 all durable)   PROVED      PROVED              PROVED
    v}

    Every refutation above is a [Refuted] verdict, never a
    [Vacuous_antecedent]: S1's antecedent (an acknowledged write awaiting a
    commit with the thread alive), S2's (an acknowledged commit at a reading of
    one) and S3's (a reading of one) all stay reachable under the mutation that
    pins them, so the pins are genuine counterexamples rather than the
    antecedent falling out of the reachable set. S1.B, S2.B1, S2.C and S3.B are
    stated because they are true, not because a mutation refutes them; each sits
    inside a conjunction that a mutation does refute. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Backend_writer_thread_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Backend_writer_thread_model.Checker.make
       (Backend_writer_thread_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Backend_writer_thread_statements.name name))
    Backend_writer_thread_statements.all

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
               (Backend_writer_thread_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Backend_writer_thread_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Backend_writer_thread_statements.prove sys st)))

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
               (Backend_writer_thread_statements.prove sys st)))

let () =
  Alcotest.run "backend_writer_thread_mutation"
    [
      ( "deleted guard end-message wedges the overlap count",
        pin Backend_writer_thread_model.No_end_txn_on_drop
          "abandoned-write-txn-still-releases-the-overlapped-physical-commit" );
      ( "deleted guard end-message turns the exported gauge into an over-count",
        pin Backend_writer_thread_model.No_end_txn_on_drop
          "exported-open-txn-gauge-is-an-exact-census-of-live-logical-txns" );
      ( "deleted shutdown break removes the discarded-write state",
        pin Backend_writer_thread_model.No_shutdown_break
          "orderly-shutdown-under-an-overlapped-txn-discards-a-barriered-write"
      );
      ( "each gate deletion leaves the other statements standing",
        [
          Alcotest.test_case "shutdown-statement:under-guard-deletion" `Quick
            (survives_under Backend_writer_thread_model.No_end_txn_on_drop
               "orderly-shutdown-under-an-overlapped-txn-discards-a-barriered-write");
          Alcotest.test_case "commit-statement:under-shutdown-deletion" `Quick
            (survives_under Backend_writer_thread_model.No_shutdown_break
               "abandoned-write-txn-still-releases-the-overlapped-physical-commit");
          Alcotest.test_case "gauge-statement:under-shutdown-deletion" `Quick
            (survives_under Backend_writer_thread_model.No_shutdown_break
               "exported-open-txn-gauge-is-an-exact-census-of-live-logical-txns");
        ] );
    ]
