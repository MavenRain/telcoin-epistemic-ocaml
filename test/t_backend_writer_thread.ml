(** Proof suite for the BACKEND_WRITER_THREAD family: the three statements
    prove on the pristine model, the model stays inside its stated size bound,
    each gate's forbidden state is genuinely unreachable, the loss S2 asserts is
    not manufactured, and - the part that matters most - every knowledge and
    ignorance claim is discharged by an explicit witness rather than by a
    collapsed view class.

    The [contingency] group carries, for each of the two positive K conjuncts of
    S3, both obligations: the knowledge is contingent (its negation is
    satisfiable somewhere reachable) and the knower's view class at the
    operative state is NOT a singleton. For each of the four ignorance conjuncts
    of S2 it carries the witness pair that makes the ignorance real.

    The class sizes were MEASURED, not assumed, on the 36 reachable pristine
    states:

    {v
      V2 (the stats consumer)
        reading 1  ->  8 states   (S3 conjunct A operative class)
        reading 0  ->  9 states   (S3 conjunct B operative class)
        reading 2  ->  1 state
      V0 (writer a)
        (committed, reading 1)  ->  2 states   (S2 conjunct B1)
        (committed, gone)       ->  5 states   (S2 conjunct B2)
      V1 (writer b)
        (open, reading 1)       ->  5 states   (S2 conjunct C)
    v}

    The reading-of-two class is a SINGLETON, which is why no statement in this
    family puts a K behind [Gauge_two] even though "a reading of two means both
    writers are open" is true and is asserted here as a plain reachability
    invariant instead. That is the R2 trap this round was told to hunt, and it
    is the reason S3 conjunct A is stated at the reading of one. *)

open Telcoin_epistemic
open Backend_writer_thread_model

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
        (st.Backend_writer_thread_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Backend_writer_thread_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Backend_writer_thread_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The exact pristine reachable count is 36. Eighteen of them have the writer
    thread alive: for each of the sixteen [(a, b)] lifecycle pairs the overlap
    count is pinned to the number of open transactions and [w]'s fate is pinned
    too, except at [(committed, open)] and [(dropped, open)] where [w] may
    either still ride the open physical transaction or already have been
    committed by an earlier drain - two extra states. The other eighteen are
    the images of those under the thread's exit, which maps a pending [w] to
    discarded and is injective on the eighteen. The raw product bound is
    4 x 4 x 3 x 4 x 2 = 384. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check int) "reachable states" 36 (Checker.reachable_count sys))

(** The counter is a census, direction one: no reachable state reads zero on the
    exported gauge while a logical write transaction is outstanding. Every
    [StartTxn] increment (layered_db.rs:188-192) is matched by exactly one
    decrement, from [CommitTxn] (:199-201) or the guard's [EndTxn] (:67,
    :202-208). *)
let no_zero_reading_while_a_txn_is_open () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a zero reading with a live logical txn is reachable" false
        (Checker.satisfiable sys
           (Formula.And (f Gauge_zero, f Some_logical_txn_open))))

(** The counter is a census, direction two: a reading of two really does mean
    both writers hold open transactions. Stated as a reachability invariant and
    NOT as a K, because the reading-of-two view class is a singleton in the
    pristine model and a K there would be degenerate (R2). *)
let a_reading_of_two_means_both_writers_are_open () =
  with_sys (fun sys ->
      Alcotest.(check bool) "a reading of two without both writers open" false
        (Checker.satisfiable sys
           (Formula.And
              ( f Gauge_two,
                Formula.Not (Formula.And (f A_holds_open_txn, f B_holds_open_txn))
              ))))

(** The only way to lose [w] is the loop's exit through
    [DBMessage::Shutdown => break] (layered_db.rs:256): no reachable state has
    [w] discarded while the writer thread is still serving messages. *)
let a_write_is_discarded_only_at_the_loops_exit () =
  with_sys (fun sys ->
      Alcotest.(check bool) "a discarded write with the thread alive" false
        (Checker.satisfiable sys
           (Formula.And (f W_discarded, f Writer_thread_alive))))

(** The gate S1 is about: the guard's [EndTxn] (layered_db.rs:67) makes the
    abandon path durable, so no reachable state has a transaction dropped
    without commit, nobody left holding one, the thread alive, and [w] still
    waiting on a physical commit. This is the state
    {!Backend_writer_thread_model.No_end_txn_on_drop} creates. *)
let the_abandon_path_leaves_no_wedge () =
  with_sys (fun sys ->
      Alcotest.(check bool) "a wedged count after an abandoned txn" false
        (Checker.satisfiable sys
           (Formula.conj
              [
                f A_dropped_without_commit;
                Formula.Not (f Some_logical_txn_open);
                f Writer_thread_alive;
                f W_awaiting_commit;
              ])))

(** S2 is not manufactured, part one: the hazard premise really is reachable -
    [a]'s [commit()] returned [Ok] and its [sync_persist()] returned while [w]
    is still only inside the open physical transaction
    (layered_db.rs:118-124, :170-172, :247-249). *)
let acknowledged_and_barriered_yet_undurable_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "an acknowledged, barriered, not-yet-durable write is reachable" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f A_commit_acknowledged; f Writer_thread_alive; f W_awaiting_commit;
              ])))

(** S2 is not manufactured, part two: the loss itself is reachable - an
    acknowledged write that the loop's exit discarded with the physical
    transaction. *)
let an_acknowledged_write_is_actually_discarded () =
  with_sys (fun sys ->
      Alcotest.(check bool) "an acknowledged write really is discarded" true
        (Checker.satisfiable sys
           (Formula.And (f A_commit_acknowledged, f W_discarded))))

(** R2 contingency for [K_V2(exists_open_logical_txn)]: the knowledge is not
    rigid - there are reachable states where the stats consumer does not have
    it, namely every zero reading. *)
let census_knowledge_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "K_V2(exists open txn) fails somewhere reachable"
        true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V2, f Some_logical_txn_open)))))

(** R2 non-singleton class for [K_V2(exists_open_logical_txn)]: at a reading of
    one the consumer does NOT know that [a]'s commit has not been acknowledged.
    That is only possible because another reachable state shares its reading -
    the same [open_txn_count] - and has [a] committed. Measured class size at
    the operative reading: eight states. *)
let census_view_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "the V2 class at a reading of one holds more than one state" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Gauge_one,
                Formula.Not
                  (Formula.K (Validator.V2, Formula.Not (f A_commit_acknowledged)))
              ))))

(** R2 contingency for [K_V2(~issued(w) \/ on_disk(w))]: at a reading of one the
    consumer does not have it, because [w] may still be riding the open physical
    transaction. *)
let durability_certificate_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "K_V2(every issued write is on disk) fails somewhere reachable" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 ( Validator.V2,
                   Formula.Or (Formula.Not (f W_issued), f W_on_disk) )))))

(** R2 non-singleton class for [K_V2(~issued(w) \/ on_disk(w))]: at a zero
    reading the consumer does not know that [a]'s commit has not been
    acknowledged, so another reachable state shares its reading and has [a]
    committed. Measured class size at the operative reading: nine states. *)
let durability_certificate_view_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "the V2 class at a zero reading holds more than one state" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Gauge_zero,
                Formula.Not
                  (Formula.K (Validator.V2, Formula.Not (f A_commit_acknowledged)))
              ))))

(** R3 ignorance witness for S2 conjunct B1, undurable side: [a]'s commit and
    barrier have returned, the gauge reads one, and [w] is still inside the open
    physical transaction. *)
let overlapped_ignorance_witness_undurable_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "an acknowledged write still awaiting commit at a reading of one" true
        (Checker.satisfiable sys
           (Formula.conj
              [ f A_commit_acknowledged; f Gauge_one; f W_awaiting_commit ])))

(** R3 ignorance witness for S2 conjunct B1, durable side: the state that makes
    the first half ignorance rather than knowledge - same view for [a], but [w]
    already reached the backend on an earlier drain and the reading of one comes
    from a transaction [b] opened afterwards. *)
let overlapped_ignorance_witness_durable_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "an acknowledged write already on disk at a reading of one" true
        (Checker.satisfiable sys
           (Formula.conj [ f A_commit_acknowledged; f Gauge_one; f W_on_disk ])))

(** The ignorance of S2 conjunct B1 is two-sided at one and the same state: [a]
    knows neither that [w] is on disk nor that it is not. *)
let overlapped_ignorance_is_two_sided () =
  with_sys (fun sys ->
      Alcotest.(check bool) "V0 knows neither side at a reading of one" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f A_commit_acknowledged;
                f Gauge_one;
                Formula.Not (Formula.K (Validator.V0, f W_on_disk));
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f W_on_disk)));
              ])))

(** R3 ignorance witness for S2 conjunct B2, lost side: the thread is gone and
    [w] went with the dropped physical transaction. *)
let post_exit_ignorance_witness_lost_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "an acknowledged write discarded at the loop's exit is reachable" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f A_commit_acknowledged;
                Formula.Not (f Writer_thread_alive);
                f W_discarded;
              ])))

(** R3 ignorance witness for S2 conjunct B2, durable side: the thread is gone
    and [w] did reach the backend - identical view for [a], since [stats()]
    answers the same [DB thread gone] error either way
    (layered_db.rs:322, :329). *)
let post_exit_ignorance_witness_durable_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "an acknowledged write on disk after the thread is gone is reachable"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f A_commit_acknowledged;
                Formula.Not (f Writer_thread_alive);
                f W_on_disk;
              ])))

(** The ignorance of S2 conjunct B2 is two-sided at one and the same state. *)
let post_exit_ignorance_is_two_sided () =
  with_sys (fun sys ->
      Alcotest.(check bool) "V0 knows neither side once the thread is gone" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f A_commit_acknowledged;
                Formula.Not (f Writer_thread_alive);
                Formula.Not (Formula.K (Validator.V0, f W_on_disk));
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f W_on_disk)));
              ])))

(** R3 ignorance witness for S2 conjunct C, hostage side: [b] holds the open
    transaction, the gauge reads one, another task's acknowledged write is
    riding on it, and [b] does not know that. *)
let hostage_ignorance_witness_true_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "b holds a transaction carrying another task's write, unknown to b" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f B_holds_open_txn;
                f Gauge_one;
                f W_awaiting_commit;
                Formula.Not (Formula.K (Validator.V1, f W_awaiting_commit));
              ])))

(** R3 ignorance witness for S2 conjunct C, false side: the same view for [b] -
    its own transaction open, the same reading of one - with nothing riding on
    it. *)
let hostage_ignorance_witness_false_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "b holds a transaction carrying nothing, same reading" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f B_holds_open_txn;
                f Gauge_one;
                Formula.Not (f W_awaiting_commit);
              ])))

let () =
  Alcotest.run "backend_writer_thread"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Backend_writer_thread_statements.name `Quick
              (prove_one st))
          Backend_writer_thread_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "no-zero-reading-while-a-txn-is-open" `Quick
            no_zero_reading_while_a_txn_is_open;
          Alcotest.test_case "a-reading-of-two-means-both-writers-open" `Quick
            a_reading_of_two_means_both_writers_are_open;
          Alcotest.test_case "a-write-is-discarded-only-at-the-loops-exit" `Quick
            a_write_is_discarded_only_at_the_loops_exit;
          Alcotest.test_case "the-abandon-path-leaves-no-wedge" `Quick
            the_abandon_path_leaves_no_wedge;
          Alcotest.test_case "acknowledged-and-barriered-yet-undurable" `Quick
            acknowledged_and_barriered_yet_undurable_is_reachable;
          Alcotest.test_case "an-acknowledged-write-is-actually-discarded" `Quick
            an_acknowledged_write_is_actually_discarded;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "census-knowledge-is-contingent" `Quick
            census_knowledge_is_contingent;
          Alcotest.test_case "census-view-class-is-not-a-singleton" `Quick
            census_view_class_is_not_a_singleton;
          Alcotest.test_case "durability-certificate-is-contingent" `Quick
            durability_certificate_is_contingent;
          Alcotest.test_case "durability-certificate-class-is-not-a-singleton"
            `Quick durability_certificate_view_class_is_not_a_singleton;
          Alcotest.test_case "overlapped-ignorance-witness-undurable-side" `Quick
            overlapped_ignorance_witness_undurable_side;
          Alcotest.test_case "overlapped-ignorance-witness-durable-side" `Quick
            overlapped_ignorance_witness_durable_side;
          Alcotest.test_case "overlapped-ignorance-is-two-sided" `Quick
            overlapped_ignorance_is_two_sided;
          Alcotest.test_case "post-exit-ignorance-witness-lost-side" `Quick
            post_exit_ignorance_witness_lost_side;
          Alcotest.test_case "post-exit-ignorance-witness-durable-side" `Quick
            post_exit_ignorance_witness_durable_side;
          Alcotest.test_case "post-exit-ignorance-is-two-sided" `Quick
            post_exit_ignorance_is_two_sided;
          Alcotest.test_case "hostage-ignorance-witness-true-side" `Quick
            hostage_ignorance_witness_true_side;
          Alcotest.test_case "hostage-ignorance-witness-false-side" `Quick
            hostage_ignorance_witness_false_side;
        ] );
    ]
