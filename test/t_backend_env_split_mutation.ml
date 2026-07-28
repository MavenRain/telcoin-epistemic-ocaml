(** Confirm-by-mutation pins for the BACKEND_ENV_SPLIT family: every statement
    proves on the pristine model and REFUTES under the gate deletion it is about,
    and - so that a pin cannot pass because some other statement happened to flip
    - each statement is also asserted to SURVIVE the mutation it is not about.

    [Merge_cache_into_epoch_env] deletes the separate cache environment
    (lib.rs:162 mdbx, :194 redb) and passes the epoch environment to
    [CompositeDatabase::open] in its place (lib.rs:165, :195), so
    [get_db(TableHint::Cache)] returns the same [LayeredDatabase] as
    [get_db(TableHint::Epoch)] (composite_db.rs:39-45): one channel, one writer
    thread, one physical transaction, one overlap count. S1's [EX] conjuncts lose
    their witness at the co-tenancy states because [end_txn] only decrements when
    another logical txn is still open (layered_db.rs:160-173), and S2's
    cross-environment tear becomes unreachable because both clears now ride one
    physical commit. No sibling path repairs it: the physical txn has exactly one
    commit trigger ([end_txn], reached only from [DBMessage::CommitTxn] and
    [DBMessage::EndTxn], db_run:199-208, while [DBMessage::Shutdown] breaks the
    loop without committing at :256), [persist]/[sync_persist] send
    [DBMessage::CaughtUp] and are answered by a bare oneshot (:463-495, :247-249),
    and [db_run] is a single FIFO loop with no priority and no per-class budget
    (:185-265).

    [No_redb_table_recreate] deletes [self.tx.open_table(td)?;] from
    [ReDbTxMut::clear_table] (redb/database.rs:61). The Cache-hint table is then
    gone after a committed clear, which refutes S3's three conjuncts at once - the
    handle, the boundary [iter]'s [expect("Missing table, ...")]
    (redb/database.rs:155-160) and the [is_empty] literal [false] (:138-146). No
    sibling path repairs it in the running process: [Database::open_table] is
    startup-only (lib.rs:167-182, :197-212, layered_db.rs:347-356), and the mem
    layer cannot mask it because the Cache-hint environment is the one opened with
    [full_memory = false] (composite_db.rs:35). A restart does repair it, the
    model has that restart, and the statement survives because the boundary drain
    re-reads the table inside the same process (close_epoch.rs:57-63). *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Backend_env_split_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Backend_env_split_model.Checker.make
       (Backend_env_split_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Backend_env_split_statements.name name))
    Backend_env_split_statements.all

(** Whether the named statement proves under [mut], failing the test if the name
    is not one of the family's. *)
let proves_under mut name k =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          k
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Backend_env_split_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " flips to refuted under the mutation")
        false proved)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  proves_under Backend_env_split_model.Pristine name (fun proved ->
      Alcotest.(check bool) (name ^ " proves on the pristine model") true proved)

(** A control case: the statement still proves under a mutation it is NOT about,
    so the pin above is attributable to its own gate. *)
let survives_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " still proves under the unrelated mutation")
        true proved)

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "backend_env_split_mutation"
    [
      ( "separate-cache-environment",
        pin Backend_env_split_model.Merge_cache_into_epoch_env
          "per-environment-writer-threads-decouple-commit-progress-and-knowledge"
        @ pin Backend_env_split_model.Merge_cache_into_epoch_env
            "table-hint-not-the-api-call-is-the-crash-atomicity-and-knowledge-boundary"
      );
      ( "redb-clear-recreates-the-table",
        pin Backend_env_split_model.No_redb_table_recreate
          "redb-clear-recreates-the-cleared-table-inside-the-same-commit" );
      ( "controls",
        [
          Alcotest.test_case "s3-survives-environment-merge" `Quick
            (survives_under Backend_env_split_model.Merge_cache_into_epoch_env
               "redb-clear-recreates-the-cleared-table-inside-the-same-commit");
          Alcotest.test_case "s1-survives-redb-mutation" `Quick
            (survives_under Backend_env_split_model.No_redb_table_recreate
               "per-environment-writer-threads-decouple-commit-progress-and-knowledge");
          Alcotest.test_case "s2-survives-redb-mutation" `Quick
            (survives_under Backend_env_split_model.No_redb_table_recreate
               "table-hint-not-the-api-call-is-the-crash-atomicity-and-knowledge-boundary");
        ] );
    ]
