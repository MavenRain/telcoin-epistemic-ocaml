(** The BACKEND_ENV_SPLIT family (S1, S2, S3): three statements about the
    per-[TableHint] split of a node's storage into separate physical
    environments, encoded over {!Backend_env_split_model}. File citations refer
    to Telcoin-Association/telcoin-network at git HEAD [0c59c15b].

    WHAT WAS MINED. [open_db] opens three backend environments on three paths
    (lib.rs:158-163 mdbx, :192-194 redb), wraps each in its own
    [LayeredDatabase] (composite_db.rs:31-37) and routes every table to exactly
    one of them by its [TableHint] constant (composite_db.rs:39-45,
    lib.rs:88-108). Each [LayeredDatabase] owns one unbounded channel and one
    background writer thread (layered_db.rs:306-315), that thread owns one
    physical write transaction (db_run's [let mut txn = None;], :179), and the
    physical txn commits only when the LAST overlapping logical txn on it ends
    ([end_txn]'s [if count <= 1], :155-174). Three consequences follow from that
    one split, and they are S1, S2 and S3.

    - S1 is the PROGRESS consequence: because the count, the physical txn and the
      thread are per environment, a Cache-hint logical txn cannot stand between
      the epoch environment's queued commit and its disk, and neither client can
      see the other environment's transaction state.
    - S2 is the ATOMICITY consequence: grouping clears in one composite write txn
      buys all-or-nothing WITHIN a hint and buys nothing ACROSS hints, because
      [CompositeDbTxMut::commit] is three sequential sends to three independent
      threads (composite_db.rs:250-261 over layered_db.rs:118-134) and not a
      two-phase commit. The epoch boundary's own route does not even group
      within a hint (close_epoch.rs:262-270).
    - S3 is the per-backend obligation that keeps a cleared table READABLE:
      redb's clear is delete-then-recreate inside one txn
      (redb/database.rs:58-63), and the cache environment is where a missing
      recreation surfaces, because it is the one [LayeredDatabase] opened with
      [full_memory = false] (composite_db.rs:35).

    READING GUIDE FOR THE K OPERANDS. Both agents are storage CLIENTS, and every
    K here targets a fact in an environment the knower does not read.

    - S2 conjunct D is the family's one POSITIVE K,
      [K_V1(index_cleared_durable)]. Its operand is not in V1's view: V1's view
      is [(route, Certificates reads empty, restarted)] and carries nothing about
      [CertificateDigestByRound]'s physical residency - no API on this path
      reports another table's disk state, and while the process lives the epoch
      environment is [full_memory = true] (composite_db.rs:33) so a certificate
      read is answered by the mem layer that [clear_table] already wiped
      (layered_db.rs:405-406, :412-418). It is not rigid either: the operand is
      false at the initial state, at every pre-commit state, and at every
      UNGROUPED post-restart state where the first of the two clears committed
      and the second did not. What makes the K true is one mechanism fact: on the
      grouped route both clears are applied into the SAME physical txn
      (db_run:238-242) and commit together (:161-164), so a post-restart
      certificate read that answers empty certifies the index cleared too. The
      operative view class is not a singleton - it spans the cross-environment
      tear, which V1 cannot see - and the R2 test in
      test/t_backend_env_split.ml witnesses that directly.
    - S1-C, S1-D and S2-E are IGNORANCE conjuncts, each with a concrete witness
      pair and a [satisfiable] test in the contingency group. S1-C and S2-E are
      V1 blind to the CACHE environment; S1-D is V2 blind to the EPOCH
      environment, and it is the sharper of the two because V2 is NOT blind to
      its own environment's durability (the cache layer is not full-memory, so
      its reads fall through to the backend, layered_db.rs:383-389, :412-418) -
      the ignorance is therefore a fact about the split and not about
      instrumentation.
    - The only per-layer instrument that could collapse any of this is
      [CompositeDatabase::stats] (composite_db.rs:47-54) over
      [LayeredDbStats { retained_inserts, open_txn_count }]
      (layered_db.rs:139-147, :250-255). Its only callers in the tree are that
      aggregator and the storage crate's own unit tests; no consensus, worker or
      node path calls it.
    - S3 carries NO K, deliberately. Every candidate operand there
      ([cache_table_absent], [cache_reports_empty]) is rigid on the pristine
      model, so a K over it would be trivially true and worthless under R1. *)

open Backend_env_split_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(* S1 - per-environment-writer-threads-decouple-commit-progress-and-knowledge
   [fairness].

   Workload-class isolation, in the only sense this slice actually provides it:
   the epoch (consensus) workload and the cache (network-fed batch) workload are
   different physical environments, so neither one's open transaction can sit
   between the other's queued commit and its disk, and neither client learns
   anything about the other's environment.

   Conjunct A: AG( epoch_commit_queued -> EX( certs_cleared_durable ) ).
   Once CompositeDbTxMut::commit has sent the epoch hint's CommitTxn
   (composite_db.rs:251-253 -> layered_db.rs:125-134), the epoch environment's
   own writer thread is the ONLY thing between that clear and disk: end_txn
   commits the physical txn as soon as this was the last open logical txn on it
   (layered_db.rs:155-174), and on the split the epoch environment has no
   Cache-hint co-tenant to keep the count above one. So disk is one thread step
   away no matter what the cache workload is doing.

   Conjunct B: AG( cache_commit_queued -> EX( cache_cleared_durable ) ).
   The mirror image, and it matters as much: the cache environment is the one
   fed by peers (batch_fetcher.rs:182-199 opens a composite write txn and writes
   NodeBatchesCache, a TableHint::Cache table, lib.rs:97), so this is the
   direction in which a shared environment would let the CONSENSUS workload
   delay the network workload. Two conjuncts, because the split is symmetric and
   a one-sided claim would understate it.

   Conjunct C: AG( epoch_commit_queued -> ~K_V1( cache_txn_open ) ).
   The certificate-store client cannot see whether a Cache-hint logical txn is
   open. There is exactly one instrument that reports it - stats()'s
   open_txn_count (composite_db.rs:47-54, layered_db.rs:139-147, :250-255) -
   and no consensus or node path calls it. Witness pair: the grouped state with
   the epoch commit queued and the cache clear staged, versus the same state
   before the cache clear was staged; both project to
   View_cert_client (Route_grouped, true, false).

   Conjunct D: AG( restarted /\ cache_cleared_durable ->
   ~K_V2( certs_cleared_durable ) ).
   The worker's batch-cache client sees its OWN environment's clear land - the
   cache environment is not full-memory (composite_db.rs:35), so its reads fall
   through to the physical backend (layered_db.rs:383-389, :412-418) - and still
   learns nothing about the epoch environment, because that is a different
   physical txn committed by a different thread. Witness pair: the post-restart
   states (certs_cleared = false, cache_cleared = true) and (true, true), both
   projecting to View_cache_client (route, true, true).

   MUTATION PIN. Merge_cache_into_epoch_env deletes the separate cache
   environment (lib.rs:162, :194) and passes the epoch environment in its place
   (lib.rs:165, :195), so get_db(TableHint::Cache) returns the same
   LayeredDatabase as get_db(TableHint::Epoch) (composite_db.rs:39-45). The
   Cache-hint logical txn then overlaps the EPOCH physical txn, end_txn's
   `if count <= 1` (layered_db.rs:160-173) sees two, and processing the epoch
   CommitTxn only decrements: conjunct A's EX has no witness at the state where
   the epoch commit is queued and the cache clear is still staged, and conjunct
   B's has none at the state where both commits are queued. Conjunct D flips too,
   because on the merged environment the two clears become durable in the same
   physical commit, so a cache-side reader that sees its clear landed now knows
   the certificate clear landed as well.

   No sibling path repairs the deletion. The physical txn has exactly one commit
   trigger, end_txn, reached only from DBMessage::CommitTxn and DBMessage::EndTxn
   (db_run:199-208); DBMessage::Shutdown breaks the loop WITHOUT committing
   (:256); persist/sync_persist send DBMessage::CaughtUp and are answered by a
   bare oneshot that forces nothing (layered_db.rs:463-495, :247-249); and there
   is no priority, no per-class budget and no fair queueing inside db_run, which
   is one `while let Ok(msg) = rx.recv()` FIFO loop (:185-265). The one genuine
   partial repair is READ visibility: the epoch layer is full_memory
   (composite_db.rs:33), so a certificate read keeps answering from memory
   however long the physical commit is deferred - the model HAS that repair
   (certs_read_empty is set at staging time, not at commit time) and S1 survives
   it only because it is about DURABILITY, which a restart tests and memory does
   not. *)
let s_1 =
  let conjunct_a =
    Formula.Ag
      (Formula.Implies
         (atom Epoch_commit_queued, Formula.Ex (atom Certs_cleared_durable)))
  in
  let conjunct_b =
    Formula.Ag
      (Formula.Implies
         (atom Cache_commit_queued, Formula.Ex (atom Cache_cleared_durable)))
  in
  let conjunct_c =
    Formula.Ag
      (Formula.Implies
         ( atom Epoch_commit_queued,
           Formula.Not (Formula.K (Validator.V1, atom Cache_txn_open)) ))
  in
  let conjunct_d =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Restarted, atom Cache_cleared_durable),
           Formula.Not (Formula.K (Validator.V2, atom Certs_cleared_durable)) ))
  in
  {
    name = "per-environment-writer-threads-decouple-commit-progress-and-knowledge";
    bucket = Statements.Fairness;
    formula = Formula.conj [ conjunct_a; conjunct_b; conjunct_c; conjunct_d ];
    antecedent = atom Epoch_commit_queued;
  }

(* S2 - table-hint-not-the-api-call-is-the-crash-atomicity-and-knowledge-boundary
   [safety].

   The epoch-boundary reset clears tables that live in two different physical
   databases (lib.rs:89-97 assigns the seven consensus tables TableHint::Epoch
   and the batch caches TableHint::Cache; composite_db.rs:39-45 routes them).
   This statement locates the atomicity boundary exactly: it is the hint, not the
   API call and not the node.

   Conjunct A: AG( restarted /\ grouped_txn ->
   ( certs_cleared_durable <-> index_cleared_durable ) ).
   On the grouped route both Epoch-hint clears are applied into the SAME physical
   write txn - LayeredDbTxMut::clear_table queues DBMessage::Clear
   (layered_db.rs:111-116) and db_run applies it with clr.clear_table_txn(txn)
   while a txn is open (:238-242) - and that txn commits once, in end_txn
   (:161-164). So a crash either finds both clears on disk or neither. This is
   CertificateStore::clear's shape verbatim (certificate_store.rs:438-447).

   Conjunct B: EF( restarted /\ grouped_txn /\ boundary_ran /\
   certs_cleared_durable /\ ~cache_cleared_durable ).
   The same grouping buys nothing across the hint boundary. CompositeDbTxMut
   holds one logical txn PER HINT, created lazily (composite_db.rs:170-199), and
   commit() commits them one after another with nothing between
   (composite_db.rs:250-261); each of those calls only SENDS CommitTxn to a
   different environment's thread and returns (layered_db.rs:118-134, whose own
   doc comment says "the commit is therefore asynchronous"). Three independent
   threads with three physical transactions is not a two-phase commit, so the
   interleaving in which the epoch commit landed and the cache commit did not is
   reachable - a half-reset node with no certificates and a populated batch
   cache.

   Conjunct C: EF( restarted /\ ungrouped_calls /\ boundary_ran /\
   certs_cleared_durable /\ ~index_cleared_durable ).
   And the route the epoch boundary actually takes does not even group within a
   hint. clear_consensus_db_for_next_epoch (close_epoch.rs:262-270) issues eight
   bare Database::clear_table calls with no transaction; each is routed by hint
   (composite_db.rs:101-103) into LayeredDatabase::clear_table
   (layered_db.rs:405-410), which wipes the mem layer and queues the clear, and
   with no physical txn open the writer thread executes each as its OWN backend
   transaction and commit (db_run:243-245 -> redb/database.rs:132-136,
   mdbx/database.rs:81-83 under MdbxDatabase::clear_table). So on that route even
   Certificates and its round index can tear apart. Conjunct A is therefore a
   statement about what grouping BUYS, not a description of what the boundary
   does today.

   Conjunct D: AG( restarted /\ grouped_txn /\ certs_read_empty ->
   K_V1( index_cleared_durable ) ).
   The knowledge half of conjunct A. After a restart the epoch environment's mem
   layer is exactly its disk image (open_table's preload, layered_db.rs:347-356,
   over the fresh map MemDatabase::open_table installs), so a certificate read
   that answers empty certifies the Certificates clear reached disk - and by
   conjunct A's shared physical txn, the round index with it. V1 never reads the
   index table; it infers it from the grouping.

   Conjunct E: AG( restarted /\ certs_read_empty ->
   ~K_V1( cache_cleared_durable ) ).
   The same reader learns nothing at all about the other environment, grouped or
   not. Witness pair: the two post-restart states that conjunct B separates,
   which agree on (route, certs read empty, restarted) and disagree on
   cache_cleared_durable.

   MUTATION PIN. Merge_cache_into_epoch_env deletes the separate cache
   environment (lib.rs:162, :194) and passes the epoch environment in its place,
   so the Cache-hint logical txn rides the EPOCH physical txn. end_txn then
   commits both clears in one physical commit (layered_db.rs:155-174): conjunct
   B's interleaving becomes unreachable and its EF is refuted, and conjunct E
   flips with it, because on the merged environment a post-restart certificate
   read that answers empty now determines the cache clear's fate too.

   No sibling path repairs the deletion, and none repairs a torn restart in the
   real code either - which is what makes the tear worth stating. Hunted: (a)
   startup compares nothing across environments, _open_mdbx and _open_redb
   (lib.rs:134-214) only open tables; (b) the full-memory reload
   (layered_db.rs:347-356) faithfully re-loads whatever each environment holds,
   so it propagates the tear rather than fixing it; (c) OurNodeBatchesCache is
   deliberately NOT cleared and is drained by the orphan recovery
   (close_epoch.rs:57-63, :259-273), which recovers OUR batches and reconciles
   nothing against the cleared certificate tables; (d) the Cache-hint consumer
   does have a fallback, but it is the wrong direction - batch_fetcher.rs:91-104
   fills MISSING rows from the consensus chain and has no path that discards
   extra stale ones; (e) the stale rows are keyed by batch digest (lib.rs:97) so
   they are content-addressed and look harmless, which is why nothing notices. *)
let s_2 =
  let conjunct_a =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Restarted, atom Route_is_grouped),
           Formula.And
             ( Formula.Implies
                 (atom Certs_cleared_durable, atom Index_cleared_durable),
               Formula.Implies
                 (atom Index_cleared_durable, atom Certs_cleared_durable) ) ))
  in
  let conjunct_b =
    Formula.Ef
      (Formula.conj
         [
           atom Restarted;
           atom Route_is_grouped;
           atom Boundary_ran;
           atom Certs_cleared_durable;
           Formula.Not (atom Cache_cleared_durable);
         ])
  in
  let conjunct_c =
    Formula.Ef
      (Formula.conj
         [
           atom Restarted;
           atom Route_is_ungrouped;
           atom Boundary_ran;
           atom Certs_cleared_durable;
           Formula.Not (atom Index_cleared_durable);
         ])
  in
  let conjunct_d =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [ atom Restarted; atom Route_is_grouped; atom Certs_read_empty ],
           Formula.K (Validator.V1, atom Index_cleared_durable) ))
  in
  let conjunct_e =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Restarted, atom Certs_read_empty),
           Formula.Not (Formula.K (Validator.V1, atom Cache_cleared_durable)) ))
  in
  {
    name =
      "table-hint-not-the-api-call-is-the-crash-atomicity-and-knowledge-boundary";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [ conjunct_a; conjunct_b; conjunct_c; conjunct_d; conjunct_e ];
    antecedent =
      Formula.conj
        [ atom Restarted; atom Route_is_grouped; atom Certs_read_empty ];
  }

(* S3 - redb-clear-recreates-the-cleared-table-inside-the-same-commit [safety].

   redb implements "clear" by DELETING the table and immediately re-creating it
   inside the same write transaction (redb/database.rs:58-63):
   `fn clear_table<T: Table>(&mut self) -> eyre::Result<()> { let td =
   TableDefinition::<KeyWrap<T::Key>, ValWrap<T::Value>>::new(T::NAME);
   self.tx.delete_table(td)?; self.tx.open_table(td)?; Ok(()) }`. open_table on a
   WriteTransaction is the create-if-absent form and both calls ride the one
   self.tx, so the pair is atomic at commit (:65-68). The mdbx sibling needs no
   such line because it empties in place (mdbx/database.rs:81-83).

   Conjunct A: AG( boundary_ran -> ~cache_table_absent ).
   Once the boundary has issued the Cache-hint clear, the table still exists.

   Conjunct B: AG( ~scan_faulted ).
   The observable consequence, and the reason conjunct A is not merely
   bookkeeping. The Cache-hint tables live on the one LayeredDatabase opened with
   full_memory = false (composite_db.rs:35), so iter goes to the physical backend
   (layered_db.rs:423-428, `self.db.iter::<T>().chain(self.mem_db.iter::<T>())`)
   and on redb that is
   `.open_table(td).expect("Missing table, DB not configured/opened correctly")`
   (redb/database.rs:155-160). The reader is real and needs no restart to reach
   it: the orphan drain iterates a Cache-hint table at every epoch boundary and
   clears it in the same breath (close_epoch.rs:57-63), so epoch N's clear is
   followed by epoch N+1's iter inside one process.

   Conjunct C: AG( cache_cleared_durable -> cache_reports_empty ).
   The emptiness instrument stays honest. LayeredDatabase::is_empty for a
   non-full-memory layer ANDs the backend answer in (layered_db.rs:412-418), and
   ReDB::is_empty returns the literal false when open_table fails
   (redb/database.rs:138-146) - so a deleted table reports "not empty" for a
   table that has no rows at all. One missing line produces three different
   failures: a panic in iter, an Err from get (:22-25) and a lie from is_empty.

   MUTATION PIN. No_redb_table_recreate deletes `self.tx.open_table(td)?;` at
   redb/database.rs:61. Applying the Cache-hint clear then leaves the table
   deleted: conjunct A is refuted at the post-clear state, the boundary scan
   transition becomes enabled and refutes conjunct B, and the is_empty answer
   inverts and refutes conjunct C.

   No sibling path repairs it in the running process. Hunted: (a)
   Database::open_table is startup-only - its only callers are _open_mdbx
   (lib.rs:167-182) and _open_redb (lib.rs:197-212), and
   LayeredDatabase::open_table (layered_db.rs:347-356) is reached only from
   there. A restart therefore DOES repair it, and the model has that repair (the
   restart transition puts the table back and clears the fault); the statement
   survives because the damage lands, and is observed, before it. (b) The mem
   layer does not mask it: this is the one environment with full_memory = false
   (composite_db.rs:35), so iter and is_empty both consult the backend
   (layered_db.rs:412-418, :423-428) - and even a full-memory layer would not
   mask it, because get falls through to the backend on a mem miss in BOTH modes
   (:383-389), and a just-cleared mem layer misses on every key. (c) The
   background writer runs the clear against the backend on both paths -
   clr.clear_table_txn(txn) inside an open txn and clr.clear_table(&db) without
   one (db_run:238-245) - so there is no route on which the delete does not
   reach disk. *)
let s_3 =
  let conjunct_a =
    Formula.Ag
      (Formula.Implies (atom Boundary_ran, Formula.Not (atom Cache_table_absent)))
  in
  let conjunct_b = Formula.Ag (Formula.Not (atom Scan_faulted)) in
  let conjunct_c =
    Formula.Ag
      (Formula.Implies (atom Cache_cleared_durable, atom Cache_reports_empty))
  in
  {
    name = "redb-clear-recreates-the-cleared-table-inside-the-same-commit";
    bucket = Statements.Safety;
    formula = Formula.conj [ conjunct_a; conjunct_b; conjunct_c ];
    antecedent = atom Boundary_ran;
  }

(** The family's statements. *)
let all = [ s_1; s_2; s_3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st = Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure degrades
    every row to [proved = false] rather than raising. *)
let reports () =
  let row proved st = { Report.name = st.name; bucket = st.bucket; proved } in
  Result.fold
    ~ok:(fun sys ->
      List.map
        (fun (st, r) ->
          row (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false) r) st)
        (prove_all sys))
    ~error:(fun Checker.Empty_init -> List.map (row false) all)
    (make ())
