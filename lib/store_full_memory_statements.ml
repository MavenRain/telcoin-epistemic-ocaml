(** The STORE_FULL_MEMORY family (S1, S2, S3): three statements about the
    [LayeredDatabase.full_memory] mode switch of telcoin-network, encoded over
    {!Store_full_memory_model}. File citations refer to
    Telcoin-Association/telcoin-network at git HEAD [0c59c15b].

    What was mined. The mode flag decides, per database, whether the in-memory
    layer is a durable MIRROR that every cursor-shaped read is served from
    (epoch and kad, composite_db.rs:33-34) or a transient WRITE BUFFER that the
    background thread evicts as it flushes (cache, :35). Under the first
    reading the physical layer is a write-only log except at [open_table]
    (layered_db.rs:347-356); under the second, [iter] has to union both layers
    (:427) or an unflushed key is invisible. S1 and S2 are the two halves of the
    first reading, S3 is the second.

    READING GUIDE FOR THE K OPERANDS. Every K in this family targets [durable(c)]
    or [batch_durable(b)] - which physical layer holds a record - and NO agent's
    view contains those bits, because the code exposes no API that reports them:
    [commit]'s doc comment warns the data "may not be committed on-disk yet"
    (layered_db.rs:118-124); [persist]/[sync_persist] are answered by a bare
    oneshot carrying no information (:463-495, :247-249); [LayeredDatabase::stats]
    exists (:317-333) but its [retained_inserts] counter is structurally 0 for a
    full-memory DB because the push at :217-219 is guarded by
    [mem_db.is_some()], and no consensus path calls it; and [iter] yields bare
    key/value pairs with no layer provenance (:420-429).

    - S1-B is the family's one POSITIVE K, and it is not a projection of V1's own
      view: [durable(c)] is false at reachable states where V1's view is
      identical to an operative one (the queued-write state [(cmem, cq)] versus
      the applied state [(cmem, cdur)] both project to [(index = true,
      point = true, restarted = false)]). It is not rigid either - [durable(c)]
      is false at the initial state and at every pre-write state. What makes the
      K true is a mechanism fact and nothing else: AFTER a restart the epoch mem
      layer is EXACTLY the disk image ([open_table]'s preload over a fresh empty
      [BTreeMap], layered_db.rs:347-356 with mem_db.rs:124-127), so a post-restart
      index hit certifies physical residency, whereas a pre-restart index hit does
      not. The operative view class is not a singleton: it spans every reachable
      cache-track configuration, which V1 cannot see, and the R2 test in
      test/t_store_full_memory.ml witnesses that directly.
    - S1-C, S2-B and S3-B are IGNORANCE conjuncts with concrete witness pairs;
      each has a [satisfiable] test in the contingency group.
    - S2-B is scoped to [~restarted] deliberately: S1-B proves the same agent DOES
      know durability after a restart, so the scope is load-bearing rather than
      decorative, and test/t_store_full_memory.ml pins that both ways. *)

open Store_full_memory_model

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

(** [weak_until p q] is [A\[p W q\]], which {!Formula} has no constructor for,
    written with the kernel identity [A\[p W q\] = ~E\[~q U (~p /\ ~q)\]]. *)
let weak_until p q =
  Formula.Not
    (Formula.Eu (Formula.Not q, Formula.And (Formula.Not p, Formula.Not q)))

(* S1 - restart-preload-is-the-only-recovery-of-round-indexed-visibility
   [safety].

   Conjunct A: AG( restarted /\ durable(c) -> index_visible(c) ).
   The consensus tables are TableHint::Epoch (lib.rs:88-95) and therefore live on
   the LayeredDatabase opened with full_memory = true (composite_db.rs:33), where
   contains_key (layered_db.rs:375-381), skip_to (:431-437), reverse_iter
   (:439-445), record_prior_to (:447-453) and iter (:423-429) are served from the
   mem layer ALONE. The only thing that puts on-disk contents into that layer
   after a restart is the preload inside open_table (:347-356), running over the
   fresh empty BTreeMap that MemDatabase::open_table has just installed
   (mem_db.rs:124-127). So this conjunct says: after a restart, everything the
   physical layer holds is back on the index surface.

   Conjunct B: AG( restarted /\ index_visible(c) -> K_V1( durable(c) ) ).
   The converse direction of the same fact, and the family's one positive K.
   Post-restart the mem layer is exactly the disk image, so for the primary's
   certificate-store reader an index hit CERTIFIES physical residency - an
   inference it cannot make before the restart, when a hit may be a still-queued
   write (layered_db.rs:391-396). The reader consuming this is the missing-parent
   computation (cert_manager.rs:156-158, header_validator.rs:213) and the DAG
   reconstruction at consensus/state.rs:98.

   Conjunct C: AG( index_visible(c) -> ~K_V2( durable(c) ) ).
   The same index hit tells a PEER nothing about durability. A peer's only route
   to a certificate is PrimaryRequest::MissingCertificates
   (network/message.rs:59-63), served by CertificateCollector, which enumerates
   rounds with next_round_number (cert_collector.rs:124 ->
   certificate_store.rs:423-435 -> skip_to, mem-only) and then reads the value
   with read_by_index (:137). The peer sees a certificate; it cannot see whether
   the serving node's copy is on disk or still in an mpsc queue that a restart
   would discard. Witness pair: (cmem, cq) with durable false and (cmem, cdur)
   with durable true, both projecting to View_peer true.

   MUTATION PIN. No_open_preload deletes the seed at layered_db.rs:350-354, so
   the restart transition rebuilds the epoch mem layer EMPTY and conjunct A is
   refuted at every post-restart state whose write had reached disk. The sibling
   repair is real and partial and is modelled: get (:383-389) still falls through,
   so point_visible(c) stays true after the mutation - which is exactly why this
   statement is about the index surface and not about read(). No other route
   re-seeds the mem layer (mem_db.rs:124-127, :92-111), and no read populates it
   (:30-38, :383-389). *)
let s_1 =
  let conjunct_a =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Restarted, atom Durable_c),
           atom Index_visible_c ))
  in
  let conjunct_b =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Restarted, atom Index_visible_c),
           Formula.K (Validator.V1, atom Durable_c) ))
  in
  let conjunct_c =
    Formula.Ag
      (Formula.Implies
         ( atom Index_visible_c,
           Formula.Not (Formula.K (Validator.V2, atom Durable_c)) ))
  in
  {
    name = "restart-preload-is-the-only-recovery-of-round-indexed-visibility";
    bucket = Statements.Safety;
    formula = Formula.conj [ conjunct_a; conjunct_b; conjunct_c ];
    antecedent = Formula.And (atom Restarted, atom Durable_c);
  }

(* S2 - full-memory-layer-is-never-evicted-so-index-and-point-reads-agree
   [safety].

   Conjunct A: AG( point_visible(c) -> index_visible(c) ).
   For the epoch DB the background writer thread is handed NO mem-layer handle:
   `let mem_db_clone = if full_memory { None } else { Some(mem_db.clone()) };`
   (layered_db.rs:311). That handle is the only eviction channel - the retention
   push at :217-219, the post-commit drain at :165-169 and the direct-write
   branch at :224-226 are all guarded by it, and clear_insert_mem itself is a
   best-effort remove with no mode test (:538-541). So the epoch mem layer is a
   monotone superset of the physical layer and the mem-only answer of
   contains_key/after_round can never say "absent" where the fall-through answer
   of get says "present". Only this direction is stated: the converse is rigid,
   since point_visible is by construction cmem \/ cdur, and a rigid conjunct
   would be worthless.

   Conjunct B: AG( point_visible(c) /\ ~restarted -> ~K_V1( durable(c) ) ).
   Before a restart the node's own reader cannot tell which layer answered.
   commit()'s doc comment says so in as many words (layered_db.rs:118-124),
   persist/sync_persist report nothing (:463-495, :247-249) and stats()'s
   retained_inserts is structurally 0 in this mode (:217-219). Witness pair:
   (cmem, cq) versus (cmem, cdur), both projecting to
   View_cert_reader (true, true, false). The ~restarted scope is load-bearing:
   S1-B proves the same agent DOES know durability after a restart.

   MUTATION PIN. No_full_memory_mode_test deletes the mode test at
   layered_db.rs:311, so the epoch DB's writer thread evicts the mirror as it
   flushes (:165-169, :224-226) and the applied-write state has cdur without
   cmem: point_visible true, index_visible false, conjunct A refuted. No sibling
   repairs it - no mem-only reader has a durable fall-back (:375-381, :412-461),
   nothing re-inserts on a read miss (:30-38, :383-389), and the startup preload
   cannot help because it runs strictly before these writes, which is also why
   this mutation leaves S1 standing. (No_open_preload refutes this statement too,
   from the other side; the pin below uses the mode test because that is the gate
   the statement is about.) *)
let s_2 =
  let conjunct_a =
    Formula.Ag
      (Formula.Implies (atom Point_visible_c, atom Index_visible_c))
  in
  let conjunct_b =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Point_visible_c, Formula.Not (atom Restarted)),
           Formula.Not (Formula.K (Validator.V1, atom Durable_c)) ))
  in
  {
    name = "full-memory-layer-is-never-evicted-so-index-and-point-reads-agree";
    bucket = Statements.Safety;
    formula = Formula.And (conjunct_a, conjunct_b);
    antecedent =
      Formula.And (atom Point_visible_c, Formula.Not (atom Restarted));
  }

(* S3 - cache-iteration-chains-the-unflushed-layer-so-orphan-batches-are-never-
   lost [liveness].

   Conjunct A: AG( cached(b) -> A[ cached(b) W (pool_restored(b) \/
   crash_lost(b)) ] ).
   A worker caches every batch it seals in OurNodeBatchesCache BEFORE waiting for
   quorum (worker.rs:293-299) and deliberately keeps the entry afterwards
   (:354-358); the epoch manager reads the table and clears it in the same breath
   (close_epoch.rs:57-63), re-injecting the transactions at :69-92. That table is
   TableHint::Cache (lib.rs:98-99) and so lives on the one LayeredDatabase opened
   with full_memory = false (composite_db.rs:35), where the writer thread DOES
   hold a mem handle and evicts the mirror as it flushes (layered_db.rs:311,
   :165-169, :224-226). The window between "inserted" and "flushed" is therefore
   a state in which the key exists in the mem layer alone, and the only thing
   that makes the boundary scan see it is the union at :427,
   `Box::new(self.db.iter::<T>().chain(self.mem_db.iter::<T>()))`. This conjunct
   says: once b is in the cache DB it STAYS there until its transactions are back
   in the pool - it is never cleared out from under itself.

   The crash disjunct is an honest escape, not a decoration. The writer thread
   and its mpsc queue die with the process (layered_db.rs:308-313) and the cache
   DB gets NO startup preload (open_table's seed is guarded by self.full_memory,
   :350-354), so a restart really does destroy an unflushed cache write - which
   close_epoch.rs:38-41 acknowledges ("Batches get orphaned when the epoch
   changes - or the node restarts"). The contingency group proves that branch is
   reachable, so the escape carries weight; and it does NOT rescue the mutation,
   because the mutation's loss happens with restarted false.

   Conjunct B: AG( cached(b) /\ ~boundary_done -> ~K_V3( batch_durable(b) ) ).
   While b sits in the cache the epoch manager cannot tell whether it is on disk
   or only in the unflushed mirror: iter yields bare (k, v) pairs with no layer
   provenance and its own doc comment (:420-422) says the layered iterator "will
   return all inserted elements even if some are duplicates while writes occur".
   That ignorance is the whole reason the union at :427 has to exist - a caller
   who knew which layer held the key could read that layer directly. Witness
   pair: (bmem, bq) versus (bdur), both projecting to
   View_cache_reader (true, false, false, _).

   MUTATION PIN. No_mem_chain_in_iter deletes `.chain(self.mem_db.iter::<T>())`
   at layered_db.rs:427. From the sealed-but-unflushed state the boundary scan
   then returns nothing, the clear at close_epoch.rs:63 wipes both layers, and
   the successor has cached(b) false, pool_restored(b) false and crash_lost(b)
   false - the weak-until is violated. No sibling repairs it: OurNodeBatchesCache
   has exactly two readers in the tree (the boundary iter at close_epoch.rs:60
   and the happy-path point remove at run_epoch.rs:543), NodeBatchesCache is
   cleared at close_epoch.rs:270 with no re-injection, the pool does not retain
   the transactions (worker.rs:322-326 states the converse), and sync_persist is
   called nowhere in the node or worker crates. The flush ordering IS the sibling
   path here, and the model has it: if the writer thread applies the insert before
   the boundary runs, db.iter() alone still finds b, so the mutation only bites in
   the window - which is why the statement is an AG over both orderings. *)
let s_3 =
  let conjunct_a =
    Formula.Ag
      (Formula.Implies
         ( atom Batch_cached,
           weak_until (atom Batch_cached)
             (Formula.Or (atom Pool_restored, atom Crash_lost_batch)) ))
  in
  let conjunct_b =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             (atom Batch_cached, Formula.Not (atom Boundary_done)),
           Formula.Not (Formula.K (Validator.V3, atom Batch_durable)) ))
  in
  {
    name = "cache-iteration-chains-the-unflushed-layer-so-orphan-batches-are-never-lost";
    bucket = Statements.Liveness;
    formula = Formula.And (conjunct_a, conjunct_b);
    antecedent =
      Formula.And (atom Batch_cached, Formula.Not (atom Boundary_done));
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
