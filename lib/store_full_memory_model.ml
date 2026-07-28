(** Finite interpreted system for the STORE_FULL_MEMORY family: the
    [LayeredDatabase.full_memory] mode switch, and the read-surface asymmetry it
    creates. File citations refer to Telcoin-Association/telcoin-network at git
    HEAD [0c59c15b]; every line range below was opened in that checkout.

    The modelled mechanism. A node's [CompositeDatabase] is three
    [LayeredDatabase]s, and the mode flag differs between them
    (composite_db.rs:31-37): [let epoch_db = LayeredDatabase::open(epoch_db,
    true); let kad_db = LayeredDatabase::open(kad_db, true); let cache_db =
    LayeredDatabase::open(cache_db, false);]. [TableHint] routes each table to
    one of them (composite_db.rs:39-45), so the consensus tables
    ([Certificates], [CertificateDigestByRound], [CertificateDigestByOrigin],
    ...) are [TableHint::Epoch] and run FULL MEMORY, while
    [OurNodeBatchesCache] is [TableHint::Cache] and runs LAYERED
    (lib.rs:88-108).

    That one flag decides three separate things, and this family is about all
    three at once.

    - WHICH LAYER THE READS COME FROM. Under [full_memory] every cursor-shaped
      read and every existence test is served from the IN-MEMORY layer alone:
      [contains_key] (layered_db.rs:375-381), [is_empty] (:412-418), [iter]
      (:423-429), [skip_to] (:431-437), [reverse_iter] (:439-445),
      [record_prior_to] (:447-453), [last_record] (:455-461). [get] alone is
      different: it is mem-first and then ALWAYS falls through to the physical
      DB (:383-389), in both modes. So [CertificateStore::read] (
      certificate_store.rs:213-215), [read_all] (:243-248) and [read_by_index]
      (:219-228) survive an empty mem layer, while [contains]/[multi_contains]
      (:230-239), [after_round] (:298-327, via [skip_to] at :302),
      [origins_after_round] (:332-341), [last_round] (:389-399),
      [highest_round_number] (:403-407), [last_round_number] (:411-419) and
      [next_round_number] (:423-435) do NOT.
    - WHETHER THE MEM LAYER IS EVER EVICTED. [LayeredDatabase::open] hands the
      background writer thread a mem handle ONLY in layered mode:
      [let mem_db_clone = if full_memory { None } else { Some(mem_db.clone()) };]
      (layered_db.rs:311). That handle is the sole eviction channel inside
      [db_run] - [if mem_db.is_some() { committed_inserts.push(ins); }]
      (:217-219), the post-commit drain [insert.clear_insert_mem(mem_db)] inside
      [end_txn] (:165-169), and the direct-write branch's
      [ins.clear_insert_mem(mem_db)] (:224-226), where [clear_insert_mem] is a
      best-effort [let _ = mem_db.remove::<T>(&self.key)] (:538-541). With
      [mem_db == None] all three are dead code, so for the epoch DB the mem
      layer is a monotone SUPERSET of the physical DB and the two read surfaces
      above agree.
    - WHAT [open_table] DOES AT STARTUP. [open_table] seeds the mem layer from
      the physical DB in full-memory mode only (layered_db.rs:347-356):
      [if self.full_memory { for (k, v) in self.db.iter::<T>() { let _ =
      self.mem_db.insert::<T>(&k, &v); } }]. Startup calls it for every table
      (lib.rs:165-183 mdbx, :195-211 redb) and [MemDatabase::open_table]
      installs a FRESH empty [BTreeMap] first (mem_db.rs:124-127), so after a
      restart the epoch mem layer is EXACTLY the disk image - nothing more and,
      absent the preload, nothing at all.

    The cache side is the mirror image. [iter] in LAYERED mode unions the two
    layers - [Box::new(self.db.iter::<T>().chain(self.mem_db.iter::<T>()))]
    (layered_db.rs:427) - because a key whose [DBMessage::Insert] is still
    queued on the writer thread (:391-396 -> :209-227) is in the mem layer only.
    That union is what makes the epoch-boundary orphan scan total: a worker
    caches every batch it seals in [OurNodeBatchesCache] before waiting for
    quorum (worker.rs:293-299, "Cache the batch early, avoid race conditions")
    and deliberately KEEPS the entry after quorum (:354-358), and the epoch
    manager reads the table and immediately clears it -
    [let mut orphan_batches: Vec<(BlockHash, Batch)> =
    self.consensus_db.iter::<OurNodeBatchesCache>().collect();
    self.consensus_db.clear_table::<OurNodeBatchesCache>()?;]
    (close_epoch.rs:57-63) - re-injecting the transactions at :69-92. A batch
    the scan misses is cleared with its transactions in no pool and no committed
    batch.

    Components (ten booleans; the pristine reachable graph is exactly 27
    states). The epoch triple tracks ONE certificate key [c] (the [Certificates]
    row and its round/origin index rows are written in one txn and share the
    hint, so they are collapsed into one key here); the cache triple tracks ONE
    sealed batch key [b].
    - [cmem] : [c] is in the epoch DB's mem layer - what [contains_key],
      [skip_to], [reverse_iter], [record_prior_to] and [iter] see
      (layered_db.rs:375-381, :423-461).
    - [cdur] : [c] is in the epoch DB's physical layer - what a restart reloads
      (:350-354) and what [get] falls through to (:383-389).
    - [cq] : the [DBMessage::Insert] for [c] is queued on the background writer
      thread and not yet applied (:391-396, applied at :209-227).
    - [bmem], [bdur], [bq] : the same three for [b] in the CACHE DB, where the
      writer thread does hold a mem handle and therefore evicts.
    - [restarted] : the one-shot process restart. The writer thread lives inside
      the process ([std::thread::spawn] at :312-313) behind a plain [mpsc]
      channel, so a restart discards whatever is still queued.
    - [sealed] : run history - the worker has executed
      [insert::<OurNodeBatchesCache>] for [b] at least once (worker.rs:294).
    - [boundary] : the epoch-close orphan scan and clear has run
      (close_epoch.rs:57-63).
    - [pool] : [b]'s transactions are back in this node's mempool
      (close_epoch.rs:69-92).

    Role mapping. The three knowledge agents are three DISTINCT reader roles,
    each with a real non-constant view; they are separate agents because they
    consume DISJOINT storage surfaces and none can see another's, which is a
    fact about the code rather than a modelling convenience.
    - V1 - THE PRIMARY'S CERTIFICATE-STORE READER on this node. Its view is
      [(index answer, point answer, restarted)]: the answer of the mem-only
      surface ([contains]/[multi_contains] at cert_manager.rs:156-158 and
      header_validator.rs:213, [after_round] at consensus/state.rs:98), the
      answer of the fall-through surface ([read]/[read_all], certifier.rs:147),
      and whether this process is a fresh one. It does NOT see [cdur] or [cq]:
      physical residency and queue residency have no reporting API on this path.
      [commit]'s own doc comment warns the data "may not be committed on-disk
      yet" (layered_db.rs:118-124); [persist]/[sync_persist] only send
      [DBMessage::CaughtUp] and are answered by a bare oneshot that carries no
      information (:463-495, :247-249); and [LayeredDatabase::stats] does exist
      (:317-333, :250-255) but its [retained_inserts] counter is STRUCTURALLY 0
      for a full-memory DB, because the push at :217-219 is guarded by
      [mem_db.is_some()] - and no consensus path calls it anyway. It also sees
      nothing of the cache DB.
    - V2 - A PEER PRIMARY FETCHING CERTIFICATES from this node. Its view is the
      single bit [(fetch answer)]. This is deliberately the INDEX answer, not
      the point answer: the only peer-facing route to a certificate is
      [PrimaryRequest::MissingCertificates] (network/message.rs:59-63), served
      by [CertificateCollector], whose round enumeration is
      [store.next_round_number(origin, current_round)] (cert_collector.rs:124,
      certificate_store.rs:423-435 -> [skip_to], mem-only) before
      [read_by_index] ever runs (cert_collector.rs:137). A peer therefore
      observes the mem-only surface and learns nothing about which layer holds
      the bytes.
    - V3 - THIS NODE'S EPOCH MANAGER / WORKER, the cache-DB reader. Its view is
      [(sealed, boundary, pool, restarted)]: it knows it sealed [b]
      (worker.rs:293-299), that it ran the boundary scan and clear
      (close_epoch.rs:57-63) and whether the scan handed it transactions to
      re-inject (:69-92). It does NOT see [bmem]/[bdur]/[bq]: [iter] yields bare
      [(k, v)] pairs with no layer provenance (layered_db.rs:423-429), and its
      own doc comment (:420-422) says the layered iterator "will return all
      inserted elements even if some are duplicates while writes occur".
    - V0 and V4..V9 are idle: constant blank view, never under K.

    Deliberate scope notes, stated so they are not mistaken for omissions.
    (i) The quorum-FAILURE route removes the cache entry on purpose
    (worker.rs:322-326, :346-351) because the batch builder leaves those
    transactions in the pool; every statement here is about a batch that reached
    quorum, so that route is out of scope by the antecedent. (ii) The happy-path
    eviction at run_epoch.rs:540-546 removes [b] once it reaches execution; that
    is the [consensed] case, also excluded by the antecedent, and it is a REMOVE
    rather than a recovery route. (iii) The crash budget is ONE, and the crash
    genuinely destroys an unflushed cache write - close_epoch.rs:38-41 says as
    much ("Batches get orphaned when the epoch changes - or the node restarts").
    S3 therefore carries that branch as an explicit escape rather than pretending
    it away. *)

(** The joint global state: the epoch-DB triple for certificate [c], the
    cache-DB triple for batch [b], and the four process/protocol flags. There is
    no separate "queued value" component: a queued insert can only have been
    queued by the step that set the corresponding mem bit, and no transition
    changes that mem bit while the queue bit stays set. *)
type state = {
  cmem : bool;
      (** [c] is in the epoch DB's mem layer: what [contains_key] (
          layered_db.rs:375-381), [skip_to] (:431-437), [reverse_iter]
          (:439-445), [record_prior_to] (:447-453) and [iter] (:423-429) return
          under [full_memory] *)
  cdur : bool;
      (** [c] is in the epoch DB's physical layer: what [open_table] reloads
          (layered_db.rs:350-354) and what [get] falls through to (:383-389) *)
  cq : bool;
      (** the [DBMessage::Insert] for [c] is queued on the background writer
          thread (layered_db.rs:391-396) and not yet applied (:209-227) *)
  bmem : bool;  (** [b] is in the CACHE DB's mem layer *)
  bdur : bool;  (** [b] is in the CACHE DB's physical layer *)
  bq : bool;
      (** the [DBMessage::Insert] for [b] is queued on the writer thread and not
          yet applied; in layered mode applying it also EVICTS the mem mirror
          (layered_db.rs:165-169, :224-226) *)
  restarted : bool;
      (** the one-shot process restart has happened; the writer thread and its
          [mpsc] queue died with the process (layered_db.rs:308-313) *)
  sealed : bool;
      (** run history: [insert::<OurNodeBatchesCache>] for [b] has executed at
          least once (worker.rs:294) *)
  boundary : bool;
      (** the epoch-close orphan scan and table clear has run
          (close_epoch.rs:57-63) *)
  pool : bool;
      (** [b]'s transactions have been re-injected into this node's mempool
          (close_epoch.rs:69-92) *)
}

(** Total deterministic comparison over ALL state fields, in field order
    [cmem, cdur, cq, bmem, bdur, bq, restarted, sealed, boundary, pool]. *)
let state_compare s1 s2 =
  let c0 = Bool.compare s1.cmem s2.cmem in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = Bool.compare s1.cdur s2.cdur in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Bool.compare s1.cq s2.cq in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare s1.bmem s2.bmem in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.bdur s2.bdur in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Bool.compare s1.bq s2.bq in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = Bool.compare s1.restarted s2.restarted in
              if Bool.not (Int.equal c6 0) then c6
              else
                let c7 = Bool.compare s1.sealed s2.sealed in
                if Bool.not (Int.equal c7 0) then c7
                else
                  let c8 = Bool.compare s1.boundary s2.boundary in
                  if Bool.not (Int.equal c8 0) then c8
                  else Bool.compare s1.pool s2.pool

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view; see the header for the full role mapping and the
    grounding of every exclusion.

    [View_cert_reader] is V1, the primary's certificate-store reader:
    [(index answer, point answer, restarted)], excluding [cdur] and [cq] because
    no API on this path reports physical or queue residency
    (layered_db.rs:118-124, :463-495, :217-219).

    [View_peer] is V2, a peer primary fetching certificates: the single
    [(fetch answer)] bit, which is the INDEX answer because
    [CertificateCollector] enumerates rounds with [next_round_number]
    (cert_collector.rs:124 -> certificate_store.rs:429 -> [skip_to], mem-only)
    before it ever reads a value.

    [View_cache_reader] is V3, this node's epoch manager / worker:
    [(sealed, boundary, pool, restarted)], excluding [bmem], [bdur] and [bq]
    because [iter] yields bare key/value pairs with no layer provenance
    (layered_db.rs:420-429).

    [View_idle] is the constant blank view of the non-agents V0 and V4..V9. *)
type view =
  | View_cert_reader of bool * bool * bool
      (** V1: (index answer, point answer, restarted) *)
  | View_peer of bool  (** V2: the fetch answer for [c] *)
  | View_cache_reader of bool * bool * bool * bool
      (** V3: (sealed, boundary, pool, restarted) *)
  | View_idle  (** the constant blank view of the non-agents V0, V4..V9 *)

(** Total deterministic order over ALL fields of the certificate reader's view. *)
let view_cert_compare (i, p, r) (i', p', r') =
  let c0 = Bool.compare i i' in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = Bool.compare p p' in
    if Bool.not (Int.equal c1 0) then c1 else Bool.compare r r'

(** Total deterministic order over ALL fields of the cache reader's view. *)
let view_cache_compare (s, b, p, r) (s', b', p', r') =
  let c0 = Bool.compare s s' in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = Bool.compare b b' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Bool.compare p p' in
      if Bool.not (Int.equal c2 0) then c2 else Bool.compare r r'

(** Total order on views: [View_idle] < [View_cert_reader] < [View_peer] <
    [View_cache_reader], with the field-wise order within each constructor.
    Every constructor pair is spelled: no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_cert_reader _ | View_peer _ | View_cache_reader _) -> -1
  | (View_cert_reader _ | View_peer _ | View_cache_reader _), View_idle -> 1
  | View_cert_reader (i, p, r), View_cert_reader (i', p', r') ->
      view_cert_compare (i, p, r) (i', p', r')
  | View_cert_reader _, (View_peer _ | View_cache_reader _) -> -1
  | (View_peer _ | View_cache_reader _), View_cert_reader _ -> 1
  | View_peer x, View_peer y -> Bool.compare x y
  | View_peer _, View_cache_reader _ -> -1
  | View_cache_reader _, View_peer _ -> 1
  | View_cache_reader (s, b1, p, r), View_cache_reader (s', b1', p', r') ->
      view_cache_compare (s, b1, p, r) (s', b1', p', r')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1, V2 and V3 are the knowledge agents with real,
    non-constant views; V0 and V4..V9 are idle non-agents with the constant
    blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V1 -> View_cert_reader (s.cmem, s.cmem || s.cdur, s.restarted)
  | Validator.V2 -> View_peer s.cmem
  | Validator.V3 -> View_cache_reader (s.sealed, s.boundary, s.pool, s.restarted)
  | Validator.V0 | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7
  | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at HEAD [0c59c15b] *)
  | No_open_preload
      (** delete the startup seed in [LayeredDatabase::open_table] -
          [if self.full_memory { for (k, v) in self.db.iter::<T>() { let _ =
          self.mem_db.insert::<T>(&k, &v); } }] (layered_db.rs:350-354). The
          restart transition then rebuilds the epoch mem layer as EMPTY instead
          of as the disk image, so a certificate that is on physical disk is
          invisible to [contains]/[after_round]/[next_round_number] while
          [read] still returns it.

          Why no sibling path repairs it, hunted and found only a PARTIAL one -
          which is exactly why S1 is scoped to the INDEX surface. (a) [get]
          (layered_db.rs:383-389) falls through to the physical DB in both
          modes, so [CertificateStore::read] (certificate_store.rs:213-215),
          [read_all] (:243-248) and [read_by_index] (:219-228) keep working;
          the model HAS this repair - [Point_visible_c] stays true after the
          restart - and S1 conjunct A survives it only by being about
          [Index_visible_c]. (b) Nothing else re-seeds the mem layer:
          [MemDatabase::open_table] installs a fresh empty [BTreeMap]
          (mem_db.rs:124-127) and is called only from
          [LayeredDatabase::open_table] and [MemDatabase::default]
          (mem_db.rs:92-111). (c) There is no read-through repopulation:
          [LayeredDbTx::get] (:30-38) and [LayeredDatabase::get] (:383-389)
          return the durable value WITHOUT writing the mirror. (d) The writer
          thread never writes the mem layer at all - it only removes from it
          (:165-169, :224-226). (e) There is no periodic re-sync: [db_run]'s
          only recurring work is [db.compact()] (:182-184, :258-264). *)
  | No_full_memory_mode_test
      (** delete the mode test at layered_db.rs:311, i.e. always pass
          [Some(mem_db.clone())] to [db_run] instead of
          [if full_memory { None } else { Some(mem_db.clone()) }]. The epoch
          DB's writer thread then evicts: [committed_inserts.push(ins)]
          (:217-219) and the drains at :165-169 and :224-226 stop being dead
          code, so applying the queued write also clears the mem mirror
          ([clear_insert_mem], :538-541). [get] keeps answering from the
          physical layer while every mem-only surface goes blind.

          Why no sibling path repairs it. (a) No mem-only reader has a durable
          fall-back to take up the slack: [contains_key] (:375-381), [is_empty]
          (:412-418), [iter] (:423-429), [skip_to] (:431-437), [reverse_iter]
          (:439-445), [record_prior_to] (:447-453) and [last_record] (:455-461)
          all take the [self.full_memory] branch unconditionally. (b) Nothing
          re-inserts on a read miss - see (c) of {!No_open_preload}. (c)
          [clear_insert_mem] itself is unguarded: a best-effort
          [let _ = mem_db.remove::<T>(&self.key)] with no test of which mode the
          key came from (:538-541). (d) The startup preload does NOT repair it
          either: the preload runs at [open_table], strictly before any of these
          writes, so it cannot restore a key evicted afterwards - which is why
          this mutation refutes S2 without touching S1. *)
  | No_mem_chain_in_iter
      (** delete [.chain(self.mem_db.iter::<T>())] from
          [LayeredDatabase::iter], leaving [Box::new(self.db.iter::<T>())]
          (layered_db.rs:427). Keys whose durable insert is still queued on the
          writer thread are then invisible to iteration, so the epoch-boundary
          orphan scan (close_epoch.rs:60) can miss a freshly sealed batch that
          the very next line (:63) then clears.

          Why no sibling path repairs it. (a) [OurNodeBatchesCache] has exactly
          two readers in the whole tree: the boundary [iter] at
          close_epoch.rs:60 and the point [remove] at run_epoch.rs:543. The
          latter is the happy-path eviction of an already-executed batch, not a
          recovery route - there is no [get] path that would rescue a missed
          iteration. (b) [NodeBatchesCache], the other copy the worker keeps
          (worker.rs:359), is cleared at close_epoch.rs:270 with no
          re-injection, and its own comment at :271-272 confirms only
          [OurNodeBatchesCache] is spared. (c) The transaction pool does not
          retain the transactions: worker.rs:322-326 states the converse - only
          on a quorum FAILURE does the builder leave them in the pool. (d)
          [sync_persist] (layered_db.rs:476-495), which would drain the queue
          before the scan, is called nowhere in the node or worker crates. (e)
          The duplicate risk the doc comment at :420-422 warns about is repaired
          downstream and only in the harmless direction: close_epoch.rs:69-92
          re-injects into the pool and worker.rs:355-358 notes that
          already-executed transactions are rejected as nonce-too-low, so the
          chain can only ever over-deliver. Under the mutation the OTHER
          direction - the [clear_table] at :63 that follows the scan - is
          modelled too, so the loss is permanent. *)

(** [enabled_list cond succs] is [succs] when the transition guard [cond] holds
    and the empty list otherwise. Every transition family below is one guard and
    one successor list, so no loop keyword and no mutable accumulator appears. *)
let enabled_list cond succs = if cond then succs else []

(** What the epoch mem layer holds for [c] after [open_table] runs at startup:
    the disk image under the pristine preload (layered_db.rs:350-354), nothing
    at all under {!No_open_preload}. Mutation-exhaustive, no wildcard arm. *)
let preloaded mut s =
  match mut with
  | Pristine | No_full_memory_mode_test | No_mem_chain_in_iter -> s.cdur
  | No_open_preload -> false

(** What [LayeredDatabase::iter] returns for the CACHE table at the epoch
    boundary: the union of both layers under the pristine [.chain]
    (layered_db.rs:427), the physical layer alone under
    {!No_mem_chain_in_iter}. Mutation-exhaustive, no wildcard arm. *)
let scan_finds mut s =
  match mut with
  | Pristine | No_open_preload | No_full_memory_mode_test -> s.bmem || s.bdur
  | No_mem_chain_in_iter -> s.bdur

(** T1 - the epoch write for [c]: [LayeredDatabase::insert]
    (layered_db.rs:391-396) writes the mem layer IMMEDIATELY and only QUEUES the
    physical write, which is why this sets [cq] rather than [cdur]. One write per
    run, before any restart. *)
let t1_epoch_insert s =
  enabled_list
    (Bool.not s.cmem && Bool.not s.cdur && Bool.not s.cq
   && Bool.not s.restarted)
    [ { s with cmem = true; cq = true } ]

(** T2 - the background writer thread applies the queued epoch write:
    [ins.insert(&db)] in the no-open-txn arm (layered_db.rs:220-227) or
    [insert_txn] plus the [current_txn.commit()] inside [end_txn] (:155-174,
    dispatched at :199-208). Under {!No_full_memory_mode_test} the same step also
    runs [clear_insert_mem] (:165-169, :224-226), evicting the mem mirror. *)
let t2_epoch_apply mut s =
  enabled_list s.cq
    (match mut with
    | Pristine | No_open_preload | No_mem_chain_in_iter ->
        [ { s with cq = false; cdur = true } ]
    | No_full_memory_mode_test ->
        [ { s with cq = false; cdur = true; cmem = false } ])

(** T4 - the worker seals [b] and caches it before waiting for quorum
    ([insert::<OurNodeBatchesCache>], worker.rs:293-299). Cache mode, so this too
    writes the mem layer and queues the physical write. One seal per run, within
    the epoch that is about to close. *)
let t4_cache_seal s =
  enabled_list
    (Bool.not s.sealed && Bool.not s.boundary && Bool.not s.restarted)
    [ { s with bmem = true; bq = true; sealed = true } ]

(** T5 - the writer thread applies the queued cache write. Cache mode hands the
    thread a mem handle (layered_db.rs:311), so applying the insert also evicts
    the mirror ([clear_insert_mem], :165-169 / :224-226, :538-541) - which is
    precisely why [iter] has to chain the two layers at :427. *)
let t5_cache_flush s =
  enabled_list s.bq [ { s with bq = false; bdur = true; bmem = false } ]

(** T3 - the one-shot process restart. The writer thread and its [mpsc] queue
    die with the process (layered_db.rs:308-313), so both queued inserts are
    lost; the epoch mem layer is rebuilt by [open_table] from the disk image
    (:347-356, empty under {!No_open_preload}) and the CACHE mem layer is rebuilt
    EMPTY because [open_table] preloads only when [full_memory]
    (composite_db.rs:35) - a genuine hole the code documents at
    close_epoch.rs:38-41. *)
let t3_restart mut s =
  enabled_list
    (Bool.not s.restarted)
    [
      {
        s with
        cmem = preloaded mut s;
        cq = false;
        bmem = false;
        bq = false;
        restarted = true;
      };
    ]

(** T6 - epoch close: scan [OurNodeBatchesCache] and clear it in the same breath
    (close_epoch.rs:57-63), re-injecting whatever the scan returned
    (:69-92). [clear_table] wipes the mem layer at once and queues the physical
    clear (layered_db.rs:405-410), so both layers end empty. *)
let t6_boundary mut s =
  enabled_list
    (Bool.not s.boundary)
    [
      {
        s with
        boundary = true;
        bmem = false;
        bdur = false;
        bq = false;
        pool = s.pool || scan_finds mut s;
      };
    ]

(** The transition relation: the six families unioned, one step per successor. A
    state with no successor at all is stutter-closed by the kernel, which is what
    makes [Af] and the weak-until encoding honest here. *)
let next_with mut s =
  List.concat
    [
      t1_epoch_insert s;
      t2_epoch_apply mut s;
      t3_restart mut s;
      t4_cache_seal s;
      t5_cache_flush s;
      t6_boundary mut s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: a freshly opened node with nothing written, nothing
    queued, nothing sealed and no boundary yet. *)
let initial =
  {
    cmem = false;
    cdur = false;
    cq = false;
    bmem = false;
    bdur = false;
    bq = false;
    restarted = false;
    sealed = false;
    boundary = false;
    pool = false;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Index_visible_c
      (** the mem-only surface sees [c]: [contains]/[multi_contains]
          (certificate_store.rs:230-239), [after_round] (:298-327),
          [next_round_number] (:423-435), [highest_round_number] (:403-407) -
          all routed to the mem layer by layered_db.rs:375-381 and :423-461 *)
  | Point_visible_c
      (** the fall-through surface sees [c]: [read] (certificate_store.rs:213-215),
          [read_all] (:243-248), [read_by_index] (:219-228), all via
          [LayeredDatabase::get] (layered_db.rs:383-389) *)
  | Durable_c
      (** [c] is in the epoch DB's physical layer, i.e. it survives a restart
          (layered_db.rs:350-354) *)
  | Epoch_write_queued
      (** the [DBMessage::Insert] for [c] is still on the writer thread's queue
          (layered_db.rs:391-396, applied at :209-227) *)
  | Restarted  (** this node's one-shot process restart has happened *)
  | Batch_sealed
      (** the worker has cached [b] in [OurNodeBatchesCache] (worker.rs:294) *)
  | Batch_cached
      (** [b] is still in some layer of the cache DB, i.e. the boundary scan
          could in principle still find it *)
  | Batch_durable  (** [b] is in the cache DB's physical layer *)
  | Boundary_done
      (** the epoch-close scan-and-clear has run (close_epoch.rs:57-63) *)
  | Pool_restored
      (** [b]'s transactions are back in this node's mempool
          (close_epoch.rs:69-92) *)
  | Crash_lost_batch
      (** [b] was sealed but the process restarted while its physical write was
          still queued, so it is in neither layer and was never re-injected.
          This is the hole close_epoch.rs:38-41 acknowledges ("or the node
          restarts"), carried as an explicit escape in S3 rather than hidden. *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Index_visible_c -> s.cmem
  | Point_visible_c -> s.cmem || s.cdur
  | Durable_c -> s.cdur
  | Epoch_write_queued -> s.cq
  | Restarted -> s.restarted
  | Batch_sealed -> s.sealed
  | Batch_cached -> s.bmem || s.bdur
  | Batch_durable -> s.bdur
  | Boundary_done -> s.boundary
  | Pool_restored -> s.pool
  | Crash_lost_batch ->
      s.restarted && s.sealed && Bool.not s.bmem && Bool.not s.bdur
      && Bool.not s.pool

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Index_visible_c -> "index_visible(c)"
  | Point_visible_c -> "point_visible(c)"
  | Durable_c -> "durable(c)"
  | Epoch_write_queued -> "epoch_write_queued(c)"
  | Restarted -> "restarted"
  | Batch_sealed -> "sealed(b)"
  | Batch_cached -> "cached(b)"
  | Batch_durable -> "batch_durable(b)"
  | Boundary_done -> "boundary_done"
  | Pool_restored -> "pool_restored(b)"
  | Crash_lost_batch -> "crash_lost(b)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation ({!Denote}, lib/internal/DESIGN.md), pinned to
    agree with {!System} at every reachable world by
    test/t_store_full_memory_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: single initial state, mutation-
    parameterized transitions, the three-agent view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
