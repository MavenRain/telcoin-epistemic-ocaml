(** Finite interpreted system for the BACKEND_ENV_SPLIT family: the deliberate
    split of a node's storage into SEPARATE PHYSICAL ENVIRONMENTS, one per
    [TableHint], and the three things that split decides - which physical
    transaction a write rides, which background thread commits it, and which
    table handle survives a clear. File citations refer to
    Telcoin-Association/telcoin-network at git HEAD [0c59c15b]; every line range
    below was opened in that checkout.

    THE MODELLED MECHANISM. [open_db] opens THREE backend environments on three
    distinct paths - [store_path.join("epoch")], [join("kad")], [join("cache")]
    (lib.rs:158-163 for mdbx, :192-194 for redb) - and hands them to
    [CompositeDatabase::open], which wraps each in its own [LayeredDatabase]
    (composite_db.rs:31-37):
    [let epoch_db = LayeredDatabase::open(epoch_db, true); let kad_db =
    LayeredDatabase::open(kad_db, true); let cache_db =
    LayeredDatabase::open(cache_db, false);]. Every table is routed to exactly
    one of them by its [TableHint] constant, with no shared path
    (composite_db.rs:39-45):
    [fn get_db(&self, hint: TableHint) -> &LayeredDatabase<DB> { match hint {
    TableHint::Epoch => &self.inner.epoch_db, TableHint::Kad =>
    &self.inner.kad_db, TableHint::Cache => &self.inner.cache_db } }]. The eight
    tables the epoch boundary resets straddle that routing: [LastProposed],
    [Votes], [Certificates], [CertificateDigestByRound],
    [CertificateDigestByOrigin], [ProposedCertificates] and [Payload] are
    [TableHint::Epoch] (lib.rs:89-95) while [NodeBatchesCache] and
    [OurNodeBatchesCache] are [TableHint::Cache] (lib.rs:97-99).

    WHY THE SPLIT IS LOAD-BEARING. Each [LayeredDatabase] spawns exactly ONE
    background writer thread behind its OWN unbounded channel
    (layered_db.rs:306-315): [let (tx, rx) = mpsc::channel(); ... let thread =
    Some(Arc::new(std::thread::spawn(move || db_run(db_cloned, mem_db_clone,
    rx))));]. That thread owns one physical write transaction ([db_run]'s local
    [let mut txn = None;], :179, opened at :191-192) and commits it only when the
    LAST overlapping logical transaction ends - [end_txn], :155-174:
    [if count <= 1 { current_txn.commit() } else { *txn = Some((current_txn,
    count - 1)) }]. So within one environment, durability is COUPLED: one
    writer's commit waits for every other open logical txn there. Across
    environments it is not coupled at all, because there are three counts, three
    physical transactions and three threads. The backends themselves are
    single-writer - redb says so verbatim at redb/database.rs:104-106 ("ReDb can
    only allows one write txn at a time ... Note that the LayeredDatabase handles
    this issues") and mdbx serialises through [begin_rw_txn]
    (mdbx/database.rs:165-167) - which is exactly why the code buys isolation by
    opening three environments rather than by scheduling inside one.

    THE COMMIT PATH IS THREE SENDS, NOT A BARRIER. A composite write txn creates
    at most one per-hint logical txn, lazily on first use
    (composite_db.rs:170-199), and [CompositeDbTxMut::commit] commits them one
    after another with nothing between (composite_db.rs:250-261):
    [if let Some(tx) = self.epoch_tx { tx.commit()?; } if let Some(tx) =
    self.kad_tx { tx.commit()?; } if let Some(tx) = self.cache_tx {
    tx.commit()?; }]. Each of those is [LayeredDbTxMut::commit]
    (layered_db.rs:118-134), which only SENDS [DBMessage::CommitTxn] to that
    environment's thread and returns - its own doc comment says "the commit is
    therefore asynchronous: when this returns, the data may not be committed
    on-disk yet". Three sends to three independent threads is not a two-phase
    commit, and nothing in the tree reconciles the three environments afterwards.

    THE TWO CLEAR ROUTES, both real and both modelled. (i) GROUPED - the clears
    ride ONE composite logical write txn, [CertificateStore::clear]'s shape
    (certificate_store.rs:438-447): [let mut txn = self.write_txn()?;
    txn.clear_table::<Certificates>()?; txn.clear_table::<CertificateDigestByRound>()?;
    txn.clear_table::<CertificateDigestByOrigin>()?; txn.commit()?;]. Every
    [clear_table] on a live logical txn becomes [DBMessage::Clear] applied INTO
    that environment's open physical txn ([clr.clear_table_txn(txn)],
    db_run:238-242), so same-hint clears are all-or-nothing at the physical
    commit. (ii) UNGROUPED - the epoch boundary's own route,
    [clear_consensus_db_for_next_epoch] (close_epoch.rs:262-270), eight bare
    [Database::clear_table] calls with NO transaction. Those route per hint
    (composite_db.rs:101-103) into [LayeredDatabase::clear_table]
    (layered_db.rs:405-410), which wipes the mem layer at once and queues a
    [DBMessage::Clear]; with no physical txn open the thread executes it as its
    OWN backend transaction and commit ([clr.clear_table(&db)], db_run:243-245 ->
    ReDB::clear_table redb/database.rs:132-136, MdbxDatabase::clear_table). So on
    the boundary route even two same-environment clears are two commits.
    NOTE, stated so it is not mistaken for an omission: no call site in the tree
    currently groups an Epoch-hint and a Cache-hint clear in one composite txn.
    [CompositeDbTxMut] is built to accept exactly that (composite_db.rs:170-199,
    :250-261) and both halves are exercised separately - the epoch pair at
    certificate_store.rs:438-447, the cache table at batch_fetcher.rs:182-199 -
    which is why S2 states what such a grouping would and would not buy.

    THE REDB CLEAR. [ReDbTxMut::clear_table] (redb/database.rs:58-63) implements
    "clear" as DELETE-then-RECREATE inside the one [self.tx]:
    [self.tx.delete_table(td)?; self.tx.open_table(td)?; Ok(())]. Both calls ride
    the same write transaction, so the pair is atomic at [commit]
    (redb/database.rs:65-68). The recreation is what keeps the table HANDLE
    alive; without it a committed clear leaves the table gone, and the cache
    environment is where that surfaces, because it is the one [LayeredDatabase]
    opened with [full_memory = false] (composite_db.rs:35) and therefore the one
    whose [iter] goes to the physical backend (layered_db.rs:423-428,
    [self.db.iter::<T>().chain(self.mem_db.iter::<T>())]) rather than being
    masked by memory. The concrete in-process reader is the orphan drain, which
    iterates a Cache-hint table at every epoch boundary and clears it in the same
    breath (close_epoch.rs:57-63): [self.consensus_db.iter::<OurNodeBatchesCache>()
    .collect(); ... self.consensus_db.clear_table::<OurNodeBatchesCache>()?;] -
    so the epoch-N clear is followed by the epoch-(N+1) iter with no restart in
    between. On a deleted redb table that iter is
    [.open_table(td).expect("Missing table, DB not configured/opened correctly")]
    (redb/database.rs:155-160), [get] propagates the error (:22-25) and
    [is_empty] returns the literal [false] (:138-146). The mdbx sibling needs no
    recreation because it empties in place (mdbx/database.rs:81-83,
    [self.inner.clear_db(self.get_dbi::<T>()?)]).

    COMPONENTS (eleven fields; the pristine reachable graph is exactly 38
    states). One Epoch-hint table pair is tracked - [Certificates] and its round
    index [CertificateDigestByRound], the two that [CertificateStore::clear]
    groups - plus one Cache-hint table standing for [NodeBatchesCache] /
    [OurNodeBatchesCache], which share the hint and hence the environment
    (lib.rs:97-99).
    - [route] : which clear route this run took, chosen once at the boundary.
    - [ep_stage] / [ca_stage] : the per-environment logical-txn pipeline of the
      grouped route - staged into the physical txn, [CommitTxn] queued, queued
      but deferred because a co-tenant logical txn is still open ([end_txn]'s
      [count <= 1] test, :160-173), committed.
    - [epoch_clear_issued] : the epoch mem layer has been wiped by [clear_table]
      (layered_db.rs:405-406, :111-116) - what a certificate read sees, since the
      epoch environment is [full_memory = true] (composite_db.rs:33).
    - [boundary_ran] : run history, the boundary issued the Cache-hint clear too.
    - [certs_cleared] / [idx_cleared] / [cache_cleared] : the clear is DURABLE in
      that environment's physical backend, i.e. it survives the crash.
    - [cache_tbl] : whether the redb Cache-hint table still exists
      (redb/database.rs:58-63).
    - [scan_faulted] : an epoch-boundary [iter] on the Cache-hint table hit
      [expect("Missing table, ...")] (redb/database.rs:155-160 via
      layered_db.rs:427).
    - [restarted] : the one-shot crash and restart. The writer threads and their
      [mpsc] queues die with the process (layered_db.rs:306-315), so everything
      staged in an uncommitted physical txn is lost, and startup reopens every
      table (lib.rs:167-182, :197-212), which recreates a deleted redb table.

    ROLE MAPPING. Two knowledge agents, each a distinct client role with a real
    non-constant view, separated because they consume DISJOINT storage surfaces
    in disjoint environments.
    - V1 - THE CERTIFICATE-STORE CLIENT (the primary). It issues
      [CertificateStore::clear] (certificate_store.rs:438-447), so it knows which
      route ran, and it reads [Certificates]. Its view is
      [(route, Certificates reads empty, restarted)]. It does NOT see
      [idx_cleared]: nothing on this path reports another table's physical
      residency, and the epoch environment is [full_memory = true], so a
      pre-restart read is answered from the mem layer that [clear_table] already
      wiped (layered_db.rs:405-406, :412-418) and says nothing about the disk. It
      does NOT see [cache_cleared] or [ca_stage] either: the only per-layer
      instrument is [CompositeDatabase::stats] (composite_db.rs:47-54) over
      [LayeredDbStats { retained_inserts, open_txn_count }]
      (layered_db.rs:139-147, produced at :250-255), and its only callers in the
      whole tree are that aggregator and the storage crate's own unit tests -
      no consensus or node path calls it.
    - V2 - THE WORKER'S BATCH-CACHE CLIENT. It reads the Cache-hint table
      ([multi_get::<NodeBatchesCache>], batch_fetcher.rs:84-89) and writes it
      (:182-199). Its view is [(route, cache reads empty, restarted)]. Because
      the cache environment is [full_memory = false], its point reads are
      mem-first then physical (layered_db.rs:383-389) and its emptiness answer is
      [mem.is_empty && db.is_empty] (:412-418), so the cache clear's DURABILITY
      is visible to it - and that is exactly why its ignorance of the EPOCH
      environment is a fact about the split rather than about instrumentation.
    - V0 and V3..V9 are idle: constant blank view, never under K.

    Both views carry [route], and that is not run history smuggled across the
    restart: which route a node takes is a STATIC property of the call site -
    [CertificateStore::clear] groups its clears in one composite write txn
    (certificate_store.rs:438-447) while
    [clear_consensus_db_for_next_epoch] issues bare per-table calls
    (close_epoch.rs:262-270) - so a client knows it as surely after a restart as
    before.

    DELIBERATE SCOPE NOTES. (i) The Kad environment is present in the code and in
    the header's citations but not in the state vector: kad writes use the
    non-transactional [Database::insert] (kad.rs:369-377) and so never open a
    logical txn, so they cannot participate in the overlap-count coupling S1 is
    about; a shared FIFO would delay them but strict FIFO delay is bounded and
    is not expressible as a CTL eventuality, so no statement here claims it.
    (ii) The crash budget is ONE and the restart is terminal: nothing in
    [_open_mdbx] / [_open_redb] (lib.rs:134-214) compares the three environments
    against each other, so a torn restart is not repaired and a second epoch adds
    no new shape. (iii) [OurNodeBatchesCache] is deliberately NOT cleared by the
    boundary reset (close_epoch.rs:259-273) and is drained by the orphan recovery
    at :57-63; that recovers OUR batches, it does not reconcile the Cache-hint
    tables against the cleared certificate tables, so it is not a repair path for
    S2 and is modelled only as the reader that S3's scan represents.
    (iv) BACKEND I/O FAILURE is out of scope, and it is a real omission worth
    naming: [end_txn] swallows a failed physical commit -
    [if let Err(e) = current_txn.commit() { tracing::error!(...) }]
    (layered_db.rs:161-164) - with no retry anywhere, so a disk error would leave
    a queued commit permanently non-durable and would refute S1 conjunct A in the
    real system as well as in a model that had it. S1 is therefore a statement
    about what the ENVIRONMENT SPLIT does and does not gate, not a claim about
    backend reliability; the mutation it is pinned by removes the split and
    nothing else. *)

(** Which API shape issued this run's epoch-boundary clears. Chosen once, at the
    boundary, and never changed afterwards. *)
type route =
  | Route_unchosen
      (** the boundary has not begun; no clear has been issued yet *)
  | Route_grouped
      (** the clears ride ONE composite logical write txn, the shape of
          [CertificateStore::clear] (certificate_store.rs:438-447), with the
          per-hint logical txns created lazily (composite_db.rs:170-199) and
          committed in sequence (:250-261) *)
  | Route_ungrouped
      (** bare [Database::clear_table] calls with no transaction, the epoch
          boundary's own route (close_epoch.rs:262-270 ->
          composite_db.rs:101-103 -> layered_db.rs:405-410), each executed by the
          writer thread as its own backend txn and commit (db_run:243-245) *)

(** Total order index for {!route}. *)
let route_index = function
  | Route_unchosen -> 0
  | Route_grouped -> 1
  | Route_ungrouped -> 2

(** Total order on {!route}. *)
let route_compare a b = Int.compare (route_index a) (route_index b)

(** The pipeline of one environment's logical write txn under the grouped
    route. The intermediate {!St_pending} exists because [end_txn] commits the
    physical txn only when the last overlapping logical txn ends
    (layered_db.rs:155-174). *)
type stage =
  | St_idle  (** no logical txn on this environment yet *)
  | St_staged
      (** the clear has been applied INTO this environment's physical write txn
          ([clr.clear_table_txn(txn)], db_run:238-242) and the logical txn is
          still open, so the environment's overlap count includes it *)
  | St_sent
      (** [commit()] ran for this hint (composite_db.rs:251-259), so
          [DBMessage::CommitTxn] is queued on this environment's channel
          (layered_db.rs:125-134) but the thread has not processed it *)
  | St_pending
      (** the thread processed the [CommitTxn] and only DECREMENTED the count,
          because another logical txn on the same physical txn is still open
          ([else { *txn = Some((current_txn, count - 1)) }],
          layered_db.rs:170-172). Unreachable while the environments are split *)
  | St_done
      (** the physical txn committed ([current_txn.commit()],
          layered_db.rs:161-164), so this environment's staged clears are on
          disk *)

(** Total order index for {!stage}. *)
let stage_index = function
  | St_idle -> 0
  | St_staged -> 1
  | St_sent -> 2
  | St_pending -> 3
  | St_done -> 4

(** Total order on {!stage}. *)
let stage_compare a b = Int.compare (stage_index a) (stage_index b)

(** Equality on {!stage}, via the total order index. *)
let stage_equal a b = Int.equal (stage_index a) (stage_index b)

(** Whether a stage still counts as an OPEN logical txn for [end_txn]'s overlap
    count (layered_db.rs:160-173): staged and commit-queued do, the rest do
    not. Exhaustive over the finite sum, no wildcard arm. *)
let stage_is_open = function
  | St_idle -> false
  | St_staged -> true
  | St_sent -> true
  | St_pending -> false
  | St_done -> false

(** Whether the redb Cache-hint table still exists after a clear
    (redb/database.rs:58-63). *)
type tbl =
  | Tbl_present  (** [delete_table] was followed by [open_table] in the same txn *)
  | Tbl_absent
      (** the table was deleted and never recreated, so [iter] panics
          (redb/database.rs:155-160), [get] errors (:22-25) and [is_empty]
          answers the literal [false] (:138-146) *)

(** Total order index for {!tbl}. *)
let tbl_index = function Tbl_present -> 0 | Tbl_absent -> 1

(** Total order on {!tbl}. *)
let tbl_compare a b = Int.compare (tbl_index a) (tbl_index b)

(** Whether the Cache-hint table handle is gone. Exhaustive, no wildcard arm. *)
let tbl_is_absent = function Tbl_present -> false | Tbl_absent -> true

(** The joint global state: the clear route, the two environments' logical-txn
    pipelines, what a certificate read sees, the boundary's run history, the
    three per-table durability bits, the redb table handle, the scan fault and
    the one-shot restart. *)
type state = {
  route : route;  (** which clear route this run took *)
  ep_stage : stage;
      (** the EPOCH environment's grouped-route pipeline; always {!St_idle} on
          the ungrouped route, where no logical txn is ever opened *)
  ca_stage : stage;  (** the CACHE environment's grouped-route pipeline *)
  epoch_clear_issued : bool;
      (** [clear_table] has wiped the epoch environment's mem layer
          (layered_db.rs:405-406), which is what a [Certificates] read sees while
          the process lives, because that environment is [full_memory = true]
          (composite_db.rs:33) *)
  boundary_ran : bool;
      (** run history that survives the restart: this node issued the Cache-hint
          clear of the boundary sequence (close_epoch.rs:270, or the grouped
          equivalent) *)
  certs_cleared : bool;
      (** the [Certificates] clear is DURABLE in the epoch environment's backend *)
  idx_cleared : bool;
      (** the [CertificateDigestByRound] clear is durable in the same
          environment *)
  cache_cleared : bool;
      (** the Cache-hint clear is durable in the CACHE environment's backend *)
  cache_tbl : tbl;  (** whether the redb Cache-hint table still exists *)
  scan_faulted : bool;
      (** an epoch-boundary [iter] on the Cache-hint table hit
          [expect("Missing table, DB not configured/opened correctly")]
          (redb/database.rs:155-160, reached through layered_db.rs:427 because
          the cache environment is not full-memory) *)
  restarted : bool;
      (** the one-shot crash and restart: the writer threads and their [mpsc]
          queues died with the process (layered_db.rs:306-315) and startup
          reopened every table (lib.rs:167-182, :197-212) *)
}

(** Total deterministic comparison over ALL state fields, in field order
    [route, ep_stage, ca_stage, epoch_clear_issued, boundary_ran, certs_cleared,
    idx_cleared, cache_cleared, cache_tbl, scan_faulted, restarted]. *)
let state_compare s1 s2 =
  let c0 = route_compare s1.route s2.route in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = stage_compare s1.ep_stage s2.ep_stage in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = stage_compare s1.ca_stage s2.ca_stage in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare s1.epoch_clear_issued s2.epoch_clear_issued in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.boundary_ran s2.boundary_ran in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Bool.compare s1.certs_cleared s2.certs_cleared in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = Bool.compare s1.idx_cleared s2.idx_cleared in
              if Bool.not (Int.equal c6 0) then c6
              else
                let c7 = Bool.compare s1.cache_cleared s2.cache_cleared in
                if Bool.not (Int.equal c7 0) then c7
                else
                  let c8 = tbl_compare s1.cache_tbl s2.cache_tbl in
                  if Bool.not (Int.equal c8 0) then c8
                  else
                    let c9 = Bool.compare s1.scan_faulted s2.scan_faulted in
                    if Bool.not (Int.equal c9 0) then c9
                    else Bool.compare s1.restarted s2.restarted

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view; see the header for the full role mapping and the
    grounding of every exclusion.

    [View_cert_client] is V1, the primary's certificate-store client:
    [(route, Certificates reads empty, restarted)]. The route is its own act
    (it is the caller of [CertificateStore::clear], certificate_store.rs:439).
    It excludes [idx_cleared], [cache_cleared] and [ca_stage] because the epoch
    environment is full-memory, so a live read is answered by the mem layer that
    [clear_table] already wiped (layered_db.rs:405-406, :412-418), and because
    the only per-layer instrument, [CompositeDatabase::stats]
    (composite_db.rs:47-54 over layered_db.rs:139-147, :250-255), has no caller
    outside the storage crate's own tests.

    [View_cache_client] is V2, the worker's batch-cache client:
    [(route, cache reads empty, restarted)]. The cache environment is NOT
    full-memory (composite_db.rs:35), so its reads fall through to the physical
    backend (layered_db.rs:383-389, :412-418) and its own environment's
    durability IS visible to it; nothing it reads touches the epoch
    environment.

    [View_idle] is the constant blank view of the non-agents V0 and V3..V9. *)
type view =
  | View_cert_client of route * bool * bool
      (** V1: (route, [Certificates] reads empty, restarted) *)
  | View_cache_client of route * bool * bool
      (** V2: (route, Cache-hint table reads empty, restarted) *)
  | View_idle  (** the constant blank view of the non-agents V0, V3..V9 *)

(** Total deterministic order over ALL fields of a client view triple. *)
let view_triple_compare (r, a, b) (r', a', b') =
  let c0 = route_compare r r' in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = Bool.compare a a' in
    if Bool.not (Int.equal c1 0) then c1 else Bool.compare b b'

(** Total order on views: [View_idle] < [View_cert_client] < [View_cache_client],
    with the field-wise order within each constructor. Every constructor pair is
    spelled out: no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_cert_client _ | View_cache_client _) -> -1
  | (View_cert_client _ | View_cache_client _), View_idle -> 1
  | View_cert_client (r, x, y), View_cert_client (r', x', y') ->
      view_triple_compare (r, x, y) (r', x', y')
  | View_cert_client _, View_cache_client _ -> -1
  | View_cache_client _, View_cert_client _ -> 1
  | View_cache_client (r, x, y), View_cache_client (r', x', y') ->
      view_triple_compare (r, x, y) (r', x', y')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 and V2 are the knowledge agents with real, non-constant
    views; V0 and V3..V9 are idle non-agents with the constant blank view and
    never appear under K. *)
let view v s =
  match v with
  | Validator.V1 -> View_cert_client (s.route, s.epoch_clear_issued, s.restarted)
  | Validator.V2 -> View_cache_client (s.route, s.cache_cleared, s.restarted)
  | Validator.V0 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at HEAD [0c59c15b] *)
  | Merge_cache_into_epoch_env
      (** delete the separate CACHE environment - [let cache_db =
          MdbxDatabase::open(store_path.join("cache"), 4, CACHE_MAX,
          CACHE_GROWTH)] (lib.rs:162, and its redb twin [let cache_db =
          ReDB::open(store_path.join("cache"))] at :194) - and pass the epoch
          environment to [CompositeDatabase::open] in its place (lib.rs:165,
          :195), so that [LayeredDatabase::open] runs once for both
          (composite_db.rs:33-35) and [get_db(TableHint::Cache)] returns the SAME
          [LayeredDatabase] as [get_db(TableHint::Epoch)]
          (composite_db.rs:39-45). Transitions changed: the Cache-hint logical
          txn now overlaps the EPOCH physical txn, so [end_txn]'s
          [if count <= 1] test (layered_db.rs:160-173) sees two logical txns and
          the epoch commit is DEFERRED to {!St_pending} instead of firing, and
          when it finally fires it makes the epoch and cache clears durable
          TOGETHER, removing the interleaving in which one landed and the other
          did not.

          Why no sibling path repairs it, hunted in the real code. (a) There is
          no second commit trigger: [db_run] commits the physical txn only
          through [end_txn], reached from [DBMessage::CommitTxn] and
          [DBMessage::EndTxn] (:199-208), and [DBMessage::Shutdown] breaks the
          loop without committing (:256). (b) [persist]/[sync_persist]
          (:463-495) send [DBMessage::CaughtUp], which is answered by a bare
          oneshot (:247-249) and forces nothing. (c) There is no priority, no
          per-class budget and no fair queueing inside [db_run] - it is one
          [while let Ok(msg) = rx.recv()] FIFO loop (:185-265). (d) On the
          other side, nothing re-establishes the cross-environment invariant
          after a torn restart: [_open_mdbx]/[_open_redb] (lib.rs:134-214) only
          open tables, the full-memory reload (:347-356) faithfully propagates
          whatever each environment holds, [OurNodeBatchesCache] is deliberately
          left intact and drained for OUR batches only (close_epoch.rs:57-63,
          :259-273), and the Cache-hint consumer's fallback
          (batch_fetcher.rs:91-104) repairs MISSING rows from the consensus
          chain, never extra stale ones. So the split really is the only thing
          decoupling the two, which is what makes deleting it a live gate
          deletion in both directions. *)
  | No_redb_table_recreate
      (** delete [self.tx.open_table(td)?;] from [ReDbTxMut::clear_table]
          (redb/database.rs:61), leaving [self.tx.delete_table(td)?;] alone.
          Transition changed: applying the Cache-hint clear now moves
          [cache_tbl] to {!Tbl_absent} instead of leaving it present, which
          enables the boundary-scan fault transition and makes the [is_empty]
          answer a lie.

          Why no sibling path repairs it, hunted in the real code. (a)
          [Database::open_table] is startup-only: its only callers are
          [_open_mdbx] (lib.rs:167-182) and [_open_redb] (lib.rs:197-212), and
          [LayeredDatabase::open_table] (layered_db.rs:347-356) is reached only
          from there - a restart therefore DOES repair it, which the model has,
          and the statement survives only because the damage lands before that
          restart. (b) The mem layer does not mask it, because the Cache-hint
          tables live on the one [LayeredDatabase] opened with
          [full_memory = false] (composite_db.rs:35), whose [iter] reads the
          physical backend (layered_db.rs:423-428) and whose [is_empty] ANDs the
          backend answer in (:412-418); even a full-memory layer would not mask
          it, since [get] falls through to the backend on a mem miss in both
          modes (:383-389). (c) The in-process reader is real and needs no
          restart: the orphan drain iterates a Cache-hint table at the boundary
          and clears it in the same breath (close_epoch.rs:57-63), so epoch N's
          clear is followed by epoch N+1's iter inside one process. *)

(** [enabled_list cond succs] is [succs] when the transition guard [cond] holds
    and the empty list otherwise. Every transition family below is one guard and
    one successor list, so no loop keyword and no mutable accumulator appears. *)
let enabled_list cond succs = if cond then succs else []

(** Whether this mutation puts the Cache-hint tables in the EPOCH environment,
    so that the two share one channel, one writer thread, one physical txn and
    one overlap count. Mutation-exhaustive, no wildcard arm. *)
let shared_env mut =
  match mut with
  | Pristine | No_redb_table_recreate -> false
  | Merge_cache_into_epoch_env -> true

(** What the redb Cache-hint table handle looks like once the clear has been
    applied to the backend: still there under the pristine recreation
    (redb/database.rs:61), gone under {!No_redb_table_recreate}.
    Mutation-exhaustive, no wildcard arm. *)
let tbl_after_clear mut =
  match mut with
  | Pristine | Merge_cache_into_epoch_env -> Tbl_present
  | No_redb_table_recreate -> Tbl_absent

(** Whether this state is one the boundary can still act from: the process is
    alive. The scan fault is deliberately NOT a guard here - a stuck flag would
    make the fault state terminal and would refute other families' statements
    for the wrong reason. *)
let live s = Bool.not s.restarted

(** T0 - the boundary begins and picks its clear route. The grouped route is
    [CertificateStore::clear]'s shape (certificate_store.rs:438-447); the
    ungrouped route is [clear_consensus_db_for_next_epoch]
    (close_epoch.rs:262-270). Nothing else in the model depends on the choice
    being nondeterministic - it is a single init state so that both routes are
    reachable from it and the EF witnesses of S2 are stated at the one initial
    world. *)
let t0_choose_route s =
  enabled_list
    (live s && Int.equal 0 (route_compare s.route Route_unchosen))
    [ { s with route = Route_grouped }; { s with route = Route_ungrouped } ]

(** T1 - ungrouped: issue the two Epoch-hint clears (close_epoch.rs:265-266).
    [LayeredDatabase::clear_table] wipes the mem layer synchronously and queues
    one [DBMessage::Clear] per table (layered_db.rs:405-410), so the certificate
    read surface goes empty at once while nothing is on disk yet. *)
let t1_ungrouped_issue_epoch s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_ungrouped)
    && Bool.not s.epoch_clear_issued)
    [ { s with epoch_clear_issued = true } ]

(** T2 - ungrouped: the epoch writer thread executes the [Certificates] clear as
    its own backend transaction and commit ([clr.clear_table(&db)],
    db_run:243-245 -> redb/database.rs:132-136). *)
let t2_ungrouped_apply_certs s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_ungrouped)
    && s.epoch_clear_issued
    && Bool.not s.certs_cleared)
    [ { s with certs_cleared = true } ]

(** T3 - ungrouped: the same thread then executes the round-index clear, as a
    SECOND backend transaction and commit. The FIFO order of [db_run]
    (layered_db.rs:185) is why this follows T2 rather than racing it, and the
    gap between the two commits is the same-environment tear. *)
let t3_ungrouped_apply_index s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_ungrouped)
    && s.certs_cleared
    && Bool.not s.idx_cleared)
    [ { s with idx_cleared = true } ]

(** T4 - ungrouped: issue the Cache-hint clear (close_epoch.rs:270). It is
    routed by hint to the OTHER environment (composite_db.rs:101-103, :39-45),
    so it lands on a different channel and a different thread. *)
let t4_ungrouped_issue_cache s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_ungrouped)
    && s.epoch_clear_issued
    && Bool.not s.boundary_ran)
    [ { s with boundary_ran = true } ]

(** T5 - ungrouped: the CACHE environment's writer thread executes its clear,
    independently of anything the epoch thread has or has not done. Under
    {!No_redb_table_recreate} this is where the table handle disappears. *)
let t5_ungrouped_apply_cache mut s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_ungrouped)
    && s.boundary_ran
    && Bool.not s.cache_cleared)
    [ { s with cache_cleared = true; cache_tbl = tbl_after_clear mut } ]

(** T6 - grouped: stage the two Epoch-hint clears into the composite txn's epoch
    logical txn (certificate_store.rs:441-442 -> composite_db.rs:246-248,
    :176-183). The logical txn is created lazily on this first use and the
    clears are applied into the environment's physical txn
    (db_run:238-242). Both are staged in one step: they are adjacent statements
    with no observable state between them, and a crash before the commit loses
    both. *)
let t6_grouped_stage_epoch s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_grouped)
    && stage_equal s.ep_stage St_idle)
    [ { s with ep_stage = St_staged; epoch_clear_issued = true } ]

(** T7 - grouped: stage the Cache-hint clear into the composite txn's CACHE
    logical txn (composite_db.rs:191-196). Under the split that is a second
    environment; under {!Merge_cache_into_epoch_env} it is a second logical txn
    on the SAME physical txn. The guard requires the epoch stage to still be
    {!St_staged}: [CompositeDbTxMut::commit] takes [self] by value
    (composite_db.rs:250), so once any hint's commit has been sent the txn is
    gone and nothing more can be staged on it. *)
let t7_grouped_stage_cache mut s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_grouped)
    && stage_equal s.ca_stage St_idle
    && stage_equal s.ep_stage St_staged)
    [
      {
        s with
        ca_stage = St_staged;
        boundary_ran = true;
        cache_tbl = tbl_after_clear mut;
      };
    ]

(** T8 - grouped: [CompositeDbTxMut::commit] commits the epoch logical txn first
    (composite_db.rs:251-253), which only sends [DBMessage::CommitTxn]
    (layered_db.rs:125-134). The guard requires the Cache-hint clear to be staged
    already, because the grouped route is the WHOLE boundary sequence in one
    composite txn and [commit] is the last call in it
    (certificate_store.rs:439-445 is the in-tree instance of that shape). *)
let t8_grouped_commit_epoch s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_grouped)
    && stage_equal s.ep_stage St_staged
    && stage_equal s.ca_stage St_staged)
    [ { s with ep_stage = St_sent } ]

(** T9 - grouped: the same call then commits the cache logical txn
    (composite_db.rs:257-259). It is strictly after the epoch send, which is why
    the guard requires the epoch stage to have left {!St_staged}. *)
let t9_grouped_commit_cache s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_grouped)
    && stage_equal s.ca_stage St_staged
    && Bool.not (stage_equal s.ep_stage St_idle)
    && Bool.not (stage_equal s.ep_stage St_staged))
    [ { s with ca_stage = St_sent } ]

(** T10 - grouped: the EPOCH environment's writer thread processes its queued
    [CommitTxn]. [end_txn] commits the physical txn only when this was the last
    open logical txn on it ([if count <= 1], layered_db.rs:160-173); otherwise it
    merely decrements, which is {!St_pending}. Under the split the epoch
    environment has no co-tenant, so the commit always fires; under
    {!Merge_cache_into_epoch_env} the Cache-hint logical txn is a co-tenant and
    the commit is deferred. When the commit does fire on the merged environment
    it makes every staged clear durable at once, including a cache clear parked
    in {!St_pending}. *)
let t10_grouped_epoch_thread mut s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_grouped)
    && stage_equal s.ep_stage St_sent)
    (if shared_env mut && stage_is_open s.ca_stage then
       [ { s with ep_stage = St_pending } ]
     else
       let promote = shared_env mut && stage_equal s.ca_stage St_pending in
       [
         {
           s with
           ep_stage = St_done;
           certs_cleared = true;
           idx_cleared = true;
           ca_stage = (if promote then St_done else s.ca_stage);
           cache_cleared = (if promote then true else s.cache_cleared);
         };
       ])

(** T11 - grouped: the CACHE environment's writer thread processes its queued
    [CommitTxn], the mirror image of T10. Under the split this is a different
    thread with its own physical txn and its own count, so it fires regardless
    of what the epoch side is doing; under the merge it is the same count. *)
let t11_grouped_cache_thread mut s =
  enabled_list
    (live s
    && Int.equal 0 (route_compare s.route Route_grouped)
    && stage_equal s.ca_stage St_sent)
    (if shared_env mut && stage_is_open s.ep_stage then
       [ { s with ca_stage = St_pending } ]
     else
       let promote = shared_env mut && stage_equal s.ep_stage St_pending in
       [
         {
           s with
           ca_stage = St_done;
           cache_cleared = true;
           ep_stage = (if promote then St_done else s.ep_stage);
           certs_cleared = (if promote then true else s.certs_cleared);
           idx_cleared = (if promote then true else s.idx_cleared);
         };
       ])

(** T12 - the epoch-boundary scan of a Cache-hint table
    (close_epoch.rs:57-63), one shot per process. Under the pristine clear the
    table is there and the scan returns; with the handle deleted it hits
    [.open_table(td).expect("Missing table, DB not configured/opened
    correctly")] (redb/database.rs:155-160), reached because the cache
    environment is not full-memory (composite_db.rs:35, layered_db.rs:423-428).
    The guard is the deleted handle, so this transition is dead in the pristine
    model - which is exactly what S3 conjunct B asserts. *)
let t12_boundary_scan s =
  enabled_list
    (live s && s.boundary_ran
    && tbl_is_absent s.cache_tbl
    && Bool.not s.scan_faulted)
    [ { s with scan_faulted = true } ]

(** T13 - the one-shot crash and restart. The writer threads and their [mpsc]
    queues die with the process (layered_db.rs:306-315), so every logical txn and
    every uncommitted physical txn is lost and only the per-environment durable
    bits survive. Startup reopens every table (lib.rs:167-182, :197-212 ->
    composite_db.rs:68-70 -> layered_db.rs:347-356), which recreates a deleted
    redb table, and the epoch environment's mem layer is reloaded from its disk
    image, so a certificate read now reports exactly what committed there. *)
let t13_crash_restart s =
  enabled_list
    (live s && Bool.not (Int.equal 0 (route_compare s.route Route_unchosen)))
    [
      {
        s with
        restarted = true;
        ep_stage = St_idle;
        ca_stage = St_idle;
        epoch_clear_issued = s.certs_cleared;
        cache_tbl = Tbl_present;
        scan_faulted = false;
      };
    ]

(** The transition relation: the fourteen families unioned, one step per
    successor. A state with no successor at all is stutter-closed by the kernel,
    which is what makes [Ex] and [Af] honest here. *)
let next_with mut s =
  List.concat
    [
      t0_choose_route s;
      t1_ungrouped_issue_epoch s;
      t2_ungrouped_apply_certs s;
      t3_ungrouped_apply_index s;
      t4_ungrouped_issue_cache s;
      t5_ungrouped_apply_cache mut s;
      t6_grouped_stage_epoch s;
      t7_grouped_stage_cache mut s;
      t8_grouped_commit_epoch s;
      t9_grouped_commit_cache s;
      t10_grouped_epoch_thread mut s;
      t11_grouped_cache_thread mut s;
      t12_boundary_scan s;
      t13_crash_restart s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: a freshly opened node whose epoch boundary has not begun,
    with all three environments quiescent and every table present. *)
let initial =
  {
    route = Route_unchosen;
    ep_stage = St_idle;
    ca_stage = St_idle;
    epoch_clear_issued = false;
    boundary_ran = false;
    certs_cleared = false;
    idx_cleared = false;
    cache_cleared = false;
    cache_tbl = Tbl_present;
    scan_faulted = false;
    restarted = false;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Route_is_grouped
      (** the clears ride one composite logical write txn
          (certificate_store.rs:438-447) *)
  | Route_is_ungrouped
      (** the clears are bare [Database::clear_table] calls, the epoch
          boundary's own route (close_epoch.rs:262-270) *)
  | Epoch_commit_queued
      (** [DBMessage::CommitTxn] for the EPOCH environment's logical txn is on
          that environment's channel and unprocessed (layered_db.rs:125-134) *)
  | Cache_commit_queued
      (** the same for the CACHE environment's logical txn
          (composite_db.rs:257-259) *)
  | Cache_txn_open
      (** the Cache-hint logical txn is still counted open by [end_txn]'s
          overlap count (layered_db.rs:160-173) *)
  | Certs_cleared_durable
      (** the [Certificates] clear is on the epoch environment's disk *)
  | Index_cleared_durable
      (** the [CertificateDigestByRound] clear is on the same environment's disk *)
  | Cache_cleared_durable
      (** the Cache-hint clear is on the CACHE environment's disk *)
  | Certs_read_empty
      (** a [Certificates] read answers empty: the mem layer was wiped by
          [clear_table] while the process lives (layered_db.rs:405-406), and
          after a restart it is the disk image (:347-356) *)
  | Boundary_ran
      (** run history: this node issued the Cache-hint clear of the boundary
          sequence (close_epoch.rs:270) *)
  | Cache_table_absent
      (** the redb Cache-hint table was deleted and not recreated
          (redb/database.rs:58-63) *)
  | Cache_reports_empty
      (** [Database::is_empty] answers TRUE for the Cache-hint table: the handle
          exists and the physical clear landed (layered_db.rs:412-418 over
          redb/database.rs:138-146) *)
  | Scan_faulted
      (** an epoch-boundary [iter] on the Cache-hint table hit
          [expect("Missing table, ...")] (redb/database.rs:155-160) *)
  | Restarted  (** this node's one-shot crash and restart has happened *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Route_is_grouped -> Int.equal 0 (route_compare s.route Route_grouped)
  | Route_is_ungrouped -> Int.equal 0 (route_compare s.route Route_ungrouped)
  | Epoch_commit_queued -> stage_equal s.ep_stage St_sent
  | Cache_commit_queued -> stage_equal s.ca_stage St_sent
  | Cache_txn_open -> stage_is_open s.ca_stage
  | Certs_cleared_durable -> s.certs_cleared
  | Index_cleared_durable -> s.idx_cleared
  | Cache_cleared_durable -> s.cache_cleared
  | Certs_read_empty -> s.epoch_clear_issued
  | Boundary_ran -> s.boundary_ran
  | Cache_table_absent -> tbl_is_absent s.cache_tbl
  | Cache_reports_empty ->
      Bool.not (tbl_is_absent s.cache_tbl) && s.cache_cleared
  | Scan_faulted -> s.scan_faulted
  | Restarted -> s.restarted

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Route_is_grouped -> "grouped_txn"
  | Route_is_ungrouped -> "ungrouped_calls"
  | Epoch_commit_queued -> "epoch_commit_queued"
  | Cache_commit_queued -> "cache_commit_queued"
  | Cache_txn_open -> "cache_txn_open"
  | Certs_cleared_durable -> "certs_cleared_durable"
  | Index_cleared_durable -> "index_cleared_durable"
  | Cache_cleared_durable -> "cache_cleared_durable"
  | Certs_read_empty -> "certs_read_empty"
  | Boundary_ran -> "boundary_ran"
  | Cache_table_absent -> "cache_table_absent"
  | Cache_reports_empty -> "cache_reports_empty"
  | Scan_faulted -> "scan_faulted"
  | Restarted -> "restarted"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation ({!Denote}, lib/internal/DESIGN.md), pinned to
    agree with {!System} at every reachable world by
    test/t_backend_env_split_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: a single initial state, mutation-
    parameterized transitions, the two-agent view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
