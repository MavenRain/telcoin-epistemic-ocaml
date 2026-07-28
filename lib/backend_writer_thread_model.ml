(** Finite interpreted system for the BACKEND_WRITER_THREAD family: the single
    background writer thread [db_run] that every [LayeredDatabase] owns, the
    overlap counter it keeps over one physical backend transaction, and the two
    ways that counter can stop meaning what its readers think it means. File
    citations refer to Telcoin-Association/telcoin-network at git HEAD
    [0c59c15b] (working tree); every line range below was opened in this
    checkout.

    THE MECHANISM, in the order the code runs it.

    - ONE PHYSICAL TXN, MANY LOGICAL ONES. [LayeredDatabase::open] spawns one
      thread running [db_run] (layered_db.rs:306-315) and hands every caller a
      [Sender] clone. [db_run]'s whole mutable state is
      [let mut txn = None] typed [Option<(DB::TXMut<'_>, u32)>]
      (layered_db.rs:179) - one physical backend transaction plus an overlap
      COUNT. [Database::write_txn] sends [DBMessage::StartTxn]
      (layered_db.rs:365-373) and the thread either bumps the count or opens the
      physical txn: [if let Some((_txn, count)) = &mut txn { *count += 1 } else
      { match db.write_txn() { Ok(ntxn) => txn = Some((ntxn, 1)), ... } }]
      (layered_db.rs:187-198). Every [DBMessage::Insert] goes into whatever txn
      is open, whoever sent it (layered_db.rs:209-219).
    - THE PHYSICAL COMMIT FIRES ONLY WHEN THE COUNT DRAINS. [end_txn] is the
      only commit point: [if let Some((current_txn, count)) = txn.take() { if
      count <= 1 { if let Err(e) = current_txn.commit() { ... } ... } else {
      *txn = Some((current_txn, count - 1)); } }] (layered_db.rs:155-174, commit
      at :161-164, the retained-insert / mem-mirror clear at :165-169, the
      not-yet branch at :170-172). It is dispatched from exactly two arms:
      [DBMessage::CommitTxn] (:199-201) and [DBMessage::EndTxn] (:202-208).
    - THE ABANDON PATH IS WHAT KEEPS THE COUNT HONEST. [LayeredDbTxMut::commit]
      sends [CommitTxn] only for the first caller across all clones
      ([if self.guard.mark_committed()], layered_db.rs:125-134, backed by the
      [AcqRel] swap at :52-58); a logical txn dropped WITHOUT commit is balanced
      by the guard instead: [impl<DB: Database> Drop for TxnGuard<DB> { fn
      drop(&mut self) { if !self.committed.load(Ordering::Acquire) { ... let _ =
      self.tx.send(DBMessage::EndTxn); } } }] (layered_db.rs:60-70, the send at
      :67). The struct's own doc states the consequence of losing it verbatim:
      "Without the end message a dropped txn would permanently skew the
      background thread's txn count - commits stop firing, writes stop
      persisting to disk, and retained inserts grow forever"
      (layered_db.rs:44-46).
    - SHUTDOWN LEAVES THE LOOP WITH THE TXN OPEN. [DBMessage::Shutdown => break]
      (layered_db.rs:256) exits [while let Ok(msg) = rx.recv()] (:185) without
      calling [end_txn]; the local [txn] is dropped at function exit and neither
      backend transaction wrapper has a [Drop] impl that could commit it - the
      declaration lists of crates/storage/src/mdbx/database.rs and
      crates/storage/src/redb/database.rs contain only [impl MdbxTxMut] (:49),
      [impl DbTx for MdbxTxMut] (:56), [impl DbTxMut for MdbxTxMut] (:67-89,
      [fn commit] at :85-88) and [impl Debug] (:32), [impl DbTx for ReDbTxMut]
      (:38), [impl DbTxMut for ReDbTxMut] (:45-69, [fn commit] at :65-68). The
      shutdown really can race a live logical txn: [LayeredDbTxMut] holds
      [mem_db], [db], [tx] and [guard] and NO [Arc<JoinHandle>]
      (layered_db.rs:72-78), so it does not keep the [LayeredDatabase] alive,
      while [Drop for LayeredDatabase] sends [Shutdown] as soon as the last
      database handle goes (:284-303, send at :288, join at :293-296).
    - THE ACKNOWLEDGEMENT IS NOT A DURABILITY POINT. [commit]'s own doc says so
      ("when this returns, the data may not be committed on-disk yet",
      layered_db.rs:118-124) and the write is already visible locally, because
      [insert] mirrors into the mem layer BEFORE queueing
      (layered_db.rs:96-102, mirror at :98) and every read is mem-first
      (:86-94, :383-389). The strongest barrier the API exports is no better:
      [persist] (:463-474) and [sync_persist] (:476-495) send
      [DBMessage::CaughtUp], whose arm is [let _ = tx.send(());]
      (:247-249) - a queue-drain acknowledgement that never touches [txn] and
      never commits.
    - THE ONLY WINDOW OUT OF THE THREAD IS A COUNTER. [DBMessage::Stats]
      answers [LayeredDbStats { retained_inserts, open_txn_count }]
      (layered_db.rs:250-255) built from [txn.as_ref().map(|(_, count)| ...)],
      and the struct's doc says what a reader is meant to conclude: "Should be 0
      whenever no write txn is outstanding; a value stuck above 0 means commits
      have stopped firing (wedged txn count)" (:137-147). [stats()] itself is
      :317-333 and returns [Err("DB thread gone, FATAL!")] once the thread has
      exited (:322, :329). Durability is NOT on that channel.

    WHICH DATABASE IS MODELLED, AND WHY IT DECIDES THE SECOND STATS FIELD. The
    modelled layer is one of the two [full_memory = true] layered databases -
    the epoch and kad stores of [CompositeDatabase::new]
    ([LayeredDatabase::open(epoch_db, true)], [(kad_db, true)],
    composite_db.rs:33-35). That choice is not cosmetic: [open] passes
    [let mem_db_clone = if full_memory { None } else { Some(mem_db.clone()) }]
    to the thread (layered_db.rs:311), so [mem_db] is [None] inside [db_run],
    the [if mem_db.is_some() { committed_inserts.push(ins) }] guard at :217-219
    never fires, [end_txn]'s mem-clearing loop at :165-169 is skipped, and
    [LayeredDbStats.retained_inserts] is therefore CONSTANTLY ZERO on this
    layer. Modelling the observer's view as [open_txn_count] alone is thus
    exact rather than a convenient omission - the other field carries no
    information here. It also settles the reads: with [mem_db] [None] on the
    thread side, [clear_insert_mem] (:538-541) never runs, so the mem mirror
    keeps [w] for the life of the process and every local read answers
    [Some(w)] in every branch (:98, :383-389).

    WHY THIS IS NOT THE own_durable FAMILY. That family models a plain
    [Database::insert] (layered_db.rs:391-396) whose queued message a PROCESS
    CRASH discards before the thread ever runs it. Here the thread DID run: the
    insert reached the physical txn, [commit()] returned [Ok], [sync_persist()]
    returned, and the write is still lost - because a second logical txn keeps
    the count above one, so [end_txn] takes its [else] branch (:170-172), and
    the orderly [Shutdown => break] then drops the uncommitted physical txn.
    Different route, different gate, opposite conclusion.

    COMPONENTS (five, all monotone, which is why the frame is a poset):
    two logical write transactions [a] and [b] inside one node, each running
    [L_idle -> L_open -> L_committed | L_dropped]; the thread's overlap counter
    [ov] in {0,1,2}; the fate of the one modelled key [w] that [a] writes,
    running [F_unwritten -> F_pending -> F_on_disk | F_dropped_at_exit]; and
    the thread itself, [Th_running -> Th_exited].

    ABSTRACTIONS, stated rather than hidden.
    - Message delivery is synchronous: a writer's action and the thread's
      handling of it are one transition. The mpsc queue only DELAYS the thread's
      reaction, it never adds a commit, so collapsing it can only make the
      lossy state harder to reach - the safe direction for the [Ef] of S2 and
      neutral for the [Ag] of S1 and S3.
    - [a]'s insert of [w] is folded into [a]'s [write_txn]: the mem mirror at
      layered_db.rs:98 and the [Insert] into the open physical txn at :210-219
      both happen there. Whether [a] uses the txn API or the non-txn
      [Database::insert] (:391-396) makes no difference to the model, because
      the thread routes EVERY [Insert] into whatever physical txn is open,
      regardless of which task sent it.
    - [a]'s [L_committed] means [commit()] returned [Ok] AND the following
      [sync_persist()] returned. Giving the writer the strongest barrier the
      API exports on EVERY commit is deliberate: it is the repair path a
      skeptic reaches for, and the statements are stated so that they survive
      it. A writer that skips the barrier is strictly worse informed, so every
      ignorance conjunct holds a fortiori for it; folding the barrier in
      removes states rather than adding favourable ones.
    - The writers are frozen once the thread has exited. The only thing that
      removes is an error return from a LATER send (:100, :131), which arrives
      after the acknowledgement the statements are about.

    ROLE MAPPING (knowledge agents have a real, non-constant view; idle
    validators carry the blank view and never appear under K):
    - V0 is logical writer [a], the task whose write [w] the family tracks. Its
      view is its own transaction's lifecycle plus the reading it gets from the
      exported [stats()] channel. It does NOT see [b]'s lifecycle, the physical
      transaction, or the disk. Its own reads are omitted from the view because
      they are constant: the mem mirror answers [Some(w)] from :98 onwards and
      the post-commit [clear_insert_mem] (:538-541) only lets the read fall
      through to a backend that has the value, so no read ever distinguishes
      the branches.
    - V1 is logical writer [b], the concurrent task whose open transaction is
      what defers [a]'s physical commit. Same shape of view over its own
      transaction.
    - V2 is the consumer of the exported observability channel: it sees exactly
      [stats()], i.e. [open_txn_count] while the thread lives and the
      [DB thread gone] error afterwards, and nothing else - the other field of
      [LayeredDbStats] is identically zero on this layer, per the paragraph on
      [full_memory] above. Reported honestly:
      the only in-repo callers of [LayeredDatabase::stats] are
      [CompositeDatabase::stats] (composite_db.rs:47-54) and tests
      (layered_db.rs:877 onwards, composite_db.rs:472), so V2 is a
      best-equipped observer of a [pub] channel rather than a task that exists
      today. That direction is the conservative one: it gives the agents MORE
      information than any production caller has.
    - V3..V9 are idle non-agents with the constant blank view and never appear
      under K. *)

(** The lifecycle of one logical write transaction, i.e. one [LayeredDbTxMut]
    and the [Arc<TxnGuard>] shared by its clones (layered_db.rs:72-78). *)
type logical =
  | L_idle  (** the task has not called [Database::write_txn] yet *)
  | L_open
      (** [write_txn] sent [DBMessage::StartTxn] and the thread counted it
          (layered_db.rs:365-373, :187-198) *)
  | L_committed
      (** [commit()] returned [Ok] - so [CommitTxn] was sent by the one caller
          that won [mark_committed] (layered_db.rs:125-134, :52-58) - and the
          following [sync_persist()] returned (:476-495) *)
  | L_dropped
      (** every clone of the guard dropped without commit, so [Drop for
          TxnGuard] ran (layered_db.rs:60-70) *)

(** Total order index for {!logical}. *)
let logical_index = function
  | L_idle -> 0
  | L_open -> 1
  | L_committed -> 2
  | L_dropped -> 3

(** Total order on {!logical}. *)
let logical_compare a b = Int.compare (logical_index a) (logical_index b)

(** [true] iff this transaction is currently outstanding. *)
let logical_is_open = function
  | L_open -> true
  | L_idle | L_committed | L_dropped -> false

(** The [u32] overlap count the writer thread carries beside the physical
    transaction ([Option<(DB::TXMut, u32)>], layered_db.rs:179). [Ov_zero] is
    the [None] case: no physical transaction is open. *)
type overlap =
  | Ov_zero  (** [txn = None] *)
  | Ov_one  (** [txn = Some(_, 1)]: the next end commits (:161-164) *)
  | Ov_two  (** [txn = Some(_, 2)]: the next end only decrements (:170-172) *)

(** Total order index for {!overlap}. *)
let overlap_index = function Ov_zero -> 0 | Ov_one -> 1 | Ov_two -> 2

(** Total order on {!overlap}. *)
let overlap_compare a b = Int.compare (overlap_index a) (overlap_index b)

(** [true] iff the count is zero, i.e. no physical transaction is open. *)
let overlap_is_zero = function Ov_zero -> true | Ov_one | Ov_two -> false

(** One more logical transaction joins the physical one ([*count += 1] /
    [txn = Some(ntxn, 1)], layered_db.rs:188-192). Saturating at two because
    the model has exactly two writers. *)
let overlap_succ = function
  | Ov_zero -> Ov_one
  | Ov_one -> Ov_two
  | Ov_two -> Ov_two

(** One logical transaction leaves ([count - 1], layered_db.rs:171). *)
let overlap_pred = function
  | Ov_zero -> Ov_zero
  | Ov_one -> Ov_zero
  | Ov_two -> Ov_one

(** The fate of the one modelled key [w], written by logical transaction [a]. *)
type fate =
  | F_unwritten  (** [a] has not issued the insert *)
  | F_pending
      (** the insert is in the mem mirror (layered_db.rs:98) and in the open
          physical transaction (:210-219), but no [current_txn.commit()] has
          carried it to the backend *)
  | F_on_disk
      (** [end_txn] took its [count <= 1] branch and the backend transaction
          committed (layered_db.rs:161-164, mdbx/database.rs:85-88,
          redb/database.rs:65-68) *)
  | F_dropped_at_exit
      (** the loop left through [DBMessage::Shutdown => break]
          (layered_db.rs:256) with the physical transaction still open, so it
          was dropped uncommitted and the backend aborted it *)

(** Total order index for {!fate}. *)
let fate_index = function
  | F_unwritten -> 0
  | F_pending -> 1
  | F_on_disk -> 2
  | F_dropped_at_exit -> 3

(** Total order on {!fate}. *)
let fate_compare a b = Int.compare (fate_index a) (fate_index b)

(** [a] issues its insert as part of opening its transaction. *)
let fate_issue = function
  | F_unwritten -> F_pending
  | F_pending -> F_pending
  | F_on_disk -> F_on_disk
  | F_dropped_at_exit -> F_dropped_at_exit

(** The physical commit fired ([count <= 1], layered_db.rs:161-164). *)
let fate_commit = function
  | F_unwritten -> F_unwritten
  | F_pending -> F_on_disk
  | F_on_disk -> F_on_disk
  | F_dropped_at_exit -> F_dropped_at_exit

(** The loop left with the physical transaction open (layered_db.rs:256). *)
let fate_discard = function
  | F_unwritten -> F_unwritten
  | F_pending -> F_dropped_at_exit
  | F_on_disk -> F_on_disk
  | F_dropped_at_exit -> F_dropped_at_exit

(** The background writer thread itself ([std::thread::spawn] in
    [LayeredDatabase::open], layered_db.rs:306-315). *)
type thread =
  | Th_running  (** inside [while let Ok(msg) = rx.recv()] (:185) *)
  | Th_exited  (** [db_run] returned (:266) *)

(** Total order index for {!thread}. *)
let thread_index = function Th_running -> 0 | Th_exited -> 1

(** Total order on {!thread}. *)
let thread_compare a b = Int.compare (thread_index a) (thread_index b)

(** [true] iff the writer thread is still serving messages. *)
let thread_is_running = function Th_running -> true | Th_exited -> false

(** The joint global state: the two logical transactions, the thread's overlap
    counter, the fate of the modelled key and the thread's own liveness. *)
type state = {
  a : logical;  (** logical write txn [a], the author of [w] (agent V0) *)
  b : logical;  (** the concurrent logical write txn [b] (agent V1) *)
  ov : overlap;  (** the thread's [u32] overlap count (layered_db.rs:179) *)
  w : fate;  (** where the modelled key [w] actually is *)
  th : thread;  (** whether [db_run] is still in its receive loop *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = logical_compare s1.a s2.a in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = logical_compare s1.b s2.b in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = overlap_compare s1.ov s2.ov in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = fate_compare s1.w s2.w in
        if Bool.not (Int.equal c3 0) then c3 else thread_compare s1.th s2.th

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** What a call to [LayeredDatabase::stats] returns (layered_db.rs:317-333),
    which is the whole of the thread's exported surface: the overlap count
    while the thread lives, an error once it is gone. *)
type gauge_read =
  | Read_zero  (** [Ok(LayeredDbStats { open_txn_count: 0, .. })] *)
  | Read_one  (** [Ok(.. open_txn_count: 1 ..)] *)
  | Read_two  (** [Ok(.. open_txn_count: 2 ..)] *)
  | Read_gone  (** [Err("DB thread gone, FATAL!")] (:322, :329) *)

(** Total order index for {!gauge_read}. *)
let gauge_read_index = function
  | Read_zero -> 0
  | Read_one -> 1
  | Read_two -> 2
  | Read_gone -> 3

(** Total order on {!gauge_read}. *)
let gauge_read_compare a b =
  Int.compare (gauge_read_index a) (gauge_read_index b)

(** The reading the exported channel gives at this state. *)
let gauge_read_of s =
  match s.th with
  | Th_exited -> Read_gone
  | Th_running -> (
      match s.ov with
      | Ov_zero -> Read_zero
      | Ov_one -> Read_one
      | Ov_two -> Read_two)

(** A validator's local view. Each writer sees its OWN transaction's lifecycle
    and the exported [stats()] reading, and nothing else: not the other
    writer's lifecycle, not the physical transaction, not the disk. The poller
    sees only the reading. *)
type view =
  | View_writer_a of logical * gauge_read  (** V0: [(a, stats())] *)
  | View_writer_b of logical * gauge_read  (** V1: [(b, stats())] *)
  | View_poller of gauge_read  (** V2: [stats()] alone *)
  | View_idle  (** the constant blank view of the non-agents V3..V9 *)

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare x y =
  match (x, y) with
  | View_idle, View_idle -> 0
  | View_idle, (View_writer_a _ | View_writer_b _ | View_poller _) -> -1
  | (View_writer_a _ | View_writer_b _ | View_poller _), View_idle -> 1
  | View_writer_a (l1, g1), View_writer_a (l2, g2) ->
      let c = logical_compare l1 l2 in
      if Bool.not (Int.equal c 0) then c else gauge_read_compare g1 g2
  | View_writer_a _, (View_writer_b _ | View_poller _) -> -1
  | (View_writer_b _ | View_poller _), View_writer_a _ -> 1
  | View_writer_b (l1, g1), View_writer_b (l2, g2) ->
      let c = logical_compare l1 l2 in
      if Bool.not (Int.equal c 0) then c else gauge_read_compare g1 g2
  | View_writer_b _, View_poller _ -> -1
  | View_poller _, View_writer_b _ -> 1
  | View_poller g1, View_poller g2 -> gauge_read_compare g1 g2

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 and V1 are the two logical writers and V2 is the
    consumer of the exported [stats()] channel; V3..V9 are idle non-agents with
    the constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V0 -> View_writer_a (s.a, gauge_read_of s)
  | Validator.V1 -> View_writer_b (s.b, gauge_read_of s)
  | Validator.V2 -> View_poller (gauge_read_of s)
  | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7
  | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine  (** the code as written at 0c59c15b *)
  | No_end_txn_on_drop
      (** delete [let _ = self.tx.send(DBMessage::EndTxn);] from [Drop for
          TxnGuard] (layered_db.rs:67, inside the guard at :60-70). Transition
          changed: the abandon edge [L_open -> L_dropped] no longer decrements
          the overlap count and therefore never reaches [end_txn]'s
          [count <= 1] commit, so the count wedges above zero for the rest of
          the process. NO SIBLING PATH REPAIRS IT. (a) [DBMessage::CommitTxn]
          (:199-201) is the only other decrement and it is sent by exactly one
          caller, [LayeredDbTxMut::commit] at :128-132, gated on
          [self.guard.mark_committed()] whose [AcqRel] swap (:52-58) is false
          forever for a guard that dropped uncommitted (:62) - so it cannot
          cover an abandoned txn. (b) The direct-write route
          [ins.insert(&db)] (:220-227) would persist each insert immediately,
          but it is the [else] of [if let Some((txn, _)) = &mut txn] at :210,
          i.e. reachable only when NO physical txn is open, which is exactly
          the state a wedged count prevents. (c) [DBMessage::Shutdown] (:256)
          leaves the loop without calling [end_txn], so it is a second hazard,
          not a repair - it is the other mutation of this family. (d)
          [persist] / [sync_persist] (:463-495) send [DBMessage::CaughtUp],
          whose arm is [let _ = tx.send(());] (:247-249): a queue-drain
          acknowledgement that never touches [txn]. (e) There is no timeout,
          watchdog or max-open-txn cap anywhere in [db_run] (:178-267) - the
          loop is a bare [while let Ok(msg) = rx.recv()] (:185). (f)
          [LayeredDbStats] (:137-147, :250-255) reports the wedge but nothing
          in the repo acts on it. *)
  | No_shutdown_break
      (** delete the [DBMessage::Shutdown => break,] arm
          (layered_db.rs:256). Transition changed: the thread then leaves only
          when [rx.recv()] fails (:185), i.e. when every [Sender] clone has
          dropped; a live [LayeredDbTxMut] holds one (:76) and its
          [TxnGuard::drop] sends [EndTxn] (:67) before that happens, so every
          logical txn is guaranteed to be ended - and hence the physical txn
          committed - before the loop exits. The model expresses that by
          enabling the exit transition only at overlap zero, which makes the
          write-discarding state unreachable. NO SIBLING PATH COMMITS THE TXN
          AT SHUTDOWN IN THE PRISTINE CODE. (a) [end_txn] is dispatched only
          from the [CommitTxn] (:199-201) and [EndTxn] (:202-208) arms, never
          from the [Shutdown] path. (b) Neither backend transaction wrapper has
          a [Drop] impl: the whole declaration list of
          crates/storage/src/mdbx/database.rs is [MdbxTx] (:15), [impl MdbxTx]
          (:20), [impl DbTx for MdbxTx] (:31), [MdbxTxMut] (:44),
          [impl MdbxTxMut] (:49), [impl DbTx for MdbxTxMut] (:56),
          [impl DbTxMut for MdbxTxMut] (:67-89) and the database/iterator
          items, and crates/storage/src/redb/database.rs is [ReDbTx] (:17),
          [impl DbTx for ReDbTx] (:21), [ReDbTxMut] (:28), [impl Debug] (:32),
          [impl DbTx for ReDbTxMut] (:38), [impl DbTxMut for ReDbTxMut]
          (:45-69) and the database/iterator items - no [impl Drop] in either.
          (c) [Drop for LayeredDatabase] sends [Shutdown] at :288 and only then
          joins at :293-296, so it cannot rescue the transaction. (d) A restart
          does not recover it: [open_table] refills the full-memory mem layer
          from the backend alone (:347-356). (e) [sync_persist] is not a
          repair, per (d) of the other mutation. HONESTY NOTE: this is a MODEL
          mutation, not a proposed patch. Removing the [break] in the real code
          would deadlock [Drop for LayeredDatabase], because it sends
          [Shutdown] and joins (:288-296) while still owning the [Sender] the
          loop is waiting to see dropped. *)

(** Does this mutation keep the guard's [EndTxn] on the abandon path
    (layered_db.rs:67)? Every arm spelled. *)
let end_message_on_drop = function
  | Pristine -> true
  | No_end_txn_on_drop -> false
  | No_shutdown_break -> true

(** Does this mutation keep [DBMessage::Shutdown => break]
    (layered_db.rs:256)? Every arm spelled. *)
let shutdown_breaks_the_loop = function
  | Pristine -> true
  | No_end_txn_on_drop -> true
  | No_shutdown_break -> false

(** One logical transaction ends: [end_txn] decrements and, when the count was
    the last one, commits the physical transaction (layered_db.rs:155-174). *)
let end_one s =
  let ov' = overlap_pred s.ov in
  let w' = if overlap_is_zero ov' then fate_commit s.w else s.w in
  { s with ov = ov'; w = w' }

(** The transition relation: each logical writer advances its own lifecycle and
    the thread reacts, and the thread can exit. Terminal once the thread has
    exited, so a state after shutdown is stutter-closed. *)
let next_with mut s =
  match s.th with
  | Th_exited -> []
  | Th_running ->
      List.concat
        [
          (match s.a with
          | L_idle ->
              [
                {
                  s with
                  a = L_open;
                  ov = overlap_succ s.ov;
                  w = fate_issue s.w;
                };
              ]
          | L_open ->
              [
                end_one { s with a = L_committed };
                (if end_message_on_drop mut then end_one { s with a = L_dropped }
                 else { s with a = L_dropped });
              ]
          | L_committed | L_dropped -> []);
          (match s.b with
          | L_idle -> [ { s with b = L_open; ov = overlap_succ s.ov } ]
          | L_open ->
              [
                end_one { s with b = L_committed };
                (if end_message_on_drop mut then end_one { s with b = L_dropped }
                 else { s with b = L_dropped });
              ]
          | L_committed | L_dropped -> []);
          (if shutdown_breaks_the_loop mut || overlap_is_zero s.ov then
             [
               {
                 s with
                 th = Th_exited;
                 w = (if overlap_is_zero s.ov then s.w else fate_discard s.w);
               };
             ]
           else []);
        ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: the thread is running, nobody holds a logical write
    transaction, the counter is zero and [w] has not been written. *)
let initial = { a = L_idle; b = L_idle; ov = Ov_zero; w = F_unwritten; th = Th_running }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | A_holds_open_txn  (** logical txn [a] is outstanding *)
  | A_commit_acknowledged
      (** [a]'s [commit()] returned [Ok] and its [sync_persist()] returned
          (layered_db.rs:125-134, :476-495) *)
  | A_dropped_without_commit
      (** every clone of [a]'s guard dropped uncommitted (layered_db.rs:60-70) *)
  | B_holds_open_txn  (** logical txn [b] is outstanding *)
  | Some_logical_txn_open
      (** SOME logical write txn is genuinely outstanding somewhere in the node:
          a fact about the two tasks' lifecycles, not about the counter *)
  | Gauge_zero  (** [stats()] answers [Ok { open_txn_count: 0 }] *)
  | Gauge_one  (** [stats()] answers [Ok { open_txn_count: 1 }] *)
  | Gauge_two  (** [stats()] answers [Ok { open_txn_count: 2 }] *)
  | Writer_thread_alive  (** [db_run] is still in its receive loop (:185) *)
  | W_issued  (** [a] has issued the insert of [w] *)
  | W_awaiting_commit  (** [w] is in the open physical txn, not on the backend *)
  | W_on_disk  (** a [current_txn.commit()] carried [w] to the backend *)
  | W_discarded
      (** the loop exited with [w] still in the open physical txn (:256) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | A_holds_open_txn -> logical_is_open s.a
  | A_commit_acknowledged -> (
      match s.a with
      | L_committed -> true
      | L_idle | L_open | L_dropped -> false)
  | A_dropped_without_commit -> (
      match s.a with
      | L_dropped -> true
      | L_idle | L_open | L_committed -> false)
  | B_holds_open_txn -> logical_is_open s.b
  | Some_logical_txn_open -> logical_is_open s.a || logical_is_open s.b
  | Gauge_zero -> (
      match gauge_read_of s with
      | Read_zero -> true
      | Read_one | Read_two | Read_gone -> false)
  | Gauge_one -> (
      match gauge_read_of s with
      | Read_one -> true
      | Read_zero | Read_two | Read_gone -> false)
  | Gauge_two -> (
      match gauge_read_of s with
      | Read_two -> true
      | Read_zero | Read_one | Read_gone -> false)
  | Writer_thread_alive -> thread_is_running s.th
  | W_issued -> (
      match s.w with
      | F_unwritten -> false
      | F_pending | F_on_disk | F_dropped_at_exit -> true)
  | W_awaiting_commit -> (
      match s.w with
      | F_pending -> true
      | F_unwritten | F_on_disk | F_dropped_at_exit -> false)
  | W_on_disk -> (
      match s.w with
      | F_on_disk -> true
      | F_unwritten | F_pending | F_dropped_at_exit -> false)
  | W_discarded -> (
      match s.w with
      | F_dropped_at_exit -> true
      | F_unwritten | F_pending | F_on_disk -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | A_holds_open_txn -> "open_txn(a)"
  | A_commit_acknowledged -> "commit_ok(a)/\\sync_persist_returned(a)"
  | A_dropped_without_commit -> "guard_dropped(a)"
  | B_holds_open_txn -> "open_txn(b)"
  | Some_logical_txn_open -> "exists_open_logical_txn"
  | Gauge_zero -> "stats().open_txn_count=0"
  | Gauge_one -> "stats().open_txn_count=1"
  | Gauge_two -> "stats().open_txn_count=2"
  | Writer_thread_alive -> "db_run_alive"
  | W_issued -> "issued(w)"
  | W_awaiting_commit -> "in_open_physical_txn(w)"
  | W_on_disk -> "on_disk(w)"
  | W_discarded -> "discarded_at_exit(w)"

(** The CTLK checker over this family's ordered state and view: the presheaf-
    topos denotation, pinned to agree with {!System} at every reachable world
    by test/t_backend_writer_thread_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state, the
    mutation-parameterized transitions, the three-agent view, the atom
    valuation. *)
let spec_of mut = { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
