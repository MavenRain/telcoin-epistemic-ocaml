(** The BACKEND_WRITER_THREAD statements: three readings of one background
    writer thread over the interpreted system of {!Backend_writer_thread_model}
    - what keeps the overlap counter draining so that durability ever happens
    at all (S1), what the orderly shutdown does to a write that has already
    been acknowledged AND barriered (S2), and what the counter the thread
    exports is worth to whoever reads it (S3).

    The three are separated by their gates, not merely by their wording. S1 and
    S3 are refuted by deleting the guard's [EndTxn] send
    (layered_db.rs:67); S2 is refuted by deleting the
    [DBMessage::Shutdown => break] arm (layered_db.rs:256).
    test/t_backend_writer_thread_mutation.ml asserts that separation
    explicitly, so no pin rides on the other gate's collapse.

    READING GUIDE for the K operands - why none is a projection of its own
    knower's view, and why none is rigid.

    - [K_V2(exists_open_logical_txn)] in S3 conjunct A. V2's view is exactly
      the exported reading [stats().open_txn_count] (layered_db.rs:250-255,
      :317-333). The operand is NOT that reading: it is a fact about the two
      tasks' lifecycles, which V2 never sees. What ties them together is the
      gate - every increment at :188-192 is matched by a decrement from
      [CommitTxn] (:199-201) or from the guard's [EndTxn] (:67, :202-208) - and
      that tie is exactly what
      {!Backend_writer_thread_model.No_end_txn_on_drop} cuts: the counter then
      keeps counting an abandoned transaction, so a reading of one is
      compatible with nobody holding a transaction at all, and the K is false
      while V2's view is unchanged. The operand is not rigid either: it is
      false at every reachable zero-reading state.
      NON-DEGENERACY (R2): at an operative [Gauge_one] state V2's view class
      holds eight reachable states, not one - every configuration with exactly
      one writer open, over both values of [w]'s fate.
      test/t_backend_writer_thread.ml discharges that as
      [Gauge_one /\\ ~K_V2(~commit_ok(a))], which can only hold because another
      reachable state shares V2's reading and has [a] committed.

    - [K_V2(~issued(w) \\/ on_disk(w))] in S3 conjunct B. Same view, and the
      operand is about the BACKEND, which no channel out of the thread reports:
      [LayeredDbStats] carries [retained_inserts] and [open_txn_count] and
      nothing else (layered_db.rs:137-147), and on the [full_memory] layer this
      family models the first of those two is identically zero
      ([mem_db_clone = None] at :311 gates the only push, :217-219). A zero
      reading is a durability
      certificate only because the counter can reach zero only through
      [end_txn]'s [count <= 1] branch, which commits (:161-164). Not rigid: the
      operand is false at every [Gauge_one] state where [w] is still riding the
      open physical transaction. This conjunct is stated because it is true,
      not because a mutation refutes it - it is the positive half whose
      soundness conjunct A is about, and it sits inside a conjunction that
      {!Backend_writer_thread_model.No_end_txn_on_drop} does refute.

    - [~K_V0(on_disk(w))] and [~K_V0(~on_disk(w))] in S2 conjuncts B1 and B2.
      V0 is the writing task, and it is given MORE than any production caller
      has: its own transaction's lifecycle AND the exported [stats()] reading.
      It still cannot tell. At a [Gauge_one] state after its own commit, V0's
      class is exactly the pair {[w] still in the open physical transaction,
      [w] already on disk from an earlier drain} - the commit is asynchronous
      by its own doc (layered_db.rs:118-124), the mem layer answers identically
      either way (:98, :383-389), and [sync_persist] only drains the queue
      (:247-249, :476-495). After the thread is gone V0's class contains both a
      state where its write reached the backend and one where the loop exited
      with the write still inside the dropped physical transaction, so the
      ignorance survives even the [DB thread gone] error.

    - [~K_V1(in_open_physical_txn(w))] in S2 conjunct C. V1 is the OTHER
      writer, the one whose still-open logical transaction is the reason
      [end_txn] took its [else] branch (:170-172). Every [DBMessage::Insert]
      goes into whatever physical transaction is open regardless of who sent it
      (:209-219), so V1's transaction is carrying another task's acknowledged
      write - and nothing in V1's view says so.

    Buckets reuse the frozen {!Statements} vocabulary. *)

open Backend_writer_thread_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;  (** unique across every family *)
  bucket : Statements.bucket;  (** Safety | Liveness | Fairness | Security *)
  formula : atom Formula.t;  (** the claim, proved with [prove_nonvacuous] *)
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - abandoned-write-txn-still-releases-the-overlapped-physical-commit
    [liveness].

    Many logical write transactions ride ONE physical backend transaction,
    counted up at [DBMessage::StartTxn] (layered_db.rs:187-198) and down at
    [end_txn] (:155-174), and the physical commit fires only on the [count <= 1]
    branch (:161-164). Durability of every writer therefore depends on every
    concurrent writer signalling an end - and the one that makes an end
    guaranteed on the error path is not a commit call but a destructor:
    [if !self.committed.load(Ordering::Acquire) { ... let _ =
    self.tx.send(DBMessage::EndTxn); }] (layered_db.rs:60-70, the send at :67).
    The struct doc states the failure mode in as many words: "Without the end
    message a dropped txn would permanently skew the background thread's txn
    count - commits stop firing, writes stop persisting to disk, and retained
    inserts grow forever" (:44-46).

    - Conjunct A (the non-blocking half): at every reachable state where [w] is
      acknowledged but still inside the open physical transaction and the
      writer thread is alive, a physical commit that carries [w] to the backend
      is still REACHABLE. This is the honest [AG(EF ...)] form rather than an
      [AF]: the thread's exit is always enabled in the pristine model
      (layered_db.rs:284-303 fires as soon as the last database handle drops),
      so no path-universal claim about eventual durability is true here, and
      pretending otherwise would be manufactured liveness. What the gate buys
      is that durability never becomes IMPOSSIBLE while the thread lives.
    - Conjunct B (the wedge): at every reachable state where no logical write
      transaction is outstanding, the thread is alive and [w] was issued, [w]
      is on the backend. Quiescence entails durability - which is precisely the
      invariant [LayeredDbStats]'s doc asks its reader to rely on ("Should be 0
      whenever no write txn is outstanding", :137-147).

    MUTATION PIN. {!Backend_writer_thread_model.No_end_txn_on_drop} deletes the
    [EndTxn] send at layered_db.rs:67. Reach the state where [a] opened its
    transaction, wrote [w] and then dropped its guard uncommitted: the count
    stays at one for the rest of the process, [end_txn]'s [count <= 1] branch
    is never taken again, and no later transaction can drive the count back to
    zero because a second writer's [StartTxn] only raises it. Conjunct A fails
    there ([w] can no longer reach the backend at all) and conjunct B fails
    there too (nobody is open, the thread is alive, [w] was issued and is not
    on disk). The sibling hunt is written out on the mutation constructor: the
    only other decrement is [CommitTxn], sent by exactly one caller behind an
    [AcqRel] swap that a dropped-uncommitted guard never wins (:52-58, :62,
    :128-132); the direct-write route [ins.insert(&db)] (:220-227) is the
    [else] of [if let Some((txn, _)) = &mut txn] and so is unreachable once the
    count is wedged; [persist]/[sync_persist] only acknowledge a drained queue
    (:247-249, :476-495); and [db_run] has no timeout, watchdog or open-txn cap
    anywhere in :178-267. *)
let s1 =
  let durability_stays_reachable =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom W_awaiting_commit, atom Writer_thread_alive),
           Formula.Ef (atom W_on_disk) ))
  in
  let quiescence_entails_durability =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [
               Formula.Not (atom Some_logical_txn_open);
               atom Writer_thread_alive;
               atom W_issued;
             ],
           atom W_on_disk ))
  in
  {
    name = "abandoned-write-txn-still-releases-the-overlapped-physical-commit";
    bucket = Statements.Liveness;
    formula =
      Formula.And (durability_stays_reachable, quiescence_entails_durability);
    antecedent = Formula.And (atom W_awaiting_commit, atom Writer_thread_alive);
  }

(** S2 - orderly-shutdown-under-an-overlapped-txn-discards-a-barriered-write
    [safety].

    A logical commit is a message, not a durability point - the method's own
    doc says "when this returns, the data may not be committed on-disk yet"
    (layered_db.rs:118-124) - and it only DECREMENTS: while another logical
    transaction is open, [end_txn] takes [*txn = Some((current_txn, count - 1))]
    (:170-172) and the physical transaction stays open. [DBMessage::Shutdown =>
    break] (:256) then leaves the receive loop without calling [end_txn], the
    local [Option<(DB::TXMut, u32)>] (:179) is dropped, and neither backend
    wrapper has a [Drop] impl that could commit it. Meanwhile the write is
    fully visible locally, because [insert] mirrors into the mem layer before
    queueing (:96-102) and every read is mem-first (:86-94, :383-389).

    - Conjunct A (the reachable loss): a state is reachable in which [a]'s
      [commit()] returned [Ok], [a]'s [sync_persist()] returned, [b] still held
      an open logical transaction, the writer thread has exited, and [w] was
      discarded with the physical transaction. The [sync_persist] is in the
      conjunction on purpose: it is the strongest barrier the API exports and
      it does not help, because [DBMessage::CaughtUp] is answered with
      [let _ = tx.send(());] (:247-249) without touching [txn].
    - Conjunct B1 (ignorance while the thread lives): at every state where
      [a]'s commit has been acknowledged and the exported gauge still reads
      one, [a] knows neither that [w] is on disk nor that it is not. Its view
      class there is exactly the pair "still riding [b]'s physical transaction"
      / "already committed by an earlier drain".
    - Conjunct B2 (ignorance after the thread is gone): the same two-sided
      ignorance survives the thread's exit, when [stats()] answers
      [Err("DB thread gone, FATAL!")] (:322, :329) - the error tells [a] the
      thread is gone, not what happened to its write.
    - Conjunct C (the other writer's ignorance): at every state where [b] holds
      an open logical transaction and the gauge reads one, [b] does not know
      that another task's acknowledged write is riding on it. Every
      [DBMessage::Insert] enters whatever physical transaction is open,
      whoever sent it (:209-219), so [b]'s transaction really is the hostage
      taker - and nothing [b] can see says so.

    MUTATION PIN. {!Backend_writer_thread_model.No_shutdown_break} deletes the
    [DBMessage::Shutdown => break,] arm (layered_db.rs:256). The loop then
    leaves only when [rx.recv()] fails (:185), which requires every [Sender]
    clone to have dropped; a live [LayeredDbTxMut] holds one (:76) and its
    guard sends [EndTxn] on the way out (:67), so the count is guaranteed to
    drain and the physical transaction to commit before the loop exits. The
    model expresses this by enabling the exit only at overlap zero. Conjunct A
    is then refuted because the discarded state is unreachable, and conjunct B2
    is refuted for the sharper reason that [a]'s post-exit view class collapses
    to states where [w] IS on disk, so [a] suddenly does know. Conjuncts B1 and
    C are untouched, which is the point: the statement flips on the shutdown
    gate alone. The antecedent stays reachable under the mutation, so the
    verdict is [Refuted] and not [Vacuous_antecedent].

    HONESTY NOTE, repeated from the mutation constructor: deleting the [break]
    is a MODEL device for removing the lossy transition, not a proposed patch -
    in the real code it would deadlock [Drop for LayeredDatabase], which sends
    [Shutdown] and joins (:288-296) while still owning the [Sender] the loop
    would be waiting to see dropped.

    SCOPE. The claim is about the storage layer's own guarantee and nothing
    else. Whether a particular lost row is recoverable ABOVE this layer - by
    refetching it from peers, or by rebuilding it from another table - is a
    property of the table and its protocol, not of the writer thread, and this
    family neither asserts nor denies it. What the storage layer itself offers
    is settled here: it does not recover, because [open_table] refills the
    full-memory mem layer from the backend alone (layered_db.rs:347-356). *)
let s2 =
  let barriered_write_is_discarded_at_exit =
    Formula.Ef
      (Formula.conj
         [
           atom A_commit_acknowledged;
           atom B_holds_open_txn;
           Formula.Not (atom Writer_thread_alive);
           atom W_discarded;
         ])
  in
  let two_sided_ignorance =
    Formula.And
      ( Formula.Not (Formula.K (Validator.V0, atom W_on_disk)),
        Formula.Not (Formula.K (Validator.V0, Formula.Not (atom W_on_disk))) )
  in
  let author_cannot_tell_while_overlapped =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom A_commit_acknowledged, atom Gauge_one),
           two_sided_ignorance ))
  in
  let author_cannot_tell_after_the_thread_is_gone =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             ( atom A_commit_acknowledged,
               Formula.Not (atom Writer_thread_alive) ),
           two_sided_ignorance ))
  in
  let overlapping_writer_cannot_see_its_hostage =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom B_holds_open_txn, atom Gauge_one),
           Formula.Not (Formula.K (Validator.V1, atom W_awaiting_commit)) ))
  in
  {
    name = "orderly-shutdown-under-an-overlapped-txn-discards-a-barriered-write";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [
          barriered_write_is_discarded_at_exit;
          author_cannot_tell_while_overlapped;
          author_cannot_tell_after_the_thread_is_gone;
          overlapping_writer_cannot_see_its_hostage;
        ];
    antecedent = Formula.And (atom A_commit_acknowledged, atom Gauge_one);
  }

(** S3 - exported-open-txn-gauge-is-an-exact-census-of-live-logical-txns
    [security].

    [LayeredDbStats] is the thread's only export
    ([DBMessage::Stats(tx) => { let _ = tx.send(LayeredDbStats {
    retained_inserts: committed_inserts.len(), open_txn_count:
    txn.as_ref().map(|(_, count)| *count as u64).unwrap_or(0) }); }],
    layered_db.rs:250-255, reached through [stats()] at :317-333), and its doc
    tells the reader what to conclude from it: "Number of logical write txns
    currently overlapped on the physical txn. Should be 0 whenever no write txn
    is outstanding; a value stuck above 0 means commits have stopped firing
    (wedged txn count)" (:137-147). This statement is that the gauge earns
    those readings - and it is the only statement of the three whose subject is
    the OBSERVER rather than the data.

    - Conjunct A (the census): whenever the gauge reads one, its reader KNOWS
      that a logical write transaction really is outstanding somewhere in the
      node. The counter is an exact census because each [StartTxn] increment
      (:188-192) is matched by exactly one decrement, from [CommitTxn]
      (:199-201) for a committed transaction and from the guard's [EndTxn]
      (:67, :202-208) for an abandoned one.
    - Conjunct B (the durability certificate): whenever the gauge reads zero,
      its reader KNOWS that every issued write is on the backend. The counter
      can only reach zero through [end_txn]'s [count <= 1] branch, and that
      branch commits (:161-164). This is the reading that makes the exported
      number useful at all, and it holds under both of this family's mutations
      - it is stated because it is true, inside a conjunction that one of them
      refutes.

    MUTATION PIN. {!Backend_writer_thread_model.No_end_txn_on_drop} deletes the
    [EndTxn] send (layered_db.rs:67). The census breaks in the direction that
    matters to a monitor: an abandoned transaction is still counted, so the
    state where [a] opened and then dropped its guard, with nobody holding a
    transaction at all, still reads one. Conjunct A fails there while the
    reader's view is unchanged - the gauge has become an over-count, which is
    exactly the failure the doc at :144-146 warns about but cannot itself
    distinguish from honest work in progress. Conjunct B survives, because an
    over-counting gauge still reaches zero only by committing; the refutation
    is therefore cleanly attributable to conjunct A. No sibling repairs it: the
    sole other decrement is unreachable for an abandoned guard (:52-58, :62,
    :128-132), and nothing in the repo cross-checks the counter -
    [CompositeDatabase::stats] (composite_db.rs:47-54) only aggregates the same
    two fields across the three layered databases (:33-35). *)
let s3 =
  let a_reading_of_one_is_a_live_transaction =
    Formula.Ag
      (Formula.Implies
         ( atom Gauge_one,
           Formula.K (Validator.V2, atom Some_logical_txn_open) ))
  in
  let a_reading_of_zero_is_a_durability_certificate =
    Formula.Ag
      (Formula.Implies
         ( atom Gauge_zero,
           Formula.K
             ( Validator.V2,
               Formula.Or (Formula.Not (atom W_issued), atom W_on_disk) ) ))
  in
  {
    name = "exported-open-txn-gauge-is-an-exact-census-of-live-logical-txns";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( a_reading_of_one_is_a_live_transaction,
          a_reading_of_zero_is_a_durability_certificate );
    antecedent = atom Gauge_one;
  }

(** The family's statements. *)
let all = [ s1; s2; s3 ]

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
