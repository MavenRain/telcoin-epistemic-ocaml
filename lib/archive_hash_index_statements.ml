(** CTLK statements mined from the linear-hash digest index of a consensus
    archive pack (crates/storage/src/archive/digest_index) at 0c59c15b. The
    three statements are the three disciplines of ONE bucket structure:
    capacity is handed out by splitting buckets in a rotation the modulus
    fixes, a bucket that fills before its turn spills into the .odx overflow
    chain, and a bucket whose buffer is resident occupies a slot of the
    FIFO-bounded clean cache. Deleting the growth gate is exactly what pushes
    traffic onto the overflow chain, so S1 and S3 are two ends of one
    mechanism rather than two subjects.

    READING GUIDE FOR THE [K] OPERANDS. This family carries no positive [K]:
    every knowledge conjunct is an IGNORANCE conjunct, and there is exactly
    one hidden fact behind both of them - {!Chain_corrupt}, whether the
    overflow record bucket 0 is chained to links at or after itself.

    - [~K_V1(chain_corrupt)] at a pending walk. V1 is the worker parked on
      [rx.await] inside [ConsensusPack::batch] (consensus_pack.rs:595-600).
      Its view is its own request lifecycle and nothing else, so
      {!Chain_corrupt} is in no sense a projection of it; and it is not rigid,
      because sound and corrupt chains are both reachable. The witness pair is
      any two pending states that differ only in {!Archive_hash_index_model.hot}.
      This is the epistemic content of the missing timeout: the caller cannot
      distinguish a walk that is long from a walk that will never return, and
      has no clock with which to find out.
    - [~K_V2(chain_corrupt)] at a pending walk. V2 is the index thread itself.
      Its view carries everything it holds in memory - append count, bucket
      count, whether bucket 0's head buffer has a non-zero overflow pointer,
      the clean-cache word, the walk - and still it cannot tell a sound chain
      from a corrupt one, because the chained record's own link lives on disk
      and is re-read into a scratch buffer on every hop
      (bucket_iter.rs:106-113), never cached. That is precisely why the
      decrease test at bucket_iter.rs:120-126 has to be a runtime check rather
      than an invariant the thread could maintain. The ignorance also survives
      across calls, which is what lets the model keep it as a global fact
      rather than a first-lookup artefact: the [crc_failure] verdict lives in
      the per-call [BucketIter] and [fetch_position] reads it and then drops
      the iterator without recording it anywhere ([let crc_failure =
      iter.crc_failure(); drop(iter);], index.rs:630-631). Nothing in
      [HdxIndex] remembers that a bucket's chain was found corrupt. *)

open Archive_hash_index_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;  (** unique across every family *)
  bucket : Statements.bucket;  (** Safety | Liveness | Fairness | Security *)
  formula : atom Formula.t;  (** the claim *)
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - split-rotation-reaches-the-cold-bucket-independent-of-occupancy
    [fairness].

    Conjunct A, no starvation: while the pack is append-open AND the overflow
    log is intact, bucket 1 - the cold bucket, which no modelled append ever
    touches and which never overflows - is INEVITABLY split. The intactness
    hypothesis is not decoration and is stated because the code has a real
    stall the statement must not paper over: a split whose target bucket owns
    a corrupt chain ends [split_one_bucket] at [if iter.crc_failure() { return
    Err(AppendError::CrcError); }] (index.rs:591-593), which [expand_buckets]
    propagates through its [?] (:442) and [Index::save] returns (:768), so
    growth stops. The modelled window cannot exhibit that stall - within one
    generation bucket 0 is split by the FIRST append, when it has no chain yet
    - which is exactly why the hypothesis is written into the formula instead
    of being left to the reader. The split trigger is aggregate only,
    [while self.header.values >= (self.capacity as f32 *
    self.header.load_factor()) as u64] (index.rs:441 inside :437-446, with
    [load_factor: (u16::MAX as f32 * 0.5) as u16] at :66), and the bucket it
    rebuilds is [let split_bucket = (self.buckets() - (old_modulus / 2)) as
    u64] (index.rs:549 inside :546-556), a function of the bucket count and
    the modulus and of nothing else - the source says so in its own doc
    comment at :544-545. The model branches on occupancy at every append (the
    key either fits in bucket 0 or overflows it into the .odx log,
    index.rs:667-685) and the [Af] holds on every one of those branches,
    including the branch where bucket 0 has already spilled: being hot buys no
    extra split, being cold costs none.

    Conjunct B, index order: bucket 1 is never split before bucket 0, written
    as the weak until [A[ ~split(b1) W split(b0) ]] through the kernel
    identity [A[p W q] = ~E[~q U (~p /\ ~q)]]. The model computes the targets
    from the real arithmetic rather than asserting an order:
    {!Archive_hash_index_model.split_target} is [bucket_count b - modulus b /
    2] over [modulus = (buckets + 1).next_power_of_two()] (index.rs:555,
    :376), giving [2 - 2 = 0] then [3 - 2 = 1].

    MUTATION PIN. {!Archive_hash_index_model.No_growth_gate} deletes the
    growth condition at index.rs:441, so [expand_buckets] never calls
    [split_one_bucket], the bucket count never leaves [B2] and conjunct A is
    refuted at every append-open state. No sibling path repairs the ROTATION:
    [split_one_bucket] (:546) has exactly one caller, [expand_buckets] (:442),
    and [inc_buckets] (:456-459) has exactly one caller, [split_one_bucket]
    (:550). The overflow spill IS a sibling and it IS in the model - with the
    gate deleted, appends still land and lookups still answer, which is why
    this mutation leaves S3 proving - but what it repairs is index
    correctness, not the rotation. *)
let s1 =
  let cold_bucket_is_never_starved =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Append_open, Formula.Not (atom Chain_corrupt)),
           Formula.Af (atom Cold_bucket_split) ))
  in
  let rotation_is_in_index_order =
    (* A[ ~split(b1) W split(b0) ] = ~E[ ~split(b0) U (split(b1) /\ ~split(b0)) ] *)
    Formula.Not
      (Formula.Eu
         ( Formula.Not (atom Hot_bucket_split),
           Formula.And
             (atom Cold_bucket_split, Formula.Not (atom Hot_bucket_split)) ))
  in
  {
    name = "split-rotation-reaches-the-cold-bucket-independent-of-occupancy";
    bucket = Statements.Fairness;
    formula =
      Formula.And (cold_bucket_is_never_starved, rotation_is_in_index_order);
    antecedent = atom Append_open;
  }

(** S2 - bucket-cache-residency-is-capped-yet-one-hot-bucket-evicts-the-cold-one
    [fairness].

    Conjunct A, the hard cap: the clean-cache FIFO never holds more than
    [CACHED_BUCKETS] slots. [add_bucket_to_cache] evicts from the front before
    it inserts, [while self.bucket_cache_fifo.len() >= Self::CACHED_BUCKETS {
    if let Some(bucket) = self.bucket_cache_fifo.pop_front() {
    self.bucket_cache.remove(&bucket); } }] (index.rs:428-432 inside
    :422-435, [CACHED_BUCKETS] at :272-276), and BOTH admission sites route
    through it - the read path returns its buffer through
    [self.add_bucket_to_cache(bucket, buffer)] (index.rs:632-639) and the
    flush path does the same (:520-522). The model's cache word is a list, so
    the cap is a checked property and not a type-level one: with the eviction
    loop deleted the word really does reach three slots.

    SCOPE, stated so the conjunct is not over-read. This is the CLEAN cache
    and nothing else. The DIRTY map [dirty_bucket_cache] has no cap at all -
    it is inserted into at index.rs:595, :596, :607 and :635 and shrinks only
    when [save_bucket_cache] drains it (:512) - so "the index's bucket memory
    is bounded" is NOT what is being claimed. What is claimed is that the
    read-side residency queue, the one thing [CACHED_BUCKETS] names, is
    capped, and it is: [bucket_cache_fifo] is touched at exactly two places in
    the whole file, the [pop_front] at :429 and the [push_back] at :434.

    Conjunct B, the honest other side: the queue admits DUPLICATES - nothing
    in :422-435 checks whether [bucket] is already queued - so admission is
    per-INSERTION, not per-bucket, and a repeatedly-touched bucket takes one
    slot per touch. The conjunct is the reachability of monopolisation: from a
    state where the cold bucket is resident, a state is reachable where the
    queue is full and every slot names the hot bucket, which is to say the
    cold bucket has been evicted by a rival that was merely touched more
    often. Bounded residency is a real fairness guarantee; equal share is not
    one, and this conjunct is what makes the family state that out loud.

    MUTATION PIN. {!Archive_hash_index_model.No_cache_eviction_loop} deletes
    the loop at index.rs:428-432. Conjunct A is refuted the moment a third
    slot is admitted, and conjunct B is refuted as well: with no eviction the
    cold bucket's slot is never removed, so no state reachable FROM a
    cold-resident state has an all-hot queue. Nothing else evicts from the
    clean cache - [remove_bucket_cache] (:471-478) and [remove_bucket]
    (:482-504) hand the buffer to a writer and [save_to_bucket] returns it to
    the DIRTY map (:601-609); [save_bucket_cache] drains that dirty map (:512)
    and re-inserts through this same function (:520-522), feeding the bound
    rather than replacing it; [Drop] (:723-758) flushes without evicting; and
    the crate has no memory-pressure hook and no expiry. *)
let s2 =
  let residency_is_capped = Formula.Ag (Formula.Not (atom Cache_over_cap)) in
  let a_hot_streak_can_evict_the_cold_bucket =
    Formula.Ef
      (Formula.And
         ( atom Cold_resident,
           Formula.Ef
             (Formula.And (atom Cache_at_cap, atom Cache_all_hot)) ))
  in
  {
    name =
      "bucket-cache-residency-is-capped-yet-one-hot-bucket-evicts-the-cold-one";
    bucket = Statements.Fairness;
    formula =
      Formula.And
        (residency_is_capped, a_hot_streak_can_evict_the_cold_bucket);
    antecedent = atom Cold_resident;
  }

(** S3 - overflow-chain-decrease-guard-answers-a-corrupt-chain-instead-of-wedging
    [liveness].

    Conjunct A, the liveness: every digest lookup that starts walking is
    inevitably answered. The walk is the [loop] of
    [HdxIndex::next_bucket_element] (bucket_iter.rs:142-169), which leaves
    only on [overflow_pos == 0], on exhaustion, or on the [?] that propagates
    a [None] out of [reset_next_overflow]. The gate that produces that [None]
    is the decrease test [if next_overflow_pos != 0 && next_overflow_pos >=
    current_pos { self.crc_failure = true; return None; }]
    (bucket_iter.rs:123-126). Note what "answered" means here and why the
    conjunct is true rather than merely hoped for: the guard does not rescue
    the DATA, it converts a corrupt chain into an ANSWER -
    [fetch_position] reports the [crc_failure] as [Err(FetchError::CrcFailed)]
    (index.rs:630-646) and the caller's oneshot resolves. Honest chains
    always decrease because a spill appends at [SeekFrom::End(0)] and stores
    that OLD end in the fresh bucket (index.rs:672-685); the corrupt shape is
    an external event, which is why the model offers it only on the sealed,
    read-only pack where [save] refuses (index.rs:762-764) and the split
    rebuild that would otherwise discard the chain (index.rs:557-559,
    :595-596) cannot run.

    Conjuncts B and C, the ignorance: at a pending walk neither the parked
    worker nor the index thread knows the chain is corrupt. See the reading
    guide at the head of this file; the witness pair for both is any two
    pending states differing only in
    {!Archive_hash_index_model.hot}, and V2's view deliberately carries the
    one bit the thread really does hold - whether bucket 0's head buffer has a
    non-zero overflow pointer - so its ignorance is about the chained record's
    own link and nothing coarser.

    MUTATION PIN. {!Archive_hash_index_model.No_chain_decrease_guard} deletes
    bucket_iter.rs:123-126, so the walk assigns [self.overflow_pos =
    next_overflow_pos] with [next_overflow_pos = current_pos] and re-reads the
    same record forever; the model gives that pending state no successor, and
    since terminals are stutter-closed the [Af] is refuted. No sibling path
    repairs it: [next_bucket_element] has no visit counter and no depth cap
    (bucket_iter.rs:142-169); the per-record [check_crc]
    (bucket_iter.rs:114-117) passes because a self-linked record is
    individually valid; [read_exact(...).ok()?] (bucket_iter.rs:113) repairs
    only a link PAST the end of the odx, not an in-range self link; the caller
    has no [tokio::time::timeout] (consensus_pack.rs:595-600, the file's only
    timeouts being the async stream reader at :1409-1419 and a test at :2042);
    and [run_pack_loop] is ONE blocking thread draining messages serially
    (consensus_pack.rs:132-193), so no concurrent split, flush or reopen can
    clear the chain while the walk spins - the wedge takes every later archive
    operation on the node with it. *)
let s3 =
  let every_walk_is_answered =
    Formula.Ag
      (Formula.Implies (atom Lookup_pending, Formula.Af (atom Lookup_answered)))
  in
  let the_parked_worker_cannot_tell =
    Formula.Ag
      (Formula.Implies
         ( atom Lookup_pending,
           Formula.Not (Formula.K (Validator.V1, atom Chain_corrupt)) ))
  in
  let the_index_thread_cannot_tell =
    Formula.Ag
      (Formula.Implies
         ( atom Lookup_pending,
           Formula.Not (Formula.K (Validator.V2, atom Chain_corrupt)) ))
  in
  {
    name =
      "overflow-chain-decrease-guard-answers-a-corrupt-chain-instead-of-wedging";
    bucket = Statements.Liveness;
    formula =
      Formula.conj
        [
          every_walk_is_answered;
          the_parked_worker_cannot_tell;
          the_index_thread_cannot_tell;
        ];
    antecedent = atom Lookup_pending;
  }

(** The family's statements. *)
let all = [ s1; s2; s3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

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
