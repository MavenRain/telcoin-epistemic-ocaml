(** Finite interpreted system for the ARCHIVE_HASH_INDEX family: the
    linear-hash digest index of a consensus archive pack
    (crates/storage/src/archive/digest_index), covering the three disciplines
    of one bucket structure - the growth rotation that hands out capacity, the
    overflow chain that absorbs a bucket which filled before its turn, and the
    FIFO-bounded clean cache that holds a resident bucket's buffer in memory -
    all of them driven by the ONE blocking thread that serves every archive
    message. File citations refer to Telcoin-Association/telcoin-network at
    0c59c15b (working tree).

    THE MECHANISM, site by site.

    - GROWTH. [Index::save] runs [expand_buckets] BEFORE it places the key
      (index.rs:762-773, the [self.expand_buckets()?] at :768).
      [expand_buckets] is [while self.header.values >= (self.capacity as f32 *
      self.header.load_factor()) as u64 { self.split_one_bucket()?; ... }]
      (:437-446) with [load_factor: (u16::MAX as f32 * 0.5) as u16] (:66), so
      the trigger reads AGGREGATE [values] only. Which bucket is rebuilt is
      [let split_bucket = (self.buckets() - (old_modulus / 2)) as u64]
      (:546-556, doc comment :544-545: "Buckets are split in order determined
      by the current modulus not based on how full any bucket is"), with
      [self.modulus = (self.buckets() + 1).next_power_of_two()] (:555, and
      :376 on open). [split_one_bucket] is the sole caller of [inc_buckets]
      (:456-459) and [expand_buckets] (:442) is the sole caller of
      [split_one_bucket]: there is no second growth route.
    - THE SPLIT REBUILDS FROM ZERO. [split_one_bucket] allocates two FRESH
      zeroed buffers ([let mut buffer = vec![0; bucket_size];] :557-559),
      re-inserts the surviving elements into them and stores them back
      (:595-596). A fresh buffer has [overflow_pos = 0], so splitting bucket b
      also DISCARDS b's overflow chain. That is modelled: an append whose
      split targets bucket 0 resets {!Hot_plain}.
    - OVERFLOW. When a bucket is full, [save_to_bucket_buffer] appends the old
      bucket at the END of the .odx log and stores that old end in the fresh
      bucket's first u64 ([let overflow_pos = self.odx_file.seek(
      SeekFrom::End(0))...; self.odx_file.write_all(buffer)...;
      buffer[0..8].copy_from_slice(&overflow_pos.to_le_bytes());], :667-685).
      An honest chain therefore points STRICTLY BACKWARDS.
    - THE WALK. [BucketIter::reset_next_overflow] re-reads a record per hop
      (:106-119, no caching of overflow records) and enforces the decrease:
      [if next_overflow_pos != 0 && next_overflow_pos >= current_pos {
      self.crc_failure = true; return None; }]
      (bucket_iter.rs:120-126). The loop it bounds is
      [HdxIndex::next_bucket_element] (bucket_iter.rs:142-169), which exits
      only on [overflow_pos == 0], on exhaustion, or on that [?].
      [fetch_position] turns a [crc_failure] into [Err(FetchError::CrcFailed)]
      (index.rs:630-646) - i.e. into an ANSWER.
    - THE CLEAN CACHE. [add_bucket_to_cache] is
      [while self.bucket_cache_fifo.len() >= Self::CACHED_BUCKETS { if let
      Some(bucket) = self.bucket_cache_fifo.pop_front() {
      self.bucket_cache.remove(&bucket); } } self.bucket_cache.insert(bucket,
      buffer); self.bucket_cache_fifo.push_back(bucket);] (:422-435) with
      [CACHED_BUCKETS: usize = 400_000] (:272-276). Both admission sites route
      through it: the read path at :632-639 and the flush path at :520-522.
      The queue admits DUPLICATES - nothing checks whether [bucket] is already
      queued - so N touches of one bucket consume N slots.
    - THE SERVICE. [run_pack_loop] is one thread draining messages serially,
      [while let Some(msg) = rx.blocking_recv()] (consensus_pack.rs:132-193,
      [PackMessage::Batch] at :175-177). The caller is
      [let (tx, rx) = oneshot::channel(); ...; rx.await.unwrap_or_default()]
      (:595-600) with NO [tokio::time::timeout]: the only two timeouts in the
      file are on the async STREAM reader (:1409-1419) and in a test (:2042).
      A walk that never returns is therefore a permanent, silent loss of every
      later archive operation on that node.

    COMPONENTS (one state vector; the phases are sequential because the
    service is single-threaded and a pack is append-open and then sealed).

    - {!appends}: how many keys the modelled epoch has appended, capped at
      two. This is the model's clock; it advances under EVERY mutation, which
      is what keeps the sealed serving phase reachable even when the growth
      gate is deleted.
    - {!buckets}: the linear-hash bucket count, [B2 -> B3 -> B4]. The split
      targets are computed from the REAL arithmetic by {!split_target}:
      [2 - 4/2 = 0] then [3 - 4/2 = 1], i.e. the hot bucket then the cold one,
      and [4 - 8/2 = 0] would restart the rotation in the next generation
      (outside the modelled window).
    - {!hot}: the shape of bucket 0's overflow chain - none, a sound (strictly
      backward) link, or the corrupt shape.
    - the clean-cache FIFO word, oldest at the front, over the two modelled
      buckets.
    - {!walk}: what the single index thread is doing.

    ROLE MAPPING. [V1] is the WORKER that issued the archive request and is
    parked on the oneshot (consensus_pack.rs:595-600): its view is its own
    request lifecycle and NOTHING else - not the bucket geometry, not the
    chain, not the cache. [V2] is the INDEX THREAD: its view is its own
    in-memory bookkeeping - the append count, the bucket count, whether bucket
    0's head buffer carries a non-zero overflow pointer, the clean-cache word
    and the walk it is running - but NOT the link stored inside an overflow
    RECORD, because overflow records live on disk and are re-read per hop into
    a scratch buffer (bucket_iter.rs:106-113) and are never cached. That is
    exactly why the decrease guard has to exist: neither agent can tell a
    sound chain from a corrupt one until the walk reads it. Every other
    committee member ([V0], [V3] and [V4]..[V9]) is an idle non-agent with the
    constant blank view and never appears under [K].

    ABSTRACTIONS, stated so they can be attacked. (a) One append per split:
    the real threshold is 16000 values for 1000 buckets, so the model
    compresses insert time; the rotation ORDER it exercises is the real one.
    (b) The [elements >= self.header.bucket_elements()] fill test (:667) is
    abstracted to a nondeterministic choice on an append to bucket 0, because
    no statement here quantifies over the fill counter. (c) Corruption of the
    .odx is an EXTERNAL event (bit rot, truncate-then-reappend) and the model
    offers it only on the SEALED pack, where [save] returns
    [Err(AppendError::ReadOnly)] (:762-764) so the split rebuild of (b) above
    genuinely cannot run: on an append-open pack that rebuild IS a repair, and
    it is modelled there. (d) The clean-cache cap is abstracted from 400_000
    to two slots, and growth under the deleted eviction loop is truncated at
    three slots - the third slot already refutes the cap. *)

(** How many keys the modelled epoch has appended into the pack, capped at the
    two appends that complete one modulus generation. *)
type appends =
  | A0  (** nothing appended yet *)
  | A1  (** one key appended *)
  | A2  (** two keys appended; the pack is ready to be sealed at epoch close *)

(** Total order index for {!appends}. *)
let appends_index = function A0 -> 0 | A1 -> 1 | A2 -> 2

(** Total order on {!appends}. *)
let appends_compare a b = Int.compare (appends_index a) (appends_index b)

(** The next append count; [A2] is the modelled ceiling. *)
let appends_bump = function A0 -> A1 | A1 -> A2 | A2 -> A2

(** The linear-hash bucket count of the modelled index (index.rs:461-464). *)
type buckets =
  | B2  (** two buckets: nothing split yet *)
  | B3  (** three buckets: bucket 0 has been split *)
  | B4  (** four buckets: buckets 0 and 1 have both been split *)

(** Total order index for {!buckets}. *)
let buckets_index = function B2 -> 0 | B3 -> 1 | B4 -> 2

(** Total order on {!buckets}. *)
let buckets_compare a b = Int.compare (buckets_index a) (buckets_index b)

(** [self.buckets()] as an integer (index.rs:461-464). *)
let bucket_count = function B2 -> 2 | B3 -> 3 | B4 -> 4

(** [modulus = (self.buckets() + 1).next_power_of_two()] (index.rs:555, :376):
    3.next_power_of_two() = 4, 4 -> 4, 5 -> 8. *)
let modulus = function B2 -> 4 | B3 -> 4 | B4 -> 8

(** [let split_bucket = (self.buckets() - (old_modulus / 2)) as u64]
    (index.rs:549) evaluated on the modelled counts: [B2 -> 0] (the hot
    bucket), [B3 -> 1] (the cold bucket), [B4 -> 0] (the first split of the
    next generation, past the modelled window). Nothing about occupancy enters
    this expression - that is the fairness claim of S1. *)
let split_target b = bucket_count b - (modulus b / 2)

(** The next bucket count once a split has run ([inc_buckets],
    index.rs:456-459); [B4] is the modelled ceiling of one generation. *)
let buckets_grown = function B2 -> B3 | B3 -> B4 | B4 -> B4

(** The shape of the overflow chain hanging off bucket 0, the hot bucket. *)
type hot =
  | Hot_plain
      (** bucket 0's head buffer holds [overflow_pos = 0]: no chain at all *)
  | Hot_spilled
      (** bucket 0 filled and spilled: its head links to an overflow record at
          an EARLIER offset, the shape [save_to_bucket_buffer] always writes
          (index.rs:672-685) *)
  | Hot_corrupt
      (** the chained overflow record's own link points at or after itself, so
          a walk that follows it re-reads the same record forever. This is the
          shape [reset_next_overflow]'s decrease test rejects
          (bucket_iter.rs:123-126); [read_exact(...).ok()?] at
          bucket_iter.rs:113 already repairs a link that points PAST the end
          of the odx, so the shape that survives every other check is exactly
          an in-range self link whose record is individually CRC-valid *)

(** Total order index for {!hot}. *)
let hot_index = function Hot_plain -> 0 | Hot_spilled -> 1 | Hot_corrupt -> 2

(** Total order on {!hot}. *)
let hot_compare a b = Int.compare (hot_index a) (hot_index b)

(** Does bucket 0's head buffer carry a non-zero overflow pointer. This is the
    ONE bit of the chain the index thread holds in memory (it lives in the
    cached head buffer); the chained record's own link does not. *)
let hot_has_chain = function
  | Hot_plain -> false
  | Hot_spilled | Hot_corrupt -> true

(** An append that lands in a FULL bucket 0 spills it into the .odx log
    (index.rs:667-685). A second spill only lengthens a chain the model
    already represents, and the corrupt shape is not undone by appending. *)
let hot_spill = function
  | Hot_plain -> Hot_spilled
  | Hot_spilled -> Hot_spilled
  | Hot_corrupt -> Hot_corrupt

(** Which modelled bucket a clean-cache slot names. *)
type slot =
  | Slot_hot  (** bucket 0, the bucket appends and lookups contend for *)
  | Slot_cold  (** bucket 1, the rival that a hot streak can evict *)

(** Total order index for {!slot}. *)
let slot_index = function Slot_hot -> 0 | Slot_cold -> 1

(** Total order on {!slot}. *)
let slot_compare a b = Int.compare (slot_index a) (slot_index b)

(** Total order on clean-cache words: shorter first, then element by element.
    Matching a list is not matching a sum, so this stays exhaustive. *)
let rec cache_compare a b =
  match (a, b) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs, y :: ys ->
      let c = slot_compare x y in
      if Bool.not (Int.equal c 0) then c else cache_compare xs ys

(** What the single index thread is doing. The pack is append-open and then
    sealed, matching a pack's life: appends during the epoch, read-only
    service afterwards ([save] refuses on a read-only index,
    index.rs:762-764). *)
type walk =
  | Walk_appending  (** append-open: the thread is taking [Index::save] calls *)
  | Walk_ready  (** sealed, no digest lookup issued yet *)
  | Walk_pending
      (** a lookup is walking bucket 0's overflow chain: the caller is parked
          on [rx.await] (consensus_pack.rs:595-600) *)
  | Walk_answered
      (** the caller's oneshot has been resolved - with the record, with
          [NotFound], or with [CrcFailed] - and the thread has taken the next
          message *)

(** Total order index for {!walk}. *)
let walk_index = function
  | Walk_appending -> 0
  | Walk_ready -> 1
  | Walk_pending -> 2
  | Walk_answered -> 3

(** Total order on {!walk}. *)
let walk_compare a b = Int.compare (walk_index a) (walk_index b)

(** The joint global state of one archive pack's digest index. *)
type state = {
  appends : appends;  (** the model clock: keys appended so far *)
  buckets : buckets;  (** the linear-hash bucket count *)
  hot : hot;  (** bucket 0's overflow chain shape *)
  cache : slot list;  (** the clean-cache FIFO word, oldest at the front *)
  walk : walk;  (** what the single index thread is doing *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = appends_compare s1.appends s2.appends in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = buckets_compare s1.buckets s2.buckets in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = hot_compare s1.hot s2.hot in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = cache_compare s1.cache s2.cache in
        if Bool.not (Int.equal c3 0) then c3 else walk_compare s1.walk s2.walk

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** What the parked worker of [ConsensusPack::batch] can observe: it sent a
    request and it is either still awaiting the oneshot or holding the answer.
    It cannot observe anything about the index. *)
type request =
  | Req_none  (** no request in flight *)
  | Req_pending  (** parked on [rx.await] with no timeout *)
  | Req_answered  (** the oneshot resolved *)

(** Total order index for {!request}. *)
let request_index = function
  | Req_none -> 0
  | Req_pending -> 1
  | Req_answered -> 2

(** Total order on {!request}. *)
let request_compare a b = Int.compare (request_index a) (request_index b)

(** The request lifecycle a worker sees, from the thread's walk state. *)
let request_of = function
  | Walk_appending | Walk_ready -> Req_none
  | Walk_pending -> Req_pending
  | Walk_answered -> Req_answered

(** A validator's local view.

    - [View_worker]: V1, the worker parked on the oneshot. It sees ONLY its
      own request lifecycle - not the bucket count, not the chain, not the
      cache, and above all not whether a pending walk will ever return.
    - [View_index]: V2, the index thread. It sees its own in-memory
      bookkeeping - append count, bucket count, whether bucket 0's head buffer
      carries a non-zero overflow pointer, the clean-cache word, and the walk
      it is running - but NOT the link inside the chained overflow record,
      which is on disk and re-read per hop into a scratch buffer
      (bucket_iter.rs:106-113).
    - [View_idle]: the constant blank view of the non-agents V0 and V3. *)
type view =
  | View_worker of request
  | View_index of appends * buckets * bool * slot list * walk
  | View_idle

(** Total order on the index thread's view tuple. *)
let view_index_compare (a1, b1, c1, k1, w1) (a2, b2, c2, k2, w2) =
  let c = appends_compare a1 a2 in
  if Bool.not (Int.equal c 0) then c
  else
    let cb = buckets_compare b1 b2 in
    if Bool.not (Int.equal cb 0) then cb
    else
      let cc = Bool.compare c1 c2 in
      if Bool.not (Int.equal cc 0) then cc
      else
        let ck = cache_compare k1 k2 in
        if Bool.not (Int.equal ck 0) then ck else walk_compare w1 w2

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_worker _ | View_index _) -> -1
  | (View_worker _ | View_index _), View_idle -> 1
  | View_worker ra, View_worker rb -> request_compare ra rb
  | View_worker _, View_index _ -> -1
  | View_index _, View_worker _ -> 1
  | View_index (a1, b1, c1, k1, w1), View_index (a2, b2, c2, k2, w2) ->
      view_index_compare (a1, b1, c1, k1, w1) (a2, b2, c2, k2, w2)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 (the parked worker) and V2 (the index thread) are the
    knowledge agents; every other committee member is an idle non-agent with
    the constant blank view and never appears under [K]. *)
let view v s =
  match v with
  | Validator.V1 -> View_worker (request_of s.walk)
  | Validator.V2 ->
      View_index (s.appends, s.buckets, hot_has_chain s.hot, s.cache, s.walk)
  | Validator.V0 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as written at 0c59c15b *)
  | No_growth_gate
      (** delete the [while self.header.values >= (self.capacity as f32 *
          self.header.load_factor()) as u64] condition of [expand_buckets]
          (index.rs:441), making it a no-op: no bucket is ever split, so the
          bucket count never leaves [B2] and neither the hot nor the cold
          bucket is ever rebuilt. No sibling path repairs the ROTATION:
          [split_one_bucket] (:546) has exactly one caller, [expand_buckets]
          (:442), and [inc_buckets] (:456-459) has exactly one caller,
          [split_one_bucket] (:550), so there is no second growth route. The
          overflow spill (:667-685) IS a sibling and it IS modelled - appends
          keep landing and lookups keep answering with the gate gone, which is
          why this mutation must not, and does not, refute S3. What it repairs
          is index CORRECTNESS, not the rotation. *)
  | No_cache_eviction_loop
      (** delete the [while self.bucket_cache_fifo.len() >=
          Self::CACHED_BUCKETS { if let Some(bucket) =
          self.bucket_cache_fifo.pop_front() { self.bucket_cache.remove(
          &bucket); } }] loop (index.rs:428-432), so admission never evicts
          and the word grows past the cap. Nothing else ever removes an entry
          from the CLEAN cache: [remove_bucket_cache] (:471-478) and
          [remove_bucket] (:482-504) take a buffer out only to hand it to a
          writer and [save_to_bucket] puts it straight back into the DIRTY map
          (:601-609); [save_bucket_cache] drains the dirty map (:512) and
          re-inserts every drained bucket through this very function
          (:520-522), feeding the bound rather than replacing it; [Drop]
          (:723-758) flushes but never evicts; and there is no memory-pressure
          hook or time-based expiry anywhere in the crate. *)
  | No_chain_decrease_guard
      (** delete [if next_overflow_pos != 0 && next_overflow_pos >=
          current_pos { self.crc_failure = true; return None; }]
          (bucket_iter.rs:123-126), so a walk that reaches a self-linked
          overflow record re-reads it forever: modelled as a pending walk with
          no successor. No sibling path repairs it. [next_bucket_element]
          (bucket_iter.rs:142-169) has no visit counter and no depth cap; the
          per-record [check_crc] (bucket_iter.rs:114-117) passes because the
          record is individually valid; the [read_exact(...).ok()?] at
          bucket_iter.rs:113 repairs only a link past the end of the odx, not
          an in-range self link; the caller has no [tokio::time::timeout]
          (consensus_pack.rs:595-600, the file's only timeouts being the async
          stream reader at :1409-1419 and a test at :2042); and because
          [run_pack_loop] is ONE blocking thread (:132-193) no split, flush or
          repair can run while the walk spins. *)

(** The eviction loop of [add_bucket_to_cache] (index.rs:428-432) written as
    the same [while len >= cap] recursion with the modelled cap of two. *)
let rec cache_evict_to_cap w =
  match w with [] | [ _ ] -> w | _ :: rest -> cache_evict_to_cap rest

(** Admission with the eviction loop deleted: the word simply grows. The model
    stops it at three slots - one slot past the cap is already a refutation
    and more slots only enlarge the graph. *)
let cache_admit_unbounded slot w =
  match w with
  | [] | [ _ ] | [ _; _ ] -> w @ [ slot ]
  | _ :: _ :: _ :: _ -> w

(** [add_bucket_to_cache] (index.rs:422-435): evict from the front until below
    the cap, then insert and push the name onto the back. Duplicates are
    admitted - nothing checks whether [slot] is already queued. *)
let cache_admit mut slot w =
  match mut with
  | Pristine | No_growth_gate | No_chain_decrease_guard ->
      cache_evict_to_cap w @ [ slot ]
  | No_cache_eviction_loop -> cache_admit_unbounded slot w

(** The bucket count after one [Index::save] (index.rs:768 then :442). *)
let buckets_after_save mut b =
  match mut with
  | No_growth_gate -> b
  | Pristine | No_cache_eviction_loop | No_chain_decrease_guard ->
      buckets_grown b

(** Bucket 0's chain after one [Index::save]. When the split scheduled for the
    CURRENT bucket count targets bucket 0, [split_one_bucket] rebuilds it into
    two fresh zeroed buffers (index.rs:557-559, :595-596) and the chain is
    discarded; otherwise the chain is untouched. *)
let hot_after_save mut s =
  match mut with
  | No_growth_gate -> s.hot
  | Pristine | No_cache_eviction_loop | No_chain_decrease_guard ->
      if Int.equal 0 (split_target s.buckets) then Hot_plain else s.hot

(** Successors while the pack is append-open: one [Index::save], whose key
    either fits in bucket 0 or overflows it, until the modelled epoch has
    appended its two keys and the pack is sealed at epoch close. *)
let next_appending mut s =
  match s.appends with
  | A2 -> [ { s with walk = Walk_ready } ]
  | A0 | A1 ->
      let base =
        {
          s with
          appends = appends_bump s.appends;
          buckets = buckets_after_save mut s.buckets;
          hot = hot_after_save mut s;
        }
      in
      [ base; { base with hot = hot_spill base.hot } ]

(** Successors while the sealed pack's thread is free: serve a lookup of the
    hot bucket or of the cold bucket, or suffer an external corruption of the
    .odx record bucket 0 is chained to. A lookup of a bucket with no chain
    answers within the message; a lookup of a chained bucket has to walk. *)
let next_serving mut s =
  let answer_cold =
    { s with walk = Walk_answered; cache = cache_admit mut Slot_cold s.cache }
  in
  let lookup_hot =
    match s.hot with
    | Hot_plain ->
        { s with walk = Walk_answered; cache = cache_admit mut Slot_hot s.cache }
    | Hot_spilled | Hot_corrupt -> { s with walk = Walk_pending }
  in
  let corruption =
    match s.hot with
    | Hot_spilled -> [ { s with hot = Hot_corrupt } ]
    | Hot_plain | Hot_corrupt -> []
  in
  answer_cold :: lookup_hot :: corruption

(** Successors of a walk in progress. A sound chain terminates; a corrupt one
    terminates too, because the decrease guard turns it into a [crc_failure]
    that [fetch_position] reports as [Err(FetchError::CrcFailed)]
    (index.rs:630-646) - an answer. With the guard deleted the walk re-reads
    the self-linked record forever, which is the empty successor list: a
    stutter-closed terminal on which [Af answered] fails. *)
let next_pending mut s =
  let answered =
    { s with walk = Walk_answered; cache = cache_admit mut Slot_hot s.cache }
  in
  match s.hot with
  | Hot_plain | Hot_spilled -> [ answered ]
  | Hot_corrupt -> (
      match mut with
      | Pristine | No_growth_gate | No_cache_eviction_loop -> [ answered ]
      | No_chain_decrease_guard -> [])

(** The transition relation: one archive message, or one external corruption
    event, per step - the service is a single blocking thread. *)
let next_with mut s =
  match s.walk with
  | Walk_appending -> next_appending mut s
  | Walk_ready | Walk_answered -> next_serving mut s
  | Walk_pending -> next_pending mut s

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: a freshly opened, append-open pack with two buckets, an
    empty bucket 0, an empty clean cache and no request in flight. *)
let initial =
  { appends = A0; buckets = B2; hot = Hot_plain; cache = []; walk = Walk_appending }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Append_open  (** the pack is append-open: [Index::save] is still accepted *)
  | Hot_bucket_split  (** bucket 0 has been rebuilt by a split *)
  | Cold_bucket_split  (** bucket 1 has been rebuilt by a split *)
  | Hot_overflowed  (** bucket 0's head carries a non-zero overflow pointer *)
  | Chain_corrupt  (** the chained overflow record links at or after itself *)
  | Cache_over_cap  (** the clean-cache word holds more slots than the cap *)
  | Cache_at_cap  (** the clean-cache word holds exactly the cap *)
  | Cache_all_hot  (** the word is non-empty and every slot names bucket 0 *)
  | Cold_resident  (** some slot of the word names bucket 1 *)
  | Lookup_pending  (** a digest lookup is walking; the caller is parked *)
  | Lookup_answered  (** the caller's oneshot has been resolved *)

(** Is this slot bucket 0. *)
let slot_is_hot = function Slot_hot -> true | Slot_cold -> false

(** Is this slot bucket 1. *)
let slot_is_cold = function Slot_hot -> false | Slot_cold -> true

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Append_open -> (
      match s.walk with
      | Walk_appending -> true
      | Walk_ready | Walk_pending | Walk_answered -> false)
  | Hot_bucket_split -> (
      match s.buckets with B2 -> false | B3 | B4 -> true)
  | Cold_bucket_split -> (
      match s.buckets with B2 | B3 -> false | B4 -> true)
  | Hot_overflowed -> hot_has_chain s.hot
  | Chain_corrupt -> (
      match s.hot with Hot_plain | Hot_spilled -> false | Hot_corrupt -> true)
  | Cache_over_cap -> (
      match s.cache with
      | [] | [ _ ] | [ _; _ ] -> false
      | _ :: _ :: _ :: _ -> true)
  | Cache_at_cap -> (
      match s.cache with
      | [] | [ _ ] -> false
      | [ _; _ ] -> true
      | _ :: _ :: _ :: _ -> false)
  | Cache_all_hot -> (
      match s.cache with
      | [] -> false
      | _ :: _ -> List.for_all slot_is_hot s.cache)
  | Cold_resident -> List.exists slot_is_cold s.cache
  | Lookup_pending -> (
      match s.walk with
      | Walk_pending -> true
      | Walk_appending | Walk_ready | Walk_answered -> false)
  | Lookup_answered -> (
      match s.walk with
      | Walk_answered -> true
      | Walk_appending | Walk_ready | Walk_pending -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Append_open -> "append_open"
  | Hot_bucket_split -> "split(b0)"
  | Cold_bucket_split -> "split(b1)"
  | Hot_overflowed -> "overflow_chain(b0)"
  | Chain_corrupt -> "link(b0)>=self"
  | Cache_over_cap -> "|fifo|>CACHED_BUCKETS"
  | Cache_at_cap -> "|fifo|=CACHED_BUCKETS"
  | Cache_all_hot -> "fifo=b0^+"
  | Cold_resident -> "cached(b1)"
  | Lookup_pending -> "walking(d)"
  | Lookup_answered -> "answered(d)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every
    reachable world by test/t_archive_hash_index_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state, the
    mutation-parameterized transitions, the two-agent view, the atom
    valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
