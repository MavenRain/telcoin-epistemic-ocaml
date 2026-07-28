(** Finite interpreted system for the STORE_NOTIFY_VISIBILITY family: the window
    between a certificate write becoming visible in a validator's own store and
    the waiters on that digest being told about it. File citations refer to
    Telcoin-Association/telcoin-network at git HEAD [0c59c15b]; every line range
    below was opened in that checkout.

    THE MODELLED MECHANISM. A primary that is asked to vote on a peer's header
    must hold every parent certificate the header names. It does not fetch them
    inline: [HeaderValidator.notify_read_parent_certificates] builds a
    [FuturesOrdered] of one [CertificateStore::notify_read] per parent digest and
    awaits them all before the vote (header_validator.rs:56-63), and the vote
    handler's own comment says "If any are missing, this call will wait until
    they are stored in the db ... NOTE: this check is necessary for correctness"
    (handler.rs:688-693). Four seams follow, and this family is about all four.

    - REGISTER, THEN RE-READ. [notify_read] (certificate_store.rs:251-269) first
      registers a oneshot on the process-wide subscriber table
      ([NOTIFY_SUBSCRIBERS], a [LazyLock<NotifyRead<HeaderDigest, Certificate>>]
      at :19-20; [register_one] at :253 -> notify_read.rs:44-49) and only THEN
      re-reads the store, under the comment "let's read the value because we
      might have missed the opportunity to get notified about it": on a hit it
      calls [NOTIFY_SUBSCRIBERS.notify(&id, &cert)] and returns the certificate
      directly (:255-263), and only on a miss does it [receiver.await] (:266).
      Registration and the store write are NOT under a common lock - the
      per-key shard mutex (notify_read.rs:26, :68-74) covers the pending map
      only - so the re-read is the sole thing that turns a registration made
      after the write into a resolution rather than a permanent wait.
    - ONE NOTIFY SERVES THE WHOLE REGISTRATION LIST. [NotifyRead::notify]
      (notify_read.rs:31-42) takes the entire list out of the map with
      [self.pending(key).remove(key)] (:33) and then fires EVERY sender
      (:38-40). Registration appends without priority (:64-66). So waiters on a
      digest are served as a set, never as a queue - and a sender that the
      notify drops is gone from the map for good.
    - THE WRITE IS VISIBLE BEFORE IT IS COMMITTED. The single notify site for
      certificates is inside [save_cert] (certificate_store.rs:144), reached by
      both write paths ([write] :176-186, [write_all] :191-209), and it fires
      BEFORE [txn.commit()] (:183, :206). What makes that safe is
      [LayeredDbTxMut::insert] (layered_db.rs:96-102), which writes the mem
      layer FIRST ([self.mem_db.insert::<T>(key, value)?;] at :98) and only then
      queues [DBMessage::Insert] for the background writer thread (:100). Reads
      have exactly two sources and mem is the first: [LayeredDatabase::get]
      (:383-389), [contains_key] (:375-381), [is_empty] (:412-418), [iter]
      (:423-429).
    - THE COMMIT IS ASYNCHRONOUS AND UNOBSERVABLE. [LayeredDbTxMut::commit]
      (:125-134) only queues [DBMessage::CommitTxn]; its own doc comment warns
      that "when this returns, the data may not be committed on-disk yet"
      (:118-124). The physical commit happens later, on the writer thread, in
      [end_txn] (:155-174, dispatched from :199-201 and :202-208).

    SCOPE CORRECTION vs the candidate card (R7). The card proposed a third
    statement about the commit-then-clear ordering of the cache mirror
    (layered_db.rs:160-169). That ordering does NOT apply to the certificate
    store: [Certificates] carries [TableHint::Epoch] (lib.rs:91), the composite
    DB opens the epoch layer with [LayeredDatabase::open(epoch_db, true)]
    (composite_db.rs:33), and [full_memory = true] hands the writer thread
    [mem_db = None] (layered_db.rs:311), which makes the retention push
    (:217-219), the post-commit drain (:165-169) and the direct-write clear
    (:224-226) all dead code for this table. The mirror is therefore never
    evicted here, and the load-bearing visibility gate for a certificate is the
    mem-FIRST write at :98, not the drain ordering. The statement was re-aimed
    at that gate; the drain ordering belongs to a cache-hint table
    ([NodeBatchesCache], [OurNodeBatchesCache], [ConsensusCache], lib.rs:97-102)
    and is out of this family's scope.

    COMPONENTS (seven; the pristine reachable graph is exactly 36 states).
    - [possessed] : the hidden global fact "some honest validator possesses the
      certificate for digest d". A header names parent digests and nothing more,
      so a Byzantine author can name a digest of nothing; this bit is the branch
      between a real parent and a fabricated one. It is rigid (no transition
      changes it) and it gates [save_cert]: a certificate nobody holds is never
      delivered and never written.
    - [written] : [save_cert] for d has executed (certificate_store.rs:129-147).
      Monotone run history.
    - [mem] : the epoch mem layer holds d, i.e. [LayeredDatabase::get] answers
      from :384 (layered_db.rs:383-389). Set by the mem-first insert at :98.
      Never cleared: this table is full-memory (see the scope correction).
    - [dur] : the background thread's physical [current_txn.commit()] for d's
      txn has returned (layered_db.rs:162 inside [end_txn]).
    - [deliv_closed] : the network has finished delivering d - no further
      [save_cert] for this digest will run. The duplicate-write sibling is REAL
      ([accept_verified_certificates] calls [write_all] on every unlocked
      certificate with no already-stored filter, cert_manager.rs:189-196 reached
      from :124 and :237; [handler.rs:267] re-writes gossiped certificates while
      catching up) and it is modelled as an explicit nondeterministic branch:
      from a state with a pending registration the model may either re-deliver
      once (which notifies again) or close delivery. Without that branch a
      re-delivery would be forced on every path and the liveness mutation below
      would be silently repaired.
    - [w1], [w2] : two CONCURRENT [notify_read] callers inside one validator,
      one per inbound vote request, each waiting on the same parent digest.
      Concurrency is structural, not hypothetical: [process_vote_request]
      spawns ONE task per inbound vote request (network/mod.rs:1517-1530), each
      of which runs [request_handler.vote] (:1532) down to the parent wait
      (handler.rs:688-693), and they all share the one process-wide
      [NOTIFY_SUBSCRIBERS] static (certificate_store.rs:19-20). Two headers of
      the same round name overlapping round-(r-1) parents, so two such tasks
      parked on ONE digest is the normal case. Their lifecycle is {!waiter}.

    ROLE MAPPING. The knowledge agents are the two waiting request handlers.
    - V1 is the FIRST handler. Its view is [(w1, store_visible)]: the state of
      its own [notify_read] call, plus the answer its own store gives - the only
      two things it observes. It does NOT see [possessed] (a fact about other
      validators' stores; the header carries digests, not certificates), does
      NOT see [dur] (the commit is asynchronous and reports nothing: :118-124,
      [persist]/[sync_persist] are answered by a bare oneshot at :247-249 and
      :463-495, and [LayeredDatabase::stats] :317-333 is called by no consensus
      path), and does NOT see [w2] (a different task's registration lives in a
      shard-locked private map, notify_read.rs:19, :64-74; [num_pending] :76-78
      is a bare count that no consensus path reads, and [save_cert] discards
      even the count [notify] returns, certificate_store.rs:144).
    - V2 is the SECOND handler, view [(w2, store_visible)] - the same
      projection over its own call. It likewise sees neither [possessed] nor
      [dur] nor [w1].
    - V0 and V3..V9 are idle: constant blank view, never under K. *)

(** The lifecycle of ONE concurrent [CertificateStore::notify_read] call on the
    parent digest d (certificate_store.rs:251-269). *)
type waiter =
  | W_idle
      (** the handler has not yet entered [notify_read] for d - no header
          naming d has reached it *)
  | W_want
      (** the handler is inside [notify_read_parent_certificates]
          (header_validator.rs:56-63) but has not yet reached [register_one]
          (certificate_store.rs:253). This is the window the write can slip
          through. *)
  | W_reg
      (** [register_one] has pushed a oneshot sender onto the pending list for
          d (notify_read.rs:64-66) and the call is parked on [receiver.await]
          (certificate_store.rs:266) *)
  | W_done
      (** the call returned the certificate, either from the re-read
          (certificate_store.rs:262) or from the oneshot the notify fired
          (notify_read.rs:39) *)
  | W_lost
      (** the registration's sender was taken out of the map by [remove(key)]
          (notify_read.rs:33) and then DROPPED instead of sent. Unreachable on
          the pristine model; it is what the fan-out deletion creates, and it is
          terminal because the sender is no longer in the map for any later
          notify to find. *)

(** Total order index for {!waiter}. *)
let waiter_index = function
  | W_idle -> 0
  | W_want -> 1
  | W_reg -> 2
  | W_done -> 3
  | W_lost -> 4

(** Total order on {!waiter}. *)
let waiter_compare a b = Int.compare (waiter_index a) (waiter_index b)

(** [true] iff the handler has not entered [notify_read] yet. *)
let waiter_is_idle = function
  | W_idle -> true
  | W_want -> false
  | W_reg -> false
  | W_done -> false
  | W_lost -> false

(** [true] iff the handler is inside [notify_read] but before [register_one]. *)
let waiter_is_want = function
  | W_idle -> false
  | W_want -> true
  | W_reg -> false
  | W_done -> false
  | W_lost -> false

(** [true] iff the handler has a live registration parked on the oneshot. *)
let waiter_is_reg = function
  | W_idle -> false
  | W_want -> false
  | W_reg -> true
  | W_done -> false
  | W_lost -> false

(** [true] iff the handler's [notify_read] returned the certificate. *)
let waiter_is_done = function
  | W_idle -> false
  | W_want -> false
  | W_reg -> false
  | W_done -> true
  | W_lost -> false

(** [true] iff the handler's sender was dropped out of the pending map. *)
let waiter_is_lost = function
  | W_idle -> false
  | W_want -> false
  | W_reg -> false
  | W_done -> false
  | W_lost -> true

(** The joint global state. There is no separate "queued write" component: the
    mem write and the queue send happen in the same call
    (layered_db.rs:96-102), so a queued-but-unapplied write is exactly
    [written && Bool.not dur]. *)
type state = {
  possessed : bool;
      (** hidden: some honest validator possesses the certificate for d. Rigid;
          gates [save_cert] because a certificate nobody holds is never
          delivered *)
  written : bool;
      (** [save_cert] for d has executed (certificate_store.rs:129-147) *)
  mem : bool;
      (** the epoch mem layer holds d, i.e. [get] answers from
          layered_db.rs:384; set by the mem-first insert at :98 *)
  dur : bool;
      (** the background thread's [current_txn.commit()] for d's txn returned
          (layered_db.rs:162) *)
  deliv_closed : bool;
      (** the network will deliver d no more times - the duplicate-write budget
          is spent (cert_manager.rs:189-196, handler.rs:267) *)
  w1 : waiter;  (** the first concurrent [notify_read] caller, V1's call *)
  w2 : waiter;  (** the second concurrent [notify_read] caller, V2's call *)
}

(** Total deterministic comparison over ALL state fields, in field order
    [possessed, written, mem, dur, deliv_closed, w1, w2]. *)
let state_compare s1 s2 =
  let c = Bool.compare s1.possessed s2.possessed in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Bool.compare s1.written s2.written in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Bool.compare s1.mem s2.mem in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare s1.dur s2.dur in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.deliv_closed s2.deliv_closed in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = waiter_compare s1.w1 s2.w1 in
            if Bool.not (Int.equal c5 0) then c5 else waiter_compare s1.w2 s2.w2

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** What [CertificateStore::read] answers for d: [LayeredDatabase::get] tries
    the mem layer and falls through to the physical layer, and there is no third
    source (layered_db.rs:383-389). *)
let store_visible s = s.mem || s.dur

(** A validator's local view. Both agents are concurrent [notify_read] callers
    inside ONE validator; each sees the state of its own call plus the answer
    the shared store gives it, and nothing else. The projection deliberately
    EXCLUDES [possessed] (a fact about other validators' stores - a header
    carries parent DIGESTS, not certificates), [dur] (the commit is
    asynchronous and reports nothing, layered_db.rs:118-124, :247-249,
    :463-495) and the other handler's [waiter] (registrations live in a
    shard-locked private map, notify_read.rs:19, :64-74). *)
type view =
  | View_v1 of waiter * bool
      (** V1, the first handler: (its own [notify_read] state, the store's
          answer) *)
  | View_v2 of waiter * bool
      (** V2, the second handler: (its own [notify_read] state, the store's
          answer) *)
  | View_idle  (** the constant blank view of the non-agents V0, V3..V9 *)

(** Total deterministic order over ALL fields of a handler's projection. *)
let handler_view_compare (w, v) (w', v') =
  let c = waiter_compare w w' in
  if Bool.not (Int.equal c 0) then c else Bool.compare v v'

(** Total order on views: [View_idle] < [View_v1] < [View_v2], with the
    field-wise order within each constructor. Every constructor pairing is
    spelled: no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_v1 _ | View_v2 _) -> -1
  | (View_v1 _ | View_v2 _), View_idle -> 1
  | View_v1 (w, v), View_v1 (w', v') -> handler_view_compare (w, v) (w', v')
  | View_v1 _, View_v2 _ -> -1
  | View_v2 _, View_v1 _ -> 1
  | View_v2 (w, v), View_v2 (w', v') -> handler_view_compare (w, v) (w', v')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 and V2 are the two concurrent [notify_read] callers and
    the only knowledge agents; V0 and V3..V9 are idle non-agents with the
    constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V1 -> View_v1 (s.w1, store_visible s)
  | Validator.V2 -> View_v2 (s.w2, store_visible s)
  | Validator.V0 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at HEAD [0c59c15b] *)
  | No_post_registration_reread
      (** delete the whole post-registration re-read block of
          [CertificateStore::notify_read] - [if let Ok(Some(cert)) =
          self.read(id) { NOTIFY_SUBSCRIBERS.notify(&id, &cert); return
          Ok(cert); }] at certificate_store.rs:255-263 - so [register_one]
          (:253) is followed straight by [receiver.await] (:266). This REMOVES
          the transition "a handler that registers while the store already
          holds d resolves immediately", and with it the second, subtler effect
          of that block: the [notify] at :259, by which one handler's re-read
          also wakes any OTHER handler already parked on the same digest.

          Why no sibling path repairs it. (a) The only other notify site for
          certificates is [save_cert] (certificate_store.rs:144) - a SECOND
          write of the same digest really does notify again, and that duplicate
          is real ([accept_verified_certificates] calls [write_all] with no
          already-stored filter, cert_manager.rs:189-196; handler.rs:267
          re-writes gossiped certificates while catching up), so it is MODELLED
          here as the [deliv_closed] branch - but it depends on the network
          re-delivering a certificate the node already holds, which nothing
          guarantees, and the single-delivery branch has no second notify at
          all. (b) There is no timeout on the production caller: the
          [FuturesOrdered] at header_validator.rs:56-63 is awaited bare, and
          only tests wrap it (certificate_processing_tests.rs uses
          [timeout(Duration::from_secs(3), ...)]). The RPC-level cancellation
          handler.rs:688-690 mentions bounds the resource, not the property.
          (c) [Registration::poll] (notify_read.rs:109-125) awaits the oneshot
          and nothing else, and [Registration::drop] (:127-135) only
          de-registers - neither re-arms nor resolves. *)
  | No_notify_fanout
      (** delete the fan-out loop [for registration in registrations {
          registration.send(value.clone()).ok(); }] of [NotifyRead::notify]
          (notify_read.rs:38-40) and send to a single registration instead. The
          transition "a write resolves every parked handler" is replaced by "a
          write resolves one parked handler and strands the rest": the model
          serves the lowest-indexed live registration and moves the others to
          {!W_lost}.

          Why no sibling path repairs it. [remove(key)] at notify_read.rs:33
          has ALREADY taken the whole list out of the sharded map before the
          send, so a stranded sender is no longer reachable by any later
          [notify] - not by a duplicate [save_cert] (certificate_store.rs:144)
          and not by another handler's re-read notify (:259), both of which
          re-enter the same [notify] and find the key absent (:34-36). The
          model reflects that by making {!W_lost} terminal. On the real code
          the stranded receiver does not even fail quietly: the dropped sender
          makes [Registration::poll]'s [.expect("Sender never drops when
          registration is pending")] (notify_read.rs:123) panic. There is no
          polling loop and no re-arm anywhere on this path. *)
  | No_mem_write_on_insert
      (** delete the mem-layer write [self.mem_db.insert::<T>(key, value)?;]
          from [LayeredDbTxMut::insert] (layered_db.rs:98) together with its
          sibling in the non-txn [LayeredDatabase::insert] (:392), leaving both
          routes to queue [DBMessage::Insert] only. The write is then invisible
          to every reader until the background thread's [current_txn.commit()]
          returns, so this ADDS states in which [save_cert] has run - and has
          already fired its notify at certificate_store.rs:144 - while
          [read(id)] still answers [None].

          Why both routes and not one: [save_cert] reaches the store through
          [txn.insert::<Certificates>] (certificate_store.rs:134) inside
          [write]/[write_all]'s [self.write_txn()] (:177, :195), i.e. through
          :98; but :98 and :392 are byte-identical siblings and deleting only
          one invites the objection that the other repairs it. Why nothing else
          repairs it: reads have exactly two sources and no retry -
          [LayeredDatabase::get] (:383-389), [contains_key] (:375-381),
          [is_empty] (:412-418), [iter] (:423-429) - [MemDatabase::get]
          (mem_db.rs:145-147, via the free function at :12-21) returns [None]
          silently rather than erroring, so a hole is indistinguishable from a
          genuine absence; the background thread's [insert_txn] (:210-219)
          writes into an UNCOMMITTED physical txn, invisible to the separate
          read the reader opens; and the only re-population of the mem layer,
          [open_table]'s preload (:347-356), runs once at process start. *)

(** [true] iff the caller re-reads the store after registering
    (certificate_store.rs:255-263). *)
let reread_enabled = function
  | Pristine -> true
  | No_notify_fanout -> true
  | No_mem_write_on_insert -> true
  | No_post_registration_reread -> false

(** What the mem layer holds after a [save_cert] for d: the mem-first insert at
    layered_db.rs:98 makes it present immediately, unless that write is the
    deleted gate. *)
let mem_after_write = function
  | Pristine -> true
  | No_post_registration_reread -> true
  | No_notify_fanout -> true
  | No_mem_write_on_insert -> false

(** Resolve a parked registration: the sender fired
    (notify_read.rs:39), so [receiver.await] returns the certificate. *)
let wake = function
  | W_idle -> W_idle
  | W_want -> W_want
  | W_reg -> W_done
  | W_done -> W_done
  | W_lost -> W_lost

(** Strand a parked registration: [remove(key)] (notify_read.rs:33) already
    took its sender out of the map and the mutated notify then dropped it
    without sending, so no later notify can ever find it. *)
let strand = function
  | W_idle -> W_idle
  | W_want -> W_want
  | W_reg -> W_lost
  | W_done -> W_done
  | W_lost -> W_lost

(** The pristine notify: the whole registration list is removed under the shard
    lock and EVERY sender is fired (notify_read.rs:31-42). *)
let notify_fanout (a, b) = (wake a, wake b)

(** The mutated notify: the list is still removed whole, but only the first
    live registration is sent to and the rest are dropped. The model fixes "the
    first" as the lowest-indexed live registration; the real list is in
    push order (notify_read.rs:65), and which single registrant wins does not
    change the property - one of them is starved either way. *)
let notify_single (a, b) =
  if waiter_is_reg a then (wake a, strand b)
  else if waiter_is_reg b then (a, wake b)
  else (a, b)

(** Apply the store's wakeup to both handler slots under a mutation. *)
let notify_with mut pair =
  match mut with
  | Pristine -> notify_fanout pair
  | No_post_registration_reread -> notify_fanout pair
  | No_mem_write_on_insert -> notify_fanout pair
  | No_notify_fanout -> notify_single pair

(** [enabled_list guard successors] is [successors] when the guard holds and the
    empty list otherwise. *)
let enabled_list guard successors = if guard then successors else []

(** T1 - a vote request naming d as a parent reaches an idle handler, which
    enters [notify_read_parent_certificates] (header_validator.rs:56-63). The
    header carries parent DIGESTS only, so this fires whether or not any
    validator actually possesses d. *)
let t1_enter_wait s =
  List.concat
    [
      enabled_list (waiter_is_idle s.w1) [ { s with w1 = W_want } ];
      enabled_list (waiter_is_idle s.w2) [ { s with w2 = W_want } ];
    ]

(** The successor of a handler reaching [register_one] and then, if the block is
    present, the post-registration re-read (certificate_store.rs:253-263). On a
    re-read hit the caller returns directly (:262) AND notifies (:259), which is
    why the other slot goes through [notify_with] too. *)
let register_step mut s ~self_is_first =
  if reread_enabled mut && store_visible s then
    let pair = if self_is_first then (W_done, s.w2) else (s.w1, W_done) in
    let a, b = notify_with mut pair in
    { s with w1 = a; w2 = b }
  else if self_is_first then { s with w1 = W_reg }
  else { s with w2 = W_reg }

(** T2 - a waiting handler registers its oneshot and (pristine) re-reads the
    store (certificate_store.rs:253-263). *)
let t2_register mut s =
  List.concat
    [
      enabled_list (waiter_is_want s.w1)
        [ register_step mut s ~self_is_first:true ];
      enabled_list (waiter_is_want s.w2)
        [ register_step mut s ~self_is_first:false ];
    ]

(** T3 - the certificate for d arrives and [save_cert] runs
    (certificate_store.rs:129-147): the mem-first insert makes it readable
    (layered_db.rs:98), the durable insert is queued (:100), and the notify at
    certificate_store.rs:144 fires - all before [txn.commit()] at :183/:206.
    Gated on [possessed]: a digest nobody holds is never delivered. *)
let t3_save_cert mut s =
  enabled_list
    (s.possessed && Bool.not s.written)
    (let a, b = notify_with mut (s.w1, s.w2) in
     [ { s with written = true; mem = mem_after_write mut; w1 = a; w2 = b } ])

(** T4 - the background writer thread commits the physical txn
    ([current_txn.commit()] in [end_txn], layered_db.rs:162, dispatched from
    :199-201 and :202-208). Nothing on the consensus path observes this. *)
let t4_background_commit s =
  enabled_list (s.written && Bool.not s.dur) [ { s with dur = true } ]

(** [true] iff some handler is parked on a live registration for d. *)
let some_registration_pending s = waiter_is_reg s.w1 || waiter_is_reg s.w2

(** T5 - THE DUPLICATE-WRITE SIBLING. The certificate is delivered a second time
    and written again ([accept_verified_certificates] -> [write_all] with no
    already-stored filter, cert_manager.rs:189-196; [handler.rs:267] for a
    catching-up node), so [save_cert] notifies a second time
    (certificate_store.rs:144). Bounded to one re-delivery, and paired with T6
    so that declining the re-delivery is a genuine branch rather than a step
    every path is forced through. *)
let t5_redeliver mut s =
  enabled_list
    (s.written && Bool.not s.deliv_closed && some_registration_pending s)
    (let a, b = notify_with mut (s.w1, s.w2) in
     [
       {
         s with
         deliv_closed = true;
         mem = mem_after_write mut;
         w1 = a;
         w2 = b;
       };
     ])

(** T6 - the single-delivery branch: the network delivers d no further times, so
    no second [save_cert] and no second notify ever happens. This is the branch
    on which the re-read of certificate_store.rs:255-263 is the ONLY thing that
    can resolve a registration made after the write. *)
let t6_close_delivery s =
  enabled_list
    (s.written && Bool.not s.deliv_closed && some_registration_pending s)
    [ { s with deliv_closed = true } ]

(** The transition relation: the six families unioned, one step per successor.
    Every step strictly advances a monotone component ([written], [mem], [dur],
    [deliv_closed] or a handler along [W_idle < W_want < W_reg < W_done/W_lost])
    and no step ever moves one back, so the reachable graph is acyclic and a
    state with no successor is stutter-closed by the kernel - which is what
    makes [Af] honest here. *)
let next_with mut s =
  List.concat
    [
      t1_enter_wait s;
      t2_register mut s;
      t3_save_cert mut s;
      t4_background_commit s;
      t5_redeliver mut s;
      t6_close_delivery s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The HONEST-PARENT initial state: the header being voted on names a real
    parent digest, some other validator holds that certificate, and nothing has
    happened yet - no handler is waiting, nothing is written, nothing is
    committed. *)
let initial =
  {
    possessed = true;
    written = false;
    mem = false;
    dur = false;
    deliv_closed = false;
    w1 = W_idle;
    w2 = W_idle;
  }

(** The FABRICATED-PARENT initial state: the header's author invented the parent
    digest and no validator anywhere holds a certificate for it, so [save_cert]
    never runs on this branch. It is the other half of every ignorance witness
    in this family - it is view-indistinguishable, for both handlers, from the
    pre-write states of {!initial}. *)
let initial_fabricated =
  {
    possessed = false;
    written = false;
    mem = false;
    dur = false;
    deliv_closed = false;
    w1 = W_idle;
    w2 = W_idle;
  }

(** Both initial states: the model branches on the hidden fact at time zero
    because a validator receiving a header cannot tell the two apart. *)
let inits = [ initial; initial_fabricated ]

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Possessed
      (** some honest validator possesses the certificate for d - the hidden
          global fact a header's parent digest does not evidence *)
  | Cert_written
      (** [save_cert] for d has executed (certificate_store.rs:129-147), which
          is also the instant its notify fires (:144) *)
  | Store_visible
      (** [CertificateStore::read(d)] answers [Some]: the mem layer holds it or
          the physical layer does (layered_db.rs:383-389) *)
  | Durable
      (** the background thread's [current_txn.commit()] for d's txn returned
          (layered_db.rs:162) *)
  | Delivery_closed
      (** the network will deliver d no more times: the duplicate-write budget
          is spent *)
  | W1_want
      (** V1's handler is inside [notify_read] but before [register_one]
          (certificate_store.rs:253) *)
  | W1_reg  (** V1's handler is parked on its oneshot (:266) *)
  | W1_done  (** V1's [notify_read] returned the certificate *)
  | W2_want  (** V2's handler is inside [notify_read] but before registering *)
  | W2_reg  (** V2's handler is parked on its oneshot *)
  | W2_done  (** V2's [notify_read] returned the certificate *)
  | W2_lost
      (** V2's registration was removed from the map and dropped without a send
          (notify_read.rs:33 then the deleted :38-40) - starved for good *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Possessed -> s.possessed
  | Cert_written -> s.written
  | Store_visible -> store_visible s
  | Durable -> s.dur
  | Delivery_closed -> s.deliv_closed
  | W1_want -> waiter_is_want s.w1
  | W1_reg -> waiter_is_reg s.w1
  | W1_done -> waiter_is_done s.w1
  | W2_want -> waiter_is_want s.w2
  | W2_reg -> waiter_is_reg s.w2
  | W2_done -> waiter_is_done s.w2
  | W2_lost -> waiter_is_lost s.w2

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Possessed -> "possessed(d)"
  | Cert_written -> "written(d)"
  | Store_visible -> "store_visible(d)"
  | Durable -> "durable(d)"
  | Delivery_closed -> "delivery_closed(d)"
  | W1_want -> "waiting_1(d)"
  | W1_reg -> "registered_1(d)"
  | W1_done -> "resolved_1(d)"
  | W2_want -> "waiting_2(d)"
  | W2_reg -> "registered_2(d)"
  | W2_done -> "resolved_2(d)"
  | W2_lost -> "starved_2(d)"

(** The CTLK checker over this family's ordered state and view: the presheaf-
    topos denotation, pinned to agree with {!System} at every reachable world by
    test/t_store_notify_visibility_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the two initial branches,
    mutation-parameterized transitions, the two-handler view, the atom
    valuation. *)
let spec_of mut = { Checker.init = inits; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
