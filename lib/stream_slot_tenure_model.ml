(** Finite interpreted system for the STREAM_SLOT_TENURE family: the whole life
    of ONE [(peer, request_digest)] entry in the primary's
    [pending_epoch_requests] admission map - created at RPC acceptance, consumed
    at stream open, evicted by the periodic cleanup. File citations refer to
    Telcoin-Association/telcoin-network at the working tree of git HEAD
    0c59c15b, all read in this checkout.

    THE MODELED MECHANISM. An epoch-pack transfer is two-legged. Leg one is a
    request-response RPC: [process_epoch_stream] hashes the request into a
    correlation digest (stream_request_digest, mod.rs:181-195) and calls
    [accept_stream_request] (mod.rs:1647-1705), which
    - takes an owned permit off the global [MAX_CONCURRENT_EPOCH_STREAMS = 5]
      semaphore, non-blocking (mod.rs:1654-1656, :66-70),
    - refuses the peer if its combined legacy + sync in-flight count has reached
      [MAX_PENDING_REQUESTS_PER_PEER = 2] (mod.rs:1664-1676, :102-105),
    - and otherwise MOVES the permit into a [PendingStreamRequest] stored under
      [(peer, request_digest)] (mod.rs:1687-1688). The permit is a field of the
      map value ([_permit], mod.rs:206-208, "Dropping the permit frees a global
      concurrency slot"), so global serve capacity is reserved from acceptance,
      BEFORE any work is done, and is released exactly when the map value is
      dropped. The peer is told the outcome by [send_stream_ack]
      (mod.rs:1707-1725, called at mod.rs:1746-1747).

    Leg two is the peer opening a libp2p stream carrying that digest.
    [process_inbound_stream] (mod.rs:1817-1861, dispatched at mod.rs:1507-1510
    with no per-peer gate of its own) reads the digest and does a CONSUMING
    lookup - [pending_map.lock().remove(&(peer, request_digest))]
    (mod.rs:1842-1845) - then hands the [Option] to
    [process_request_epoch_stream] (handler.rs:1130-1199), whose first act is
    [let Some(request) = pending_request else { return
    Err(PrimaryNetworkError::UnknownStreamRequest(request_digest)) }]
    (handler.rs:1139-1149). That error maps to [Penalty::Mild]
    (error/network.rs:189-191) and is reported at mod.rs:1848-1856.

    The map has exactly TWO removal routes and this model has both:
    - the consuming lookup above (mod.rs:1843-1845), which needs the peer to
      act, and
    - the periodic cleanup [cleanup_stale_pending_requests] (mod.rs:1450-1456),
      [.retain(|_, pending| now.duration_since(pending.created_at) <
      PENDING_REQUEST_TIMEOUT)], driven off a 15s interval tick in the network
      task's [tokio::select!] loop (mod.rs:1426, :1442-1444) with
      [PENDING_REQUEST_TIMEOUT = 30s] (mod.rs:64) and
      [PENDING_REQUEST_PRUNE_INTERVAL = 15s] (mod.rs:61).
    A repeat RPC for a key that is already pending does NOT open a third route:
    it REPLACES the value, and the replacement deliberately carries the ORIGINAL
    timestamp - [let created_at = pending_map.get(&(peer, request_digest))
    .map(|p| p.created_at).unwrap_or_else(Instant::now);] (mod.rs:1683-1686),
    whose comment (mod.rs:1678-1682) names the attack it neuters: "Without this,
    a peer could hold a slot indefinitely by re-requesting before the 30s
    timeout." A grep of the whole crate for [pending_epoch_requests] finds only
    the field (mod.rs:1363), the constructor (mod.rs:1411), the retain
    (mod.rs:1453), the insert path (mod.rs:1658), the stream task's clone
    (mod.rs:1820) and [try_admit_sync]'s read-only per-peer count
    (mod.rs:1878, :326-341) - so those three writers are all of them.

    COMPONENTS (one key, one peer, one epoch):
    - [slot]: is there a [PendingStreamRequest] under this key. Held means one
      global permit is reserved for this peer.
    - [age]: has [now - created_at] passed [PENDING_REQUEST_TIMEOUT] for the
      admission currently in force. A cleanup tick advances [Age_fresh] to
      [Age_expired] and evicts an entry that is ALREADY [Age_expired] - the
      15s-interval / 30s-timeout ratio means the earliest eviction is the second
      tick after creation, so ageing and eviction are one tick apart by
      construction, not by convenience.
    - [service]: how the CURRENT admission has been used - untouched, served
      once, served once then re-opened, or served twice. It is reset by a new
      admission (a [get] miss at mod.rs:1683-1685 means a genuinely new
      reservation), so every claim below is per-admission and survives the
      repair path the real code has: a peer whose entry was consumed may simply
      request again and be served again, legitimately, on a NEW reservation.
    - [charged]: has this peer been charged the [Penalty::Mild] of
      [UnknownStreamRequest] (error/network.rs:189-191). Sticky: peer scores
      accumulate.
    - [phase]: the position of the responder's [tokio::select!] loop
      (mod.rs:1427-1446). [Ph_peer_first] -> ([Ph_peer_second] | [Ph_cleanup]),
      [Ph_peer_second] -> [Ph_cleanup], [Ph_cleanup] -> [Ph_peer_first]: the
      peer gets ONE OR TWO events served per cleanup interval, and the interval
      tick is not something the peer can starve, because it is a timer arm of
      the same [select!] and not a queued event. That is the modeled scheduling
      assumption, stated rather than hidden: it is what makes the [Af]
      statements structural rather than an unquoted fairness axiom, and the
      two-event window is what makes the [Non_consuming_open] replay trace
      (open, open, before the next tick) realistic for a 15s interval.
    - [requester]: FROZEN, fixed by the two initial states, touched by no
      transition. [Req_silent] is a requester that never opens the correlated
      stream and never requests again - crashed, disconnected, or squatting;
      [Req_active] may idle, re-request or open, in any order, forever. Nothing
      the responder can read separates the two: the RPC is identical in both
      worlds and neither the map nor the ack carries an intention.

    DELIBERATE ABSTRACTIONS, all of which make the responder's job HARDER, never
    easier:
    - the global semaphore is not modeled, so a re-request is always admitted.
      In the real code it can fail on [try_acquire_owned] (mod.rs:1654) and the
      peer is answered [ack = false]; removing that branch only gives the
      adversary more moves.
    - the per-peer cap is not modeled either: with a single key the peer's
      legacy count is at most 1, and [1 < MAX_PENDING_REQUESTS_PER_PEER = 2]
      (mod.rs:1664-1667), so in the real code the cap never fires on this
      family's traces anyway.
    - epoch teardown is out of scope. [PrimaryNetwork::spawn] runs "the network
      for the epoch" (mod.rs:1422-1424), so an epoch boundary drops the whole
      map and with it every permit; this model is scoped inside one epoch, and
      that is the only in-code release route it does not carry.
    - the sync protocol's admission path ([try_admit_sync], mod.rs:326-341,
      :1873-1881) is a different mechanism with its own counter and no pending
      map; it only READS this map to count, so it cannot free this entry.
    - an inbound stream whose 32-byte digest read fails or times out
      (mod.rs:1824-1839) returns BEFORE the map lookup, so it touches neither
      the entry nor the [UnknownStreamRequest] penalty; its effect on this
      state vector is exactly [A_idle]'s, which is why it has no separate
      action. (It does charge a different penalty - [StdIo] is [Penalty::Medium],
      error/network.rs:192-193 - which this family's [charged] atom, scoped to
      the Mild [UnknownStreamRequest] charge, deliberately does not carry.)
    - two stream opens racing on the same digest are serialised by the
      [Arc<Mutex<..>>] around the map (mod.rs:1363, :1843-1845), so the
      interleaving the sequential model enumerates is the only outcome the real
      code has: with [remove], exactly one of the two racers gets the entry.

    ROLE MAPPING (a knowledge agent needs a real, non-constant view; a blank-view
    party may never appear under [K]):
    - V0 = the responder primary, owner of [pending_epoch_requests], runner of
      the cleanup interval and charger of the penalty. Its view is
      [(slot, age, service, charged, phase)] - its own map entry and that
      entry's age against the public timeout, the serve tasks it spawned itself,
      its own peer-score bookkeeping and its own loop position. It does NOT see
      [requester]: that is the hidden fact of this family, and it is hidden
      permanently rather than temporarily, because an [Req_active] peer is free
      to idle forever and so produces, for as long as it likes, exactly the
      trace an [Req_silent] peer produces.
    - V1 = the requesting peer. Its view is
      [(requester, age, service, charged)] - its own disposition, its own
      elapsed time against [PENDING_REQUEST_TIMEOUT] (which is [pub],
      mod.rs:64, so the peer can compute the deadline), the outcome of each of
      its own stream opens, and the charge bit. The charge bit is given to V1
      on purpose: the responder charges [Penalty::Mild] exactly when an open
      finds no entry, which is exactly the event the peer sees as a stream that
      served it nothing, so pretending the peer cannot infer it would MANUFACTURE
      ignorance. V1 does NOT see [slot] - the cleanup notifies nobody
      (mod.rs:1450-1456 sends no message) - and does NOT see [phase]: the
      interval's alignment is the responder's, so the peer cannot know whether
      the tick that would evict its reservation has already run.
    - V2..V9 are idle non-agents with the constant blank view and never appear
      under [K]. *)

(** The requester's disposition toward the correlated stream. FROZEN: fixed by
    the initial state, read by no gate, invisible to the responder. *)
type requester =
  | Req_silent
      (** never opens the correlated stream and never requests again: the
          abandoned or squatting reservation. *)
  | Req_active
      (** may idle, re-request the same [(peer, digest)] or open the stream, in
          any order, forever. *)

(** Total order index for {!requester}. *)
let requester_index = function Req_silent -> 0 | Req_active -> 1

(** Total order on {!requester}. *)
let requester_compare a b =
  Int.compare (requester_index a) (requester_index b)

(** Presence of this [(peer, request_digest)] key in
    [pending_epoch_requests] (mod.rs:1363). *)
type slot =
  | Slot_empty  (** no entry: no permit reserved for this peer under this key *)
  | Slot_held
      (** a [PendingStreamRequest] is in the map, holding one owned permit off
          the global semaphore (mod.rs:206-208, :1687-1688) *)

(** Total order index for {!slot}. *)
let slot_index = function Slot_empty -> 0 | Slot_held -> 1

(** Total order on {!slot}. *)
let slot_compare a b = Int.compare (slot_index a) (slot_index b)

(** [now - created_at] against [PENDING_REQUEST_TIMEOUT] (mod.rs:64) for the
    admission currently in force. *)
type age =
  | Age_fresh  (** inside the 30s window: the retain at mod.rs:1453-1455 keeps it *)
  | Age_expired
      (** past the 30s window: the next cleanup tick evicts it (mod.rs:1453-1455) *)

(** Total order index for {!age}. *)
let age_index = function Age_fresh -> 0 | Age_expired -> 1

(** Total order on {!age}. *)
let age_compare a b = Int.compare (age_index a) (age_index b)

(** How the CURRENT admission has been used. Reset to {!Svc_none} by every new
    admission, because a [get] miss at mod.rs:1683-1685 mints a genuinely new
    reservation with its own [created_at]. *)
type service =
  | Svc_none  (** the admission has not been served *)
  | Svc_served
      (** served exactly once: one [process_request_epoch_stream] run reached
          the [StreamRequestKind] match (handler.rs:1151-1199) *)
  | Svc_replayed
      (** served once, then the peer opened the correlated stream AGAIN for the
          same digest; pristine that second open finds no entry and is answered
          [UnknownStreamRequest] (handler.rs:1139-1149) *)
  | Svc_double
      (** the second open was SERVED as well: two epoch-pack transfers off one
          admission. Reachable only under {!Non_consuming_open}. *)

(** Total order index for {!service}. *)
let service_index = function
  | Svc_none -> 0
  | Svc_served -> 1
  | Svc_replayed -> 2
  | Svc_double -> 3

(** Total order on {!service}. *)
let service_compare a b = Int.compare (service_index a) (service_index b)

(** Position of the responder's [tokio::select!] loop (mod.rs:1427-1446): one or
    two peer events are served per cleanup interval, and the interval arm is a
    timer the peer cannot starve. *)
type phase =
  | Ph_peer_first  (** first peer event of this cleanup interval *)
  | Ph_peer_second  (** optional second peer event of this interval *)
  | Ph_cleanup
      (** the [prune_requests.tick()] arm runs [cleanup_stale_pending_requests]
          (mod.rs:1442-1444) *)

(** Total order index for {!phase}. *)
let phase_index = function
  | Ph_peer_first -> 0
  | Ph_peer_second -> 1
  | Ph_cleanup -> 2

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The joint global state: one admission slot, its deadline, how it has been
    used, the peer's accumulated penalty, the responder's loop position and the
    frozen hidden disposition of the requester. *)
type state = {
  requester : requester;  (** frozen hidden disposition of the peer *)
  slot : slot;  (** the pending-map entry for this key *)
  age : age;  (** this admission's deadline status *)
  service : service;  (** how this admission has been used *)
  charged : bool;  (** a [Penalty::Mild] has been reported for this peer *)
  phase : phase;  (** the responder's select! loop position *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = requester_compare s1.requester s2.requester in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = slot_compare s1.slot s2.slot in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = age_compare s1.age s2.age in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = service_compare s1.service s2.service in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.charged s2.charged in
          if Bool.not (Int.equal c4 0) then c4
          else phase_compare s1.phase s2.phase

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    V0 (responder) sees its own map entry, that entry's age against the public
    timeout, the serve tasks it ran, its own peer-score bookkeeping and its own
    loop position - everything except the requester's disposition.

    V1 (requester) sees its own disposition, the elapsed time against the [pub]
    [PENDING_REQUEST_TIMEOUT] (mod.rs:64), the outcome of each of its own stream
    opens and the charge bit (which it can infer: the Mild penalty is charged on
    exactly the event the peer observes as a stream that served it nothing). It
    does NOT see whether its reservation is still in the map - the cleanup
    notifies nobody (mod.rs:1450-1456) - and does NOT see when the 15s interval
    next fires (mod.rs:1426, :1442-1444). *)
type view =
  | View_responder of slot * age * service * bool * phase
      (** V0: everything but {!requester} *)
  | View_requester of requester * age * service * bool
      (** V1: everything but {!slot} and {!phase} *)
  | View_idle  (** the constant blank view of the non-agents V2..V9 *)

(** Total order on the responder's view tuple. *)
let responder_view_compare (sl1, ag1, sv1, ch1, ph1) (sl2, ag2, sv2, ch2, ph2) =
  let c = slot_compare sl1 sl2 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = age_compare ag1 ag2 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = service_compare sv1 sv2 in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare ch1 ch2 in
        if Bool.not (Int.equal c3 0) then c3 else phase_compare ph1 ph2

(** Total order on the requester's view tuple. *)
let requester_view_compare (rq1, ag1, sv1, ch1) (rq2, ag2, sv2, ch2) =
  let c = requester_compare rq1 rq2 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = age_compare ag1 ag2 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = service_compare sv1 sv2 in
      if Bool.not (Int.equal c2 0) then c2 else Bool.compare ch1 ch2

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_responder (sl1, ag1, sv1, ch1, ph1), View_responder (sl2, ag2, sv2, ch2, ph2)
    ->
      responder_view_compare (sl1, ag1, sv1, ch1, ph1)
        (sl2, ag2, sv2, ch2, ph2)
  | View_responder _, (View_requester _ | View_idle) -> -1
  | (View_requester _ | View_idle), View_responder _ -> 1
  | View_requester (rq1, ag1, sv1, ch1), View_requester (rq2, ag2, sv2, ch2) ->
      requester_view_compare (rq1, ag1, sv1, ch1) (rq2, ag2, sv2, ch2)
  | View_requester _, View_idle -> -1
  | View_idle, View_requester _ -> 1
  | View_idle, View_idle -> 0

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 (responder) and V1 (requester) are the knowledge agents;
    V2..V9 are idle non-agents with the constant blank view and never appear
    under [K]. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_responder (s.slot, s.age, s.service, s.charged, s.phase)
  | Validator.V1 -> View_requester (s.requester, s.age, s.service, s.charged)
  | Validator.V2
  | Validator.V3
  | Validator.V4
  | Validator.V5
  | Validator.V6
  | Validator.V7
  | Validator.V8
  | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | No_stale_prune
      (** delete the retain body of [cleanup_stale_pending_requests]
          (mod.rs:1453-1455), i.e. the whole timeout eviction, keeping the tick
          itself (mod.rs:1442-1444) so time still passes. REMOVES the
          [Slot_held, Age_expired] -> [Slot_empty] edge from the cleanup step.
          A reservation whose peer never opens the stream is then held forever.

          SIBLING HUNT. The only other write that can remove this key is the
          consuming lookup at mod.rs:1843-1845, and it requires the peer to open
          the correlated stream - which is exactly what the refuting branch's
          peer never does, so it is not a path "the code would have taken
          anyway" (R8). The permit itself has no independent timeout: it is an
          [OwnedSemaphorePermit] field of the map value (mod.rs:206-208) and is
          freed only when that value is dropped. A repeat RPC does not free it
          either - it replaces the value, immediately re-reserving
          (mod.rs:1687-1688). [try_admit_sync] reads this map to count and never
          writes it (mod.rs:326-341). Epoch teardown (mod.rs:1422-1424) frees
          everything, and is the one out-of-scope release: this model is scoped
          inside a single epoch and says so. *)
  | Rearm_created_at
      (** delete the timestamp-preserving lookup at mod.rs:1683-1686, leaving
          [let created_at = Instant::now();] so a replacement entry is minted
          fresh. ADDS [Slot_held, Age_expired] -> [Slot_held, Age_fresh] to the
          re-request action: every repeat RPC re-arms the cleanup deadline, so a
          peer that re-requests once per interval holds the reservation
          forever - the attack the code comment at mod.rs:1678-1682 names.

          SIBLING HUNT. Nothing else bounds tenure. The cleanup predicate reads
          [created_at] and nothing else (mod.rs:1453-1455), so re-arming it is
          total. The per-peer cap (mod.rs:1664-1667) bounds the DAMAGE to two
          slots per identity but frees nothing, and the global semaphore
          (mod.rs:1654-1656) only refuses NEW admissions - it cannot revoke a
          held permit. The consuming lookup (mod.rs:1843-1845) would end the
          tenure but needs the peer to open the stream, which this adversary
          never does. Note the code punishes a second stream OPEN, not a repeat
          REQUEST: the repeat request is answered [ack = true] again
          (mod.rs:1746-1747) with no penalty at all. *)
  | Non_consuming_open
      (** weaken the lookup at mod.rs:1843-1845 from [remove] to a non-consuming
          [get], deleting the consume-on-open side effect. REMOVES the
          [Slot_held] -> [Slot_empty] edge from the open action, so the entry
          survives the serve and a second open before the next cleanup tick is
          SERVED AGAIN with no penalty.

          SIBLING HUNT. [process_request_epoch_stream] has no served-flag of any
          kind: it matches on [request.kind()] and streams
          (handler.rs:1151-1199), so nothing downstream can notice the replay.
          [process_inbound_stream] is dispatched straight off the network event
          with no per-peer gate (mod.rs:1507-1510) and no dedup on the digest.
          The cleanup would evict the un-consumed entry, but only at a later
          tick (mod.rs:1453-1455): it bounds replays in TIME and does not
          prevent the second serve, which is why the model's window carries two
          peer events. The per-peer cap does not repair it either - the
          un-consumed entry counts 1, still below the cap of 2
          (mod.rs:1664-1667) - and the permit stays inside the entry, so nothing
          is leaked that could block the replay. *)

(** One peer event the responder's [select!] loop can serve. *)
type action =
  | A_idle  (** the peer does nothing this slice *)
  | A_request
      (** a [PrimaryRequest::StreamEpoch] for the SAME [(peer, digest)]:
          [process_epoch_stream] -> [accept_stream_request]
          (mod.rs:1731-1747, :1647-1705) *)
  | A_open
      (** the peer opens the correlated libp2p stream carrying the digest:
          [process_inbound_stream] (mod.rs:1507-1510, :1817-1861) *)

(** The peer events available in a state. [Req_silent] is the abandoned
    reservation: it never requests again and never opens. *)
let actions s =
  match s.requester with
  | Req_silent -> [ A_idle ]
  | Req_active -> [ A_idle; A_request; A_open ]

(** Service bookkeeping when an open FINDS the entry: one more epoch-pack
    transfer off this admission (handler.rs:1151-1199). *)
let served_step = function
  | Svc_none -> Svc_served
  | Svc_served -> Svc_double
  | Svc_replayed -> Svc_double
  | Svc_double -> Svc_double

(** Service bookkeeping when an open finds NO entry: the responder answers
    [UnknownStreamRequest] (handler.rs:1139-1149). If the admission had already
    been served, this open is a replay of a consumed reservation. *)
let unmatched_step = function
  | Svc_none -> Svc_none
  | Svc_served -> Svc_replayed
  | Svc_replayed -> Svc_replayed
  | Svc_double -> Svc_double

(** A repeat [StreamEpoch] RPC for a key that is ALREADY pending
    (mod.rs:1683-1688). Pristine the replacement carries the original
    [created_at], so the deadline is untouched and the step is a no-op on the
    observable state; {!Rearm_created_at} mints a fresh timestamp. *)
let rerequest_age mut a =
  match mut with
  | Rearm_created_at -> Age_fresh
  | Pristine | No_stale_prune | Non_consuming_open -> a

(** Does an open leave the entry in the map. Pristine (and under every mutation
    but {!Non_consuming_open}) the lookup is [remove], so the reservation is
    consumed (mod.rs:1843-1845). *)
let slot_after_open mut =
  match mut with
  | Non_consuming_open -> Slot_held
  | Pristine | No_stale_prune | Rearm_created_at -> Slot_empty

(** Apply one peer event. A request on an empty slot is a genuinely NEW
    admission - [pending_map.get] misses, so [created_at] is [Instant::now()]
    (mod.rs:1683-1686) and the per-admission service counter restarts; that is
    the repair path the real code has, and it is modeled rather than omitted. *)
let apply mut s a =
  match a with
  | A_idle -> s
  | A_request -> (
      match s.slot with
      | Slot_empty ->
          { s with slot = Slot_held; age = Age_fresh; service = Svc_none }
      | Slot_held -> { s with age = rerequest_age mut s.age })
  | A_open -> (
      match s.slot with
      | Slot_held ->
          {
            s with
            slot = slot_after_open mut;
            service = served_step s.service;
          }
      | Slot_empty ->
          { s with service = unmatched_step s.service; charged = true })

(** The [prune_requests.tick()] arm (mod.rs:1442-1444). Time advances - so an
    in-window entry becomes deadline-passed - and, pristine, the retain evicts
    an entry that was ALREADY deadline-passed on entry to the tick
    (mod.rs:1453-1455). The two are one tick apart because the 15s interval is
    half the 30s timeout (mod.rs:61, :64). {!No_stale_prune} keeps the tick and
    deletes the eviction. *)
let cleanup mut s =
  let evicted =
    match mut with
    | No_stale_prune -> s.slot
    | Pristine | Rearm_created_at | Non_consuming_open -> (
        match (s.slot, s.age) with
        | Slot_held, Age_expired -> Slot_empty
        | Slot_held, Age_fresh -> Slot_held
        | Slot_empty, Age_fresh -> Slot_empty
        | Slot_empty, Age_expired -> Slot_empty)
  in
  { s with slot = evicted; age = Age_expired; phase = Ph_peer_first }

(** The transition relation: the responder's loop serves one or two peer events
    per cleanup interval, then ticks. The interval arm is a timer, not a queued
    event, so no amount of peer traffic can starve it. *)
let next_with mut s =
  match s.phase with
  | Ph_peer_first ->
      List.concat_map
        (fun a ->
          let s' = apply mut s a in
          [ { s' with phase = Ph_peer_second }; { s' with phase = Ph_cleanup } ])
        (actions s)
  | Ph_peer_second ->
      List.map
        (fun a -> { (apply mut s a) with phase = Ph_cleanup })
        (actions s)
  | Ph_cleanup -> [ cleanup mut s ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: [accept_stream_request] has just returned [true]
    (mod.rs:1687-1704) and the ack has been sent (mod.rs:1746-1747), so one
    permit is reserved, the deadline is fresh, nothing has been served and no
    penalty has been charged. This branch's requester may still follow through. *)
let initial =
  {
    requester = Req_active;
    slot = Slot_held;
    age = Age_fresh;
    service = Svc_none;
    charged = false;
    phase = Ph_peer_first;
  }

(** The sibling initial state: the identical admission from a requester that
    will never open the correlated stream and never request again. The two
    initial states differ ONLY in the frozen hidden disposition, which is
    exactly what the responder cannot read off an accepted RPC. *)
let initial_requester_silent = { initial with requester = Req_silent }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Slot_reserved
      (** slot = Slot_held : a [PendingStreamRequest] for this
          [(peer, digest)] is in [pending_epoch_requests], holding one global
          permit (reserved(p,d)) *)
  | Deadline_passed
      (** age = Age_expired : [now - created_at >= PENDING_REQUEST_TIMEOUT] for
          the admission in force (past_deadline(p,d)) *)
  | Served_once
      (** service in {Svc_served, Svc_replayed, Svc_double} : this admission has
          been served at least one epoch-pack transfer (served(p,d)) *)
  | Served_twice
      (** service = Svc_double : this admission was served TWICE
          (double_served(p,d)) *)
  | Reopened_after_serve
      (** service in {Svc_replayed, Svc_double} : the peer opened the correlated
          stream again after this admission had already been served
          (replayed(p,d)) *)
  | Penalty_charged
      (** charged : a [Penalty::Mild] has been reported for this peer
          (error/network.rs:189-191, mod.rs:1848-1856) (charged(p)) *)
  | Requester_gone_silent
      (** requester = Req_silent : the hidden disposition - this requester never
          opens the correlated stream and never requests again (abandoned(p)) *)
  | Cleanup_due
      (** phase = Ph_cleanup : the responder's next loop step is the
          [prune_requests.tick()] arm (mod.rs:1442-1444) (cleanup_next) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Slot_reserved -> (
      match s.slot with Slot_held -> true | Slot_empty -> false)
  | Deadline_passed -> (
      match s.age with Age_expired -> true | Age_fresh -> false)
  | Served_once -> (
      match s.service with
      | Svc_served | Svc_replayed | Svc_double -> true
      | Svc_none -> false)
  | Served_twice -> (
      match s.service with
      | Svc_double -> true
      | Svc_none | Svc_served | Svc_replayed -> false)
  | Reopened_after_serve -> (
      match s.service with
      | Svc_replayed | Svc_double -> true
      | Svc_none | Svc_served -> false)
  | Penalty_charged -> s.charged
  | Requester_gone_silent -> (
      match s.requester with Req_silent -> true | Req_active -> false)
  | Cleanup_due -> (
      match s.phase with
      | Ph_cleanup -> true
      | Ph_peer_first | Ph_peer_second -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Slot_reserved -> "reserved(p,d)"
  | Deadline_passed -> "past_deadline(p,d)"
  | Served_once -> "served(p,d)"
  | Served_twice -> "double_served(p,d)"
  | Reopened_after_serve -> "replayed(p,d)"
  | Penalty_charged -> "charged(p)"
  | Requester_gone_silent -> "abandoned(p)"
  | Cleanup_due -> "cleanup_next"

(** The CTLK checker over this family's ordered state and view: the presheaf
    topos denotation, pinned to agree with {!System} at every reachable world by
    test/t_stream_slot_tenure_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the two initial states (the frozen
    requester-disposition branch), mutation-parameterized transitions, the
    two-agent view projection, the atom valuation. *)
let spec_of mut =
  {
    Checker.init = [ initial; initial_requester_silent ];
    next = next_with mut;
    view;
    label;
  }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
