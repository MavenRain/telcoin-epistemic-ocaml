(** Finite interpreted system for the SERVE_SLOT_QUOTA family: one serving
    PRIMARY's request-admission bookkeeping across its TWO service classes - the
    epoch-stream class (one semaphore shared by the legacy request-response
    admission and the inbound sync admission) and the epoch-record class (its own
    semaphore and its own per-peer counter) - and what a capacity denial on the
    stream class tells the peer that receives it.

    File citations refer to Telcoin-Association/telcoin-network at the working
    tree of git HEAD 0c59c15b; every one of them was opened in this checkout.
    Unqualified [mod.rs:N] means
    [crates/consensus/primary/src/network/mod.rs].

    RELATION TO THE FAMILIES ALREADY IN THIS LIBRARY. Three integrated families
    already sit on neighbouring code and this one deliberately states none of
    what they state. {!Worker_stream_quota} is the WORKER's batch-stream
    accounting (crates/consensus/worker/src/network/mod.rs, a three-source
    [peer_in_flight]); {!Stream_slot_tenure} is the tenure of a PRIMARY pending
    entry (release, re-request, at-most-once serve); {!Record_serve_pool} is the
    INTERNAL arithmetic and opacity of the primary's epoch-record pool. What is
    left, and what this family takes, is (a) the DISJOINTNESS of the two class
    budgets, (b) the union of the two stream admission paths under one per-peer
    cap on the primary, and (c) the positive knowledge a stream-class denial
    hands its recipient - the primary's stream class ANSWERS a denial where its
    record class is silent, and that answer is informative about other peers.

    THE MODELLED MECHANISM.

    - TWO DISJOINT BUDGETS. The primary holds two [Arc<Semaphore>]s built at
      mod.rs:1402 ([Semaphore::new(MAX_CONCURRENT_EPOCH_STREAMS)]) and
      mod.rs:1413 ([Semaphore::new(MAX_CONCURRENT_EPOCH_RECORD_REQUESTS)]),
      stored in the distinct fields [epoch_stream_semaphore] (mod.rs:1357) and
      [epoch_record_semaphore] (mod.rs:1375) whose doc states the intent
      verbatim: "Separate from [epoch_stream_semaphore] so an epoch-record flood
      and the stream-serving paths never starve one another" (mod.rs:1373-1374),
      repeated at the constant (mod.rs:72-81). Their per-peer counters are
      distinct too: [sync_stream_peers] / [pending_epoch_requests]
      (mod.rs:1370, :1411) versus [epoch_record_peers] (mod.rs:1378).
      [try_admit_epoch_record] (mod.rs:351-363) touches only the record pair;
      its own doc says so at mod.rs:349-350.
    - ONE STREAM BUDGET, TWO ADMISSION PATHS. The legacy request-response
      admission [accept_stream_request] (mod.rs:1647-1705) and the inbound sync
      admission [try_admit_sync] (mod.rs:326-341) both draw on
      [epoch_stream_semaphore] (mod.rs:1654 and the call at mod.rs:1876-1881),
      and each computes the per-peer count over the UNION of both sources:
      mod.rs:1664-1666 is [let legacy_count = pending_map.keys().filter(|(p, _)|
      *p == peer).count(); let sync_count =
      self.sync_stream_peers.lock().get(&peer).copied().unwrap_or(0); let
      peer_count = legacy_count + sync_count;] and mod.rs:334-337 is the mirror
      [let legacy_count = pending_guard.keys().filter(|(p, _)| *p ==
      peer).count(); ... let sync_count =
      sync_guard.get(&peer).copied().unwrap_or(0); (legacy_count + sync_count <
      MAX_PENDING_REQUESTS_PER_PEER).then(...)]. The refusals are mod.rs:1667-
      1676 ([if peer_count >= MAX_PENDING_REQUESTS_PER_PEER { ... // permit drops
      here, freeing the slot; return false; }]) and the [.then] guard itself.
      Constants: [MAX_CONCURRENT_EPOCH_STREAMS = 5] (mod.rs:66-70),
      [MAX_PENDING_REQUESTS_PER_PEER = 2] (mod.rs:102-105).
    - THE DENIAL IS DELIVERED. Unlike the record class, which sheds by dropping
      the response channel and sends nothing (mod.rs:1604-1612), both stream
      paths TELL the requester. Legacy: [let ack = self.accept_stream_request(
      peer, request_digest, kind); self.send_stream_ack(ack, ...)]
      (mod.rs:1746-1747) puts the bool on the wire as
      [PrimaryResponse::StreamRequestAck { ack }] (mod.rs:1715), and the client
      branches on it - [if !ack { continue; }] (mod.rs:976-984). Sync: the shed
      branch writes [SyncFrame::<PrimarySyncRequest>::Deny(DenyReason::
      AtCapacity)] (mod.rs:1892-1906, the variant at
      crates/network-libp2p/src/sync/frame.rs:51) without reading, as its doc
      says at mod.rs:1863-1872.
    - WHAT A DENIAL MEANS. [try_admit_sync] returns [None] on EITHER an empty
      semaphore (mod.rs:332) or an over-cap peer (mod.rs:337), so a denial by
      itself is ambiguous. For a requester holding no slot of its own the second
      disjunct is impossible, so the denial pins the first: the pool was full;
      and a full pool with a per-peer cap strictly below it is necessarily spread
      over more than one peer. That arithmetic is the content of S3.

    SCOPE - THE ADMISSION WINDOW, STATED SO IT IS NOT MISTAKEN FOR AN OMISSION.
    Every modelled step is an ADMISSION; nothing releases. The two real release
    routes are the drop of a [PendingStreamRequest] (its [_permit] field,
    mod.rs:206-208) when the correlated stream is served, and the 15-second
    sweep [cleanup_stale_pending_requests] (mod.rs:1451-1456) evicting entries
    older than [PENDING_REQUEST_TIMEOUT = 30s] (mod.rs:61, :64). Both are the
    subject matter of the {!Stream_slot_tenure} family and neither is a repair
    path for anything asserted here: S1 is an [EX] claim about the admission
    test at a state, which no later release can make true retroactively; S2's
    two conjuncts are invariants that a release only ever moves further inside;
    and S3's knowledge operand is deliberately phrased as the MONOTONE fact
    "two distinct peers have been admitted stream slots", which stays true after
    any release, rather than as a claim about the instantaneous occupancy.

    ABSTRACTION OF THE POOL SIZE. The global stream pool is modelled with THREE
    permits rather than the real five, and the per-peer cap is kept EXACT at
    two. What is load-bearing for every statement here is the relation
    [per_peer_cap < stream_pool <= 2 * per_peer_cap], not the absolute size: it
    is what makes an exhausted pool require more than one holder while still
    letting a single peer be refused. Under the real 5-and-2 the same argument
    yields "at least three distinct holders" where this model yields "at least
    two"; {!Record_serve_pool} carries the exact-five reading of that arithmetic
    on the other class.

    COMPONENTS AND ROLE MAPPING.

    - [V1] is P, the flooding peer. It is the only modelled peer that uses BOTH
      stream protocols: [p_leg] counts its entries in [pending_epoch_requests]
      (admitted by [accept_stream_request]) and [p_syn] counts its inbound sync
      streams (admitted by [try_admit_sync]). Its view is its own two admitted
      counts - the acks and Deny frames it has received - and nothing of the
      server's totals.
    - [V3] is T, an ordinary second peer using the legacy path only ([t_str]).
      Its view is its own admitted count.
    - [V2] is Q, the honest requester and THE ONLY KNOWLEDGE AGENT: it makes one
      inbound sync stream request ([q_str]) and holds one outstanding
      [PrimaryRequest::EpochRecord] ([q_rec]). Its view is exactly the pair of
      its own outcomes - the [Ack]/[Deny] it got for its stream request and
      whether its record request has been answered. It contains NO component of
      the server's semaphore counts, of [pending_epoch_requests], of
      [sync_stream_peers] or of any other peer's holdings, which is why the K
      operands below are about hidden global facts and not about Q's own
      projection.
    - [V0] and [V4] .. [V9] are idle: the constant blank view, never an operand
      of [K] in this family's statements. (The committee type carries ten
      members; this family models one responder and three of its peers, so the
      remaining seven are non-agents.)

    The serving primary itself is the system, not an agent: the state IS its
    bookkeeping. *)

(** The global epoch-stream budget, [MAX_CONCURRENT_EPOCH_STREAMS] (mod.rs:66-70,
    taken at mod.rs:1402) abstracted from 5 to 3; see the ABSTRACTION note in the
    header for why only [per_peer_cap < stream_pool <= 2 * per_peer_cap] is
    load-bearing. *)
let stream_pool = 3

(** [MAX_PENDING_REQUESTS_PER_PEER] (mod.rs:102-105), exact. It is the same
    constant on both stream admission paths (mod.rs:337, mod.rs:1667). *)
let per_peer_cap = 2

(** How many inbound sync streams the flooder P is modelled as able to open. One
    is enough: with [p_leg] able to reach the cap on its own, one sync stream is
    exactly the extra slot the union term at mod.rs:1665-1666 denies it. *)
let flooder_sync_bound = 1

(** Q's inbound sync stream request and the answer it got back
    (mod.rs:1873-1907). *)
type qstream =
  | Qs_unsent  (** Q has not opened its sync stream yet. *)
  | Qs_denied
      (** Q opened and the responder wrote
          [SyncFrame::Deny(DenyReason::AtCapacity)] without reading
          (mod.rs:1892-1906). *)
  | Qs_admitted
      (** [try_admit_sync] returned a [PeerSlotPermit] (mod.rs:337-340), so Q
          holds one global stream permit. *)

(** Total order index for {!qstream}. *)
let qstream_index = function
  | Qs_unsent -> 0
  | Qs_denied -> 1
  | Qs_admitted -> 2

(** Total order on {!qstream}. *)
let qstream_compare a b = Int.compare (qstream_index a) (qstream_index b)

(** Q's outstanding [PrimaryRequest::EpochRecord] request-response
    (mod.rs:1586-1640). *)
type qrecord =
  | Qr_asking  (** the request has reached the responder and is unanswered *)
  | Qr_served
      (** [try_admit_epoch_record] returned a permit (mod.rs:1602-1603) and the
          spawned serve delivered a response (mod.rs:1619-1634) *)

(** Total order index for {!qrecord}. *)
let qrecord_index = function Qr_asking -> 0 | Qr_served -> 1

(** Total order on {!qrecord}. *)
let qrecord_compare a b = Int.compare (qrecord_index a) (qrecord_index b)

(** The joint global state: the serving primary's whole admission bookkeeping
    over one admission window. *)
type state = {
  p_leg : int;
      (** P's entries in [pending_epoch_requests], i.e. its [legacy_count]
          (mod.rs:1664) *)
  p_syn : int;
      (** P's entry in [sync_stream_peers], i.e. its [sync_count]
          (mod.rs:336, :1665) *)
  t_str : int;  (** T's [legacy_count]; T never uses the sync path *)
  q_str : qstream;  (** Q's sync stream request and its answer *)
  q_rec : qrecord;  (** Q's epoch-record request-response *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = Int.compare s1.p_leg s2.p_leg in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Int.compare s1.p_syn s2.p_syn in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Int.compare s1.t_str s2.t_str in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = qstream_compare s1.q_str s2.q_str in
        if Bool.not (Int.equal c3 0) then c3
        else qrecord_compare s1.q_rec s2.q_rec

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** How many global stream permits Q holds. *)
let q_stream_slots q =
  match q with Qs_admitted -> 1 | Qs_unsent -> 0 | Qs_denied -> 0

(** Permits taken from [epoch_stream_semaphore] right now. *)
let occupancy s = s.p_leg + s.p_syn + s.t_str + q_stream_slots s.q_str

(** The semaphore test both stream paths make first (mod.rs:332, mod.rs:1654). *)
let pool_has_room s = occupancy s < stream_pool

(** P's combined stream in-flight count: the [legacy_count + sync_count] of
    mod.rs:1666 and mod.rs:337. *)
let flooder_in_flight s = s.p_leg + s.p_syn

(** A validator's local view. Each agent sees only its OWN admitted counts and
    its OWN answers; no view carries the responder's semaphore counts, its
    [pending_epoch_requests] map, or any other peer's holdings. *)
type view =
  | View_flooder of int * int
      (** V1 = P: its own [legacy_count] and [sync_count], i.e. which of its own
          opens were acked. *)
  | View_third of int  (** V3 = T: its own admitted legacy count. *)
  | View_honest of qstream * qrecord
      (** V2 = Q, the knowledge agent: the answer to its stream request and
          whether its record request came back. *)
  | View_idle  (** the constant blank view of the non-agent V0. *)

(** Total order index for {!view}. *)
let view_index = function
  | View_flooder _ -> 0
  | View_third _ -> 1
  | View_honest _ -> 2
  | View_idle -> 3

(** Total order on views: every constructor pair reached, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_flooder (l1, s1), View_flooder (l2, s2) ->
      let c = Int.compare l1 l2 in
      if Bool.not (Int.equal c 0) then c else Int.compare s1 s2
  | View_third t1, View_third t2 -> Int.compare t1 t2
  | View_honest (a1, b1), View_honest (a2, b2) ->
      let c = qstream_compare a1 a2 in
      if Bool.not (Int.equal c 0) then c else qrecord_compare b1 b2
  | View_idle, View_idle -> 0
  | ( (View_flooder _ | View_third _ | View_honest _ | View_idle),
      (View_flooder _ | View_third _ | View_honest _ | View_idle) ) ->
      Int.compare (view_index a) (view_index b)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V2 is the knowledge agent; V1 and V3 are modelled actors
    whose own outcomes they see but who never appear under [K]; V0 is idle with
    the constant blank view. *)
let view v s =
  match v with
  | Validator.V1 -> View_flooder (s.p_leg, s.p_syn)
  | Validator.V3 -> View_third s.t_str
  | Validator.V2 -> View_honest (s.q_str, s.q_rec)
  | Validator.V0 -> View_idle
  | Validator.V4 -> View_idle
  | Validator.V5 -> View_idle
  | Validator.V6 -> View_idle
  | Validator.V7 -> View_idle
  | Validator.V8 -> View_idle
  | Validator.V9 -> View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the model as the code is *)
  | No_cross_path_count
      (** delete the CROSS terms of the per-peer stream count: [+ sync_count] in
          [accept_stream_request] (mod.rs:1665-1666, leaving [let peer_count =
          legacy_count;]) and [legacy_count +] in [try_admit_sync]
          (mod.rs:334-337, leaving [(sync_count <
          MAX_PENDING_REQUESTS_PER_PEER).then(...)]). Each path then caps only
          its own source, so one peer holds [per_peer_cap] legacy entries AND a
          sync stream at the same time. Nothing repairs it: those two
          expressions are the only places the two counters are added, the
          semaphore at mod.rs:332 / :1654 is a GLOBAL bound that does not
          distinguish peers, [PeerSlotPermit]'s [Drop] (mod.rs:305-315)
          decrements the same counter the admission incremented and so cannot
          re-couple them, and the libp2p per-peer inbound limiter
          ([inbound_rate_limited], crates/network-libp2p/src/stream/
          behavior.rs:281-290) is a RATE of [MAX_INBOUND_PER_WINDOW = 256] per
          one-second window (behavior.rs:42-45) that neither reserves nor
          releases a slot. *)
  | No_per_peer_stream_cap
      (** delete the per-peer refusal on both stream paths outright: the [if
          peer_count >= MAX_PENDING_REQUESTS_PER_PEER { ... return false; }]
          block of [accept_stream_request] (mod.rs:1667-1676) and the [(... <
          MAX_PENDING_REQUESTS_PER_PEER)] guard of [try_admit_sync]
          (mod.rs:337). The global semaphore alone survives, so one peer can
          take every permit. Same sibling hunt as above and same conclusion; in
          particular [begin_serving]-style handoffs do not exist on this path
          (the primary's pending entry holds its permit from acceptance to
          service, mod.rs:206-208) so there is no second site that could
          re-impose a per-peer bound. *)
  | Shared_permit_pool
      (** delete the dedicated epoch-record budget: drop the field
          [epoch_record_semaphore] (mod.rs:1375) and its construction
          [Arc::new(Semaphore::new(MAX_CONCURRENT_EPOCH_RECORD_REQUESTS))]
          (mod.rs:1413), and pass [epoch_stream_semaphore] to the
          [try_admit_epoch_record] call at mod.rs:1602-1603. Epoch-record
          admission then competes for the stream permits. Nothing inside one
          serving primary repairs it: the shed branch sends NOTHING over the
          wire (mod.rs:1604-1612, "Dropping the channel sends no rejection over
          the wire"), so there is no retry signal; the record serve holds its
          permit for its whole lifetime (mod.rs:1619-1622) so there is no early
          release; and the only other recovery the code names - the caller
          rotating to ANOTHER peer after its request-response timeout
          (mod.rs:1607-1609) - leaves this responder, which is precisely the
          node whose fairness is at issue. *)

(** P's per-peer test on the LEGACY admission path (mod.rs:1664-1676). *)
let flooder_legacy_allowed mut s =
  match mut with
  | Pristine -> flooder_in_flight s < per_peer_cap
  | Shared_permit_pool -> flooder_in_flight s < per_peer_cap
  | No_cross_path_count -> s.p_leg < per_peer_cap
  | No_per_peer_stream_cap -> true

(** P's per-peer test on the SYNC admission path (mod.rs:334-337). *)
let flooder_sync_allowed mut s =
  match mut with
  | Pristine -> flooder_in_flight s < per_peer_cap
  | Shared_permit_pool -> flooder_in_flight s < per_peer_cap
  | No_cross_path_count -> s.p_syn < per_peer_cap
  | No_per_peer_stream_cap -> true

(** T's per-peer test. T holds no sync stream, so its [sync_count] term is zero
    and {!No_cross_path_count} leaves its gate unchanged - which is exactly why
    that mutation is attributable to the cross term and not to the cap. *)
let third_allowed mut s =
  match mut with
  | Pristine -> s.t_str < per_peer_cap
  | Shared_permit_pool -> s.t_str < per_peer_cap
  | No_cross_path_count -> s.t_str < per_peer_cap
  | No_per_peer_stream_cap -> true

(** The epoch-record admission test (mod.rs:1602-1603). Pristine it consults the
    dedicated [epoch_record_semaphore], which no stream admission can touch;
    under {!Shared_permit_pool} it consults the stream pool instead. Q is the
    only modelled record requester, so pristine the test never refuses - that IS
    the disjointness, not an omission: the intra-class contention this model
    leaves out is exactly what {!Record_serve_pool} certifies. *)
let record_admits mut s =
  match mut with
  | Pristine -> true
  | No_cross_path_count -> true
  | No_per_peer_stream_cap -> true
  | Shared_permit_pool -> pool_has_room s

(** The transition relation: one admission per step. Every step strictly
    advances a component, so the window accumulates and never undoes itself (see
    the SCOPE note in the header). A refused admission contributes no successor,
    matching the code's order - the permit is taken first (mod.rs:332,
    mod.rs:1654) and released again on a per-peer refusal ("permit drops here,
    freeing the slot", mod.rs:1674) - so a refusal leaves the budget exactly as
    it found it. *)
let next_with mut s =
  let flood_legacy =
    if pool_has_room s && flooder_legacy_allowed mut s then
      [ { s with p_leg = s.p_leg + 1 } ]
    else []
  in
  let flood_sync =
    if
      pool_has_room s && flooder_sync_allowed mut s
      && s.p_syn < flooder_sync_bound
    then [ { s with p_syn = s.p_syn + 1 } ]
    else []
  in
  let third =
    if pool_has_room s && third_allowed mut s then
      [ { s with t_str = s.t_str + 1 } ]
    else []
  in
  let honest_stream =
    match s.q_str with
    | Qs_unsent ->
        (* [try_admit_sync] is a function of the counters: a permit and a
           sub-cap count give [Some] (mod.rs:337-340), anything else gives
           [None] and the Deny frame (mod.rs:1892-1906). Q holds no slot, so its
           own per-peer term is 0 under every mutation and only the pool test
           decides. *)
        if pool_has_room s then [ { s with q_str = Qs_admitted } ]
        else [ { s with q_str = Qs_denied } ]
    | Qs_denied -> []
    | Qs_admitted -> []
  in
  let honest_record =
    match s.q_rec with
    | Qr_asking ->
        if record_admits mut s then [ { s with q_rec = Qr_served } ] else []
    | Qr_served -> []
  in
  flood_legacy @ flood_sync @ third @ honest_stream @ honest_record

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: nothing admitted anywhere, Q's stream request not yet
    opened and Q's epoch-record request already outstanding at the responder. *)
let initial =
  { p_leg = 0; p_syn = 0; t_str = 0; q_str = Qs_unsent; q_rec = Qr_asking }

(** The atom vocabulary this family's statements quantify over. The first three
    constructors are the contingent ones {!Topos_gate.seeds} picks up. *)
type atom =
  | Stream_pool_full
      (** every [epoch_stream_semaphore] permit is taken: occupancy =
          [stream_pool] *)
  | Two_stream_holders
      (** two distinct peers other than Q have been admitted stream slots -
          monotone over the admission window, so it survives any later release *)
  | Q_stream_denied
      (** Q's sync open was answered [Deny(DenyReason::AtCapacity)]
          (mod.rs:1892-1906) *)
  | Q_stream_unsent  (** Q has not opened a stream at all *)
  | Q_holds_stream_slot  (** Q's open was admitted and holds a global permit *)
  | Flooder_at_cap
      (** P's combined [legacy_count + sync_count] equals
          [MAX_PENDING_REQUESTS_PER_PEER] *)
  | Q_record_pending  (** Q's [EpochRecord] request is outstanding *)
  | Q_record_served  (** Q's [EpochRecord] request has been answered *)
  | Peer_over_stream_cap
      (** some peer holds MORE stream slots than
          [MAX_PENDING_REQUESTS_PER_PEER]: the state the two per-peer gates
          forbid *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Stream_pool_full -> Int.equal (occupancy s) stream_pool
  | Two_stream_holders -> flooder_in_flight s > 0 && s.t_str > 0
  | Q_stream_denied -> (
      match s.q_str with
      | Qs_denied -> true
      | Qs_unsent -> false
      | Qs_admitted -> false)
  | Q_stream_unsent -> (
      match s.q_str with
      | Qs_unsent -> true
      | Qs_denied -> false
      | Qs_admitted -> false)
  | Q_holds_stream_slot -> (
      match s.q_str with
      | Qs_admitted -> true
      | Qs_unsent -> false
      | Qs_denied -> false)
  | Flooder_at_cap -> Int.equal (flooder_in_flight s) per_peer_cap
  | Q_record_pending -> (
      match s.q_rec with Qr_asking -> true | Qr_served -> false)
  | Q_record_served -> (
      match s.q_rec with Qr_served -> true | Qr_asking -> false)
  | Peer_over_stream_cap ->
      flooder_in_flight s > per_peer_cap || s.t_str > per_peer_cap

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Stream_pool_full -> "stream_permits_taken = 3"
  | Two_stream_holders -> "distinct_other_stream_holders >= 2"
  | Q_stream_denied -> "denied_at_capacity(Q)"
  | Q_stream_unsent -> "no_stream_request(Q)"
  | Q_holds_stream_slot -> "holds_stream_slot(Q)"
  | Flooder_at_cap -> "stream_inflight(P) = 2"
  | Q_record_pending -> "record_request_outstanding(Q)"
  | Q_record_served -> "record_served(Q)"
  | Peer_over_stream_cap -> "some_peer_stream_inflight > 2"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every reachable
    world by test/t_serve_slot_quota_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state, the
    mutation-parameterised transitions, the view projection (V1, V2 and V3 see
    their own outcomes; every other validator is blank) and the atom
    valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
