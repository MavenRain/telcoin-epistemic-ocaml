(** Finite interpreted system for the RECORD_SERVE_POOL family: the primary's
    [EpochRecord] request-response arm from admission control through dispatch
    and penalty. File citations refer to Telcoin-Association/telcoin-network
    (HEAD 0c59c15b), every one of them read in this checkout.

    THE MODELLED MECHANISM.

    - THE TWO CAPS. [MAX_CONCURRENT_EPOCH_RECORD_REQUESTS = 5]
      (network/mod.rs:72-81, whose doc comment records the reason: "The
      `EpochRecord` request-response arm is reachable by any peer whose
      identity resolves (not committee membership) ... Without a bound a peer
      could spawn unbounded concurrent, penalty-free serve tasks ... See
      GHSA-vc2r-9cp2-w74j") and [MAX_PENDING_REQUESTS_PER_PEER = 2]
      (network/mod.rs:102-105, "Prevents a single malicious peer from filling
      all global slots").
    - THE ADMITTER. [try_admit_epoch_record] (network/mod.rs:343-363) takes a
      global permit first and then gates per peer, verbatim at :356-362:
      [let permit = semaphore.clone().try_acquire_owned().ok()?; let mut guard
      = peers.lock(); let count = guard.get(&peer).copied().unwrap_or(0);
      (count < MAX_PENDING_REQUESTS_PER_PEER).then(|| { *guard.entry(peer)
      .or_insert(0) += 1; PeerSlotPermit { _permit: permit, peers:
      peers.clone(), peer } })]. Both caps are therefore ONE gate: they live in
      one function and a caller either gets a [PeerSlotPermit] or gets [None].
    - THE ACCOUNTING. [PeerSlotPermit]'s [Drop] (network/mod.rs:288-315)
      decrements the peer's entry, removes it at zero and releases the global
      permit, so the slot table is exact and a finished serve frees capacity
      again. That release is why the model's flooding requesters may decrement
      as well as increment.
    - THE SHED. [process_epoch_record_request] (network/mod.rs:1586-1640)
      calls the admitter at :1602-1603 and, on [None], returns at :1612 with
      the response channel undelivered. Its comment at :1605-1611 is the
      epistemic content of statement S2 verbatim: "shed in O(1) by dropping
      the response channel rather than spawning work ... Dropping the channel
      sends no rejection over the wire, so the caller (`request_epoch_cert`)
      rotates to another peer only after its request-response timeout
      elapses". An ADMITTED request holds its permit for the serve's lifetime
      (:1619-1622).
    - THE DISPATCH. [retrieve_epoch_record] (handler.rs:990-1003) selects on
      the request's two [Option] fields, verbatim at :996-1000:
      [match (epoch, hash) { (_, Some(hash)) => self.get_epoch_by_hash(hash)
      .await?, (Some(epoch), _) => self.get_epoch_by_number(epoch).await?,
      (None, None) => return Err(PrimaryNetworkError::InvalidEpochRequest) }].
      [get_epoch_by_number] (handler.rs:1006-1026) does a database read and,
      when the record is present without its certificate, waits five times
      300ms (:1014-1021) before giving up with [UnavailableEpoch].
    - THE PENALTY SPLIT. [From<&PrimaryNetworkError> for Option<Penalty>]
      (error/network.rs:141-205) maps [InvalidEpochRequest] to
      [Some(Penalty::Medium)] (:192-193) but maps [UnavailableEpoch] and
      [UnavailableEpochDigest] to [None] (:196-197, commented "A node might
      not have this yet..."), so an honest catch-up miss is deliberately
      penalty-free. The charge is applied in the spawned serve at
      network/mod.rs:1627-1630.
    - THE DIVERGENT WIRE CONTRACT. The request type's own documentation says
      the charged case is legal: [PrimaryRequest::EpochRecord]'s doc comment
      (network/message.rs:70-80) reads "If neither number or hash are set then
      will return the latest epoch record the node has available." Nothing
      caller-side enforces the code's stricter rule: [request_epoch_cert]
      (network/mod.rs:809-829) forwards [epoch] and [hash] verbatim.

    COMPONENTS (two, both finite).

    - [load] - the responder's [epoch_record_peers] table for the three
      NON-probing requesters, as a multiset of their in-flight serve counts,
      canonicalised ascending. A multiset rather than a labelled triple
      because those three peers are interchangeable: none of them is a
      knowledge agent and no statement names one of them, while the two
      quantities the statements do use - total occupancy and the number of
      DISTINCT holders - are multiset invariants.
    - [probe] - the fate of ONE request from the probing requester: not yet
      sent, shed, admitted and being served, or answered. Its selector (what
      the request names, and whether its author is a client following
      message.rs:73-74 or a peer probing for a penalty-free flood) rides on
      the in-flight constructors.

    The probing requester holds AT MOST ONE in-flight epoch-record serve
    because [request_epoch_cert] is sequential: [for _ in 0..3 { let res =
    self.handle.send_request_any(request.clone()).await?; if let Ok(Ok(...)) =
    res.await { return ... } }] (network/mod.rs:816-827) awaits each response
    before trying the next peer. Its per-peer cap can therefore never bind on
    it; it is shed only by the global pool, which is exactly the interesting
    case.

    ADMISSION WINDOW (scope restriction, stated so it is auditable rather than
    hidden). The three flooding requesters' slots churn freely - admissions
    and [Drop] releases alike - while the probe has nothing in flight; once
    the probe's request has been ADMITTED OR SHED the model follows that one
    request to completion with the table held fixed. This is a scope choice
    forced by the size rule (the free product is about 200 states). It is
    sound for every statement here: an admitted serve holds its own
    [PeerSlotPermit] for its lifetime (network/mod.rs:1619-1622), so no other
    peer's admission or release can preempt, accelerate or re-shed it, and
    every occupancy the free-churn model can reach is reached here too - the
    flooders already range over the whole gate-permitted table at the idle
    stage, and the probe's own slot is taken on top of it at admission.

    THE CANCELLATION ARM (not modelled, and why no statement leans on that).
    The spawned serve runs inside [tokio::select!] against the network layer's
    cancel oneshot, and its [_ = cancel => ()] arm (network/mod.rs:1623, :1636)
    aborts the serve WITHOUT sending a response and WITHOUT reporting a
    penalty. The model has no such branch. Every conjunct of every statement in
    this family is insensitive to adding one, which is why its absence is a
    size choice and not a load-bearing omission: a cancelled serve is (i) not
    [replied(P)], so S3's "never answered without the charge" conjunct - stated
    as a [~EF] over answered states precisely so a cancel cannot satisfy it -
    and S2's [K (V1, admitted(P))] view class are both untouched; (ii) not
    [penalty_medium(P)], so S3's two penalty-free conjuncts stay true; (iii)
    invisible to V1, which would see the same [Pv_inflight] value it sees while
    shed or served, so a cancelled state could only ENLARGE the class that
    already refutes [K (V1, shed(P))] and [K (V1, serving(P))]; and (iv) a
    permit release, so occupancy can only fall and S1 and S2's bounds are
    unaffected.

    WHAT "DISTINCT REQUESTERS" MEANS (scope of the S1 guarantee). The per-peer
    counter is keyed by [BlsPublicKey] (network/mod.rs:1378) and the arm admits
    "any peer whose identity resolves (not committee membership)"
    (network/mod.rs:74-75), so the fairness guarantee is per RESOLVED IDENTITY:
    three Sybil identities exhaust the pool just as three honest peers do. S1
    claims exactly that and no more. What makes it exact rather than
    best-effort is that [try_admit_epoch_record] reads and increments the
    counter under ONE [peers.lock()] guard (network/mod.rs:357-362), so there
    is no read-then-increment window in which two admissions could both see the
    same sub-cap count.

    MODELLING HORIZONS (inert on the pristine model, stated for honesty).
    Deleting a cap makes the real system unbounded, which a finite model
    cannot represent, so the universe carries two horizons that no pristine
    transition ever reaches: a single requester never holds more than
    {!peer_horizon} = 5 concurrent serves, and total occupancy never exceeds
    {!occ_horizon} = 6. The real gates (2 and 5) bind strictly first, so the
    pristine reachable set is exactly what the code permits; the horizons only
    keep the two cap-deleting mutants finite while still letting each witness
    its violation.

    ROLE MAPPING (knowledge agents must be validators with a real,
    non-constant view; a blank-view party may never appear under K).

    - V1 is the PROBING REQUESTER, a peer running [request_epoch_cert]
      (network/mod.rs:809-829). It SEES what it itself asked for - the
      selector and its own intent - and whether a response has come back. It
      DOES NOT see the responder's slot table, and above all it does not see
      which branch of :1602-1613 its request took: shed and slow-serve are the
      same "sent, nothing back yet" for it. That is not a modelling
      convenience, it is the shed comment's own claim (:1607-1609), and the
      client layer discards the failure kind anyway - [request_epoch_cert]
      pattern-matches [if let Ok(Ok(NetworkResponseMessage { .. })) =
      res.await] (:820-826) and every failure, whatever its cause, falls
      through identically to the next peer.
    - V0 is the RESPONDER primary that owns [epoch_record_semaphore] and
      [epoch_record_peers] (network/mod.rs:1375-1378, :1413-1414). It SEES its
      own slot table, the stage its own pipeline has reached, and the request
      as BYTES - the [(epoch, hash)] pair is a parameter of
      [process_epoch_record_request] (:1586-1592), so whether the request is
      unaddressed is NOT hidden from it. What is hidden is WHO sent it and
      why: a client written to message.rs:73-74 and a peer farming a
      penalty-free flood emit the identical [(None, None)] bytes.
    - V2, V3 and V4 are the three other requesters. They appear only through
      the occupancy multiset, are idle non-agents with the constant blank view
      and never appear under K. V5..V9 take no part in this model and have the
      same blank view. *)

(** The responder's global concurrency budget for [EpochRecord] serves:
    [MAX_CONCURRENT_EPOCH_RECORD_REQUESTS = 5] (network/mod.rs:72-81). *)
let pool_cap = 5

(** The per-requester in-flight cap: [MAX_PENDING_REQUESTS_PER_PEER = 2]
    (network/mod.rs:102-105), read by [try_admit_epoch_record] at
    network/mod.rs:359. *)
let per_peer_cap = 2

(** Modelling horizon: a single requester is never modelled as holding more
    than this many concurrent serves. Never reached pristine ([per_peer_cap]
    binds at 2); it exists so {!No_per_peer_record_cap} can witness one peer
    taking the whole pool. *)
let peer_horizon = 5

(** Modelling horizon: total in-flight occupancy is never modelled above this.
    Never reached pristine ([pool_cap] binds at 5); it exists so
    {!No_record_admission_gate} can witness an over-cap occupancy. *)
let occ_horizon = 6

(** The responder's [epoch_record_peers] in-flight counts for the three
    non-probing requesters (network/mod.rs:1378, maintained at :360 and
    released by [Drop] at :305-315), canonicalised ascending because those
    three peers are interchangeable in every statement of this family. *)
type load = {
  a : int;  (** the smallest of the three in-flight counts *)
  b : int;  (** the middle in-flight count *)
  c : int;  (** the largest in-flight count *)
}

(** Total deterministic comparison over ALL load fields. *)
let load_compare l1 l2 =
  let c0 = Int.compare l1.a l2.a in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = Int.compare l1.b l2.b in
    if Bool.not (Int.equal c1 0) then c1 else Int.compare l1.c l2.c

(** Build a canonical (ascending) load from three raw counts. The non-triple
    list arms are unreachable - [List.sort] preserves length - and are spelled
    out only because a bare wildcard arm is forbidden. *)
let mk_load x y z =
  match List.sort Int.compare [ x; y; z ] with
  | [ p; q; r ] -> { a = p; b = q; c = r }
  | [] | [ _ ] | [ _; _ ] | _ :: _ :: _ :: _ :: _ -> { a = x; b = y; c = z }

(** A canonical position in the load multiset. Positions, not peer names: the
    three flooding requesters are interchangeable here. *)
type slot =
  | Slot_lo  (** the requester holding the fewest slots *)
  | Slot_mid  (** the requester holding the middle number of slots *)
  | Slot_hi  (** the requester holding the most slots *)

(** The three canonical positions, for building transition fan-outs. *)
let all_slots = [ Slot_lo; Slot_mid; Slot_hi ]

(** The in-flight serve count at one canonical position. *)
let count_at l s =
  match s with Slot_lo -> l.a | Slot_mid -> l.b | Slot_hi -> l.c

(** One more admitted serve for the requester at position [s]
    ([*guard.entry(peer).or_insert(0) += 1], network/mod.rs:360). *)
let bump l s =
  match s with
  | Slot_lo -> mk_load (l.a + 1) l.b l.c
  | Slot_mid -> mk_load l.a (l.b + 1) l.c
  | Slot_hi -> mk_load l.a l.b (l.c + 1)

(** One finished serve for the requester at position [s]: the [PeerSlotPermit]
    [Drop] decrement (network/mod.rs:305-315). *)
let unbump l s =
  match s with
  | Slot_lo -> mk_load (l.a - 1) l.b l.c
  | Slot_mid -> mk_load l.a (l.b - 1) l.c
  | Slot_hi -> mk_load l.a l.b (l.c - 1)

(** Slots held by the three flooding requesters together. *)
let load_total l = l.a + l.b + l.c

(** How many of the three flooding requesters hold at least one slot - the
    "distinct holders" the fairness statement counts. *)
let load_holders l =
  (if l.a > 0 then 1 else 0)
  + (if l.b > 0 then 1 else 0)
  + if l.c > 0 then 1 else 0

(** The largest number of slots any one flooding requester holds; the load is
    canonicalised ascending, so this is [c]. *)
let load_peak l = l.c

(** What the probe's request names, and who wrote it. The [(epoch, hash)]
    selector of [PrimaryRequest::EpochRecord] (network/message.rs:70-80) drives
    the dispatch match at handler.rs:996-1000. *)
type sel =
  | Sel_addressed
      (** [EpochRecord { epoch: Some(e), .. }] (or a [Some(hash)]): the
          [(Some(epoch), _)] / [(_, Some(hash))] arms of handler.rs:997-998 *)
  | Sel_none_doc
      (** [EpochRecord { epoch: None, hash: None }] from a client written to
          the request type's own documented contract, network/message.rs:73-74
          ("If neither number or hash are set then will return the latest
          epoch record the node has available") *)
  | Sel_none_grief
      (** the byte-for-byte identical unaddressed request from a peer probing
          the arm for a penalty-free flood. Nothing on the wire separates it
          from {!Sel_none_doc}: that indistinguishability is the epistemic
          content of statement S3 *)

(** Total order index for {!sel}. *)
let sel_index = function
  | Sel_addressed -> 0
  | Sel_none_doc -> 1
  | Sel_none_grief -> 2

(** Total order on {!sel}. *)
let sel_compare x y = Int.compare (sel_index x) (sel_index y)

(** The three request shapes the probe may send. *)
let all_sels = [ Sel_addressed; Sel_none_doc; Sel_none_grief ]

(** What reached the probing requester when its admitted serve finished. *)
type outcome =
  | Out_answered
      (** a penalty-free answer: either [PrimaryResponse::EpochRecord]
          (handler.rs:1002) or [Error(UnavailableEpoch)] for an epoch this node
          does not have, which error/network.rs:196-197 deliberately maps to
          [None] penalty so honest catch-up is never scored down *)
  | Out_charged
      (** [Error(InvalidEpochRequest)] (handler.rs:999) PLUS the
          [report_penalty(peer, Penalty::Medium)] of network/mod.rs:1627-1630,
          the mapping being error/network.rs:192-193 *)

(** Total order index for {!outcome}. *)
let outcome_index = function Out_answered -> 0 | Out_charged -> 1

(** Total order on {!outcome}. *)
let outcome_compare x y = Int.compare (outcome_index x) (outcome_index y)

(** The fate of the probing requester's single request. *)
type probe =
  | Pb_idle  (** nothing in flight: [request_epoch_cert] has not sent yet *)
  | Pb_shed of sel
      (** [try_admit_epoch_record] returned [None] and
          [process_epoch_record_request] returned at network/mod.rs:1612,
          dropping the response channel. No slot is held and nothing goes on
          the wire *)
  | Pb_serve of sel
      (** admitted: a [PeerSlotPermit] is held for the serve's lifetime
          (network/mod.rs:1619-1622) while [retrieve_epoch_record] runs, up to
          and including the five-times-300ms certificate wait of
          handler.rs:1014-1021 *)
  | Pb_done of outcome
      (** the serve finished, the response was sent (network/mod.rs:1632-1633)
          and the permit dropped, freeing both caps *)

(** Total order index for the {!probe} constructors. *)
let probe_index = function
  | Pb_idle -> 0
  | Pb_shed _ -> 1
  | Pb_serve _ -> 2
  | Pb_done _ -> 3

(** Total order on {!probe}: constructor order first, then payload. Every
    cross-constructor pair is decided by the index, so no wildcard arm. *)
let probe_compare p q =
  let ci = Int.compare (probe_index p) (probe_index q) in
  if Bool.not (Int.equal ci 0) then ci
  else
    match (p, q) with
    | Pb_idle, Pb_idle -> 0
    | Pb_shed s, Pb_shed t -> sel_compare s t
    | Pb_serve s, Pb_serve t -> sel_compare s t
    | Pb_done o, Pb_done r -> outcome_compare o r
    | Pb_idle, (Pb_shed _ | Pb_serve _ | Pb_done _)
    | Pb_shed _, (Pb_idle | Pb_serve _ | Pb_done _)
    | Pb_serve _, (Pb_idle | Pb_shed _ | Pb_done _)
    | Pb_done _, (Pb_idle | Pb_shed _ | Pb_serve _) ->
        ci

(** Slots the probing requester itself occupies in the responder's table: one
    exactly while its admitted serve is running. *)
let probe_slots = function
  | Pb_idle -> 0
  | Pb_shed _ -> 0
  | Pb_serve _ -> 1
  | Pb_done _ -> 0

(** The joint global state: the responder's slot table for the other three
    requesters, and the fate of the probing requester's own request. *)
type state = { load : load; probe : probe }

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c0 = load_compare s1.load s2.load in
  if Bool.not (Int.equal c0 0) then c0 else probe_compare s1.probe s2.probe

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** Total concurrent [EpochRecord] serves the responder is holding permits for:
    the three flooders plus the probe's own admitted serve. This is exactly
    what [MAX_CONCURRENT_EPOCH_RECORD_REQUESTS] bounds. *)
let occupancy s = load_total s.load + probe_slots s.probe

(** How many DISTINCT requesters hold at least one serve slot. *)
let holders s = load_holders s.load + probe_slots s.probe

(** The probing requester's local view. It carries what V1 itself composed and
    whether a reply came back - and nothing else. Crucially {!Pv_inflight} does
    NOT record which branch of network/mod.rs:1602-1613 the request took. *)
type pview =
  | Pv_idle  (** V1 has nothing outstanding *)
  | Pv_inflight of sel
      (** V1 sent this request and has had nothing back: the shed branch and
          the running-serve branch are literally this same value *)
  | Pv_replied of outcome  (** a response reached V1 *)

(** Total order index for {!pview}. *)
let pview_index = function
  | Pv_idle -> 0
  | Pv_inflight _ -> 1
  | Pv_replied _ -> 2

(** Total order on {!pview}: constructor order, then payload; no wildcard arm. *)
let pview_compare x y =
  let ci = Int.compare (pview_index x) (pview_index y) in
  if Bool.not (Int.equal ci 0) then ci
  else
    match (x, y) with
    | Pv_idle, Pv_idle -> 0
    | Pv_inflight s, Pv_inflight t -> sel_compare s t
    | Pv_replied o, Pv_replied r -> outcome_compare o r
    | Pv_idle, (Pv_inflight _ | Pv_replied _)
    | Pv_inflight _, (Pv_idle | Pv_replied _)
    | Pv_replied _, (Pv_idle | Pv_inflight _) ->
        ci

(** The request as the responder sees it on the wire: the shape of the
    [(epoch, hash)] pair it is handed at network/mod.rs:1589-1590. *)
type wire =
  | W_addressed  (** at least one of [epoch] / [hash] is [Some] *)
  | W_unaddressed  (** the [(None, None)] pair of handler.rs:999 *)

(** Total order index for {!wire}. *)
let wire_index = function W_addressed -> 0 | W_unaddressed -> 1

(** Total order on {!wire}. *)
let wire_compare x y = Int.compare (wire_index x) (wire_index y)

(** Which wire shape a selector presents. The doc-conformant client and the
    griefer are the SAME bytes - this is where V0's ignorance comes from. *)
let wire_of = function
  | Sel_addressed -> W_addressed
  | Sel_none_doc -> W_unaddressed
  | Sel_none_grief -> W_unaddressed

(** How far the responder's own pipeline has taken the probe's request. *)
type stage =
  | Rs_idle  (** no request from the probing requester *)
  | Rs_shed of wire  (** it shed this request at network/mod.rs:1612 *)
  | Rs_serving of wire  (** it is serving this request under a permit *)
  | Rs_done of outcome  (** it answered, and charged or did not charge *)

(** Total order index for {!stage}. *)
let stage_index = function
  | Rs_idle -> 0
  | Rs_shed _ -> 1
  | Rs_serving _ -> 2
  | Rs_done _ -> 3

(** Total order on {!stage}: constructor order, then payload; no wildcard arm. *)
let stage_compare x y =
  let ci = Int.compare (stage_index x) (stage_index y) in
  if Bool.not (Int.equal ci 0) then ci
  else
    match (x, y) with
    | Rs_idle, Rs_idle -> 0
    | Rs_shed u, Rs_shed v -> wire_compare u v
    | Rs_serving u, Rs_serving v -> wire_compare u v
    | Rs_done o, Rs_done r -> outcome_compare o r
    | Rs_idle, (Rs_shed _ | Rs_serving _ | Rs_done _)
    | Rs_shed _, (Rs_idle | Rs_serving _ | Rs_done _)
    | Rs_serving _, (Rs_idle | Rs_shed _ | Rs_done _)
    | Rs_done _, (Rs_idle | Rs_shed _ | Rs_serving _) ->
        ci

(** A validator's local view. [View_requester] is V1's projection (its own
    request and whether a reply arrived, never the responder's table nor the
    admission branch); [View_responder] is V0's projection (its own slot table,
    its own pipeline stage, and the request's wire shape but NOT its author's
    intent); [View_idle] is the constant blank view of the non-agents. *)
type view =
  | View_requester of pview
  | View_responder of load * stage
  | View_idle

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare x y =
  match (x, y) with
  | View_idle, View_idle -> 0
  | View_idle, (View_requester _ | View_responder _) -> -1
  | (View_requester _ | View_responder _), View_idle -> 1
  | View_requester p, View_requester q -> pview_compare p q
  | View_requester _, View_responder _ -> -1
  | View_responder _, View_requester _ -> 1
  | View_responder (l, s), View_responder (m, t) ->
      let cl = load_compare l m in
      if Bool.not (Int.equal cl 0) then cl else stage_compare s t

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** V1's projection of the probe's fate: shed and running-serve collapse. *)
let requester_view = function
  | Pb_idle -> Pv_idle
  | Pb_shed s -> Pv_inflight s
  | Pb_serve s -> Pv_inflight s
  | Pb_done o -> Pv_replied o

(** V0's projection of the probe's fate: it knows exactly which branch it took
    and what the bytes were, but not who wrote them. *)
let responder_stage = function
  | Pb_idle -> Rs_idle
  | Pb_shed s -> Rs_shed (wire_of s)
  | Pb_serve s -> Rs_serving (wire_of s)
  | Pb_done o -> Rs_done o

(** View projection. V1 (the probing requester) and V0 (the responder) are the
    knowledge agents; V2..V9 are idle non-agents with the constant blank view
    and never appear under K. *)
let view v s =
  match v with
  | Validator.V1 -> View_requester (requester_view s.probe)
  | Validator.V0 -> View_responder (s.load, responder_stage s.probe)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_per_peer_record_cap
      (** delete the [count < MAX_PENDING_REQUESTS_PER_PEER] conjunct of
          [try_admit_epoch_record]
          (crates/consensus/primary/src/network/mod.rs:359), admitting on the
          global permit alone. Adds the transitions in which one requester
          takes a third, fourth and fifth slot, so tables such as [(0, 0, 5)]
          become reachable: the pool is exhausted by a SINGLE holder and one
          requester is over the per-peer cap, refuting both conjuncts of S1.
          The global gate at :356 and the whole dispatch path are untouched,
          so S2 and S3 keep proving and the refutation is attributable.

          NO SIBLING REPAIRS IT. (1) The libp2p stream layer's per-peer
          inbound limiter (network-libp2p/src/stream/behavior.rs:41-45 and
          :280-290) is a RATE - [MAX_INBOUND_PER_WINDOW = 256] per one-second
          window - and it counts inbound STREAMS on the sync/legacy stream
          protocols, not request-response RPCs, so five concurrent
          [EpochRecord] RPCs pass it without touching it. (2)
          [try_admit_sync] (network/mod.rs:317-341) enforces a per-peer cap
          too, but over a DIFFERENT semaphore and a different counter
          ([epoch_stream_semaphore] / [sync_stream_peers]); the epoch-record
          admitter "neither consults nor contends the stream pending map"
          (its own doc comment, :349-350). (3) The request-response behaviour
          is built with [request_response::Config::default()]
          (network-libp2p/src/consensus.rs:367-371) and the QUIC transport
          with [max_concurrent_stream_limit = 10_000]
          (config/src/network.rs:291, :305): both are orders of magnitude
          above five and neither is a per-peer epoch-record concurrency cap.
          (4) The arm is reachable by any peer whose identity resolves, not
          committee members only (network/mod.rs:74-75). *)
  | No_record_admission_gate
      (** delete the [try_admit_epoch_record] call and its [else { return; }]
          arm (crates/consensus/primary/src/network/mod.rs:1602-1613), so
          [process_epoch_record_request] spawns a serve task for every
          request. Removes the shed transition entirely and removes both caps
          at once (they live in the one deleted call), so occupancy above
          [MAX_CONCURRENT_EPOCH_RECORD_REQUESTS] becomes reachable and S2's
          bound conjunct fails. It ALSO collapses V1's ignorance: with the
          shed branch gone, "sent and nothing back" can only be a running
          serve, so a serving requester now KNOWS it is being served and S2's
          serve-opacity conjunct fails as well.

          NO SIBLING REPAIRS IT. (1) There is no second bound on this task
          family: [task_spawner.spawn_task] (used at :1619) is an unbounded
          spawn, and the only other epoch-record limiter in the crate is the
          deleted one. (2) The libp2p layer does not restore it - see the
          sibling hunt on {!No_per_peer_record_cap}: the stream rate window
          does not cover request-response, and the request-response and QUIC
          defaults (100 per peer, 10_000 streams) are far above five. (3) The
          admission is the FIRST statement of the function, so nothing
          downstream can re-shed: [retrieve_epoch_record] always runs and
          always answers or errors. (4) Its own doc comment states the
          pre-fix behaviour was exactly this unbounded spawn
          (network/mod.rs:1596-1601, GHSA-vc2r-9cp2-w74j), and the crate's
          regression tests
          (tests/network_tests.rs:1624-1656 and :1658-1696) assert both caps
          against this very function. *)
  | No_unaddressed_request_reject
      (** delete the [(None, None) => return
          Err(PrimaryNetworkError::InvalidEpochRequest)] arm of
          [retrieve_epoch_record]
          (crates/consensus/primary/src/network/handler.rs:999) and serve the
          latest record instead, exactly as the request type's own
          documentation specifies (network/message.rs:73-74). Changes exactly
          one transition: an admitted unaddressed serve now steps to
          [Pb_done Out_answered] rather than [Pb_done Out_charged], so
          [Out_charged] becomes unreachable and S3's "an admitted unaddressed
          request is inevitably charged Medium" conjunct fails. The load
          transitions are untouched, so S1 and S2 keep proving.

          NO SIBLING REPAIRS IT. (1) [InvalidEpochRequest] is CONSTRUCTED
          nowhere else in the tree - the only site is handler.rs:999; every
          other occurrence is a classification arm
          (error/network.rs:56, :132, :192, network/message.rs:354) or a unit
          test (error/network.rs:272, :356). (2) No caller-side validation
          exists: [request_epoch_cert] (network/mod.rs:809-829) forwards
          [epoch] and [hash] verbatim with no non-[None] requirement, and the
          dispatch site (network/mod.rs:1478-1480) passes them straight
          through. (3) The admission shed drops the channel WITHOUT any
          penalty and runs strictly BEFORE the dispatch match, so it cannot
          re-establish the charge. (4) [PrimaryResponse::Error] is produced
          for any handler error ([header.into_response()],
          network/mod.rs:1632, mapped at network/message.rs:330-357) but
          carries no penalty of its own: the charge comes solely from the
          [Option<Penalty>] mapping at error/network.rs:141-205. *)

(** Whether one more serve may be admitted for the flooding requester at
    position [k], under the mutation in force. The pristine conjunction is
    [try_admit_epoch_record]'s own: a global permit
    ([semaphore.try_acquire_owned().ok()?], network/mod.rs:356) and then
    [count < MAX_PENDING_REQUESTS_PER_PEER] (:359). Every mutation arm is
    spelled. *)
let flooder_admits mut s k =
  let cnt = count_at s.load k in
  let occ = occupancy s in
  match mut with
  | Pristine | No_unaddressed_request_reject ->
      cnt < per_peer_cap && occ < pool_cap
  | No_per_peer_record_cap -> cnt < peer_horizon && occ < pool_cap
  | No_record_admission_gate -> cnt < peer_horizon && occ < occ_horizon

(** Whether the probe's own request is admitted. The probing requester holds no
    other epoch-record serve (its [request_epoch_cert] loop is sequential,
    network/mod.rs:816-827), so its per-peer count is 0 at admission and only
    the global permit can refuse it. Every mutation arm is spelled. *)
let probe_admitted mut s =
  match mut with
  | Pristine | No_per_peer_record_cap | No_unaddressed_request_reject ->
      occupancy s < pool_cap
  | No_record_admission_gate -> true

(** What an admitted serve of [sel] answers with. Pristine, the dispatch match
    of handler.rs:996-1000 sends an unaddressed request to
    [InvalidEpochRequest] and thence to [Penalty::Medium]
    (error/network.rs:192-193); under {!No_unaddressed_request_reject} it is
    answered like any other. Every mutation arm is spelled. *)
let serve_outcome mut sel =
  match mut with
  | Pristine | No_per_peer_record_cap | No_record_admission_gate -> (
      match sel with
      | Sel_addressed -> Out_answered
      | Sel_none_doc -> Out_charged
      | Sel_none_grief -> Out_charged)
  | No_unaddressed_request_reject -> (
      match sel with
      | Sel_addressed -> Out_answered
      | Sel_none_doc -> Out_answered
      | Sel_none_grief -> Out_answered)

(** The flooding requesters' admissions available at [s]. *)
let flooder_admit_steps mut s =
  List.concat_map
    (fun k ->
      if flooder_admits mut s k then [ { s with load = bump s.load k } ] else [])
    all_slots

(** The flooding requesters' [PeerSlotPermit] releases available at [s]
    (network/mod.rs:305-315). *)
let flooder_release_steps s =
  List.concat_map
    (fun k ->
      if count_at s.load k > 0 then [ { s with load = unbump s.load k } ]
      else [])
    all_slots

(** The probe sending one request of each shape, each landing on the branch
    [try_admit_epoch_record] picks for it. *)
let probe_send_steps mut s =
  List.map
    (fun sel ->
      {
        s with
        probe = (if probe_admitted mut s then Pb_serve sel else Pb_shed sel);
      })
    all_sels

(** The transition relation. While the probe has nothing in flight the other
    requesters' table churns and the probe may send; once its request has been
    decided the model follows that one request to completion with the table
    held fixed (see the header's ADMISSION WINDOW note). A shed request and a
    delivered response are both terminal, hence stutter-closed. *)
let next_with mut s =
  match s.probe with
  | Pb_idle ->
      flooder_admit_steps mut s @ flooder_release_steps s @ probe_send_steps mut s
  | Pb_shed _ -> []
  | Pb_serve sel -> [ { s with probe = Pb_done (serve_outcome mut sel) } ]
  | Pb_done _ -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The single initial state: an idle responder with an empty slot table and a
    probing requester that has not sent yet. *)
let initial = { load = { a = 0; b = 0; c = 0 }; probe = Pb_idle }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Pool_exhausted
      (** occupancy equals [MAX_CONCURRENT_EPOCH_RECORD_REQUESTS] = 5, i.e. the
          next [try_acquire_owned] (network/mod.rs:356) fails *)
  | Pool_over_cap
      (** occupancy EXCEEDS 5: the state the global semaphore forbids *)
  | Three_distinct_holders
      (** at least three DISTINCT requesters hold a serve slot *)
  | Requester_over_cap
      (** some requester holds more than [MAX_PENDING_REQUESTS_PER_PEER] = 2
          concurrent serves: the state network/mod.rs:359 forbids *)
  | Probe_shed
      (** the probe's request took the shed branch: its response channel was
          dropped at network/mod.rs:1612 *)
  | Probe_serving
      (** the probe's request is admitted and its serve is running under a
          held [PeerSlotPermit] (network/mod.rs:1619-1622) *)
  | Probe_admitted
      (** the probe's request was admitted at all - it is being served, or was
          served and answered *)
  | Probe_replied  (** a response reached the probing requester *)
  | Serve_addressed
      (** the serve now running is of a request naming an epoch or a hash *)
  | Serve_unaddressed
      (** the serve now running is of a [(None, None)] request - the case
          handler.rs:999 rejects and network/message.rs:73-74 documents as
          legal *)
  | Serving_deviant
      (** the unaddressed request now being served was sent to farm a
          penalty-free flood rather than by a client following
          network/message.rs:73-74. Identical bytes either way: this is the
          fact V0 provably cannot resolve *)
  | Probe_charged
      (** a [Penalty::Medium] was reported against the probing requester
          (network/mod.rs:1627-1630 via error/network.rs:192-193) *)

(** Atom valuation over the global state. *)
let label at s =
  match at with
  | Pool_exhausted -> Int.equal (occupancy s) pool_cap
  | Pool_over_cap -> occupancy s > pool_cap
  | Three_distinct_holders -> holders s >= 3
  | Requester_over_cap ->
      load_peak s.load > per_peer_cap || probe_slots s.probe > per_peer_cap
  | Probe_shed -> (
      match s.probe with
      | Pb_shed _ -> true
      | Pb_idle | Pb_serve _ | Pb_done _ -> false)
  | Probe_serving -> (
      match s.probe with
      | Pb_serve _ -> true
      | Pb_idle | Pb_shed _ | Pb_done _ -> false)
  | Probe_admitted -> (
      match s.probe with
      | Pb_serve _ | Pb_done _ -> true
      | Pb_idle | Pb_shed _ -> false)
  | Probe_replied -> (
      match s.probe with
      | Pb_done _ -> true
      | Pb_idle | Pb_shed _ | Pb_serve _ -> false)
  | Serve_addressed -> (
      match s.probe with
      | Pb_serve Sel_addressed -> true
      | Pb_serve (Sel_none_doc | Sel_none_grief) -> false
      | Pb_idle | Pb_shed _ | Pb_done _ -> false)
  | Serve_unaddressed -> (
      match s.probe with
      | Pb_serve (Sel_none_doc | Sel_none_grief) -> true
      | Pb_serve Sel_addressed -> false
      | Pb_idle | Pb_shed _ | Pb_done _ -> false)
  | Serving_deviant -> (
      match s.probe with
      | Pb_serve Sel_none_grief -> true
      | Pb_serve (Sel_addressed | Sel_none_doc) -> false
      | Pb_idle | Pb_shed _ | Pb_done _ -> false)
  | Probe_charged -> (
      match s.probe with
      | Pb_done Out_charged -> true
      | Pb_done Out_answered -> false
      | Pb_idle | Pb_shed _ | Pb_serve _ -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Pool_exhausted -> "occupancy = 5"
  | Pool_over_cap -> "occupancy > 5"
  | Three_distinct_holders -> "distinct_holders >= 3"
  | Requester_over_cap -> "some_requester_slots > 2"
  | Probe_shed -> "shed(P)"
  | Probe_serving -> "serving(P)"
  | Probe_admitted -> "admitted(P)"
  | Probe_replied -> "replied(P)"
  | Serve_addressed -> "serving_addressed(P)"
  | Serve_unaddressed -> "serving_unaddressed(P)"
  | Serving_deviant -> "deviant_request(P)"
  | Probe_charged -> "penalty_medium(P)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every
    reachable world by test/t_record_serve_pool_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state, the
    mutation-parameterised transitions, the two-agent view and the atom
    valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
