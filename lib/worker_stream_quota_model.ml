(** Finite interpreted system for the WORKER_STREAM_QUOTA family: the worker's
    batch-stream admission accounting - the shared global semaphore, the
    combined per-peer in-flight cap, the pending -> serving handoff, and the
    sync path's read-nothing load shed. File citations refer to
    Telcoin-Association/telcoin-network at the working tree of git HEAD
    0c59c15b; every one of them was opened in this checkout.

    THE MODELLED MECHANISM. A worker responder [R] serves batch bytes over two
    protocols that share ONE budget.

    - THE TWO CAPS. [MAX_CONCURRENT_BATCH_STREAMS = 5]
      (network/mod.rs:41-45, "A semaphore permit is held from RPC acceptance
      through stream completion, so this bounds the true concurrent count-not
      just the pending map size") and [MAX_PENDING_REQUESTS_PER_PEER = 2]
      (network/mod.rs:60-65, "Counts a peer's legacy pending requests, legacy
      streams currently being served, and sync streams together, so no single
      peer can fill all global slots ... and starve its peers").
    - THE COMBINED COUNTER. [peer_in_flight] (network/mod.rs:206-216) is
      verbatim [let legacy = pending.keys().filter(|(p, _)| p == peer).count();
      let serving = active_legacy.get(peer).copied().unwrap_or(0); let syncing
      = sync_streams.get(peer).copied().unwrap_or(0); legacy + serving +
      syncing]. It is the SAME function on both admission paths, which is why
      one model has to carry both protocols: a legacy flood is what denies a
      sync requester and vice versa.
    - THE LEGACY ADMITTER. [try_admit_legacy] (network/mod.rs:260-315) takes a
      global permit first ([let Ok(permit) = semaphore.clone()
      .try_acquire_owned() else { return false; }], :271-273), then refuses at
      :280-289 ([if peer_count >= MAX_PENDING_REQUESTS_PER_PEER { ... // permit
      drops here, freeing the slot; return false; }]), then parks the permit
      inside a [PendingBatchStream] stored under [(peer, request_digest)]
      (:299-300). The permit is a FIELD of the stored value
      ([_permit: OwnedSemaphorePermit], :94-96), so a global slot is reserved
      from RPC acceptance. Called from [process_request_batches_stream]
      (:576-587), whose answer to the peer is the bare boolean
      [WorkerResponse::RequestBatchesStream { ack }] (:589).
    - THE HANDOFF. When the requester opens its stream,
      [process_inbound_stream] (:623-671) reads the correlation digest
      (:631-647) and calls [begin_serving_legacy] (:323-332), verbatim
      [let mut pending_guard = pending.lock(); let removed =
      pending_guard.remove(&key); let guard = removed.as_ref().map(|_|
      LegacyStreamGuard::admit(active_legacy, key.0)); (removed, guard)]. The
      entry LEAVES [pending_batch_requests] while its permit lives on inside
      the removed value, so without the second half of that pair the peer's
      tally would drop to zero for the whole serve. [LegacyStreamGuard::admit]
      (:177-188) increments [active_legacy_streams] and its [Drop] (:190-200)
      decrements it. The in-tree regression tests name the CVE this closes:
      [// Regression guard for GHSA-h9fv-qwvh-jv37] (:860-863, :907-910).
    - THE SYNC ADMITTER AND ITS SHED. [process_inbound_sync_stream] (:684-801)
      calls [try_admit_sync] (:228-246) SYNCHRONOUSLY, before spawning
      anything (:687-693). [try_admit_sync] takes the global permit
      ([semaphore.clone().try_acquire_owned().ok()?], :235), locks all three
      maps (:236-238) and refuses on the same combined count (:239-243). On
      [None] the spawned task takes the shed arm at :704-722 - it writes
      [SyncFrame::Deny(DenyReason::AtCapacity)] and closes WITHOUT EVER
      READING the opening request frame. Only an ADMITTED stream reaches the
      [read_frame::<_, WorkerSyncRequest>] at :728-739 and so discloses the
      requester's digest set to the responder application.

    COMPONENTS. Five, all finite.

    - [pend] - how many of the flooder's legacy requests sit in
      [pending_batch_requests] (network/mod.rs:347, keyed by
      [(BlsPublicKey, B256)] at :99-100). Because the key carries the request
      digest and a repeat of the SAME digest set REPLACES the entry rather than
      adding one (:295-307), each unit of [pend] is a distinct digest set, which
      is what a flooder trivially supplies.
    - [serv] - the flooder's legacy streams being served AND counted, i.e. its
      entry in [active_legacy_streams] (:360-369).
    - [ghost] - the flooder's legacy streams being served while holding a
      global permit that R's [peer_in_flight] does NOT charge to it. This is
      the GHSA-h9fv-qwvh-jv37 shape and no pristine transition ever produces
      it; it exists so {!No_serving_guard} can witness the count vanishing
      across the handoff. Note it still consumes a global permit, because the
      permit lives inside the removed [PendingBatchStream] (:94-96) and is
      untouched by the deletion - modelling it any other way would make the
      mutation stronger than the real defect.
    - [sync] - the victim's entry in [sync_stream_peers] (:353-359), i.e. its
      admitted sync exchanges.
    - [att] - the fate of the victim's CURRENT sync stream at R, including the
      responder-side bit the epistemic statement needs: whether R decoded that
      stream's opening request frame.

    THE SCALED POOL, AND WHAT THE CAP DOES AND DOES NOT BUY. {!Validator.t} is
    a ten-node committee ([quorum = 7], f = 3), so a responder faces NINE
    requesters against a pool of five. The per-peer cap therefore does NOT buy
    non-starvation: nine peers can hold eighteen slots' worth of demand, and a
    peer holding nothing is denied whenever three OTHER identities already hold
    the five permits. The candidate card this family was mined from claimed
    "a fresh request from the third peer is always admitted on the next step",
    which is arithmetic for a three-requester committee and is FALSE here; that
    conjunct was dropped rather than encoded.

    What the cap does buy is exactly what the constant's own doc comment claims
    - "no single peer can fill all global slots
    ([MAX_CONCURRENT_BATCH_STREAMS]) and starve its peers"
    (network/mod.rs:60-64) - and, quantitatively, that draining the pool takes
    at least [ceil(pool_cap / per_peer_cap)] DISTINCT resolved identities:
    three in the real code, two here. That is what the model is scaled to
    witness. [per_peer_cap = 2] is unchanged and {!pool_cap} is 3, the smallest
    value with [pool_cap > per_peer_cap], so exhaustion needs two distinct
    holders and one modelled flooder plus one modelled victim suffice. At
    [pool_cap = 4] the two modelled peers could never exhaust the pool at all
    and the property would go vacuous; at 2 a single peer could, and it would
    be false.

    SCOPE CHOICES, STATED SO THEY ARE AUDITABLE.

    - ONE PROTOCOL PER REQUESTER. The flooder V1 drives only the legacy path
      and the victim V2 only the sync path. Both caps still couple them - V1's
      legacy load is summed into [peer_in_flight] and consumes the shared
      semaphore that gates V2's admission - so the cross-path interaction the
      code has (:239-243 sums all three sources; :352 is one semaphore for
      both) is present. What is out of scope is a peer using BOTH paths at
      once. This matters for exactly one claim and is disclosed there: see the
      legacy-disclosure note under {!No_pre_read_sync_shed}.
    - THE ADMISSION DECISION IS ATOMIC. {!At_open} is placed at the instant
      [try_admit_sync] is entered, and it is the only state from which no other
      transition is enabled. That is faithful rather than convenient:
      [try_admit_sync] is called synchronously in [process_inbound_sync_stream]
      before any task is spawned (:687-693) and holds [pending],
      [active_legacy] and [sync_peers] simultaneously (:236-238), and every
      admission and every RAII release ([SyncStreamPermit::drop] :147-157,
      [LegacyStreamGuard::drop] :190-200) takes those same locks. So no
      admission, release or handoff can interleave between the entry to
      [try_admit_sync] and its verdict.
    - NO WALL CLOCK. [PENDING_REQUEST_TIMEOUT] (30s, :47-48) and
      [SYNC_REQUEST_READ_TIMEOUT] (5s, :78-82) are modelled as the
      always-enabled transitions {!legacy_expire} and the ability to leave any
      decided attempt, not as a clock. Both are capacity RELEASES, so a
      statement can only be made harder by them, never easier.

    REPAIR PATHS THAT ARE MODELLED (so no statement is true by omission).

    - [cleanup_stale_pending_requests] (:803-809,
      [.retain(|_, pending| now.duration_since(pending.created_at) <
      PENDING_REQUEST_TIMEOUT)]) removes a pending entry without it ever being
      served: transition {!legacy_expire}.
    - Every finished exchange releases its slot on both paths: the legacy
      guard's [Drop] (:190-200) and the sync permit's [Drop] (:147-157). The
      model releases [serv], [ghost] and [sync] freely, so no statement here
      holds because the model can only fill up.
    - A denied sync requester does not fall back to legacy on the SAME peer:
      [SyncFrame::Deny(_)] maps to [SyncAttempt::Failed] (handle.rs:450-453)
      and [request_batches_from_peer] falls back to legacy only on
      [SyncAttempt::Unsupported] (handle.rs:327-335), while [Failed] caches the
      peer as sync-capable and returns [Err] (handle.rs:336-340). The outer
      retry loop (handle.rs:204-280) does come back to the same peer, but over
      SYNC again because the capability cache now says [true]. So the model's
      "a denied attempt is cleared and may be retried over sync" is the whole
      of the requester's behaviour towards R.

    ROLE MAPPING (a knowledge agent must be a validator with a real,
    non-constant view; a blank-view party may never appear under K).

    - V0 is the RESPONDER worker R. It SEES its own three maps and its own
      semaphore occupancy, and it sees the request bytes of a stream it has
      actually read. It does not appear under K in any statement of this
      family; it is the party whose hidden state the victim reasons about.
    - V1 is the FLOODING REQUESTER on the legacy path. It SEES its own
      outstanding requests and its own open streams - and that is exactly
      [pend] and [serv + ghost] together, because the split between "charged"
      and "uncharged" is R's bookkeeping and is invisible from the wire. It
      never appears under K.
    - V2 is the VICTIM REQUESTER on the sync path and the only knowledge agent.
      It SEES how many exchanges it itself has open at R and the phase of the
      stream it most recently opened. It does NOT see R's semaphore, R's
      per-peer maps, V1's load, or - crucially - whether R decoded its request
      frame before denying it: {!At_shed} and {!At_shed_read} are the SAME
      [SyncFrame::Deny(DenyReason::AtCapacity)] on the wire, and that enum
      variant deliberately does not name the cause either
      (network-libp2p/src/sync/frame.rs:48-51, "The responder is at its
      concurrency cap (global or per-peer) and is shedding load").
    - V3..V9 take no part; they have the constant blank view and never appear
      under K. Modelling seven further requesters would only make the pool
      easier to exhaust and the victim's ignorance about WHO holds the permits
      larger, so their absence weakens no statement here. *)

(** The responder's global batch-stream budget, scaled from
    [MAX_CONCURRENT_BATCH_STREAMS = 5] (network/mod.rs:41-45) to the smallest
    value strictly above {!per_peer_cap}, so that draining it still takes more
    than one identity - the property the cap actually buys - while two modelled
    requesters suffice to witness both the drained and the undrained case. *)
let pool_cap = 3

(** The combined per-peer in-flight cap, [MAX_PENDING_REQUESTS_PER_PEER = 2]
    (network/mod.rs:60-65), unscaled. Read by [try_admit_legacy] at
    network/mod.rs:280 and by [try_admit_sync] at network/mod.rs:239-241. *)
let per_peer_cap = 2

(** The fate of the victim's current inbound sync stream at R. *)
type att =
  | At_idle
      (** V2 has no sync stream awaiting or holding a verdict at R. Exchanges
          admitted earlier may still be running; they live in the [sync]
          counter. *)
  | At_open
      (** V2 has opened a [StreamKind::Sync] stream and written its request in
          the opening [SyncFrame::Req] frame (handle.rs:392-407), and
          [process_inbound_sync_stream] has entered [try_admit_sync]
          (network/mod.rs:687-693). The verdict is the only thing that can
          happen next. *)
  | At_shed
      (** [try_admit_sync] returned [None] and the task took the shed arm at
          network/mod.rs:704-722: [SyncFrame::Deny(DenyReason::AtCapacity)] was
          written and the stream closed WITHOUT the request frame ever being
          read. *)
  | At_shed_read
      (** the same [Deny(AtCapacity)] on the wire, but the responder decoded
          the requester's digest set first. Unreachable on the pristine model;
          it is what deleting the early shed (see {!No_pre_read_sync_shed})
          makes reachable. *)
  | At_served
      (** admitted: [try_admit_sync] handed back a [SyncStreamPermit]
          (network/mod.rs:244-245), the opening request frame was read
          (network/mod.rs:728-739) and [process_sync_batches_stream] is
          serving. The exchange is counted in [sync]. *)

(** Total order index for {!att}. *)
let att_index = function
  | At_idle -> 0
  | At_open -> 1
  | At_shed -> 2
  | At_shed_read -> 3
  | At_served -> 4

(** Total order on {!att}. *)
let att_compare a b = Int.compare (att_index a) (att_index b)

(** Has the responder decoded the opening request frame of the victim's current
    sync stream? True exactly on the two arms that reach
    [read_frame::<_, WorkerSyncRequest>] (network/mod.rs:728-739). *)
let att_request_read a =
  match a with
  | At_served | At_shed_read -> true
  | At_idle | At_open | At_shed -> false

(** Has the responder answered the victim's current stream with
    [Deny(DenyReason::AtCapacity)]? Both shed arms write the identical frame. *)
let att_denied a =
  match a with
  | At_shed | At_shed_read -> true
  | At_idle | At_open | At_served -> false

(** The joint global state: the responder's accounting for the flooder, its
    accounting for the victim, and the fate of the victim's current stream. *)
type state = {
  pend : int;
      (** the flooder's entries in [pending_batch_requests]
          (network/mod.rs:347) *)
  serv : int;
      (** the flooder's legacy serves counted in [active_legacy_streams]
          (network/mod.rs:360-369) *)
  ghost : int;
      (** the flooder's legacy serves that hold a global permit but are
          charged to nobody; pristine-unreachable, see {!No_serving_guard} *)
  sync : int;
      (** the victim's entries in [sync_stream_peers] (network/mod.rs:353-359) *)
  att : att;  (** the victim's current sync stream, {!att} *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c0 = Int.compare s1.pend s2.pend in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = Int.compare s1.serv s2.serv in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Int.compare s1.ghost s2.ghost in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Int.compare s1.sync s2.sync in
        if Bool.not (Int.equal c3 0) then c3 else att_compare s1.att s2.att

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** Global permits the responder is holding: every pending legacy request,
    every legacy serve (charged or not) and every sync exchange holds one, per
    the doc comment at network/mod.rs:41-45. *)
let held s = s.pend + s.serv + s.ghost + s.sync

(** What [peer_in_flight] (network/mod.rs:206-216) computes for the flooder:
    its pending entries plus its entry in [active_legacy_streams]. An uncounted
    serve is by definition absent from both, which is the whole point. *)
let charged_v1 s = s.pend + s.serv

(** What [peer_in_flight] computes for the victim: it has no legacy activity in
    this model, so its combined count is its [sync_stream_peers] entry. *)
let charged_v2 s = s.sync

(** Global permits the flooder is actually holding, charged or not. *)
let held_v1 s = s.pend + s.serv + s.ghost

(** The phase of the victim's current stream AS THE VICTIM SEES IT. The two
    shed arms collapse here because they are the identical
    [Deny(DenyReason::AtCapacity)] frame on the wire (network/mod.rs:710-717,
    read back at handle.rs:450-453). *)
type v2phase =
  | Ph_idle  (** nothing opened, or the last verdict has been acted on *)
  | Ph_open  (** the stream is open and the request frame has been written *)
  | Ph_denied  (** a [Deny(AtCapacity)] frame came back *)
  | Ph_served  (** an [Ack] came back and batches are arriving *)

(** Total order index for {!v2phase}. *)
let v2phase_index = function
  | Ph_idle -> 0
  | Ph_open -> 1
  | Ph_denied -> 2
  | Ph_served -> 3

(** Total order on {!v2phase}. *)
let v2phase_compare a b = Int.compare (v2phase_index a) (v2phase_index b)

(** The victim's projection of {!att}: {!At_shed} and {!At_shed_read} are
    indistinguishable to it, which is the epistemic content of this family. *)
let v2phase_of a =
  match a with
  | At_idle -> Ph_idle
  | At_open -> Ph_open
  | At_shed | At_shed_read -> Ph_denied
  | At_served -> Ph_served

(** A validator's local view. *)
type view =
  | View_responder of int * int * int * int * att
      (** V0 = R: its [pending_batch_requests] count for the flooder, its
          [active_legacy_streams] count, the permits it holds for uncharged
          serves, its [sync_stream_peers] count for the victim, and the full
          state of the victim's current stream INCLUDING whether it decoded the
          request frame. *)
  | View_flooder of int * int
      (** V1: its own outstanding legacy requests and its own open serving
          streams. The charged/uncharged split is R's bookkeeping and is not
          on the wire, so the flooder sees only the SUM [serv + ghost]. *)
  | View_requester of int * v2phase
      (** V2: how many sync exchanges it itself has open at R, and the phase of
          the stream it most recently opened. It sees no counter of R's and
          nothing of V1. *)
  | View_blank  (** the constant blank view of the non-agent V3 *)

(** Total order index for {!view}. *)
let view_index = function
  | View_responder _ -> 0
  | View_flooder _ -> 1
  | View_requester _ -> 2
  | View_blank -> 3

(** Total order on the responder's five-field view payload. *)
let responder_compare (p, s, g, y, t) (p', s', g', y', t') =
  let c0 = Int.compare p p' in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = Int.compare s s' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Int.compare g g' in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Int.compare y y' in
        if Bool.not (Int.equal c3 0) then c3 else att_compare t t'

(** Total order on the flooder's two-field view payload. *)
let flooder_compare (p, o) (p', o') =
  let c0 = Int.compare p p' in
  if Bool.not (Int.equal c0 0) then c0 else Int.compare o o'

(** Total order on the victim's two-field view payload. *)
let requester_compare (y, ph) (y', ph') =
  let c0 = Int.compare y y' in
  if Bool.not (Int.equal c0 0) then c0 else v2phase_compare ph ph'

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare a b =
  let ci = Int.compare (view_index a) (view_index b) in
  if Bool.not (Int.equal ci 0) then ci
  else
    match (a, b) with
    | View_responder (p, s, g, y, t), View_responder (p', s', g', y', t') ->
        responder_compare (p, s, g, y, t) (p', s', g', y', t')
    | View_flooder (p, o), View_flooder (p', o') ->
        flooder_compare (p, o) (p', o')
    | View_requester (y, ph), View_requester (y', ph') ->
        requester_compare (y, ph) (y', ph')
    | View_blank, View_blank -> 0
    | View_responder _, (View_flooder _ | View_requester _ | View_blank)
    | View_flooder _, (View_responder _ | View_requester _ | View_blank)
    | View_requester _, (View_responder _ | View_flooder _ | View_blank)
    | View_blank, (View_responder _ | View_flooder _ | View_requester _) ->
        ci

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V2 is the knowledge agent; V0 and V1 have real
    non-constant views but never appear under K; V3 is the idle non-agent with
    the constant blank view. *)
let view v s =
  match v with
  | Validator.V0 -> View_responder (s.pend, s.serv, s.ghost, s.sync, s.att)
  | Validator.V1 -> View_flooder (s.pend, s.serv + s.ghost)
  | Validator.V2 -> View_requester (s.sync, v2phase_of s.att)
  | Validator.V3
  | Validator.V4
  | Validator.V5
  | Validator.V6
  | Validator.V7
  | Validator.V8
  | Validator.V9 ->
      View_blank

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as written at HEAD 0c59c15b *)
  | No_legacy_per_peer_cap
      (** delete the per-peer refusal in [try_admit_legacy]
          (crates/consensus/worker/src/network/mod.rs:280-289): [if peer_count
          >= MAX_PENDING_REQUESTS_PER_PEER { debug!(...); // permit drops here,
          freeing the slot; return false; }]. This ADDS legacy admissions from
          a peer already holding [per_peer_cap] slots, so the flooder walks up
          to the whole global pool and a victim holding nothing is denied.

          NO SIBLING PATH REPAIRS IT. (1) [try_admit_sync] carries the
          identical check (:239-243), but it gates only the SYNC path
          ([process_inbound_sync_stream], :684-693); a legacy flood arrives as
          [WorkerRequest::RequestBatchesStream] and is routed to
          [process_request_batches_stream] (:438-446, :576-587), which never
          traverses it. Both paths are in this model and the sync check is
          left intact, so the model cannot hide that. (2) The global semaphore
          (:271-273) survives the deletion and is modelled - it is peer-blind,
          which is exactly why one peer can drain it. (3)
          [cleanup_stale_pending_requests] (:803-809) is modelled as
          {!legacy_expire}: it expires an entry after 30s and never refuses an
          admission, so it bounds nothing. (4) The same-digest replacement at
          :295-307 only stops a peer re-arming ONE key; distinct digest sets
          are free, so it is not a concurrency bound. (5) The requester-side
          cap in [WorkerNetworkHandle::request_batches] (handle.rs:204-236) is
          the flooder's own code. (6) The transport does not restore it: the
          crate registers no [libp2p::connection_limits] behaviour at all, the
          request-response protocols are built with
          [request_response::Config::default()]
          (network-libp2p/src/consensus.rs:370, :381), and the QUIC stream
          ceiling is [n_stream_limit = 10_000] (config/src/network.rs) - none
          of these is a per-identity batch-stream concurrency cap. *)
  | No_serving_guard
      (** delete the second half of [begin_serving_legacy]
          (crates/consensus/worker/src/network/mod.rs:330): [let guard =
          removed.as_ref().map(|_| LegacyStreamGuard::admit(active_legacy,
          key.0));], returning [(removed, None)]. This REMOVES the transition
          that moves a peer's tally from [pending_batch_requests] into
          [active_legacy_streams] and ADDS one that drops the tally entirely
          while the permit lives on, so a peer serving [per_peer_cap] streams
          is admitted again. This is the shape of GHSA-h9fv-qwvh-jv37, named in
          the in-tree regression guards at :860-863 and :907-910.

          NO SIBLING PATH KEEPS A SERVING STREAM CHARGEABLE. (1) The
          [OwnedSemaphorePermit] inside the removed [PendingBatchStream]
          (:94-96) does survive - the model keeps it, as {!state.ghost} counts
          into {!held} - but it is peer-blind, so it bounds the pool, not the
          peer. (2) [sync_stream_peers] (:353-359) counts sync streams only and
          is untouched by the legacy handoff. (3)
          [cleanup_stale_pending_requests] (:803-809) retains over
          [pending_batch_requests], which the entry has already left. (4)
          [SEND_STREAM_TIMEOUT] (handler.rs:39, 200s, applied at handler.rs:299
          and :363) bounds how long ONE serve runs, not how many a peer holds.
          (5) The 5s correlation-digest read timeout (:631-646) fires strictly
          before the handoff. *)
  | No_pre_read_sync_shed
      (** delete the early shed arm of [process_inbound_sync_stream]
          (crates/consensus/worker/src/network/mod.rs:704-722), the [let
          Some(_permit) = permit else { ... write_frame(... Deny(AtCapacity)
          ...) ... return Ok(()); };] block, letting a shed task fall through
          to the [read_frame::<_, WorkerSyncRequest>] at :728-739 and deny
          afterwards. The wire answer is unchanged, so the requester's view is
          unchanged; what changes is that R has now decoded the digest set of a
          request it refused. This REPLACES the {!At_shed} transition with an
          {!At_shed_read} one.

          NO SIBLING PATH GIVES R THOSE DIGESTS ON THE PRISTINE SYNC PATH.
          (1) The [Deny] frame carries only a [DenyReason]
          (network-libp2p/src/sync/frame.rs:48-54) and nothing of the
          requester's. (1a) There is EXACTLY ONE [SyncFrame::Deny] write in the
          whole worker crate, and it is this shed arm (:712): the serve path
          [RequestHandler::process_sync_batches_stream] writes only [Ack],
          [Data], [End] and, on an internal failure,
          [Err(SyncFrameError::Internal)] (handler.rs:332-390). So a [Deny] on
          a worker sync stream can never be a POST-read refusal on the pristine
          code - which is what makes the victim's knowledge sound rather than
          an artefact of the model having only one deny site. (2) A denied sync
          requester does NOT retry the same peer
          over legacy: [SyncFrame::Deny(_) => Err(SyncAttempt::Failed(...))]
          (handle.rs:450-453) and only [SyncAttempt::Unsupported] falls back to
          legacy (handle.rs:327-335); [Failed] re-caches the peer as
          sync-capable (handle.rs:336-340), so the outer retry loop
          (handle.rs:204-280) comes back over sync again. (3) Gossip carries
          one digest published by an AUTHOR ([WorkerGossip::Batch(Epoch,
          BlockHash)], network/message.rs:10-15), never a requester's set.

          THE ONE REAL ASYMMETRY, DISCLOSED. On the LEGACY path R decodes the
          digest set BEFORE admitting:
          [WorkerRequest::RequestBatchesStream { batch_digests, epoch }] is
          destructured at :438-446, [generate_batch_request_id] hashes the set
          at :577 (handle.rs:816-821), and only then does :578 call
          [try_admit_legacy]. So a REFUSED LEGACY request has already disclosed
          its digests. That is why the statement pinned by this mutation is
          scoped to the sync protocol and why the model gives the victim only
          the sync path: the claim is about the stream R shed, not about
          everything R could ever learn about that peer. *)

(** Does [try_admit_legacy] still refuse a peer at its combined cap
    (network/mod.rs:280-289) under [mut]? *)
let legacy_peer_gate_on mut =
  match mut with
  | Pristine | No_serving_guard | No_pre_read_sync_shed -> true
  | No_legacy_per_peer_cap -> false

(** Does [begin_serving_legacy] still charge the serve to its peer
    (network/mod.rs:330) under [mut]? *)
let handoff_charges mut =
  match mut with
  | Pristine | No_legacy_per_peer_cap | No_pre_read_sync_shed -> true
  | No_serving_guard -> false

(** Does the sync shed still happen BEFORE the request-frame read
    (network/mod.rs:704-722 preceding :728-739) under [mut]? *)
let shed_before_read mut =
  match mut with
  | Pristine | No_legacy_per_peer_cap | No_serving_guard -> true
  | No_pre_read_sync_shed -> false

(** [try_admit_legacy]'s verdict under [mut]: a global permit must be free
    (network/mod.rs:271-273) and, unless the gate is deleted, the flooder's
    combined count must be under the cap (network/mod.rs:280). *)
let legacy_admits mut s =
  held s < pool_cap
  && (Bool.not (legacy_peer_gate_on mut) || charged_v1 s < per_peer_cap)

(** [try_admit_sync]'s verdict (network/mod.rs:235, :239-243). No mutation in
    this family touches it, which is exactly the sibling-path argument for
    {!No_legacy_per_peer_cap}. *)
let sync_admits s = held s < pool_cap && charged_v2 s < per_peer_cap

(** The transition relation under a mutation.

    Two states are indivisible, and both for the same reason - the code they
    abstract is a straight-line region with nothing awaited inside it.

    - From {!At_open} the ONLY move is [try_admit_sync]'s verdict:
      [process_inbound_sync_stream] calls it synchronously before spawning
      anything (network/mod.rs:687-693) and it holds [pending],
      [active_legacy] and [sync_peers] together (:236-238), which every
      admission and every RAII release also take.
    - From {!At_shed} / {!At_shed_read} the ONLY move is the requester
      consuming the verdict. The shed arm (network/mod.rs:704-722) writes one
      [Deny(AtCapacity)] frame, closes and returns [Ok(())]; the requester's
      very next act is to classify that frame (handle.rs:414-453). So these two
      constructors NAME THE DENIAL INSTANT, and every statement about them is a
      statement about that instant. Letting the responder's counters churn here
      instead would only add states in which the victim was denied and capacity
      has SINCE been freed - a fact about staleness, not about the shed - and
      would make "denied" mean "denied at some earlier time". {!Formula} has no
      past-time operator, so naming the instant with a frozen state is the only
      faithful encoding available; the alternative is not a weaker true
      statement but a different (and uninteresting) one about how long a denial
      stays informative.

    {!At_served} is deliberately NOT frozen: an admitted exchange streams
    batches through [process_sync_batches_stream] and is long-lived, so the
    responder's other peers plainly act during it. Everywhere else the
    responder's two peers act independently, one event per step. *)
let next_with mut s =
  match s.att with
  | At_open ->
      if sync_admits s then [ { s with sync = s.sync + 1; att = At_served } ]
      else if shed_before_read mut then [ { s with att = At_shed } ]
      else [ { s with att = At_shed_read } ]
  | At_shed | At_shed_read -> [ { s with att = At_idle } ]
  | At_idle | At_served ->
      let legacy_admit =
        if legacy_admits mut s then [ { s with pend = s.pend + 1 } ] else []
      in
      let legacy_handoff =
        if s.pend > 0 then
          if handoff_charges mut then
            [ { s with pend = s.pend - 1; serv = s.serv + 1 } ]
          else [ { s with pend = s.pend - 1; ghost = s.ghost + 1 } ]
        else []
      in
      let legacy_finish = if s.serv > 0 then [ { s with serv = s.serv - 1 } ] else [] in
      let ghost_finish = if s.ghost > 0 then [ { s with ghost = s.ghost - 1 } ] else [] in
      let legacy_expire = if s.pend > 0 then [ { s with pend = s.pend - 1 } ] else [] in
      let sync_open =
        match s.att with
        | At_idle -> [ { s with att = At_open } ]
        | At_open | At_shed | At_shed_read | At_served -> []
      in
      let sync_clear =
        match s.att with
        | At_shed | At_shed_read | At_served -> [ { s with att = At_idle } ]
        | At_idle | At_open -> []
      in
      let sync_release =
        match s.att with
        | At_idle -> if s.sync > 0 then [ { s with sync = s.sync - 1 } ] else []
        | At_open | At_shed | At_shed_read | At_served -> []
      in
      List.concat
        [
          legacy_admit;
          legacy_handoff;
          legacy_finish;
          ghost_finish;
          legacy_expire;
          sync_open;
          sync_clear;
          sync_release;
        ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The single initial state: an idle responder with empty maps and a full
    semaphore. *)
let initial = { pend = 0; serv = 0; ghost = 0; sync = 0; att = At_idle }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | V1_over_peer_cap
      (** the flooder holds strictly more than [MAX_PENDING_REQUESTS_PER_PEER]
          of the responder's stream slots, counting every global permit it
          holds however R charges it *)
  | V2_over_peer_cap
      (** the victim holds strictly more than [MAX_PENDING_REQUESTS_PER_PEER]
          sync exchanges *)
  | V1_uncounted_serve
      (** the flooder holds a global permit for a serving legacy stream that
          [peer_in_flight] (network/mod.rs:206-216) does not charge to it: the
          count has vanished across the pending -> serving handoff *)
  | V1_serving_at_cap
      (** the flooder is serving [MAX_PENDING_REQUESTS_PER_PEER] legacy
          streams, charged or not *)
  | V1_serving_any  (** the flooder is serving at least one legacy stream *)
  | V1_pending_any
      (** the flooder holds at least one entry in [pending_batch_requests] *)
  | V1_holds_any
      (** the flooder holds at least one of the responder's global permits, on
          any of the three counters *)
  | Pool_exhausted
      (** [batch_stream_semaphore] has no permit left: [try_acquire_owned]
          (network/mod.rs:235, :271) would fail *)
  | V2_attempt_open
      (** the victim's stream is open and [try_admit_sync] has been entered *)
  | V2_idle_at_r
      (** the victim holds none of the responder's stream slots *)
  | V2_at_own_cap
      (** the victim already holds [MAX_PENDING_REQUESTS_PER_PEER] exchanges,
          so its OWN cap is a possible cause of a denial *)
  | V2_denied
      (** the responder answered the victim's current stream with
          [SyncFrame::Deny(DenyReason::AtCapacity)] *)
  | V2_served
      (** the responder admitted the victim's current stream and is serving it *)
  | Resp_read_v2_request
      (** the responder decoded the opening [SyncFrame::Req] frame of the
          victim's current stream (network/mod.rs:728-739) and therefore holds
          the batch digests that stream asked for *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | V1_over_peer_cap -> held_v1 s > per_peer_cap
  | V2_over_peer_cap -> s.sync > per_peer_cap
  | V1_uncounted_serve -> s.ghost > 0
  | V1_serving_at_cap -> s.serv + s.ghost >= per_peer_cap
  | V1_serving_any -> s.serv + s.ghost > 0
  | V1_pending_any -> s.pend > 0
  | V1_holds_any -> held_v1 s > 0
  | Pool_exhausted -> held s >= pool_cap
  | V2_attempt_open -> (
      match s.att with
      | At_open -> true
      | At_idle | At_shed | At_shed_read | At_served -> false)
  | V2_idle_at_r -> Int.equal s.sync 0
  | V2_at_own_cap -> s.sync >= per_peer_cap
  | V2_denied -> att_denied s.att
  | V2_served -> (
      match s.att with
      | At_served -> true
      | At_idle | At_open | At_shed | At_shed_read -> false)
  | Resp_read_v2_request -> att_request_read s.att

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | V1_over_peer_cap -> "over_cap(V1)"
  | V2_over_peer_cap -> "over_cap(V2)"
  | V1_uncounted_serve -> "uncounted_serve(V1)"
  | V1_serving_at_cap -> "serving_at_cap(V1)"
  | V1_serving_any -> "serving(V1)>0"
  | V1_pending_any -> "pending(V1)>0"
  | V1_holds_any -> "in_flight(V1)>0"
  | Pool_exhausted -> "pool_exhausted(R)"
  | V2_attempt_open -> "stream_open(V2)"
  | V2_idle_at_r -> "in_flight(V2)=0"
  | V2_at_own_cap -> "at_own_cap(V2)"
  | V2_denied -> "denied(V2)"
  | V2_served -> "served(V2)"
  | Resp_read_v2_request -> "read_request(R,V2)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} by
    test/t_worker_stream_quota_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation. *)
let spec_of mut = { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
