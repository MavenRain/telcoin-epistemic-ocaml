(** Finite interpreted system for the STREAM_INBOUND_QUOTA family: the libp2p
    stream behaviour's per-peer INBOUND stream rate window, the two silent
    drop paths an accepted-at-the-transport stream can still fall into, and
    what each side can and cannot infer from them. File citations refer to
    Telcoin-Association/telcoin-network at the working tree of git HEAD
    0c59c15b; every one of them was opened in this checkout.

    THE MODELLED MECHANISM. A responder [R] meters inbound stream opens per
    opening peer and then forwards what survives to the application.

    - THE CONSTANTS. [const INBOUND_RATE_WINDOW: Duration =
      Duration::from_secs(1);] and [const MAX_INBOUND_PER_WINDOW: usize = 256;]
      (crates/network-libp2p/src/stream/behavior.rs:41-45). One uniform bound
      for every peer: there is no per-identity tier and no committee exemption
      on this path.
    - THE METER. [inbound_rate_limited] (behavior.rs:280-290) is verbatim
      [let window = self.inbound.entry(peer).or_insert(InboundWindow { count: 0,
      started: now });] (:283) then [if now.duration_since(window.started) >=
      INBOUND_RATE_WINDOW { window.count = 0; window.started = now; }] (:284-287)
      then [window.count += 1; window.count > MAX_INBOUND_PER_WINDOW]
      (:288-289). Three facts matter and all three are modelled: the map is
      keyed BY PEER ([inbound: HashMap<PeerId, InboundWindow>], :132-133), the
      window is TUMBLING rather than sliding (:284-287), and [started] is [R]'s
      own [Instant], so no opener can see where the window boundary lies.
    - THE RATE GATE. [on_connection_handler_event] (behavior.rs:340-362): [if
      self.inbound_rate_limited(peer_id) { // drop the stream; report for
      scoring ... StreamFailure::InboundRateLimited } else { ...
      StreamEvent::InboundStream { peer: peer_id, kind, stream } }] (:346-357).
      The rejected branch DROPS the [Stream] value; it writes nothing.
    - THE IDENTITY GATE. [process_stream_event] (consensus.rs:1654-1696): [if
      let Some(bls) = self.swarm.behaviour().peer_manager.peer_to_bls(&peer) {
      ... try_send(NetworkEvent::InboundStream { peer: bls, kind, stream }) ... }
      else { warn!(target: "network", ?peer, "received inbound stream from
      unknown peer"); }] (:1665-1675). The [else] arm also drops the [Stream]
      and writes nothing. [peer_to_bls] is peers/manager.rs:934-936 delegating
      to [bls_for_peer] (peers/all_peers.rs:827-829), a lookup in
      [bls_by_peer_id].
    - THE WINDOW RESET ON DISCONNECT. [on_disconnected] (behavior.rs:256-263):
      [self.connected.remove(&peer); self.inbound.remove(&peer);] (:257-258),
      reached from [FromSwarm::ConnectionClosed { peer_id,
      remaining_established: 0, .. }] (behavior.rs:323-330). The peer's whole
      window entry is deleted, so the quota is scoped to a CONNECTION EPISODE
      and not to the identity.
    - WHAT THE OPENER CAN SEE. Nothing distinguishes the two drops on the wire:
      neither path writes a frame, and no scoring reaction follows either -
      [StreamFailure::InboundRateLimited] maps to [Some(Penalty::Medium)]
      (stream/upgrade.rs:139-161, arm at :159-160) but the consumer only logs,
      "Classified for scoring but reported metrics-only until telemetry confirms
      the classification does not fire on healthy peers (see #739)"
      (consensus.rs:1677-1693). By contrast a stream that IS delivered reaches
      the application, and the application does answer on the wire: the primary
      writes [SyncFrame::Deny(DenyReason::AtCapacity)] when it sheds
      (consensus/primary/src/network/mod.rs:1892-1909) and [SyncFrame::Ack] when
      it serves (mod.rs:1984). That asymmetry - silence for both network-layer
      drops, a frame once the application has the stream - is what the third
      statement is about.

    COMPONENTS. Five, all finite.

    - {!meter} - [R]'s [inbound] entry for the opening peer W: how many of W's
      opens the window at behavior.rs:283 currently carries.
      [MAX_INBOUND_PER_WINDOW] is abstracted from 256 to 1, the smallest bound
      that still separates "spent its allowance" from "over its allowance", so
      the three values are exactly [count = 0], [count = MAX] (admitted, the
      [>] at :289 is false) and [count > MAX] (rejected). This is a bound
      abstraction only: it does not change WHICH peer the [entry(peer)] call
      charges, which is the whole content of the first statement.
    - {!own} - W's OWN cumulative opens against R, measured against the same
      abstracted bound. This is W's private truth, not R's bookkeeping, and the
      gap between the two is the second statement.
    - {!rst} - which of the two meter resets has happened: the tumbling roll
      (behavior.rs:284-287) or the disconnect/redial (behavior.rs:258). See the
      scope note below on why at most one of them fires per run.
    - {!res} - whether [peer_to_bls] resolves W (consensus.rs:1665). It starts
      [Unresolved]: the repo documents the race verbatim, "A peer is `Connected`
      before its `NodeRecord` resolves its BLS identity, so a live mesh neighbor
      can relay a message before `peer_to_bls` can resolve it"
      (consensus.rs:1007-1016).
    - {!att} - the fate of W's most recent inbound stream, and hence what W
      observes: nothing yet, a silent close charged to the rate gate, a silent
      close charged to the identity gate, or an answered exchange.

    SCOPE CHOICES, STATED SO THEY ARE AUDITABLE.

    - ONE RESET PER RUN. {!rst} carries [R_none], [R_rolled] or
      [R_reconnected], so a run sees at most one meter reset. Both statements
      that use a reset are about a SINGLE reset event, and the restriction is
      conservative in the direction that matters: a larger reset history only
      enlarges the opener's indistinguishability class (making S3's ignorance
      conjuncts easier), while S3's positive [K] operand is true at EVERY
      reachable answered state and so is insensitive to class size.
    - THE NEIGHBOUR IS A TRANSITION, NOT A COMPONENT. A second opening peer
      floods R through {!neighbour_step}. Under the pristine keying that event
      touches nothing this family observes - behavior.rs:283 keys the window by
      [peer], so another identity's opens cannot move W's entry - so it
      contributes no successor. Under {!No_per_peer_keying} the very same event
      bumps the one shared window. Modelling the neighbour as an event rather
      than as state is what keeps the neighbour's own counter out of the
      product without weakening anything: no statement here mentions the
      neighbour's own rejection.
    - THE DISCONNECT AND THE REDIAL ARE ONE STEP. behaviour.rs:323-330 fires
      [on_disconnected] on [remaining_established: 0] and a later
      [ConnectionEstablished] re-adds the peer; nothing this family observes
      happens in between, so the pair is one atomic {!reconnect_step}.
    - NO WALL CLOCK. The one-second window is the {!roll_step} event, not a
      clock.

    REPAIR AND SIBLING PATHS, MODELLED OR EXPLICITLY DISCLOSED (so that no
    statement is true only because the model left something out).

    - THE TUMBLING ROLL IS MODELLED. behavior.rs:284-287 resets [count] to 0
      once a second, which is a second, smaller way for the meter to fall
      behind the opener's true rate. It is in the model as {!roll_step}, it is
      the hidden variable S3's ignorance actually rests on, and S2's evasion
      witness explicitly excludes it (the [Window_rolled] conjunct) precisely so
      that the disconnect deletion - and not the roll - is what pins S2.
    - THE SCORING PATH IS MODELLED AS INERT, WHICH IS WHAT IT IS. The penalty
      classification exists (upgrade.rs:159-160) but is not enforced
      (consensus.rs:1677-1693), so there is no ban or disconnect that a flooded
      shared window would trigger. Modelling an enforced penalty would be
      modelling code that is not there.
    - QUIC's [max_concurrent_stream_limit] (config/network.rs:289-291, default
      10_000 at :305, applied at consensus.rs:451-452) bounds CONCURRENT streams
      per connection, not the open RATE, and it does not separate identities on
      separate connections, so it is not a sibling of the per-peer keying.
    - THE APPLICATION LAYER DOES NOT RE-CHECK THE IDENTITY. The consumers of
      [NetworkEvent::InboundStream] are primary/src/network/mod.rs:1507-1510 and
      worker/src/network/mod.rs:466, and both dispatch straight on
      [StreamKind] with no membership test; the only [Deny] writer on the
      primary's inbound sync path is the capacity shed at mod.rs:1892-1909,
      which WRITES A FRAME and runs only after delivery. So deleting the guard
      at consensus.rs:1665 is not silently repaired one layer up.
    - IDENTITY RESOLUTION IS TREATED AS MONOTONE, AND THAT WAS CHECKED. The
      only remover of a [bls_by_peer_id] entry is [evict]
      (all_peers.rs:126-134); its callers are the two prune paths
      [prune_banned_peers] (:1051-1057) and [prune_disconnected_peers]
      (:1077-1080), which select only records in [Banned] or [Disconnected]
      status, and the key-rotation paths at :202-205 and :225 which re-insert
      immediately at :208 and :254. A peer that is connected and opening
      streams is therefore never de-resolved, which is what {!res} being
      monotone encodes.
    - NOTHING BYPASSES THE RATE GATE. [self.inbound] is touched at exactly three
      sites - the removal at behavior.rs:258, the [entry] at :283 and the gate
      call at :348 - and [StreamEvent::InboundStream] has exactly one producer,
      behavior.rs:355, inside the [else] of that gate. There is no second
      inbound route for the model to be missing.
    - THREE FURTHER SILENT-DROP CAUSES ARE OMITTED, ALL DISCLOSED AND ALL
      CONSERVATIVE IN THE SAME DIRECTION. (1) [push_event] sheds when the
      behaviour's queue is saturated - [if self.events.len() < MAX_EVENTS {
      self.events.push_back(event); }] (behavior.rs:215-218, [MAX_EVENTS = 1024]
      at :31-32), and the in-tree test [push_event_sheds_when_full]
      (behavior.rs:594-605) shows the shed is live - so an admitted inbound
      stream can be dropped with the event. (2) The forward at
      consensus.rs:1666-1672 is a [try_send] whose [Err] arm also drops the
      stream ("During epoch change the event_stream reciever can be closed", the
      same comment pattern at :1045 and :1160). (3) A delivered stream whose
      opener never sends a request frame is dropped on the responder's read
      timeout (primary/src/network/mod.rs:1912-1920) without a frame; that one
      is under the OPENER's control, so it changes nothing an opener could not
      already rule out. Every one of the three ADDS a member to the opener's
      silent class, which makes S3's [~K] conjuncts HARDER to satisfy, never
      easier - so S3 is not true by these omissions. What they do mean is that
      in the real code {!No_identity_guard} would not collapse the silent class
      all the way down to one cause, which is why S3's robust half is its
      answered-implies-resolved conjunct, whose flip does not depend on the
      class collapsing at all.

    ROLE MAPPING (a knowledge agent must have a real, non-constant view; a
    blank-view party may never appear under K).

    - V1 is the OPENING PEER W and the family's opener-side knowledge agent. It
      SEES its own cumulative opens, whether it dropped and redialled its own
      connection, and what came back on its own stream - and the last of those
      is exactly the three-valued {!observation}, because a rate-gate drop and
      an identity-gate drop are byte-identical on the wire (both are a bare
      [Stream] drop, behavior.rs:348-353 and consensus.rs:1673-1675). It does
      NOT see R's window count, R's window phase, or R's resolution state.
    - V0 is the METERING RESPONDER R and the family's responder-side knowledge
      agent. It SEES its own [inbound] entry, its own window phase, its own
      [peer_to_bls] result and its own disposition of the stream - everything
      except {!own}, W's true cumulative rate, which after
      [self.inbound.remove(&peer)] (behavior.rs:258) is simply gone from R's
      state. That single omission is S2's ignorance conjunct.
    - The flooding neighbour is the {!neighbour_step} event and carries no
      modelled state, so it is not a knowledge agent.
    - V2..V9 take no part; they hold the constant blank view {!View_idle} and
      never appear under K. *)

(** R's [inbound] window count for one peer (behavior.rs:283-289), with
    [MAX_INBOUND_PER_WINDOW] abstracted from 256 to 1. *)
type count =
  | M_zero  (** [window.count = 0]: no open charged in the current window *)
  | M_at_cap
      (** [window.count = MAX_INBOUND_PER_WINDOW]: the allowance is spent but
          the [>] test at behavior.rs:289 is still false, so the stream is
          admitted *)
  | M_over
      (** [window.count > MAX_INBOUND_PER_WINDOW]: behavior.rs:289 is true and
          behavior.rs:348 drops the stream *)

(** Total order index for {!count}. *)
let count_index = function M_zero -> 0 | M_at_cap -> 1 | M_over -> 2

(** Total order on {!count}. *)
let count_compare a b = Int.compare (count_index a) (count_index b)

(** [window.count += 1] (behavior.rs:288), saturating: once the count is past
    the bound every further open is past it too. *)
let count_bump = function
  | M_zero -> M_at_cap
  | M_at_cap -> M_over
  | M_over -> M_over

(** W's OWN cumulative inbound opens against R, against the same abstracted
    [MAX_INBOUND_PER_WINDOW]. This is the opener's private truth; R's {!count}
    is R's bookkeeping, and the two are not the same number. *)
type own =
  | Own_within  (** W has opened at most [MAX_INBOUND_PER_WINDOW] streams *)
  | Own_over  (** W has opened strictly more than [MAX_INBOUND_PER_WINDOW] *)

(** Total order index for {!own}. *)
let own_index = function Own_within -> 0 | Own_over -> 1

(** Total order on {!own}. *)
let own_compare a b = Int.compare (own_index a) (own_index b)

(** Which meter reset has fired. The two are different lines of the real code
    and, crucially, differ in visibility: R's clock rolling the window is
    invisible to the opener, while the opener's own redial is not. *)
type reset =
  | R_none  (** neither reset has fired yet *)
  | R_rolled
      (** the tumbling window crossed its boundary and [window.count] was set
          back to 0 (behavior.rs:284-287); [started] is R's own [Instant], so
          the opener cannot see this happen *)
  | R_reconnected
      (** W's last connection closed and W redialled, so [self.inbound
          .remove(&peer)] (behavior.rs:258) deleted the whole window entry *)

(** Total order index for {!reset}. *)
let reset_index = function R_none -> 0 | R_rolled -> 1 | R_reconnected -> 2

(** Total order on {!reset}. *)
let reset_compare a b = Int.compare (reset_index a) (reset_index b)

(** Whether [peer_manager.peer_to_bls(&peer)] resolves W
    (consensus.rs:1665, peers/manager.rs:934-936). *)
type resolution =
  | Unresolved
      (** [peer_to_bls] returns [None]: W is connected but its [NodeRecord] has
          not resolved yet, the race the repo documents at
          consensus.rs:1007-1016 *)
  | Resolved  (** [peer_to_bls] returns [Some(bls)] *)

(** Total order index for {!resolution}. *)
let resolution_index = function Unresolved -> 0 | Resolved -> 1

(** Total order on {!resolution}. *)
let resolution_compare a b =
  Int.compare (resolution_index a) (resolution_index b)

(** The fate of W's most recent inbound stream at R. *)
type attempt =
  | At_none  (** W has not opened an inbound stream yet *)
  | At_quota
      (** the rate gate dropped it: [if self.inbound_rate_limited(peer_id) {
          // drop the stream; report for scoring ... }]
          (behavior.rs:346-353). Nothing is written to the stream *)
  | At_unknown_peer
      (** the identity gate dropped it: [warn!(target: "network", ?peer,
          "received inbound stream from unknown peer")] (consensus.rs:1673-1675)
          with the [Stream] value dropped. Nothing is written to the stream *)
  | At_answered
      (** the stream reached the application (consensus.rs:1666-1670) and the
          application answered on the wire - [SyncFrame::Ack]
          (primary/src/network/mod.rs:1984) or
          [SyncFrame::Deny(DenyReason::AtCapacity)] (mod.rs:1892-1909) *)

(** Total order index for {!attempt}. *)
let attempt_index = function
  | At_none -> 0
  | At_quota -> 1
  | At_unknown_peer -> 2
  | At_answered -> 3

(** Total order on {!attempt}. *)
let attempt_compare a b = Int.compare (attempt_index a) (attempt_index b)

(** The joint global state: R's meter and its two reset histories, R's identity
    resolution, W's own rate, and the fate of W's current stream. *)
type state = {
  meter : count;  (** R's [inbound] entry for W (behavior.rs:283) *)
  own : own;  (** W's own cumulative opens *)
  rst : reset;  (** which meter reset has fired *)
  res : resolution;  (** R's [peer_to_bls] result for W *)
  att : attempt;  (** the fate of W's most recent stream *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = count_compare s1.meter s2.meter in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = own_compare s1.own s2.own in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = reset_compare s1.rst s2.rst in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = resolution_compare s1.res s2.res in
        if Bool.not (Int.equal c3 0) then c3
        else attempt_compare s1.att s2.att

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** What the opener observes on its own stream. The two silent drops collapse
    here on purpose: behavior.rs:348-353 and consensus.rs:1673-1675 both just
    drop the [Stream], neither writes a frame, and neither triggers an
    observable scoring reaction (consensus.rs:1677-1693). *)
type observation =
  | Obs_none  (** the opener has not opened a stream yet *)
  | Obs_silent  (** the stream closed with nothing ever written to it *)
  | Obs_answered  (** a frame came back on the stream *)

(** Total order index for {!observation}. *)
let observation_index = function
  | Obs_none -> 0
  | Obs_silent -> 1
  | Obs_answered -> 2

(** Total order on {!observation}. *)
let observation_compare a b =
  Int.compare (observation_index a) (observation_index b)

(** What the opener knows about its own connection: it dropped and redialled,
    or it did not. It emphatically does NOT include R's window phase. *)
type episode_seen =
  | Ep_original  (** W is still on the connection it first opened *)
  | Ep_redialled  (** W closed its last connection and redialled *)

(** Total order index for {!episode_seen}. *)
let episode_index = function Ep_original -> 0 | Ep_redialled -> 1

(** Total order on {!episode_seen}. *)
let episode_compare a b = Int.compare (episode_index a) (episode_index b)

(** A validator's local view.

    - [View_opener] is W (V1): its own cumulative opens, its own connection
      episode, and the wire observation. It does NOT carry {!count} (R's
      bookkeeping), does not distinguish [R_none] from [R_rolled] (R's window
      phase is R's own [Instant], behavior.rs:283), and does not carry
      {!resolution} (R's [bls_by_peer_id] lookup).
    - [View_responder] is R (V0): every field of the state EXCEPT {!own}, which
      is W's private rate and which [self.inbound.remove(&peer)]
      (behavior.rs:258) erases any trace of.
    - [View_idle] is the constant blank view of the non-agents. *)
type view =
  | View_opener of own * episode_seen * observation
  | View_responder of count * reset * resolution * attempt
  | View_idle  (** the constant blank view of V2..V9 *)

(** Total order on the opener's view triple. *)
let opener_compare (o1, e1, b1) (o2, e2, b2) =
  let c = own_compare o1 o2 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = episode_compare e1 e2 in
    if Bool.not (Int.equal c1 0) then c1 else observation_compare b1 b2

(** Total order on the responder's view quadruple. *)
let responder_compare (m1, r1, s1, t1) (m2, r2, s2, t2) =
  let c = count_compare m1 m2 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = reset_compare r1 r2 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = resolution_compare s1 s2 in
      if Bool.not (Int.equal c2 0) then c2 else attempt_compare t1 t2

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_opener (o1, e1, b1), View_opener (o2, e2, b2) ->
      opener_compare (o1, e1, b1) (o2, e2, b2)
  | View_opener _, (View_responder _ | View_idle) -> -1
  | View_responder _, View_opener _ -> 1
  | View_responder (m1, r1, s1, t1), View_responder (m2, r2, s2, t2) ->
      responder_compare (m1, r1, s1, t1) (m2, r2, s2, t2)
  | View_responder _, View_idle -> -1
  | View_idle, (View_opener _ | View_responder _) -> 1
  | View_idle, View_idle -> 0

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** The opener's wire observation of its own stream: the two silent drops are
    the same three bytes of nothing. *)
let observation_of att =
  match att with
  | At_none -> Obs_none
  | At_quota | At_unknown_peer -> Obs_silent
  | At_answered -> Obs_answered

(** The opener sees its own redial but not R's window roll. *)
let episode_seen_of rst =
  match rst with
  | R_none | R_rolled -> Ep_original
  | R_reconnected -> Ep_redialled

(** View projection. V1 is the opening peer W and V0 is the metering responder
    R; both are knowledge agents with genuinely partial views. V2..V9 are idle
    non-agents with the constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V1 -> View_opener (s.own, episode_seen_of s.rst, observation_of s.att)
  | Validator.V0 -> View_responder (s.meter, s.rst, s.res, s.att)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as written at HEAD 0c59c15b *)
  | No_per_peer_keying
      (** delete the per-peer keying of the rate window: replace
          [self.inbound.entry(peer).or_insert(InboundWindow { count: 0, started:
          now })] (behavior.rs:283) with one behaviour-wide [InboundWindow], so
          the neighbour's opens charge the SAME counter as W's. The effect in
          the model is that {!neighbour_step}, which is a no-op under the
          pristine keying, now bumps {!meter}; a first-ever open by W can then
          be rejected. NO SIBLING REPAIRS IT: the classification
          [StreamFailure::InboundRateLimited -> Some(Penalty::Medium)]
          (upgrade.rs:159-160) is reported metrics-only and never enforced
          (consensus.rs:1677-1693), so no ban evicts the flooder; QUIC's
          [max_concurrent_stream_limit] (consensus.rs:451-452,
          config/network.rs:289-291) bounds concurrency per connection and does
          not separate identities on separate connections; and the peer
          manager's excess-peer logic governs connection counts, not stream
          rate. The [entry(peer)] key is the only thing separating the
          identities. *)
  | No_window_reset_on_disconnect
      (** delete [self.inbound.remove(&peer);] (behavior.rs:258) from
          [on_disconnected], so a redial no longer starts the peer from a zero
          counter. The effect in the model is that {!reconnect_step} leaves
          {!meter} untouched. NO SIBLING REPAIRS IT WITHIN THE STATEMENT'S
          SCOPE: the only other reset is the tumbling roll (behavior.rs:284-287),
          and S2's witness formula excludes it explicitly, so the roll cannot
          stand in for the deleted line; and the peer manager's
          excess-reconnection handling covers peers WE shed, not a peer that
          closes its own connection, so it supplies no reset either. *)
  | No_identity_guard
      (** delete the [if let Some(bls) = self.swarm.behaviour().peer_manager
          .peer_to_bls(&peer)] gate on inbound stream delivery
          (consensus.rs:1665) and forward the stream regardless. The effect in
          the model is that an open that clears the rate gate is answered even
          while {!res} is [Unresolved]. NO SIBLING REPAIRS IT: the consumers of
          [NetworkEvent::InboundStream] dispatch straight on [StreamKind]
          (primary/src/network/mod.rs:1507-1510, worker/src/network/mod.rs:466)
          with no membership test, and the only [Deny] writer on that path is
          the capacity shed at primary/src/network/mod.rs:1892-1909, which
          writes a FRAME and runs only after delivery - so nothing one layer up
          re-imposes a silent drop for an unresolved identity. *)

(** [peer_to_bls] starts returning [Some] for W: the [NodeRecord] resolution
    that consensus.rs:1007-1016 documents as lagging the connection. Monotone,
    per the [evict] analysis in the header. *)
let resolve_step s =
  match s.res with
  | Unresolved -> [ { s with res = Resolved } ]
  | Resolved -> []

(** The tumbling window crosses its boundary: [if now.duration_since(window
    .started) >= INBOUND_RATE_WINDOW { window.count = 0; window.started = now; }]
    (behavior.rs:284-287). Invisible to the opener. *)
let roll_step s =
  match s.rst with
  | R_none -> [ { s with rst = R_rolled; meter = M_zero } ]
  | R_rolled | R_reconnected -> []

(** W's last connection closes and W redials: [on_disconnected] runs
    [self.inbound.remove(&peer);] (behavior.rs:258) under every model except
    the one that deletes exactly that line. *)
let reconnect_step mut s =
  match s.rst with
  | R_none ->
      let cleared =
        match mut with
        | Pristine | No_per_peer_keying | No_identity_guard -> M_zero
        | No_window_reset_on_disconnect -> s.meter
      in
      [ { s with rst = R_reconnected; meter = cleared } ]
  | R_rolled | R_reconnected -> []

(** W opens one inbound stream. The rate gate runs FIRST (behavior.rs:348) and
    the identity gate only on what it admits (consensus.rs:1665), which is the
    order this successor computes. *)
let open_step mut s =
  let meter' = count_bump s.meter in
  let own' =
    match s.att with
    | At_none -> Own_within
    | At_quota | At_unknown_peer | At_answered -> Own_over
  in
  let att' =
    match meter' with
    | M_over -> At_quota
    | M_zero | M_at_cap -> (
        match (s.res, mut) with
        | Resolved, (Pristine | No_per_peer_keying | No_window_reset_on_disconnect | No_identity_guard)
          ->
            At_answered
        | Unresolved, No_identity_guard -> At_answered
        | Unresolved, (Pristine | No_per_peer_keying | No_window_reset_on_disconnect)
          ->
            At_unknown_peer)
  in
  [ { s with meter = meter'; own = own'; att = att' } ]

(** A neighbouring peer opens an inbound stream at R. Under the pristine keying
    this charges the NEIGHBOUR's own [inbound] entry (behavior.rs:283), which
    this family does not observe, so it contributes no successor; under
    {!No_per_peer_keying} there is one shared window and the same event bumps
    W's meter. *)
let neighbour_step mut s =
  match mut with
  | No_per_peer_keying -> [ { s with meter = count_bump s.meter } ]
  | Pristine | No_window_reset_on_disconnect | No_identity_guard -> []

(** The transition relation: one event per step. *)
let next_with mut s =
  resolve_step s @ roll_step s @ reconnect_step mut s @ open_step mut s
  @ neighbour_step mut s

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: W is connected with a fresh window, has opened nothing,
    and its [NodeRecord] has not resolved yet (consensus.rs:1007-1016). *)
let initial =
  { meter = M_zero; own = Own_within; rst = R_none; res = Unresolved; att = At_none }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Meter_full
      (** R's [inbound] entry for W carries more than [MAX_INBOUND_PER_WINDOW]
          opens, so behavior.rs:289 rejects W's next stream *)
  | Rejected
      (** R dropped W's most recent stream at the rate gate
          (behavior.rs:346-353) *)
  | Own_over_cap
      (** W itself opened strictly more than [MAX_INBOUND_PER_WINDOW] inbound
          streams at R *)
  | Silent_drop
      (** W's most recent stream was closed with nothing ever written to it -
          either drop path *)
  | Identity_drop
      (** R dropped W's most recent stream because [peer_to_bls] returned
          [None] (consensus.rs:1673-1675) *)
  | Answered
      (** the application answered on W's most recent stream
          (primary/src/network/mod.rs:1892-1909, :1984) *)
  | Identity_resolved
      (** [peer_to_bls(&peer)] resolves W (consensus.rs:1665) *)
  | Window_rolled
      (** R's tumbling window crossed its boundary and zeroed the count
          (behavior.rs:284-287) *)
  | Reconnected
      (** W closed its last connection and redialled, so behavior.rs:258
          deleted its window entry *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Meter_full -> (
      match s.meter with M_over -> true | M_zero | M_at_cap -> false)
  | Rejected -> (
      match s.att with
      | At_quota -> true
      | At_none | At_unknown_peer | At_answered -> false)
  | Own_over_cap -> (
      match s.own with Own_over -> true | Own_within -> false)
  | Silent_drop -> (
      match s.att with
      | At_quota | At_unknown_peer -> true
      | At_none | At_answered -> false)
  | Identity_drop -> (
      match s.att with
      | At_unknown_peer -> true
      | At_none | At_quota | At_answered -> false)
  | Answered -> (
      match s.att with
      | At_answered -> true
      | At_none | At_quota | At_unknown_peer -> false)
  | Identity_resolved -> (
      match s.res with Resolved -> true | Unresolved -> false)
  | Window_rolled -> (
      match s.rst with R_rolled -> true | R_none | R_reconnected -> false)
  | Reconnected -> (
      match s.rst with R_reconnected -> true | R_none | R_rolled -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Meter_full -> "window_count(R,W) > MAX"
  | Rejected -> "rate_limited(R,W)"
  | Own_over_cap -> "opened(W,R) > MAX"
  | Silent_drop -> "silently_dropped(R,W)"
  | Identity_drop -> "unknown_peer_drop(R,W)"
  | Answered -> "answered(R,W)"
  | Identity_resolved -> "peer_to_bls(W) = Some"
  | Window_rolled -> "window_rolled(R,W)"
  | Reconnected -> "redialled(W)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} by
    test/t_stream_inbound_quota_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation. *)
let spec_of mut = { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
