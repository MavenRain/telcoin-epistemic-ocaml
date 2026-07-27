(** Finite interpreted system for the EXEX_FANOUT family: the ExEx manager's
    bounded, non-blocking fan-out pipeline, abstracted from
    [crates/exex/src/manager.rs] of Telcoin-Association/telcoin-network. All
    file citations refer to that repository at the checkout this model was
    written against.

    The modeled mechanism. The manager is ONE async task running a single
    [try_fold] over one merged stream (manager.rs:209-220); each fold iteration
    is a synchronous [Router::handle] dispatch (manager.rs:254-283) that ends in
    at most two [fan_out] passes, and [fan_out] is a plain synchronous
    [for handle in &mut self.exexes { handle.send(notification) }]
    (manager.rs:286-290). Each registered ExEx is a SEPARATELY spawned consumer
    task with its own bounded [mpsc] channel
    (crates/node/src/manager/node.rs:927-960), draining it through
    [TnExExContext::next_notification] (context.rs:117-124). That split - one
    router task, N independent consumer tasks - is load-bearing for the fairness
    statement and is the one place the mining card was wrong.

    Components:
    - [phase]: the global scheduler, a cycle of ONE OR TWO manager fold
      iterations per live-consumer poll: [Ph_fan_a] -> ([Ph_fan_b] |
      [Ph_poll]), [Ph_fan_b] -> [Ph_poll], [Ph_poll] -> [Ph_fan_a]. The router
      and each ExEx are separately spawned tasks
      (crates/node/src/manager/node.rs:927-960), so how many router iterations
      land between two consumer polls is the tokio scheduler's choice; the model
      leaves it nondeterministic. Both regimes are load-bearing: the two-fan
      branch is the minimum ratio at which a downstream drop can occur at all on
      a capacity-1 channel, and the one-fan branch is what produces the states in
      which the channel is empty with NO outstanding drop - the states in which a
      canonical gap is detectable and the [canon_gap] marker is the only thing
      standing between a skip and a silent hole. Every branch still reaches
      [Ph_poll] within two steps, so the consumer's eventual drain remains a
      structural property of the graph rather than an unmodelled fairness
      assumption.
    - [sib]: the stalled sibling ExEx's capacity-1 channel. It fills on the
      first fan-out and NEVER drains - the "exex0 never reads its channel"
      scenario. It is first in the [exexes] vector, so under a blocking send it
      is what parks the router before the live ExEx is ever reached.
    - [chan]: the live ExEx's capacity-1 bounded channel, holding at most one
      item: a [Lagged] marker or a payload
      ([CertificateAccepted] / [ConsensusOutput] / [ChainExecuted]).
    - [dropped]: the real per-handle [ExExHandle::dropped] counter for the live
      ExEx (manager.rs:45-49), saturated to a boolean because [missed] is
      deliberately "a best-effort magnitude, not a single unit"
      (notification.rs:131-136).
    - [tip]: the real [Router::last_canon_tip] (manager.rs:126-129, :248-252),
      abstracted to "no baseline yet" / "a baseline exists". It is [None] until
      the first canonical commit (manager.rs:152) and [canon_gap] can report a
      discontinuity only against an existing baseline (manager.rs:449-452,
      pinned by the crate's own "First commit: no baseline -> no gap" unit test,
      manager.rs:528-534). Modelling it is what keeps the [canon_gap] gate
      deletion honest: at [Tip_none] deleting the block changes nothing at all.
    - four ghosts, in the state only so the statements can quantify over them:
      [owed] (a SIGNALABLE loss has occurred that no delivered marker has
      signalled yet),
      [loss] (sticky: some notification or commit was lost, either cause),
      [down] (sticky: the loss included a drop on the live ExEx's OWN channel,
      i.e. the manager-private [dropped] route), and [hole] (a monitor: a
      payload enqueue SUCCEEDED while a marker was owed).

    The four manager inputs, one per [Router::handle] dispatch:
    - [In_payload]: an accepted certificate or consensus output
      (manager.rs:258-273). One payload fan-out, and [last_canon_tip] is
      untouched - a certificate never establishes a canonical baseline.
    - [In_canon_commit]: a canonical commit contiguous with the baseline, or the
      very first commit. [canon_gap] returns [None] and still advances the tip
      monotonically (manager.rs:449-455), then the [ChainExecuted] payload is
      fanned out (manager.rs:354).
    - [In_commit_gap]: a canonical commit whose first block number skips
      (manager.rs:342-355). reth's canonical-state stream drops broadcast lag
      SILENTLY (manager.rs:126-129, :312-315), so this is the only place the
      hole can be noticed; WITH a baseline the marker is fanned out BEFORE the
      payload, and WITHOUT one ([Tip_none]) [canon_gap] takes its [_ => None]
      arm and the blocks are lost with no marker - a real, admitted hole in the
      pristine pipeline, which is exactly why [owed] is defined over signalable
      losses only (see below).
    - [In_cert_lag]: [BroadcastStreamRecvError::Lagged] on a consensus broadcast
      source, turned into a marker by [deliver_broadcast] (manager.rs:294-307).
      It is present deliberately as the SIBLING marker route to [In_commit_gap]
      so that {!No_canon_gap_marker} can be shown NOT to be repaired by it: the
      canonical stream is mapped with [canon_state_stream.map(RouterEvent::Canon)]
      (manager.rs:189-191) and [RouterEvent::Canon] carries a bare
      [CanonStateNotification] with no [Result] (manager.rs:235-236), so this
      arm can never fire for a canonical gap.

    Role mapping (a knowledge agent must be a {!Validator.t} with a real,
    non-constant view; a blank-view party may never appear under [K]):
    - V1 is THE knowledge agent: it is the live ExEx, and its view is exactly
      the head of its own [mpsc::Receiver] - nothing else. [TnExExContext]'s
      fields are private on purpose and the only notification surface is
      [next_notification] (context.rs:22-33, :117-124). V1 does NOT see
      [phase] (the manager's scheduler), [sib] (the sibling's occupancy),
      [dropped] ([ExExHandle::dropped] is manager-private, manager.rs:45-49,
      only [warn!]-logged at :67-72 and :91-96, and [TnExExManagerHandle]
      exposes nothing but [min_finished_height], manager.rs:398-412 - a handle
      the node discards), nor any ghost.
    - V0 is the stalled sibling ExEx: a modelled component with a real
      non-constant view of its own channel occupancy, but NEVER an argument to
      [K] - nothing is asserted about what the stalled ExEx knows.
    - V2 and V3 are idle non-agents: the constant blank view, never under [K].

    The critical omission from V1's view is [down]: [TnExExNotification::Lagged]
    is a single-field variant carrying only [missed], with no cause tag
    (notification.rs:141-144), and its own doc says the two causes - downstream
    per-ExEx drop and upstream source lag - surface "the same 'a gap exists'
    signal" (notification.rs:109-136). So the pure-upstream world and the
    pure-downstream world project to the SAME [View_live Chan_lagged].

    Deliberate, conservative simplifications, each argued not to make any
    statement true:
    - capacity 1, not the real 256 (manager.rs:29-34). With capacity 1 the
      pre-send marker itself fills the channel, so the payload that follows it
      always drops and [dropped] never returns to 0 as an end-of-step value;
      the real recovery is unit-tested at manager.rs:489-495. This only removes
      no-loss states, so it cannot make the safety invariant, the security
      [leads_to], or the fairness [Af] true.
    - the stalled sibling's own [dropped] counter is not modelled: it is
      unobservable from anywhere in the crate and no statement mentions it.
    - the [Closed] arms (manager.rs:80-83, :98-100) are not modelled. They are
      also non-blocking and only REMOVE deliveries, which is conservative for
      the two Ag statements and would weaken, not strengthen, the fairness one.
    - honest residual on {!No_canon_gap_marker}: a consumer can notice a height
      jump itself from the delivered [Chain]. That is consumer discretion
      outside the delivery pipeline; the statements are scoped to what the
      pipeline emits.
    - ADMITTED HOLE, modelled rather than hidden: a canonical skip that happens
      before the manager has ever delivered a commit is undetectable, because
      [canon_gap] has no baseline to compare against (manager.rs:449-452, unit
      test :528-534). The model takes that transition ([In_commit_gap] at
      [Tip_none]) and sets [loss] on it, but does NOT set [owed], because the
      pipeline is not contracted to signal a gap it provably cannot see. The
      safety statement is therefore a claim about signalable gaps, and the
      startup window is excluded explicitly instead of being modelled away. An
      earlier revision of this model let [In_commit_gap] emit a marker at
      startup; that made the pristine model stronger than the real manager and
      made {!No_canon_gap_marker}'s refutation land on the one transition where
      pristine and mutated Rust are byte-identical.

    Two environment assumptions are baked into the transition relation and must
    be read as part of every statement, not hidden behind them:
    - AT A FAN PHASE THE MANAGER ALWAYS HAS AN EVENT. There is no idle input:
      the merged stream (manager.rs:199-207) is never modelled as [Pending]. The
      real pipeline surfaces a pending [Lagged] only piggybacked on the NEXT
      [ExExHandle::send] (manager.rs:64-85), so on a node whose source streams
      went quiet forever an owed marker would never be delivered. The security
      statement's [AF] therefore holds under continuing chain activity, which is
      the operating regime of a running node, and NOT unconditionally.
    - AT A POLL PHASE THE LIVE CONSUMER ALWAYS TAKES ITS ITEM. The live ExEx's
      task is modelled as draining one slot every cycle
      (node.rs:927-960, context.rs:117-124). This is what the fairness
      statement's consumption conjunct asserts and checks; its whole purpose is
      to make the {!Blocking_send} refutation of the delivery conjunct mean
      STARVATION (the router stopped) rather than global stutter (everything
      stopped).

    Reachable-set size: 25 states pristine, and 37 / 53 / 21 under
    {!No_canon_gap_marker} / {!No_lagged_presend} / {!Blocking_send}. The
    pristine graph stays small because a capacity-1 channel saturates fast: on
    the two-fan branch the second send always finds the slot taken. The
    invariants that prune the 3 * 2 * 3 * 2 * 2 * 2 * 2 * 2 * 2 = 1152 product
    are [hole] false everywhere, [owed] -> [dropped] at every end-of-step state,
    [dropped] -> [down] -> [loss], and [sib] / [tip] absorbing at
    [Sib_full] / [Tip_some]. *)

(** The scheduler position: ONE OR TWO manager fold iterations
    (manager.rs:209-220, each one [Router::handle] + [fan_out], synchronous and
    atomic) per live-consumer poll (context.rs:117-124). The router and each
    ExEx are SEPARATELY spawned tasks (crates/node/src/manager/node.rs:927-960),
    so the number of router iterations between two consumer polls is chosen by
    the tokio scheduler, not by the manager; the model leaves that choice
    nondeterministic between one and two. *)
type phase =
  | Ph_fan_a  (** first manager fold iteration of the cycle *)
  | Ph_fan_b  (** second manager fold iteration of the cycle *)
  | Ph_poll
      (** the live ExEx's own spawned task takes one item off its channel *)

(** Total order index for {!phase}. *)
let phase_index = function Ph_fan_a -> 0 | Ph_fan_b -> 1 | Ph_poll -> 2

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The scheduler's successor positions. After the first fold iteration the
    consumer either gets the CPU ([Ph_poll], the keeping-up regime, in which the
    live channel is drained before the next fan and no drop occurs) or the
    router runs once more ([Ph_fan_b], the falling-behind regime, in which the
    second fan finds the capacity-1 channel full and drops). Bounding the run at
    two fans per poll is conservative: a longer router run only adds further
    drops, which can never make the safety invariant or either [Af] true. *)
let phase_next = function
  | Ph_fan_a -> [ Ph_fan_b; Ph_poll ]
  | Ph_fan_b -> [ Ph_poll ]
  | Ph_poll -> [ Ph_fan_a ]

(** The stalled sibling ExEx's capacity-1 channel. It fills on the first
    fan-out and never drains ([Sib_full] is absorbing). *)
type sib =
  | Sib_empty  (** the sibling has not been sent anything yet *)
  | Sib_full  (** the sibling's channel holds an item it will never take *)

(** Total order index for {!sib}. *)
let sib_index = function Sib_empty -> 0 | Sib_full -> 1

(** Total order on {!sib}. *)
let sib_compare a b = Int.compare (sib_index a) (sib_index b)

(** [true] iff the stalled sibling's channel is full. *)
let sib_is_full = function Sib_empty -> false | Sib_full -> true

(** One [ExExHandle::send] to the stalled sibling: it fills the channel once and
    every later send is a silent drop (manager.rs:87-97). The sibling's own
    [dropped] counter is unobservable and therefore not modelled. *)
let sib_send = function Sib_empty -> Sib_full | Sib_full -> Sib_full

(** The live ExEx's capacity-1 bounded notification channel. *)
type chan =
  | Chan_empty  (** nothing buffered for the live ExEx *)
  | Chan_lagged  (** the head is a [TnExExNotification::Lagged] marker *)
  | Chan_payload
      (** the head is a [CertificateAccepted] / [ConsensusOutput] /
          [ChainExecuted] payload *)

(** Total order index for {!chan}. *)
let chan_index = function Chan_empty -> 0 | Chan_lagged -> 1 | Chan_payload -> 2

(** Total order on {!chan}. *)
let chan_compare a b = Int.compare (chan_index a) (chan_index b)

(** [true] iff the live ExEx's channel has room for one item. *)
let chan_is_empty = function
  | Chan_empty -> true
  | Chan_lagged -> false
  | Chan_payload -> false

(** What a single [ExExHandle::send] carries (manager.rs:62-102). *)
type item =
  | It_lagged  (** a [TnExExNotification::Lagged] gap marker *)
  | It_payload  (** a live payload notification *)

(** The channel occupancy an {!item} produces when it lands. *)
let item_chan = function It_lagged -> Chan_lagged | It_payload -> Chan_payload

(** [true] iff the item is a live payload rather than a gap marker. *)
let item_is_payload = function It_lagged -> false | It_payload -> true

(** The manager's canonical baseline, [Router::last_canon_tip]
    (manager.rs:126-129, :251). It is [None] until the first canonical commit
    (manager.rs:152) and [canon_gap] can only report a discontinuity against a
    baseline that exists: its guard is
    [Some(prev) if first > prev.saturating_add(1) => .., _ => None]
    (manager.rs:449-452), pinned by the crate's own unit test
    "First commit: no baseline -> no gap" (manager.rs:528-534). It is
    manager-private: no [TnExExContext] surface exposes it, so it is not part of
    any validator's view. *)
type tip =
  | Tip_none  (** [last_canon_tip = None]: no canonical commit delivered yet *)
  | Tip_some
      (** [last_canon_tip = Some(_)]: a baseline exists, so a later skip is
          detectable *)

(** Total order index for {!tip}. *)
let tip_index = function Tip_none -> 0 | Tip_some -> 1

(** Total order on {!tip}. *)
let tip_compare a b = Int.compare (tip_index a) (tip_index b)

(** [true] iff the manager has a canonical baseline to compare against. *)
let tip_has_baseline = function Tip_none -> false | Tip_some -> true

(** One merged manager input, i.e. one [Router::handle] dispatch
    (manager.rs:254-283). *)
type input =
  | In_payload
      (** an accepted certificate or consensus output delivered through
          [deliver_broadcast] (manager.rs:258-273, :294-307): exactly one
          payload fan-out, and it does NOT touch [last_canon_tip] *)
  | In_canon_commit
      (** a canonical commit contiguous with the baseline, or the very first
          commit: [canon_gap] returns [None] and still advances [last_tip]
          monotonically (manager.rs:449-455), then the [ChainExecuted] payload
          is fanned out (manager.rs:354). One payload fan-out, and the baseline
          becomes [Tip_some] *)
  | In_commit_gap
      (** a canonical commit whose first block number skips. With a baseline
          ([Tip_some]) [canon_gap] fires, a [Lagged] marker is fanned out first
          and the [ChainExecuted] payload second (manager.rs:342-355). WITHOUT a
          baseline ([Tip_none]) the very same input is invisible - [canon_gap]'s
          [_ => None] arm (manager.rs:451) returns nothing, as the crate's own
          test pins (manager.rs:528-534) - so the blocks really are lost but no
          marker is or can be emitted *)
  | In_cert_lag
      (** [BroadcastStreamRecvError::Lagged] on a consensus broadcast source:
          [deliver_broadcast] fans out a marker in place of the item
          (manager.rs:294-307) *)

(** Every merged input the manager can dispatch, in a fixed order. *)
let inputs = [ In_payload; In_canon_commit; In_commit_gap; In_cert_lag ]

(** The joint global state. [phase], [sib], [chan], [dropped] and [tip] are the
    real machine; [owed], [loss], [down] and [hole] are ghosts the statements
    quantify over and no Rust value corresponds to them. *)
type state = {
  phase : phase;  (** the scheduler position *)
  sib : sib;  (** the stalled sibling's channel *)
  chan : chan;  (** the live ExEx's channel *)
  dropped : bool;  (** [ExExHandle::dropped > 0] for the live handle *)
  tip : tip;  (** [Router::last_canon_tip] (manager.rs:251) *)
  owed : bool;
      (** a SIGNALABLE loss has occurred that no delivered marker signalled: a
          downstream drop, a broadcast lag, or a canonical skip against an
          existing baseline. A canonical skip with NO baseline is deliberately
          excluded - see {!In_commit_gap} *)
  loss : bool;  (** sticky: some notification or commit was lost *)
  down : bool;  (** sticky: the loss included a drop on the live ExEx's channel *)
  hole : bool;  (** monitor: a payload enqueue succeeded while a marker was owed *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = sib_compare s1.sib s2.sib in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = chan_compare s1.chan s2.chan in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare s1.dropped s2.dropped in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = tip_compare s1.tip s2.tip in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Bool.compare s1.owed s2.owed in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = Bool.compare s1.loss s2.loss in
              if Bool.not (Int.equal c6 0) then c6
              else
                let c7 = Bool.compare s1.down s2.down in
                if Bool.not (Int.equal c7 0) then c7
                else Bool.compare s1.hole s2.hole

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. [View_live] is V1's - exactly the head of its own
    [mpsc::Receiver] (context.rs:26-33, :117-124), which is all an ExEx ever
    gets: not [phase], not [sib], not [dropped], not [tip]
    ([Router::last_canon_tip] is a private field of a struct the node never
    hands out, manager.rs:248-252), and no ghost. [View_stalled] is V0's own
    channel occupancy; V0 is a modelled component but never an argument to [K].
    [View_idle] is the constant blank view of the non-agents V2 and V3. *)
type view =
  | View_live of chan  (** V1, the live ExEx: the head of its own channel *)
  | View_stalled of sib  (** V0, the stalled sibling: its own occupancy *)
  | View_idle  (** the constant blank view of the non-agents V2, V3 *)

(** Total order on views: [View_idle] < [View_live] < [View_stalled], with the
    field order within each constructor. Every constructor pair is spelled: no
    wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_live _ | View_stalled _) -> -1
  | (View_live _ | View_stalled _), View_idle -> 1
  | View_live c, View_live c' -> chan_compare c c'
  | View_live _, View_stalled _ -> -1
  | View_stalled _, View_live _ -> 1
  | View_stalled s, View_stalled s' -> sib_compare s s'

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 is the knowledge agent (the live ExEx); V0 is the
    stalled sibling, modelled but never under [K]; V2 and V3 are idle
    non-agents with the constant blank view. *)
let view v s =
  match v with
  | Validator.V1 -> View_live s.chan
  | Validator.V0 -> View_stalled s.sib
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 -> View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine  (** the real pipeline *)
  | No_canon_gap_marker
      (** delete manager.rs:345-353 - the whole
          [canon_gap(&mut self.last_canon_tip, first, *range.end()).into_iter()
          .for_each(|missed| { warn!(..); self.fan_out(&Lagged { missed }) })]
          block inside [handle_canon_commit], so it falls straight through to
          [fan_out(&ChainExecuted)] at manager.rs:354. In the model
          [In_commit_gap] AT A STATE WITH A BASELINE ([tip = Tip_some]) still
          sets [loss]/[owed] (the loss really happened) but skips the marker
          fan-out, ADDING the transition (tip = [Tip_some], chan = [Chan_empty],
          dropped = false, owed = true) -> (chan = [Chan_payload],
          hole = true): a [ChainExecuted] lands with no preceding marker. The
          baseline guard is what makes this deletion load-bearing rather than
          decorative: at [tip = Tip_none] the pristine and mutated Rust are
          byte-identical, because [canon_gap]'s [_ => None] arm
          (manager.rs:449-452, pinned by the unit test at manager.rs:528-534)
          emits nothing with no baseline. The model therefore only refutes at a
          state where a canonical commit has already been delivered - exactly
          where deleting the block really does change the delivered stream.
          Sibling-repair hunt, five routes, the two that exist
          are modelled and left INTACT by this mutation: (1) [deliver_broadcast]'s
          [BroadcastStreamRecvError::Lagged] arm (manager.rs:294-307) covers only
          the two [BroadcastStream]s - the canonical stream is mapped with
          [canon_state_stream.map(RouterEvent::Canon)] (manager.rs:189-191) and
          [RouterEvent::Canon] carries a bare [CanonStateNotification] with no
          [Result] (manager.rs:235-236), so it can never fire for a canonical
          gap; it is modelled as {!In_cert_lag} and still does not repair
          {!In_commit_gap}. (2) The per-handle [dropped > 0] pre-send
          (manager.rs:64-85) cannot fire, because the manager DID receive the
          commit and had room, so [dropped] is 0 on that transition; it is
          modelled and left intact. (3) The degraded [Reorg] arm
          (manager.rs:327-335) routes through the very same
          [handle_canon_commit], so it is not a second unmutated route.
          (4) [dedup_chain_executed] (context.rs:218-223) only drops duplicate
          [ChainExecuted] heights and explicitly passes [Lagged] markers through
          unchanged; it never synthesises one. (5) [ReplayStream] (replay.rs:39-61)
          yields only [ChainExecuted], never a marker. *)
  | No_lagged_presend
      (** delete manager.rs:64-85 - the whole
          [if self.dropped > 0 { match self.notifications.try_send(Lagged { missed: self.dropped }) { Ok(()) => .. self.dropped = 0, Err(Full(_)) => { self.dropped += 1; return } Err(Closed(_)) => return } }]
          pre-send block in [ExExHandle::send], so [send] goes straight to the
          payload [try_send] at manager.rs:87. In the model this REMOVES the
          (chan = [Chan_empty], dropped = true) -> (chan = [Chan_lagged],
          dropped = false, owed = false) marker-recovery transition and ADDS
          (chan = [Chan_empty], dropped = true, owed = true) ->
          (chan = [Chan_payload], hole = true). Sibling-repair hunt, four
          routes: (1) [canon_gap] (manager.rs:342-355) fires only on an UPSTREAM
          canonical discontinuity and cannot fire for a downstream drop - the
          manager received the commit fine - so it is modelled as
          {!In_commit_gap}, left intact, and does not repair this. (2)
          [deliver_broadcast] (manager.rs:294-307) marks only source-broadcast
          lag, same argument; modelled as {!In_cert_lag} and left intact.
          (3) Outside this marker, [dropped] is only [warn!]-logged
          (manager.rs:91-96) and read nowhere else in the crate, and
          [TnExExManagerHandle] exposes only [min_finished_height]
          (manager.rs:398-412) - no metric, event or handle route exists.
          (4) [ReplayStream] re-derives [ChainExecuted] only (replay.rs:39-61)
          and nothing downstream reconstructs a marker. *)
  | Blocking_send
      (** delete the non-blocking delivery contract stated at manager.rs:9 and
          :11-17: replace [self.notifications.try_send(notification.clone())]
          (manager.rs:87, and the identical pre-send at :65) by an awaited
          [send(..).await]. Because [Router::handle] is a plain synchronous [fn]
          folded once over the merged stream (manager.rs:209-220, :254-283), an
          awaited send on a channel whose consumer never reads parks the ENTIRE
          fan-out for the node's lifetime. In the model, whenever the stalled
          sibling's channel is full this REMOVES every fan transition and leaves
          only a bare phase advance - the router task is parked while the
          separately-spawned live-ExEx consumer task keeps polling, so the poll
          transition survives. Sibling-repair hunt, four routes: (1) there is no
          per-ExEx delivery task and no timeout inside the manager - it is one
          [try_fold] over one merged stream (manager.rs:209-220) and [fan_out]
          is one synchronous [for handle in &mut self.exexes] pass
          (manager.rs:286-290); the per-ExEx tasks spawned at
          crates/node/src/manager/node.rs:927-960 are the CONSUMERS, not
          deliverers, which is exactly why the model must keep the poll alive.
          (2) The reverse path [report_finished_height] is also a [try_send]
          (context.rs:106-115), so an ExEx cannot back-pressure the manager
          either; it does not repair the forward direction. (3) The
          producer-side guard [notify_exex] skips the clone only when
          [receiver_count() == 0] (consensus_bus.rs:582-591) - it protects the
          producer from an ABSENT ExEx, never a starved sibling from a stalled
          one. (4) The pre-send at manager.rs:65 is the same [try_send], so the
          mutation converts it too; leaving it non-blocking would only weaken
          the mutation, not repair the claim. *)

(** [true] iff the mutation keeps the [canon_gap] marker fan-out
    (manager.rs:345-353). Every constructor spelled. *)
let mut_keeps_canon_gap_marker = function
  | Pristine -> true
  | No_canon_gap_marker -> false
  | No_lagged_presend -> true
  | Blocking_send -> true

(** [true] iff the mutation keeps the [dropped > 0] pre-send in
    [ExExHandle::send] (manager.rs:64-85). Every constructor spelled. *)
let mut_keeps_lagged_presend = function
  | Pristine -> true
  | No_canon_gap_marker -> true
  | No_lagged_presend -> false
  | Blocking_send -> true

(** [true] iff the mutation turns the non-blocking [try_send] into an awaited
    [send] (manager.rs:65, :87). Every constructor spelled. *)
let mut_send_blocks = function
  | Pristine -> false
  | No_canon_gap_marker -> false
  | No_lagged_presend -> false
  | Blocking_send -> true

(** The channel-full arm of [ExExHandle::send] (manager.rs:89-97) and the
    identical [Full] arm of the pre-send (manager.rs:75-79): the drop is
    counted, a real loss has occurred on the live ExEx's OWN channel, and the
    obligation to signal it is outstanding. *)
let live_drop st =
  { st with dropped = true; down = true; loss = true; owed = true }

(** The payload/marker [try_send] proper (manager.rs:87-101). On success the
    item lands; a landed marker discharges the outstanding obligation, while a
    landed payload leaves it outstanding and - if one was outstanding - trips
    the [hole] monitor. On a full channel this is the counted drop. *)
let send_live_item item st =
  if chan_is_empty st.chan then
    {
      st with
      chan = item_chan item;
      owed = (if item_is_payload item then st.owed else false);
      hole = st.hole || (item_is_payload item && st.owed);
    }
  else live_drop st

(** One whole [ExExHandle::send] to the live ExEx (manager.rs:62-102) under a
    mutation: the [dropped > 0] pre-send (manager.rs:64-85) - whose [Full] arm
    RETURNS, withholding the payload too - followed by the item's own send. *)
let send_live mut item st =
  if mut_keeps_lagged_presend mut && st.dropped then
    if chan_is_empty st.chan then
      send_live_item item { st with chan = Chan_lagged; dropped = false; owed = false }
    else live_drop st
  else send_live_item item st

(** One [Router::handle] dispatch and the [fan_out] passes it performs
    (manager.rs:254-290), atomic within a single fold iteration. The stalled
    sibling is first in the [exexes] vector, so it is sent to first on every
    pass. *)
let fan mut inp st =
  match inp with
  | In_payload -> send_live mut It_payload { st with sib = sib_send st.sib }
  | In_canon_commit ->
      send_live mut It_payload
        { st with tip = Tip_some; sib = sib_send st.sib }
  | In_commit_gap -> (
      match st.tip with
      | Tip_none ->
          (* No baseline: [canon_gap] takes its [_ => None] arm
             (manager.rs:449-452, unit test :528-534), so the skipped blocks are
             really lost ([loss]) but the manager neither knows nor can signal
             it - the obligation [owed] is NOT incurred, and the commit falls
             through to the bare [fan_out(&ChainExecuted)] at manager.rs:354.
             The tip is still advanced (manager.rs:454). *)
          send_live mut It_payload
            { st with loss = true; tip = Tip_some; sib = sib_send st.sib }
      | Tip_some ->
          let gapped = { st with loss = true; owed = true } in
          let marked =
            if mut_keeps_canon_gap_marker mut then
              send_live mut It_lagged { gapped with sib = sib_send gapped.sib }
            else gapped
          in
          send_live mut It_payload { marked with sib = sib_send marked.sib })
  | In_cert_lag ->
      send_live mut It_lagged
        { st with loss = true; owed = true; sib = sib_send st.sib }

(** The transition relation under a mutation: at a fan phase the manager
    dispatches one of the four merged inputs (or, under {!Blocking_send} with
    the stalled sibling full, is parked and dispatches nothing) and the
    scheduler then picks one of {!phase_next}'s successors; at the poll phase
    the live ExEx's own spawned task takes the head off its channel. No state is
    terminal, so the kernel's stutter-closure never fires and every [Af] is
    honest. *)
let next_with mut s =
  match s.phase with
  | Ph_fan_a | Ph_fan_b ->
      let successors = phase_next s.phase in
      if mut_send_blocks mut && sib_is_full s.sib then
        List.map (fun p -> { s with phase = p }) successors
      else
        List.concat_map
          (fun i ->
            let fanned = fan mut i s in
            List.map (fun p -> { fanned with phase = p }) successors)
          inputs
  | Ph_poll -> [ { s with chan = Chan_empty; phase = Ph_fan_a } ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: node startup - both ExEx channels empty, no drops, no
    losses, and NO canonical baseline ([last_canon_tip = None],
    manager.rs:152). [Sib_empty] holds at the initial state ONLY; the first
    fan-out fills the sibling permanently, which is why [Sib_chan_full] is a
    reachable but non-initial antecedent. [Tip_none] is likewise left only by a
    canonical commit, which is why {!No_canon_gap_marker} can refute only after
    one has been delivered. *)
let initial =
  {
    phase = Ph_fan_a;
    sib = Sib_empty;
    chan = Chan_empty;
    dropped = false;
    tip = Tip_none;
    owed = false;
    loss = false;
    down = false;
    hole = false;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | V1_marker_head
      (** the live ExEx's channel head is a [Lagged] marker: the operative state
          of every [K] conjunct *)
  | V1_payload_head
      (** the head is a [CertificateAccepted] / [ConsensusOutput] /
          [ChainExecuted] payload *)
  | V1_chan_empty
      (** the live ExEx's channel is empty: the target of both [Af] conjuncts of
          the fairness statement *)
  | Loss_occurred
      (** sticky: some notification or commit was lost, upstream or downstream -
          the positive [K] operand *)
  | Down_drop
      (** sticky: the loss included a drop on the live ExEx's own bounded
          channel, i.e. the manager-private [ExExHandle::dropped] route - the
          [~K] operand *)
  | Marker_owed
      (** a SIGNALABLE loss has occurred that no delivered [Lagged] has
          signalled yet: the non-vacuity antecedent of the safety and security
          statements. A pre-baseline canonical skip is excluded by construction
          (see {!In_commit_gap}), because [canon_gap] provably cannot report it
          (manager.rs:449-452, :528-534) *)
  | Silent_hole
      (** monitor: a payload enqueue into the live ExEx's channel SUCCEEDED
          while a marker was owed - constantly false on the pristine model *)
  | Sib_chan_full
      (** the stalled sibling ExEx's channel is full: the fairness antecedent *)
  | Canon_baseline
      (** the manager holds a canonical baseline ([last_canon_tip = Some(_)],
          manager.rs:126-129), so a later skip is detectable at all. It scopes
          the safety statement's claim and witnesses that
          {!No_canon_gap_marker}'s refutation happens where the deleted block
          genuinely changes the delivered stream *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | V1_marker_head -> Int.equal 0 (chan_compare s.chan Chan_lagged)
  | V1_payload_head -> Int.equal 0 (chan_compare s.chan Chan_payload)
  | V1_chan_empty -> chan_is_empty s.chan
  | Loss_occurred -> s.loss
  | Down_drop -> s.down
  | Marker_owed -> s.owed
  | Silent_hole -> s.hole
  | Sib_chan_full -> sib_is_full s.sib
  | Canon_baseline -> tip_has_baseline s.tip

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | V1_marker_head -> "head_1(Lagged)"
  | V1_payload_head -> "head_1(payload)"
  | V1_chan_empty -> "empty_1"
  | Loss_occurred -> "loss_occurred"
  | Down_drop -> "down_drop"
  | Marker_owed -> "marker_owed"
  | Silent_hole -> "silent_hole"
  | Sib_chan_full -> "sib_full"
  | Canon_baseline -> "canon_baseline"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml).

    This family's reachability relation is a PREORDER rather than a poset: it
    models a mechanism that undoes itself, so two distinct states can be
    mutually reachable and {!Frame.certify_functorial} refuses antisymmetry.
    That is recorded in test/t_topos_frames.ml and it does not obstruct the
    denotation: [W] is still a thin category, so parallel arrows are still
    unique and presheaf restriction is still path-independent, and the
    executable reduction gate is green on this family. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: single initial state, mutation-
    parameterized transitions, the one-knower view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
