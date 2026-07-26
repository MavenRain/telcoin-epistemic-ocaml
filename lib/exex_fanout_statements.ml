(** The EXEX_FANOUT statement family, encoded over the {!Exex_fanout_model}
    interpreted system. Three statements about the ExEx manager's bounded,
    non-blocking fan-out pipeline: one safety ordering contract, one security
    knowledge/ignorance pair, one fairness non-starvation claim. All file
    citations refer to Telcoin-Association/telcoin-network.

    Reading guide for the [K] operands. The single knower is V1, the live ExEx,
    and its view is EXACTLY the head of its own [mpsc::Receiver]
    (context.rs:26-33, :117-124) - [TnExExContext]'s fields are private on
    purpose so third-party ExEx code has no other notification surface. The
    positive operand [loss_occurred] is a manager/producer-side sticky fact, not
    a projection of that view: it is false at the initial state and at every
    reachable no-loss state, so [K (V1, loss_occurred)] genuinely fails at
    empty-channel and payload-head states, and it becomes known only because
    every marker the pipeline emits is emitted after a REAL loss (the three
    emission sites are [canon_gap]'s [first > prev + 1] test at
    manager.rs:449-452, [deliver_broadcast]'s [BroadcastStreamRecvError::Lagged]
    arm at manager.rs:294-307, and the [dropped > 0] pre-send at
    manager.rs:64-65). The negative operand [down_drop] is the manager-private
    [ExExHandle::dropped] route (manager.rs:45-49), which is [warn!]-logged and
    read nowhere else, with [TnExExManagerHandle] exposing only
    [min_finished_height] (manager.rs:398-412): it has NO out-of-band recovery
    path, which is what makes the ignorance genuine rather than a modelling
    artefact.

    On what this family deliberately does NOT claim. An earlier draft asserted
    that V1 cannot learn WHICH certificate it missed. That is not safe:
    [TnExExContext::consensus_chain] hands every ExEx a read handle on the
    consensus DB, including committed sub-DAGs (context.rs:91-104), so
    certificate identity is recoverable out of band and the [~K] would have been
    an artefact of omitting a real repair path. The retargeted operand,
    [down_drop], has no such route. *)

open Exex_fanout_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a false antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - payload-never-delivered-while-a-gap-marker-is-owed [safety]. On the
    live ExEx's bounded notification channel, a payload is NEVER enqueued while
    a SIGNALABLE loss that has already occurred is still un-signalled: every
    such hole in the delivered stream is preceded by a [Lagged] marker,
    whichever of the entangled routes produced it.

    Scope, stated in the claim rather than buried in the model. "Signalable"
    means a loss the manager can detect at all: a drop on the live ExEx's own
    channel (manager.rs:89-97), a broadcast lag (manager.rs:300-305), or a
    canonical skip measured against an EXISTING baseline (manager.rs:449-452).
    A canonical skip before the manager has ever delivered a commit is NOT
    covered, and deliberately so: [canon_gap]'s [_ => None] arm returns nothing
    when [last_canon_tip] is [None] (manager.rs:449-452), which the crate's own
    unit test pins ("First commit: no baseline -> no gap", manager.rs:528-534),
    so the pipeline emits no marker and cannot. The model takes that transition
    ({!Exex_fanout_model.In_commit_gap} at [Tip_none]) and records the real
    [loss] on it without incurring an obligation, so this statement is a claim
    the real manager keeps rather than one the model manufactured by omitting
    the startup window.

    Encoded as the single invariant AG( ~silent_hole ), where [silent_hole] is a
    ghost monitor set exactly when a payload enqueue into the live ExEx's
    channel SUCCEEDS while the model's [owed] flag is true. Three real facts
    make it constantly false:

    (a) [handle_canon_commit] fans out [Lagged { missed }] BEFORE
    [fan_out(&ChainExecuted { new })] whenever [canon_gap] reports a
    discontinuity (manager.rs:342-355; reth's canonical stream drops broadcast
    lag silently, manager.rs:126-129, :312-315, so this is the only place an
    upstream canonical hole is noticed);

    (b) [ExExHandle::send] pre-sends [Lagged { missed: self.dropped }] before the
    payload whenever [self.dropped > 0] (manager.rs:62-85), which is exactly the
    recovery the manager's own unit test pins
    ([full_channel_drops_then_surfaces_lagged_marker], manager.rs:470-496);

    (c) when that pre-send ITSELF finds the channel [Full], the drop count is
    bumped and the function RETURNS (manager.rs:75-79) - the payload is withheld
    too, so no payload can slip past an owed marker. Fact (c) is what makes the
    claim cover both routes as one ordering contract rather than the canonical
    gap alone: a canon-gap marker that hits a full channel folds into [dropped]
    and is re-emitted later, and the payload waits for it.

    Non-vacuity antecedent: [marker_owed] - reachable pristine, because a
    payload sent into a channel that already holds an item drops and sets
    [dropped]/[owed] (manager.rs:89-97). The obligation is a live one.

    No [K] operand, so R1 does not bite. The protected proposition is
    nevertheless not knower-local: [owed] tracks the manager's private [dropped]
    field (manager.rs:45-49), which is read nowhere outside [ExExHandle::send]
    and only [warn!]-logged (manager.rs:67-72, :91-96).

    Mutation pin: BOTH {!Exex_fanout_model.No_canon_gap_marker} and
    {!Exex_fanout_model.No_lagged_presend} refute it, each by ADDING a
    transition into a [silent_hole] state - the first lets a [ChainExecuted]
    land in an empty channel while [owed] holds, the second lets the payload
    after a downstream drop land with no preceding marker.
    {!Exex_fanout_model.Blocking_send} deliberately leaves it alone: it removes
    deliveries, it never adds an unmarked one.

    Load-bearingness of the first pin, checked rather than asserted. Under
    {!Exex_fanout_model.No_canon_gap_marker} EVERY [silent_hole] state has
    [canon_baseline] - the mutation test asserts the invariant
    AG( silent_hole -> canon_baseline ) on the mutant - so the refutation is
    carried only by states in which a canonical commit has already been
    delivered, i.e. states where deleting manager.rs:345-353 really does change
    the bytes the ExEx receives. At [Tip_none] the pristine and mutated Rust are
    indistinguishable, and the model no longer pretends otherwise; an earlier
    revision refuted ONLY there, which is the defect this scope repairs. *)
let s_no_silent_hole =
  {
    name = "payload-never-delivered-while-a-gap-marker-is-owed";
    bucket = Statements.Safety;
    formula = Formula.Ag (Formula.Not (atom Silent_hole));
    antecedent = atom Marker_owed;
  }

(** S2 - lagged-marker-is-delivered-and-known-but-its-cause-is-opaque
    [security]. Every un-signalled loss is eventually surfaced to the live ExEx
    as a [Lagged] marker, and on receiving it the ExEx KNOWS that a notification
    or commit really was lost - but it does NOT know, and cannot rule out,
    whether the loss was a drop on its own bounded channel (downstream) or a
    lag/skip upstream of the manager.

    (A) Delivery and soundness:
    AG( marker_owed -> AF( head_1(Lagged) /\\ K_V1(loss_occurred) ) ).
    [marker_owed] holds after a downstream drop (manager.rs:89-97), a broadcast
    lag (manager.rs:300-305), or a canonical discontinuity measured against an
    existing baseline (manager.rs:345-353, :449-452) - a pre-baseline skip
    incurs no obligation because [canon_gap] provably cannot report it
    (manager.rs:528-534), which is why the antecedent is [marker_owed] and not
    [loss_occurred]; the [dropped > 0] pre-send at
    manager.rs:64-85 guarantees it is surfaced on the next send that finds room,
    which is precisely what [full_channel_drops_then_surfaces_lagged_marker]
    pins (manager.rs:470-496). The [K] is honest because a marker is only ever
    emitted AFTER a real loss - the three emission sites are [canon_gap]'s
    [first > prev + 1] test (manager.rs:449-452), [deliver_broadcast]'s
    [BroadcastStreamRecvError::Lagged] arm (manager.rs:294-307) and the
    [dropped > 0] pre-send (manager.rs:64-65) - so every reachable state whose
    channel head is a marker has [loss_occurred].

    (B) Cause opacity:
    AG( head_1(Lagged) -> ~K_V1(down_drop) /\\ ~K_V1(~down_drop) ).
    [TnExExNotification::Lagged] is a single-field variant carrying only
    [missed] and no cause tag (notification.rs:141-144), and its own doc says
    the downstream (manager -> ExEx) and upstream (source -> manager) cases both
    surface "the same 'a gap exists' signal" and that [missed] is "a best-effort
    magnitude, not a single unit" - dropped per-ExEx notifications OR lagged
    broadcast messages OR skipped canonical block numbers depending on which gap
    it reports (notification.rs:109-136). The downstream cause lives solely in
    [ExExHandle::dropped] (manager.rs:45-49), which is [warn!]-logged and read
    nowhere else; [TnExExManagerHandle] exposes only [min_finished_height]
    (manager.rs:398-412) and the node discards that handle entirely.

    R2/R3 witnesses, both reachable, sharing V1's view [View_live Chan_lagged]
    and disagreeing on [down_drop]:
    - W_up = (Sib_full, Chan_lagged, dropped = false, tip = Tip_none,
      owed = false, loss = true, down = FALSE), reached by one [In_cert_lag]
      fan-out from the initial state ([deliver_broadcast]'s [Lagged] arm,
      manager.rs:300-305);
    - W_down = (Sib_full, Chan_lagged, dropped = true, tip = Tip_none,
      owed = true, loss = true, down = TRUE), reached by [In_payload],
      [In_payload] (the second drops on the full capacity-1 channel), poll,
      [In_payload] (the [dropped > 0] pre-send lands the marker, the payload
      then drops).
    Identical V1 view, opposite [down_drop]: this single pair is simultaneously
    the R2 non-singleton witness for [K_V1(loss_occurred)] and the R3 ignorance
    witness for both [~K] conjuncts.

    Scope of the [AF] in (A), stated rather than hidden: a pending marker is
    surfaced only piggybacked on the NEXT [ExExHandle::send] (manager.rs:64-85),
    so the eventuality is relative to the model's standing assumption that the
    manager always has an event to dispatch at a fan phase (see the
    {!Exex_fanout_model} header). On a node whose source streams went quiet
    forever an owed marker would simply never be sent. The claim is therefore
    about the operating regime of a running node, and it is still R8-honest:
    the mutation that refutes it deletes a real gate (the pre-send), not that
    assumption.

    Non-vacuity antecedent: [marker_owed], reachable pristine and under every
    mutation, so the pins flip by [Refuted] and never by [Vacuous_antecedent].

    Mutation pin: {!Exex_fanout_model.No_lagged_presend} refutes conjunct (A) -
    deleting manager.rs:64-85 REMOVES the (empty channel, [dropped]) ->
    (marker delivered) transition, so a run that only ever feeds contiguous
    payloads never delivers a marker after a downstream drop and the [AF] fails.
    {!Exex_fanout_model.No_canon_gap_marker} refutes (A) by the sibling route:
    deleting manager.rs:345-353 leaves a post-baseline canonical skip with an
    obligation ([owed]) that no [dropped] pre-send can ever discharge, because
    the manager received that commit and had room, so [dropped] is 0 on the
    transition; a run that then feeds only payloads never surfaces it. That
    refutation is confined to post-baseline states, exactly where the deletion
    is a real change to the Rust (manager.rs:449-452, :528-534). Conjunct (B) is
    untouched by both, so each refutation is cleanly attributable to the
    delivery half.

    NOT pinned by {!Exex_fanout_model.Blocking_send}, and why the earlier
    revision's pin there is gone rather than merely unfashionable: once the
    stalled sibling's channel is full the router is parked, so the live ExEx's
    channel is never written again and can never overflow - [ExExHandle::dropped]
    for the live handle stays 0 (manager.rs:87-97 is unreachable while parked)
    and no obligation is ever incurred. The antecedent [marker_owed] is
    therefore UNREACHABLE under that mutation and [prove_nonvacuous] would fail
    with [Vacuous_antecedent] rather than [Refuted]. A vacuity flip is not
    evidence that the gate matters, so it is not claimed as a pin. *)
let s_marker_delivered_cause_opaque =
  let delivered_and_known =
    Formula.leads_to (atom Marker_owed)
      (Formula.And
         (atom V1_marker_head, Formula.K (Validator.V1, atom Loss_occurred)))
  in
  let cause_opaque =
    Formula.Ag
      (Formula.Implies
         ( atom V1_marker_head,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom Down_drop)),
               Formula.Not
                 (Formula.K (Validator.V1, Formula.Not (atom Down_drop))) ) ))
  in
  {
    name = "lagged-marker-is-delivered-and-known-but-its-cause-is-opaque";
    bucket = Statements.Security;
    formula = Formula.And (delivered_and_known, cause_opaque);
    antecedent = atom Marker_owed;
  }

(** S3 - stalled-sibling-exex-cannot-starve-the-live-exex [fairness]. An ExEx
    that never drains its bounded channel - so that channel is permanently full
    - can neither stop the fan-out loop nor starve any sibling ExEx: the live
    ExEx's channel keeps being refilled by the manager and keeps being emptied
    by its own task, forever.

    (A) Delivery half: AG( sib_full -> AF( ~empty_1 ) ). With the sibling
    permanently full, the live ExEx's channel still becomes non-empty again.
    Grounded in [fan_out]'s single synchronous
    [for handle in &mut self.exexes { handle.send(notification) }] pass
    (manager.rs:286-290) over a [send] that is [try_send]-only on both the
    marker and the payload (manager.rs:64-65, :87-101), inside one [try_fold]
    over the merged stream with a plain synchronous [Router::handle]
    (manager.rs:209-220, :254-283) - no per-ExEx delivery task, no timeout. The
    delivery contract is stated in the module header at manager.rs:11-17. Both
    conjuncts are [AF]s over EVERY path of the nondeterministic one-or-two-fans
    per poll scheduler ({!Exex_fanout_model.phase_next}), so neither is carried
    by a convenient interleaving: whichever branch the scheduler takes, a fan
    follows every poll and a poll follows every fan within two steps.

    (B) Consumption half: AG( sib_full -> AF( empty_1 ) ). The live ExEx keeps
    polling and emptying its channel INDEPENDENTLY of the manager, grounded in
    the per-ExEx spawned consumer task and per-ExEx [mpsc] channel
    (crates/node/src/manager/node.rs:927-960) and in [next_notification] being
    the ExEx's own [await] (context.rs:117-124). This conjunct survives
    {!Exex_fanout_model.Blocking_send} by design; it is exactly what makes
    conjunct (A)'s failure under that mutation mean STARVATION rather than
    global stutter. The mining card asserted the blocking send "halts the whole
    router" - correct - but implicitly halted the consumer too, which would have
    manufactured the liveness failure (R8). Read (B) for what it is: the model's
    consumer-keeps-draining assumption made explicit and machine-checked, so
    that its survival under the mutation is verified rather than assumed. It is
    a claim about the model's live consumer, not an independent claim about
    telcoin-network's relative producer/consumer rates.

    Non-vacuity antecedent: [sib_full] - reachable pristine after the first
    fan-out (the sibling's capacity-1 channel fills and never drains) and still
    reachable under {!Exex_fanout_model.Blocking_send}, so the pin flips by
    [Refuted].

    No [K] operand, so R1 does not bite; the property is inherently
    cross-consumer, since no single ExEx's view contains the sibling's
    occupancy.

    Mutation pin: {!Exex_fanout_model.Blocking_send}. With the sibling's channel
    full the router is parked at the fan phase, REMOVING every delivery
    transition into the live ExEx's channel while the poll transition
    ([chan := Chan_empty]) survives; the reachable tail therefore has [empty_1]
    forever and conjunct (A) fails at a state where [sib_full] holds.
    {!Exex_fanout_model.No_canon_gap_marker} and
    {!Exex_fanout_model.No_lagged_presend} leave this statement alone - they
    change WHAT is delivered, never WHETHER. *)
let s_stalled_sibling_cannot_starve =
  let refilled =
    Formula.Ag
      (Formula.Implies
         (atom Sib_chan_full, Formula.Af (Formula.Not (atom V1_chan_empty))))
  in
  let drained =
    Formula.Ag
      (Formula.Implies (atom Sib_chan_full, Formula.Af (atom V1_chan_empty)))
  in
  {
    name = "stalled-sibling-exex-cannot-starve-the-live-exex";
    bucket = Statements.Fairness;
    formula = Formula.And (refilled, drained);
    antecedent = atom Sib_chan_full;
  }

(** The family's statements: one safety ordering contract, one security
    knowledge/ignorance pair, one fairness non-starvation claim. *)
let all =
  [ s_no_silent_hole; s_marker_delivered_cause_opaque;
    s_stalled_sibling_cannot_starve ]

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
