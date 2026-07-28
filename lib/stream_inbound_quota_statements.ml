(** The STREAM_INBOUND_QUOTA statements: what the libp2p stream behaviour's
    per-peer inbound rate window buys, exactly how far its scope reaches, and
    what a peer on either side of it can infer from a stream that died without
    a byte. Mined from crates/network-libp2p/src/stream/behavior.rs and
    crates/network-libp2p/src/consensus.rs at git HEAD 0c59c15b; every citation
    below was opened in that checkout.

    READING GUIDE FOR THE [K] OPERANDS. Three knowledge conjuncts appear here
    and none of them is a projection of its own knower's view.

    - S2's [~K_V0(opened(W,R) > MAX)]. The operand is W's OWN cumulative rate.
      V0 is the responder R, whose view is its [inbound] entry, its window
      phase, its [peer_to_bls] result and its own disposition of the stream -
      W's true rate is exactly the one thing R does not have, because
      [self.inbound.remove(&peer)] (behavior.rs:258) throws the evidence away.
      It is not rigid: both truth values are reachable and the ignorance
      witness pair is named in the statement doc.
    - S3's [~K_V1(rate_limited(R,W))] and [~K_V1(unknown_peer_drop(R,W))]. Both
      operands are R's hidden reason for discarding the stream. V1 is the
      opener W, whose view carries the collapsed wire observation
      ({!Stream_inbound_quota_model.observation}) and nothing of R's counters
      or R's [bls_by_peer_id] lookup. Both are contingent.
    - S3's positive [K_V1(peer_to_bls(W) = Some)]. The operand is R's identity
      resolution state, which is emphatically not in W's view - W is told
      nothing at all on either drop path - and it is not rigid: the initial
      state has it false and consensus.rs:1007-1016 documents the lag that
      makes it so. Its view class at every answered state is provably larger
      than one: R's window may or may not have rolled since the answer
      (behavior.rs:284-287) and W cannot see which, so the class holds at
      least two reachable states. That non-singleton fact has its own test in
      test/t_stream_inbound_quota.ml.

    THE OPERATIVE BOUND. [MAX_INBOUND_PER_WINDOW] is abstracted from 256 to 1
    throughout, so "over the allowance" means "at least two opens in the
    window". That is a bound abstraction and nothing else: it does not touch
    which peer [self.inbound.entry(peer)] (behavior.rs:283) charges, which is
    the whole content of S1. *)

open Stream_inbound_quota_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;  (** unique across every family *)
  bucket : Statements.bucket;  (** Safety | Liveness | Fairness | Security *)
  formula : atom Formula.t;  (** the claim, proved with [prove_nonvacuous] *)
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - inbound-rate-window-charges-only-the-opening-peers-own-streams
    [fairness].

    AG( rate_limited(R,W) -> opened(W,R) > MAX ) /\
    AG( window_count(R,W) > MAX -> opened(W,R) > MAX )

    CONJUNCT A. A rate-limit rejection is always self-inflicted. R drops an
    inbound stream only when [inbound_rate_limited] returns true
    (behavior.rs:346-353), and that function tests [window.count >
    MAX_INBOUND_PER_WINDOW] (behavior.rs:288-289) on the entry it took with
    [self.inbound.entry(peer).or_insert(..)] (behavior.rs:283) - the entry
    keyed by the OPENING peer. So the count that rejects W was incremented by
    W's own opens and by nothing else, and W must therefore have exceeded its
    own allowance.

    CONJUNCT B. The same disjointness stated on the meter rather than the
    outcome, which is the stronger half: R's window entry for W is never
    driven past the bound by anyone but W. Conjunct A does not imply it at a
    common state - the outcome atom is the fate of W's LAST stream and can be
    stale relative to the meter after a reset - and conjunct B is what actually
    rules out a neighbour parking W permanently at the limit.

    The uniform constant matters as much as the keying: [const
    MAX_INBOUND_PER_WINDOW: usize = 256] (behavior.rs:44-45) is one bound for
    every peer, with no per-identity tier and no committee exemption on this
    path, so the guarantee is equal-treatment and not merely a bound.

    MUTATION PIN. {!Stream_inbound_quota_model.No_per_peer_keying} replaces the
    keyed [entry(peer)] at behavior.rs:283 with one behaviour-wide window. The
    neighbour event, inert under the pristine keying, then bumps W's meter, and
    the state (meter over the bound, W within its own allowance) becomes
    reachable - refuting conjunct B outright, and refuting conjunct A on W's
    very first open. No sibling repairs it: the [InboundRateLimited] penalty
    classification (upgrade.rs:159-160) is reported metrics-only and never
    enforced (consensus.rs:1677-1693), QUIC's [max_concurrent_stream_limit]
    (consensus.rs:451-452) bounds concurrency per connection rather than open
    rate across identities, and the peer manager's excess-peer logic governs
    connection counts. *)
let s_1 =
  let self_inflicted =
    Formula.Ag (Formula.Implies (atom Rejected, atom Own_over_cap))
  in
  let meter_is_disjoint =
    Formula.Ag (Formula.Implies (atom Meter_full, atom Own_over_cap))
  in
  {
    name = "inbound-rate-window-charges-only-the-opening-peers-own-streams";
    bucket = Statements.Fairness;
    formula = Formula.And (self_inflicted, meter_is_disjoint);
    antecedent = atom Rejected;
  }

(** S2 - inbound-quota-is-scoped-to-a-connection-episode-not-to-the-peer-identity
    [fairness].

    E[ (~rate_limited /\ ~window_rolled)
       U (opened(W,R) > MAX /\ ~window_rolled /\ ~rate_limited) ]
    /\
    AG( redialled(W) /\ ~rate_limited(R,W) /\ opened(W,R) > MAX
        -> ~K_V0( opened(W,R) > MAX ) )

    CONJUNCT A - THE EVASION IS REACHABLE. [on_disconnected] runs
    [self.inbound.remove(&peer);] (behavior.rs:258), reached whenever a peer's
    last connection closes ([ConnectionClosed { peer_id, remaining_established:
    0, .. }], behavior.rs:323-330). The whole window entry goes, so the next
    [entry(peer).or_insert(InboundWindow { count: 0, .. })] (behavior.rs:283)
    starts the peer from zero. A peer can therefore spend its whole allowance,
    close its own connection, redial and spend it again, exceeding the nominal
    per-second bound without ever being rate-limited. This is a reachability
    claim and it is deliberately what the code guarantees rather than a
    stronger per-identity claim, which would be false. The [~window_rolled]
    conjunct is load-bearing: without it the tumbling reset at
    behavior.rs:284-287 would supply the same evasion for a different reason,
    and the pin below would not be attributable to the deleted line.

    CONJUNCT B - R CANNOT RECOVER THE HISTORY. The reset does not merely zero
    a counter, it erases the evidence. After the redial R's whole observable
    state - its [inbound] entry, its window phase, its [peer_to_bls] result,
    its disposition of the stream - is identical for a peer that has opened
    its whole allowance and redialled and for a peer that just connected and
    opened once. The claim is scoped to states where R has NOT rate-limited W,
    because a rejection is itself evidence of two opens in one window and
    would let R infer the rate; and to redialled states, because that is the
    situation the deleted line creates.

    IGNORANCE WITNESS (R3) for conjunct B. State A: W opens once (admitted,
    answered), redials, opens once more - R's entry reads count = MAX, R saw a
    redial, R resolved W, R answered. State B: W redials first, then opens once
    - R's entry reads count = MAX, R saw a redial, R resolved W, R answered.
    R's view is character-for-character the same; [opened(W,R) > MAX] holds in
    A and fails in B. Both are reachable and the pair has a test.

    MUTATION PIN. {!Stream_inbound_quota_model.No_window_reset_on_disconnect}
    deletes [self.inbound.remove(&peer);] (behavior.rs:258) and nothing else.
    The redial then leaves the count in place, so reaching [opened > MAX]
    without a roll necessarily crosses the bound and is rate-limited: conjunct
    A's until-path no longer exists and the statement refutes. Conjunct B does
    not flip - its antecedent stops being reachable under the mutation, so the
    implication goes vacuously true - which is stated here rather than papered
    over; conjunct A is the load-bearing half of this pin. No sibling repairs
    it: the only other reset is the tumbling roll (behavior.rs:284-287), which
    conjunct A excludes by construction, and the peer manager's
    excess-reconnection handling covers peers the node itself sheds, not a peer
    that closes its own connection. *)
let s_2 =
  let evasion_is_reachable =
    Formula.Eu
      ( Formula.And
          (Formula.Not (atom Rejected), Formula.Not (atom Window_rolled)),
        Formula.conj
          [
            atom Own_over_cap;
            Formula.Not (atom Window_rolled);
            Formula.Not (atom Rejected);
          ] )
  in
  let responder_cannot_recover_the_rate =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [
               atom Reconnected;
               Formula.Not (atom Rejected);
               atom Own_over_cap;
             ],
           Formula.Not (Formula.K (Validator.V0, atom Own_over_cap)) ))
  in
  {
    name =
      "inbound-quota-is-scoped-to-a-connection-episode-not-to-the-peer-identity";
    bucket = Statements.Fairness;
    formula = Formula.And (evasion_is_reachable, responder_cannot_recover_the_rate);
    antecedent = Formula.And (atom Reconnected, atom Own_over_cap);
  }

(** S3 - a-silently-dropped-inbound-stream-hides-which-gate-killed-it
    [security].

    AG( silently_dropped(R,W) /\ opened(W,R) > MAX /\ ~redialled(W)
        -> ~K_V1( rate_limited(R,W) ) /\ ~K_V1( unknown_peer_drop(R,W) ) )
    /\
    AG( answered(R,W) -> K_V1( peer_to_bls(W) = Some ) )

    CONJUNCT A - THE TWO SILENT DROPS ARE ONE OBSERVATION. An inbound stream
    that negotiated successfully can still die at R for two unrelated reasons,
    and neither writes anything back. Cause 1 is the rate gate: [if
    self.inbound_rate_limited(peer_id) { // drop the stream; report for
    scoring ... }] (behavior.rs:346-353), where the [Stream] value simply goes
    out of scope. Cause 2 is the identity gate: [else { warn!(target:
    "network", ?peer, "received inbound stream from unknown peer"); }]
    (consensus.rs:1673-1675), again dropping the [Stream]. Neither writes a
    [SyncFrame::Deny] or any other signal, and the penalty classification that
    exists for cause 1 (upgrade.rs:159-160) is reported metrics-only
    (consensus.rs:1677-1693), so no disconnect or ban follows that W could
    observe. Contrast the responder-side capacity shed at
    primary/src/network/mod.rs:1892-1909, which DOES write
    [SyncFrame::Deny(DenyReason::AtCapacity)] before closing precisely so the
    requester can retry elsewhere - the point of this statement is that the two
    network-layer drops have no such courtesy.

    The [opened(W,R) > MAX] conjunct in the antecedent is not decoration: a
    peer that has opened only its allowance can rule the rate gate out by
    arithmetic, so the genuine ambiguity begins exactly where the quota becomes
    a live possibility. The [~redialled(W)] conjunct scopes the claim to a
    single connection episode, because W does see its own redial.

    IGNORANCE WITNESS (R3). State A: W opens twice with no roll - the second
    open crosses the bound and is dropped by the rate gate. State B: W opens
    once, R's tumbling window rolls (behavior.rs:284-287) unseen, W opens
    again - the second open is inside the bound but W's [NodeRecord] has not
    resolved, so the identity gate drops it. W's view in both is: two opens, no
    redial, a stream that closed with nothing written. The hidden variable is
    R's window PHASE - [started] is R's own [Instant] (behavior.rs:283), so no
    opener knows where the boundary is - and it is what makes the class
    genuinely two-sided rather than an artefact.

    CONJUNCT B - AN ANSWER IS PROOF OF RESOLUTION. The converse direction is
    sharp and is the half that survives every scoping worry. The only route
    from the stream behaviour to the application is
    [try_send(NetworkEvent::InboundStream { peer: bls, .. })] inside the
    [if let Some(bls) = ... peer_to_bls(&peer)] arm (consensus.rs:1665-1670),
    and the application is the only thing that writes on that stream
    (primary/src/network/mod.rs:1984, :1892-1909). So a byte coming back proves
    R had resolved W's BLS identity, even though W is told nothing about the
    lookup and the lookup is invisible in W's view. The knowledge is genuine
    rather than collapsed: the class at an answered state contains at least the
    rolled and the unrolled window, and W cannot tell those apart.

    MUTATION PIN. {!Stream_inbound_quota_model.No_identity_guard} deletes the
    [if let Some(bls) = ...] gate at consensus.rs:1665 and forwards regardless.
    Conjunct B refutes immediately: an answered stream no longer implies a
    resolved identity. Conjunct A refutes too, because with cause 2 gone the
    silent class collapses to the quota alone. No sibling repairs the deletion:
    the consumers of [NetworkEvent::InboundStream] dispatch straight on
    [StreamKind] with no membership test (primary/src/network/mod.rs:1507-1510,
    worker/src/network/mod.rs:466), and the only [Deny] writer on that path is
    the capacity shed at mod.rs:1892-1909, which writes a frame and runs after
    delivery.

    DISCLOSED OMISSIONS. The real code has three further silent causes the
    model leaves out: the behaviour's own queue shed ([if self.events.len() <
    MAX_EVENTS { .. }], behavior.rs:215-218, exercised by the in-tree test at
    :594-605), the [Err] arm of the [try_send] forward
    (consensus.rs:1666-1672), and the responder's request-read timeout
    (primary/src/network/mod.rs:1912-1920). Each of them only ADDS a member to
    the opener's silent class, and a bigger class makes [~K] easier while a
    smaller one makes it harder, so conjunct A is not true by these omissions -
    it is proved against the strictest class the mechanism admits. What they do
    mean is that the real code's silent class would not collapse all the way
    under the mutation, which is why conjunct B, whose flip is independent of
    the class, is this pin's robust half. *)
let s_3 =
  let cause_is_hidden =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [
               atom Silent_drop;
               atom Own_over_cap;
               Formula.Not (atom Reconnected);
             ],
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom Rejected)),
               Formula.Not (Formula.K (Validator.V1, atom Identity_drop)) ) ))
  in
  let an_answer_proves_resolution =
    Formula.Ag
      (Formula.Implies
         (atom Answered, Formula.K (Validator.V1, atom Identity_resolved)))
  in
  {
    name = "a-silently-dropped-inbound-stream-hides-which-gate-killed-it";
    bucket = Statements.Security;
    formula = Formula.And (cause_is_hidden, an_answer_proves_resolution);
    antecedent = Formula.And (atom Silent_drop, atom Own_over_cap);
  }

(** The family's statements. *)
let all = [ s_1; s_2; s_3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st = Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

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
