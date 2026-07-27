(** Interpreted system for the GOSSIP-AUTH family: authenticated publishing
    on the certificate gossip topic of telcoin-network's libp2p layer.

    Abstraction. One certificate frame [C] (V0's aggregated R1 anchor
    certificate) travels the authorized path: V0 aggregates and publishes it
    (publish_certificate, crates/consensus/primary/src/network/mod.rs:423-428)
    and the mesh delivers it to the honest subscribers V1 and V2 under
    bounded delay. One rogue frame [C'] is signed and published by a phantom
    outsider O - a live mesh peer with a confirmed non-committee identity
    (add_self_advertised_peer, crates/network-libp2p/src/peers/manager.rs:
    799-838) - and is dropped by the authorized-publisher containment in
    verify_gossip. Modeled mechanisms, keyed to
    Telcoin-Association/telcoin-network:
    - gossipsub envelopes are author-signed under strict validation with
      application-level acceptance (MessageAuthenticity::Signed +
      ValidationMode::Strict + validate_messages,
      crates/network-libp2p/src/consensus.rs:342-362), and the author's BLS
      identity is bound to its peer id by the verified node record
      (peer_record_valid / decode_and_verify,
      crates/network-libp2p/src/consensus.rs:529-565) - the publisher
      identity behind a frame is unforgeable by construction;
    - the per-topic authorized-publisher set
      (crates/network-libp2p/src/consensus.rs:194-198) is installed with
      exactly the committee's BLS keys at every epoch start
      (crates/node/src/manager/node/start_epoch.rs:481-486 and 517-524), so
      authorized(cert_topic) = committee is a constant of the model, baked
      into the transition relation at zero state cost;
    - verify_gossip accepts a frame only when the resolved author key is
      contained in that set, else Reject(UnauthorizedAuthor)
      (crates/network-libp2p/src/consensus.rs:1491-1514; the containment arm
      at 1504-1508 is this family's mutation gate);
    - acceptance is what forwards the payload to the application layer
      (crates/network-libp2p/src/consensus.rs:1004-1047), which is the
      [delivered] bit here.

    Role mapping (the kernel's agent universe is {!Validator.t}): V0 is the
    committee aggregator-publisher of [C]; V1 and V2 are the honest
    committee subscribers and the ONLY knowledge agents of this family (the
    i = V0 instance of the statement collapses - its operand is V0's own
    publish act); V3 is a passive committee slot, epistemically inert:
    constant empty view, never under K / Everyone / Common. The outsider O
    is NOT a validator: it lives purely in global state fields
    ([published_c_prime]), exactly as the card requires.

    Hidden branching gives K its contingency: [Leader_crash_post_vote] is
    identical to [Cooperate] through the Vote phase and only then drops V0,
    so a crash-branch state where nothing was ever published collides, in
    V1's (and V2's) view, with the cooperative run's publish-in-flight
    window - delivery is exactly the knowledge-producing event. *)

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

(** The two frames that can appear on the certificate gossip topic:
    [Cert_c] is V0's aggregated anchor certificate, [Cert_c_prime] is the
    outsider-signed certificate O attempts to publish. *)
type msg = Cert_c | Cert_c_prime

(** Render a frame for atom strings. *)
let msg_to_string = function Cert_c -> "C" | Cert_c_prime -> "C'"

(** The hidden branch resolved at the first transition. [Cooperate] follows
    the protocol: V0 aggregates [Cert_c] at Certify and performs the publish
    act. [Leader_crash_post_vote] is identical to [Cooperate] through Vote
    (anchor header proposed, subscriber votes cast) and only then omits V0
    from Certify onward: [Cert_c] never forms and is never published. The
    post-vote timing is load-bearing: a crash before Vote would leave the
    subscribers' vote records different from the cooperative run and no view
    collision would survive into the publish window (the {!Tn_model}
    [Leader_crash] diverges exactly that early, which is why this family
    needs its own branch). *)
type strategy = Strategy_unchosen | Cooperate | Leader_crash_post_vote

(** Total order on strategies for {!state_compare}. *)
let strategy_index = function
  | Strategy_unchosen -> 0
  | Cooperate -> 1
  | Leader_crash_post_vote -> 2

(** See {!strategy_index}. *)
let strategy_compare a b = Int.compare (strategy_index a) (strategy_index b)

(** O's hidden sub-choice, resolved at Certify (the phase where O would
    observe the certificate traffic it imitates): on [Outsider_publishes]
    the outsider signs its own gossipsub envelope for [Cert_c_prime] - a
    valid signature over its OWN identity, so the envelope layer cannot
    reject it (consensus.rs:342-362) - and publishes on the certificate
    topic; the authorized-publisher containment is then the only gate that
    drops the frame (consensus.rs:1504-1508). *)
type outsider = Outsider_unchosen | Outsider_silent | Outsider_publishes

(** Total order on outsider choices for {!state_compare}. *)
let outsider_index = function
  | Outsider_unchosen -> 0
  | Outsider_silent -> 1
  | Outsider_publishes -> 2

(** See {!outsider_index}. *)
let outsider_compare a b = Int.compare (outsider_index a) (outsider_index b)

(** Whose delivery of [Cert_c] is deferred by one deliver phase
    (bounded-delay fairness as in {!Tn_model}: deferred at Deliver-R1,
    forced at Deliver-R2). The deferral window is the reachable state in
    which [Cert_c] is published yet the deferred subscriber's view still
    collides with the crash branch - the card's false-witness pair. *)
type delay = Delay_unchosen | No_delay | Delay_v1 | Delay_v2

(** Total order on delay choices for {!state_compare}. *)
let delay_index = function
  | Delay_unchosen -> 0
  | No_delay -> 1
  | Delay_v1 -> 2
  | Delay_v2 -> 3

(** See {!delay_index}. *)
let delay_compare a b = Int.compare (delay_index a) (delay_index b)

(** The subscriber whose [Cert_c] delivery the delay choice defers. *)
let delayed_validator = function
  | Delay_unchosen -> None
  | No_delay -> None
  | Delay_v1 -> Some Validator.V1
  | Delay_v2 -> Some Validator.V2

(** The phase machine: the R1 slice of the round structure that the anchor
    certificate's publish-and-deliver lifecycle occupies ([Propose], [Vote],
    [Certify] are Propose/Vote/Certify R1), the two deliver phases
    (deferral, then forced repair), and the terminal stutter. *)
type phase = Propose | Vote | Certify | Deliver_r1 | Deliver_r2 | Done

(** Total order on phases for {!state_compare}. *)
let phase_index = function
  | Propose -> 0
  | Vote -> 1
  | Certify -> 2
  | Deliver_r1 -> 3
  | Deliver_r2 -> 4
  | Done -> 5

(** See {!phase_index}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** Per-subscriber local state - the knowledge ground for K_i:
    [voted_anchor] is i's own vote record on the anchor header (the bit that
    makes the crash-post-vote branch view-identical to the cooperative run);
    [delivered_c] / [delivered_c_prime] are the application-layer delivery
    bits (consensus.rs:1004-1047). Publish acts, the strategy branch, the
    outsider's attempt, and other nodes' deliveries are global facts,
    invisible to the local view. *)
type local = {
  voted_anchor : bool;
  delivered_c : bool;
  delivered_c_prime : bool;
}

(** The empty local: nothing voted, nothing delivered. Also the constant
    view of the non-agent validators V0 and V3. *)
let local_empty =
  { voted_anchor = false; delivered_c = false; delivered_c_prime = false }

(** Total order on locals, field-lexicographic over ALL fields. *)
let local_compare l1 l2 =
  let c = Bool.compare l1.voted_anchor l2.voted_anchor in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Bool.compare l1.delivered_c l2.delivered_c in
    if Bool.not (Int.equal c1 0) then c1
    else Bool.compare l1.delivered_c_prime l2.delivered_c_prime

(** Validator-keyed finite maps for the locals. *)
module Validator_map = Map.Make (Validator)

(** The global state. [published_c] and [published_c_prime] are the monotone
    publish-history bits of the card: set when the publish act happens
    (V0's aggregate-and-publish for [Cert_c], O's attempt for
    [Cert_c_prime]), never cleared, and functionally determined by
    (phase, strategy, outsider) - so they cost no extra reachable states. *)
type state = {
  phase : phase;
  strategy : strategy;
  outsider : outsider;
  delay : delay;
  published_c : bool;
  published_c_prime : bool;
  locals : local Validator_map.t;
}

(** Total order over ALL fields, as {!System.Make} requires. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = strategy_compare s1.strategy s2.strategy in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = outsider_compare s1.outsider s2.outsider in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = delay_compare s1.delay s2.delay in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.published_c s2.published_c in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 =
              Bool.compare s1.published_c_prime s2.published_c_prime
            in
            if Bool.not (Int.equal c5 0) then c5
            else Validator_map.compare local_compare s1.locals s2.locals

(** The ordered global-state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** The ordered view module: a validator's view is a {!local}. *)
module View = struct
  type t = local

  let compare = local_compare
end

(** The honest validators: the range of the no-outsider-frame clause. *)
let honest = [ Validator.V0; Validator.V1; Validator.V2 ]

(** The honest non-author committee subscribers - the modeled delivery
    targets for [Cert_c] and the ONLY knowledge agents of this family. V0
    is excluded because its instance of the statement collapses (the
    operand is its own publish act); V3 is a passive committee slot whose
    deliveries are elided (no atom quantifies over it). *)
let subscribers = [ Validator.V1; Validator.V2 ]

(** The single initial state: Propose phase, every hidden choice
    unresolved, no publish acts, empty locals. *)
let initial =
  {
    phase = Propose;
    strategy = Strategy_unchosen;
    outsider = Outsider_unchosen;
    delay = Delay_unchosen;
    published_c = false;
    published_c_prime = false;
    locals =
      List.fold_left
        (fun acc v -> Validator_map.add v local_empty acc)
        Validator_map.empty roster;
  }

(** The local of [v], empty when absent - total by construction. *)
let local_of st v =
  Option.fold ~none:local_empty ~some:Fun.id
    (Validator_map.find_opt v st.locals)

(** Rewrite one validator's local through [f]. *)
let update_local v f st =
  { st with locals = Validator_map.add v (f (local_of st v)) st.locals }

(** Gate deletion for the confirm-by-mutation pin. [Drop_publisher_auth]
    deletes the authorized-publisher containment inside verify_gossip (the
    [auth.contains(&bls_key)] arm,
    crates/network-libp2p/src/consensus.rs:1504-1508): the outsider's
    validly-signed [Cert_c_prime] then passes every remaining check (the
    envelope signature is O's own and verifies; the size bound does not
    bite) and is delivered, so [Delivered (i, Cert_c_prime)] becomes
    reachable at states where no committee member ever published it. No
    sibling path repairs the deletion (the Unbounded_delay lesson):
    {!deliver_c_prime} is the unique writer of the [delivered_c_prime]
    bits, the bits are monotone, and neither the model nor the code path
    has a second committee-containment check behind the deleted one. *)
type mutation = Pristine | Drop_publisher_auth

(** Propose: resolve the hidden strategy branch into BOTH branches (the
    {!Tn_model} hidden-branching pattern). The anchor header itself is
    proposed in both branches; header existence is not quantified over, so
    it stays implicit. *)
let propose st =
  List.map
    (fun strategy -> { st with strategy; phase = Vote })
    [ Cooperate; Leader_crash_post_vote ]

(** Vote: the subscribers record their votes on the anchor header -
    identically in both strategy branches, which is exactly what makes the
    post-vote crash collide with the cooperative run in their views. V0's
    and V3's votes are elided: the quorum arithmetic behind V0's
    aggregation is pinned by the parent model's statements (S1/S4), not by
    this family. *)
let vote st =
  [
    {
      (List.fold_left
         (fun acc v ->
           update_local v (fun l -> { l with voted_anchor = true }) acc)
         st subscribers)
      with
      phase = Certify;
    };
  ]

(** Certify: resolve the outsider sub-choice into both branches. Under
    [Cooperate], V0 aggregates [Cert_c] and performs the publish act
    (publish_certificate,
    crates/consensus/primary/src/network/mod.rs:423-428) - the
    [published_c] history bit; under [Leader_crash_post_vote] V0 is omitted
    from this phase onward, so no publish ever happens. On
    [Outsider_publishes], O's publish act sets [published_c_prime]. *)
let certify st =
  let published_c =
    match st.strategy with
    | Strategy_unchosen -> false
    | Cooperate -> true
    | Leader_crash_post_vote -> false
  in
  List.map
    (fun outsider ->
      {
        st with
        outsider;
        published_c;
        published_c_prime =
          (match outsider with
          | Outsider_unchosen -> false
          | Outsider_silent -> false
          | Outsider_publishes -> true);
        phase = Deliver_r1;
      })
    [ Outsider_silent; Outsider_publishes ]

(** Deliver [Cert_c] to every subscriber except the deferred one:
    verify_gossip accepts the frame - V0's key is contained in the topic's
    authorized set (consensus.rs:1491-1514) - and acceptance forwards it to
    the application layer (consensus.rs:1004-1047). *)
let deliver_c skip st =
  List.fold_left
    (fun acc v ->
      if Option.fold ~none:false ~some:(Validator.equal v) skip then acc
      else update_local v (fun l -> { l with delivered_c = true }) acc)
    st subscribers

(** The fate of the outsider frame. Pristine: verify_gossip rejects it -
    O's resolved key is not contained in the topic's authorized set
    (Reject(UnauthorizedAuthor), consensus.rs:1504-1512) - so no delivery
    bit is ever written. Under {!Drop_publisher_auth} the containment is
    gone and the accepted frame is delivered to every honest node in one
    step; the delay choice models the anchor's bounded delivery
    specifically, and the pin needs only reachability of the outsider
    delivery. *)
let deliver_c_prime mut st =
  match mut with
  | Pristine -> st
  | Drop_publisher_auth ->
      if st.published_c_prime then
        List.fold_left
          (fun acc v ->
            update_local v (fun l -> { l with delivered_c_prime = true }) acc)
          st honest
      else st

(** Deliver-R1: resolve the delay choice into all three branches when
    [Cert_c] is in flight (the deferred subscriber is repaired at
    Deliver-R2); in the crash branch nothing is in flight and the choice
    degenerates to [No_delay]. The outsider frame's fate is applied in the
    same phase. *)
let deliver_r1 mut st =
  let with_c_prime = deliver_c_prime mut st in
  if st.published_c then
    List.map
      (fun d ->
        {
          (deliver_c (delayed_validator d) with_c_prime) with
          delay = d;
          phase = Deliver_r2;
        })
      [ No_delay; Delay_v1; Delay_v2 ]
  else [ { with_c_prime with delay = No_delay; phase = Deliver_r2 } ]

(** Deliver-R2: the forced repair - the deferred subscriber receives
    [Cert_c] (delivery is bounded, exactly as {!Tn_model} forces the
    delayed anchor at Deliver R2) and the run terminates. *)
let deliver_r2 st =
  let repaired =
    Option.fold ~none:st
      ~some:(fun v ->
        if st.published_c then
          update_local v (fun l -> { l with delivered_c = true }) st
        else st)
      (delayed_validator st.delay)
  in
  [ { repaired with phase = Done } ]

(** The mutation-parameterized transition relation; [Done] is terminal and
    the kernel stutter-closes it. *)
let next_with mut st =
  match st.phase with
  | Propose -> propose st
  | Vote -> vote st
  | Certify -> certify st
  | Deliver_r1 -> deliver_r1 mut st
  | Deliver_r2 -> deliver_r2 st
  | Done -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The atom vocabulary: exactly what the family's statement quantifies
    over, plus the vote-record bit its false witness names. *)
type atom =
  | Delivered of Validator.t * msg
      (** v's node accepted the frame from the certificate topic and
          forwarded it to the application layer (consensus.rs:1004-1047);
          for [Cert_c_prime] this is the event the authorized-publisher
          gate makes unreachable *)
  | Committee_published of msg
      (** some CURRENT committee member performed the publish act for the
          frame. For [Cert_c] the only committee publish act in the model
          is V0's aggregate-and-publish (mod.rs:423-428), so the
          existential collapses to the [published_c] history bit; for
          [Cert_c_prime] it is false at every reachable state - O is not
          committee *)
  | Outsider_published
      (** the phantom outsider O performed the publish act for
          [Cert_c_prime] - a global state fact, not a validator's act *)
  | Anchor_voted of Validator.t
      (** v's own vote record on the anchor header - the local bit the
          card's false witness names *)

(** Truth of an atom at a state. *)
let label a st =
  match a with
  | Delivered (v, Cert_c) -> (local_of st v).delivered_c
  | Delivered (v, Cert_c_prime) -> (local_of st v).delivered_c_prime
  | Committee_published Cert_c -> st.published_c
  | Committee_published Cert_c_prime -> false
  | Outsider_published -> st.published_c_prime
  | Anchor_voted v -> (local_of st v).voted_anchor

(** Render an atom with the surface notation of the statement docs. *)
let atom_to_string = function
  | Delivered (v, m) ->
      "delivered(" ^ Validator.to_string v ^ "," ^ msg_to_string m ^ ")"
  | Committee_published m -> "committee-published(" ^ msg_to_string m ^ ")"
  | Outsider_published -> "outsider-published(C')"
  | Anchor_voted v -> "anchor-voted(" ^ Validator.to_string v ^ ")"

(** View projection: the knowledge agents V1 and V2 see exactly their
    local; V0 and V3 are not knowledge agents in this family and get a
    constant empty view, so they can never ground K and never appear under
    K / Everyone / Common in the statements. *)
let view v st =
  match v with
  | Validator.V1 | Validator.V2 -> local_of st v
  | Validator.V0 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      local_empty

(** The exact CTLK checker over this family's finite interpreted system. *)
module Checker = System.Make (State) (View)

(** The spec under a mutation: same initial state, view, and labeling; only
    the transition relation carries the gate deletion. *)
let spec_of mut = { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine system. *)
let make () = Checker.make spec
