(** Peer-scoring/ban family: the fatal content-fault charge routing and the
    committee TrustBasis exemption of telcoin-network's libp2p peer manager,
    abstracted to a finite interpreted system on the shared kernel
    {!Denote.Make}.

    Role mapping of the four {!Validator.t} slots: [V0], [V1], [V2] are the
    HONEST knowledge agents - their view is exactly their peer-manager local
    (evidence held, fatal charge issued, ban applied) and they are the only
    validators that may appear under [K]/[Everyone]/[Common]. [V3] is the
    Byzantine peer: it carries NO peer-score state, its view is the constant
    empty local, and it never appears as a knowledge agent.

    The hidden Byzantine branch is resolved at the first transition into
    [Cooperate] plus four [Invalid_gossip] delivery plans. Every invalid plan
    is protocol-transparent on the consensus path (same headers, votes and
    certificates as [Cooperate]) plus ONE invalidly-authored side gossip
    message; because the consensus path contributes nothing that
    distinguishes the branches, it is abstracted away entirely and honest
    pre-delivery views collide with the [Cooperate] branch - the collision
    that keeps [K] contingent.

    Modeled mechanisms, cited against Telcoin-Association/telcoin-network:
    - gossip deep-validation failure raises a content-fault network error
      whose severity is Fatal (error taxonomy
      crates/consensus/primary/src/error/network.rs:73-139 and 141-206;
      gossip processing crates/network-libp2p/src/consensus.rs:1004-1100,
      verdict handling consensus.rs:2046-2098);
    - the fatal charge routes to the message's UNFORGEABLE authenticated
      author, never the propagation source that relayed it (the
      is_author_content_fault selection,
      crates/consensus/primary/src/network/mod.rs:1780-1812, branch at
      mod.rs:1803 - [Charge_relayer] deletes exactly this branch);
    - an honest node forwards gossip on the mesh before the application-level
      deep-validation verdict lands, so an honest relayer can propagate the
      bad payload (publish/forward path consensus.rs:346-359 and 783-795);
    - Fatal penalty processing jumps the score to the ban floor in one step
      (crates/network-libp2p/src/peers/manager.rs:424-443, score.rs:84-100,
      ban application all_peers.rs:847-895 and 261-303) - no score arithmetic
      is modeled, only the boolean ban outcome;
    - the TrustBasis exemption short-circuits the score model for committee
      validators, suppressing the ban with a warn log (peer.rs:209-237,
      bypass at peer.rs:218-231, exemption basis peer.rs:239-253 -
      [No_exemption] deletes exactly this short-circuit).

    Exemption asymmetry, per the grounding note on statement #2: [V3] sits in
    a seeded current-committee slot, so it is exempt at every charging state;
    the honest peers are modeled as mesh relayers charged inside the
    committee-slot seeding-lag window (all_peers.rs:1126-1132), where the
    TrustBasis lookup misses and the author-routing layer is the SOLE
    protection - so they are NON-exempt. This is load-bearing: it is what
    makes the [Charge_relayer] mutation form a real ban on the honest
    relayer instead of being silently repaired by the exemption.

    Unforgeability by construction: the bad envelope carries author [V3] and
    exists only downstream of [V3]'s send, so an honest node holding it can
    ground [K_i (authored_bad V3)] - no reachable state gives it that local
    evidence without [V3] having authored the payload. *)

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

(** The honest knowledge agents of this family, in canonical order. *)
let honest = [ Validator.V0; Validator.V1; Validator.V2 ]

(** The Byzantine peer: authors the one invalid side message, carries no
    peer-score state, and is never a knowledge agent. *)
let byz = Validator.V3

(** Phase machine: [Choose] resolves the hidden Byzantine branch and delivers
    the first hop of the invalid message; [Forward] delivers the single relay
    hop of the via-branches (a no-op elsewhere); [Done] is terminal and
    stutter-closed by the kernel. *)
type phase = Choose | Forward | Done

(** Total order witness for {!phase}. *)
let phase_index = function Choose -> 0 | Forward -> 1 | Done -> 2

(** Total deterministic comparison for {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** Render a phase for debugging output. *)
let phase_to_string = function
  | Choose -> "choose"
  | Forward -> "forward"
  | Done -> "done"

(** The hidden Byzantine branch, resolved at the first transition.
    [Cooperate] follows the protocol and authors nothing bad. The four
    invalid plans merge the card's target sub-choice {V1-only, all-honest}
    with its relay-path sub-choice {direct, via-V1, via-V2}:
    [Invalid_to_v1] delivers the bad message directly to V1 only (the
    K-contingency witness branch of statement #5), [Invalid_broadcast]
    delivers directly to every honest peer (the bcast branch), and
    [Invalid_via_v1]/[Invalid_via_v2] deliver to one honest relayer which
    forwards to the other honest victim one bounded-delay hop later (the
    relay witness branch of statement #2). *)
type strategy =
  | Strat_unchosen
  | Cooperate
  | Invalid_to_v1
  | Invalid_broadcast
  | Invalid_via_v1
  | Invalid_via_v2

(** Total order witness for {!strategy}. *)
let strategy_index = function
  | Strat_unchosen -> 0
  | Cooperate -> 1
  | Invalid_to_v1 -> 2
  | Invalid_broadcast -> 3
  | Invalid_via_v1 -> 4
  | Invalid_via_v2 -> 5

(** Total deterministic comparison for {!strategy}. *)
let strategy_compare a b = Int.compare (strategy_index a) (strategy_index b)

(** Render a strategy for debugging output. *)
let strategy_to_string = function
  | Strat_unchosen -> "unchosen"
  | Cooperate -> "cooperate"
  | Invalid_to_v1 -> "invalid-to-v1"
  | Invalid_broadcast -> "invalid-broadcast"
  | Invalid_via_v1 -> "invalid-via-v1"
  | Invalid_via_v2 -> "invalid-via-v2"

(** The hidden RUN-FACT byz(V3): the branch chosen this run is an
    Invalid_gossip plan - equivalently, V3 has authored the invalid payload
    this run. Deliberately not the rigid designation "V3 is the Byzantine
    validator", which would make [K (i, byz)] trivially true everywhere. *)
let invalid_gossip = function
  | Strat_unchosen -> false
  | Cooperate -> false
  | Invalid_to_v1 -> true
  | Invalid_broadcast -> true
  | Invalid_via_v1 -> true
  | Invalid_via_v2 -> true

(** Per-honest peer-manager local - the knowledge ground for [K_i].
    [evidence]: i holds the invalid envelope (delivered and deep-validation
    failed); [charged]: the peer i fatally charged with the content fault
    (at most one - i receives the envelope at most once); [banned]: the peer
    i banned as a result (at most one; identically [None] in the pristine
    model because the charge routes to the exempt author). Global fields
    (the branch taken, other peers' locals, in-flight copies) are invisible
    to it. *)
type local = {
  evidence : bool;
  charged : Validator.t option;
  banned : Validator.t option;
}

(** The empty local: no evidence, no charge, no ban. *)
let local_empty = { evidence = false; charged = None; banned = None }

(** Total deterministic comparison over ALL local fields. *)
let local_compare l1 l2 =
  let c = Bool.compare l1.evidence l2.evidence in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Option.compare Validator.compare l1.charged l2.charged in
    if Bool.not (Int.equal c1 0) then c1
    else Option.compare Validator.compare l1.banned l2.banned

(** Maps keyed by validator identity. *)
module Validator_map = Map.Make (Validator)

(** The global state: phase, hidden branch, per-validator locals (V3's local
    is never written and stays {!local_empty}). *)
type state = {
  phase : phase;
  strategy : strategy;
  locals : local Validator_map.t;
}

(** Total deterministic comparison over ALL global-state fields. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = strategy_compare s1.strategy s2.strategy in
    if Bool.not (Int.equal c1 0) then c1
    else Validator_map.compare local_compare s1.locals s2.locals

(** Ordered global-state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** Ordered view module for {!System.Make}: a view is a peer-manager local. *)
module View = struct
  type t = local

  let compare = local_compare
end

(** The local of [v] in [state], {!local_empty} when absent. *)
let local_of state v =
  Option.fold ~none:local_empty ~some:Fun.id
    (Validator_map.find_opt v state.locals)

(** View projection: an honest validator sees exactly its own peer-manager
    local; the Byzantine [V3] is not a knowledge agent in this family and
    gets the constant empty view. *)
let view v state =
  match v with
  | Validator.V0 | Validator.V1 | Validator.V2 -> local_of state v
  | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7
  | Validator.V8 | Validator.V9 ->
      local_empty

(** The single initial state: branch unchosen, every local empty. *)
let initial =
  {
    phase = Choose;
    strategy = Strat_unchosen;
    locals =
      List.fold_left
        (fun acc v -> Validator_map.add v local_empty acc)
        Validator_map.empty roster;
  }

(** Gate deletions for the confirm-by-mutation tests. [Charge_relayer]
    deletes the is_author_content_fault author selection (network
    mod.rs:1803): the fatal charge lands on the envelope's last-hop sender
    (the propagation source) instead of the authenticated author, so the
    relayed run bans the honest non-exempt relayer - pinning statement #2.
    [No_exemption] deletes the TrustBasis short-circuit (peer.rs:218-231):
    Fatal penalties reach the ban step even for committee validators, so
    every evidence-holding honest node bans V3 - pinning statement #5. *)
type mutation = Pristine | Charge_relayer | No_exemption

(** TrustBasis exemption at the charging state: V3's current-committee slot
    is seeded, so V3 is exempt (peer.rs:209-237, 239-253); the honest peers
    are modeled as mesh relayers inside the committee-slot seeding-lag
    window (all_peers.rs:1126-1132), so they are NOT exempt - the author
    routing is their sole protection, which is exactly what makes the
    [Charge_relayer] mutation form a real ban. *)
let committee_exempt p = Validator.equal p byz

(** Charge routing (network mod.rs:1780-1812): the pristine model charges
    the envelope's unforgeable authenticated [author]; [Charge_relayer]
    deletes the author selection at mod.rs:1803 so the charge lands on the
    last-hop [sender] instead. On a direct hop the sender IS the author, so
    the mutation bites only on the relayed copies. *)
let charge_target mut ~author ~sender =
  match mut with
  | Pristine -> author
  | No_exemption -> author
  | Charge_relayer -> sender

(** Ban gate on a Fatal content-fault charge (manager.rs:424-443,
    score.rs:84-100, all_peers.rs:847-895): the exemption short-circuit
    (peer.rs:218-231) suppresses the ban for exempt peers; [No_exemption]
    deletes the short-circuit so Fatal always bans. *)
let ban_gate mut target l =
  match mut with
  | Pristine | Charge_relayer ->
      if committee_exempt target then l else { l with banned = Some target }
  | No_exemption -> { l with banned = Some target }

(** Rebuild the state with [v]'s local passed through [f]. *)
let update_local v f state =
  { state with locals = Validator_map.add v (f (local_of state v)) state.locals }

(** Delivery of the invalid envelope (author [V3], last hop [sender]) to
    honest [i]: deep validation fails (consensus.rs:1004-1100, verdict
    handling consensus.rs:2046-2098), so atomically i records the evidence,
    issues the routed fatal charge, and runs the ban gate. Folding the
    penalty micro-transition into delivery keeps the reachable set free of
    half-processed charge states. *)
let receive mut ~sender i state =
  let target = charge_target mut ~author:byz ~sender in
  update_local i
    (fun l -> ban_gate mut target { l with evidence = true; charged = Some target })
    state

(** First-hop recipients of the invalid message, per delivery plan: the
    direct plans reach their targets, the via-plans reach only the relayer.
    Cooperative branches send nothing. *)
let first_hop = function
  | Strat_unchosen -> []
  | Cooperate -> []
  | Invalid_to_v1 -> [ Validator.V1 ]
  | Invalid_broadcast -> honest
  | Invalid_via_v1 -> [ Validator.V1 ]
  | Invalid_via_v2 -> [ Validator.V2 ]

(** The single relay hop [(relayer, victim)] of the via-branches: the honest
    relayer forwards the gossip before its own deep-validation verdict lands
    (mesh propagation, consensus.rs:346-359 and 783-795), so the victim
    receives the bad payload with the relayer as propagation source one
    bounded-delay step later. *)
let relay_hop = function
  | Strat_unchosen -> None
  | Cooperate -> None
  | Invalid_to_v1 -> None
  | Invalid_broadcast -> None
  | Invalid_via_v1 -> Some (Validator.V1, Validator.V2)
  | Invalid_via_v2 -> Some (Validator.V2, Validator.V1)

(** Resolve the hidden branch to [strategy], author the bad payload (in the
    invalid plans), and deliver its first hop; the branch choice, the send,
    and the first delivery are one transition, so the only branch-unchosen
    state is the initial one (the tn_model hidden-branching pattern). *)
let resolve mut strategy state =
  let sent =
    List.fold_left
      (fun acc i -> receive mut ~sender:byz i acc)
      { state with strategy }
      (first_hop strategy)
  in
  { sent with phase = Forward }

(** Deliver the relay hop where the plan has one (the via-branches), then
    terminate; every other branch just steps to [Done]. *)
let forward mut state =
  Option.fold
    ~none:{ state with phase = Done }
    ~some:(fun (relayer, victim) ->
      { (receive mut ~sender:relayer victim state) with phase = Done })
    (relay_hop state.strategy)

(** The mutation-parameterized transition relation: [Choose] fans out over
    the five resolvable branches, [Forward] delivers the relay hop, [Done]
    is terminal ([make] stutter-closes it). *)
let next_with mut state =
  match state.phase with
  | Choose ->
      List.map
        (fun strategy -> resolve mut strategy state)
        [ Cooperate; Invalid_to_v1; Invalid_broadcast; Invalid_via_v1; Invalid_via_v2 ]
  | Forward -> [ forward mut state ]
  | Done -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** Atom vocabulary of the BAN family - exactly what the two statements
    quantify over, plus the delivery-evidence probe the witness tests use. *)
type atom =
  | Authored_bad of Validator.t
      (** p authored the invalid payload this run - true for V3 from its
          send onward in the invalid branches, false for every honest p in
          every reachable state (unforgeability by construction) *)
  | Fatal_charge of Validator.t * Validator.t
      (** [Fatal_charge (i, p)]: i has issued its fatal content-fault charge
          against p *)
  | Banned of Validator.t * Validator.t
      (** [Banned (i, j)]: i has banned j *)
  | Evidence of Validator.t
      (** i holds the delivered invalid envelope *)
  | Byz_v3  (** the hidden run-fact byz(V3): see {!invalid_gossip} *)
  | Bcast  (** the branch is the all-honest direct broadcast plan *)
  | At_done  (** the terminal phase *)

(** Atom valuation over global states. *)
let label a state =
  match a with
  | Authored_bad p -> (
      match p with
      | Validator.V3 -> invalid_gossip state.strategy
      | Validator.V0 | Validator.V1 | Validator.V2 | Validator.V4
      | Validator.V5 | Validator.V6 | Validator.V7 | Validator.V8
      | Validator.V9 ->
          false)
  | Fatal_charge (i, p) ->
      Option.fold ~none:false ~some:(Validator.equal p) (local_of state i).charged
  | Banned (i, j) ->
      Option.fold ~none:false ~some:(Validator.equal j) (local_of state i).banned
  | Evidence i -> (local_of state i).evidence
  | Byz_v3 -> invalid_gossip state.strategy
  | Bcast -> (
      match state.strategy with
      | Invalid_broadcast -> true
      | Strat_unchosen | Cooperate | Invalid_to_v1 | Invalid_via_v1
      | Invalid_via_v2 ->
          false)
  | At_done -> (
      match state.phase with Done -> true | Choose | Forward -> false)

(** Render an atom with the surface names used in the statement docs. *)
let atom_to_string = function
  | Authored_bad p -> "authored-bad(" ^ Validator.to_string p ^ ")"
  | Fatal_charge (i, p) ->
      "fatal-charge(" ^ Validator.to_string i ^ "," ^ Validator.to_string p
      ^ ",content-fault)"
  | Banned (i, j) ->
      "banned(" ^ Validator.to_string i ^ "," ^ Validator.to_string j ^ ")"
  | Evidence i -> "evidence(" ^ Validator.to_string i ^ ",v3)"
  | Byz_v3 -> "byz(v3)"
  | Bcast -> "bcast"
  | At_done -> "done"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The interpreted-system spec under a mutation: single initial state,
    mutation-parameterized transitions, peer-manager view projection. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine system. *)
let make () = Checker.make spec
