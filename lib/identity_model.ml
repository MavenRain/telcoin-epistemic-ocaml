(** The signed peer-record identity binding of telcoin-network, abstracted
    to an isolated finite interpreted system on the shared kernel
    {!System.Make}: an honest node confirms a remote validator's
    (BLS key, libp2p PeerId) binding only through a signature-verified
    NodeRecord, so a confirmed identity carries knowledge of the remote
    signing act.

    Mechanisms modeled, keyed to Telcoin-Association/telcoin-network:
    - NodeRecord admission [peer_record_valid]
      (crates/network-libp2p/src/consensus.rs:529-565); its signature gate
      [NodeRecord::decode_and_verify] (consensus.rs:534-535) is encoded as
      membership in the global monotone [signed] set - BLS unforgeability
      by construction, no crypto detail. The mutation
      {!Drop_record_verify} deletes exactly this gate;
    - admission scope: committee key or self-advertised source
      (consensus.rs:1912-1944; [add_self_advertised_peer]
      crates/network-libp2p/src/peers/all_peers.rs:213-256);
    - confirmed-identity bookkeeping on the peer manager
      (crates/network-libp2p/src/peers/manager.rs:799-838 and 851-875,
      peers/all_peers.rs:190-210, peers/types.rs:13-34): the per-honest
      partial map [confirmed : peer -> validator];
    - startup record publish over the static committee mesh
      (consensus.rs:397-440, 587-600) and record delivery through the kad
      record paths, both gated by [peer_record_valid]
      (consensus.rs:1602-1613, 1744-1771, 2014-2024). Records are pushed at
      {!Propose} and delivered at {!Deliver} under the house bounded-delay
      fairness - no separate delay branch: the Propose-to-Deliver phase
      window supplies the in-flight states the false witness needs;
    - operator-provisioned bindings (bootstrap/trusted provisioning,
      crates/node/src/manager/node/start_epoch.rs:780-782; kad-DB restore,
      peers/all_peers.rs:823-829): each node's own binding, the
      {!Provisioned} escape hatch of the self conjuncts.

    Role mapping of the four validator slots: V0, V1, V2 are the honest
    committee nodes and the only knowledge agents; V3 is the Byzantine
    subject whose hidden identity strategy (publish, withhold, forge) is
    resolved into all branches at the first transition, so honest
    pre-delivery views collide across branches - that collision is what
    keeps K contingent. V3 is not a knowledge agent: its view is constantly
    empty and it never appears under K, Everyone, or Common. *)

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

(** The libp2p PeerId space, finite (peers/types.rs:13-34): the canonical
    peer id of each committee slot. [P3] is the fresh peer id V3 connects
    under; the forged record claims V1's committee key at [P3]. [P4]..[P9]
    are the canonical ids of the extended tn committee slots, outside this
    four-validator family. *)
type peer = P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9

(** Total order witness for {!peer}. *)
let peer_index = function
  | P0 -> 0
  | P1 -> 1
  | P2 -> 2
  | P3 -> 3
  | P4 -> 4
  | P5 -> 5
  | P6 -> 6
  | P7 -> 7
  | P8 -> 8
  | P9 -> 9

(** Total deterministic comparison over {!peer}. *)
let peer_compare a b = Int.compare (peer_index a) (peer_index b)

(** Equality on {!peer}, derived from {!peer_compare}. *)
let peer_equal a b = Int.equal (peer_compare a b) 0

(** Render a {!peer} for atom strings. *)
let peer_to_string = function
  | P0 -> "p0"
  | P1 -> "p1"
  | P2 -> "p2"
  | P3 -> "p3"
  | P4 -> "p4"
  | P5 -> "p5"
  | P6 -> "p6"
  | P7 -> "p7"
  | P8 -> "p8"
  | P9 -> "p9"

(** The canonical peer id each validator advertises (the genuine binding
    subject of its NodeRecord, consensus.rs:529-565). *)
let peer_of = function
  | Validator.V0 -> P0
  | Validator.V1 -> P1
  | Validator.V2 -> P2
  | Validator.V3 -> P3
  | Validator.V4 -> P4
  | Validator.V5 -> P5
  | Validator.V6 -> P6
  | Validator.V7 -> P7
  | Validator.V8 -> P8
  | Validator.V9 -> P9

(** A claimed (validator key, peer id) binding. The type serves two roles,
    distinguished by the field it sits in: an entry of the global [signed]
    set is a binding the named validator actually signed (the private
    signing act behind NodeRecord::sign); an entry of [pushed] or a local
    [held] set is the claim a broadcast NodeRecord carries, verified only at
    admission (consensus.rs:529-565). *)
type binding = { b_validator : Validator.t; b_peer : peer }

(** Total deterministic comparison over {!binding} - all fields. *)
let binding_compare b1 b2 =
  let c = Validator.compare b1.b_validator b2.b_validator in
  if Int.equal c 0 then peer_compare b1.b_peer b2.b_peer else c

(** Render a {!binding} for atom strings. *)
let binding_to_string b =
  Validator.to_string b.b_validator ^ "@" ^ peer_to_string b.b_peer

(** Ordered module over {!peer} for map keys. *)
module Peer = struct
  type t = peer

  let compare = peer_compare
end

(** Per-node confirmed-identity maps are keyed by peer id
    (peers/all_peers.rs:190-210). *)
module Peer_map = Map.Make (Peer)

(** Ordered module over {!binding} for set elements. *)
module Binding = struct
  type t = binding

  let compare = binding_compare
end

(** Sets of bindings: the global signed set, the in-flight records, and the
    per-node record stores. *)
module Binding_set = Set.Make (Binding)

(** Per-validator local-state table. *)
module Validator_map = Map.Make (Validator)

(** The hidden Byzantine identity strategy, resolved at the first
    transition out of {!Propose}: [Cooperate] signs and publishes the
    genuine (V3, p3) NodeRecord; [Silent] withholds - V3 never performs the
    signing act, so no (V3, p3) binding ever exists; [Forge_record] pushes
    an unsigned record claiming V1's committee key at p3 with
    source == advertised - it passes the admission scope but is dropped by
    the [decode_and_verify] signature gate (consensus.rs:534-535).
    [Strat_unchosen] is the pre-choice initial value. *)
type strategy = Strat_unchosen | Cooperate | Silent | Forge_record

(** Total order witness for {!strategy}. *)
let strategy_index = function
  | Strat_unchosen -> 0
  | Cooperate -> 1
  | Silent -> 2
  | Forge_record -> 3

(** Total deterministic comparison over {!strategy}. *)
let strategy_compare a b = Int.compare (strategy_index a) (strategy_index b)

(** Render a {!strategy} for diagnostics. *)
let strategy_to_string = function
  | Strat_unchosen -> "unchosen"
  | Cooperate -> "cooperate"
  | Silent -> "silent"
  | Forge_record -> "forge-record"

(** The phase machine of one startup round: records are pushed on the
    transition out of {!Propose} (startup publish, consensus.rs:397-440),
    ride in flight through {!Vote} and {!Certify} (the intra-round window
    realizing the card's delivery delay without a new hidden choice), and
    are delivered and admitted on the transition out of {!Deliver}
    (kad record paths, consensus.rs:1602-1613, 1744-1771, 2014-2024).
    {!Done} is terminal; the kernel stutter-closes it. *)
type phase = Propose | Vote | Certify | Deliver | Done

(** Total order witness for {!phase}. *)
let phase_index = function
  | Propose -> 0
  | Vote -> 1
  | Certify -> 2
  | Deliver -> 3
  | Done -> 4

(** Total deterministic comparison over {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** Render a {!phase} for diagnostics. *)
let phase_to_string = function
  | Propose -> "propose"
  | Vote -> "vote"
  | Certify -> "certify"
  | Deliver -> "deliver"
  | Done -> "done"

(** Per-honest-validator local state - the knowledge ground for K_i:
    [held], the NodeRecords its kad store has admitted delivery of
    (consensus.rs:1602-1613); [confirmed], its peer-manager
    confirmed-identity map (manager.rs:799-838, all_peers.rs:190-210).
    Global fields (in-flight records, the signed set, the hidden strategy)
    are invisible to it. *)
type local = { held : Binding_set.t; confirmed : Validator.t Peer_map.t }

(** The empty local: no records held, nothing confirmed. Also the constant
    view of the non-agent V3. *)
let local_empty = { held = Binding_set.empty; confirmed = Peer_map.empty }

(** Total deterministic comparison over {!local} - all fields. *)
let local_compare l1 l2 =
  let c = Binding_set.compare l1.held l2.held in
  if Int.equal c 0 then
    Peer_map.compare Validator.compare l1.confirmed l2.confirmed
  else c

(** The global state: phase machine position, the hidden Byzantine identity
    strategy, the monotone set of bindings actually signed (unforgeable by
    construction), the broadcast records in flight, and the honest locals. *)
type state = {
  phase : phase;
  strategy : strategy;
  signed : Binding_set.t;
  pushed : Binding_set.t;
  locals : local Validator_map.t;
}

(** Total deterministic comparison over {!state} - all fields. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = strategy_compare s1.strategy s2.strategy in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Binding_set.compare s1.signed s2.signed in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Binding_set.compare s1.pushed s2.pushed in
        if Bool.not (Int.equal c3 0) then c3
        else Validator_map.compare local_compare s1.locals s2.locals

(** Ordered global-state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** Ordered view module for {!System.Make}: an honest node's local state. *)
module View = struct
  type t = local

  let compare = local_compare
end

(** The honest committee nodes - the only knowledge agents of this family. *)
let honest = [ Validator.V0; Validator.V1; Validator.V2 ]

(** The Byzantine identity subject. Never a knowledge agent. *)
let byz = Validator.V3

(** Project a validator's local state, defaulting to {!local_empty}. *)
let local_of state v =
  Option.fold ~none:local_empty ~some:Fun.id
    (Validator_map.find_opt v state.locals)

(** The view projection handed to the kernel: honest validators see exactly
    their local state; the non-agent V3 gets the constant empty view, so it
    can never ground knowledge and never appears under K / Everyone /
    Common. *)
let view v state =
  match v with
  | Validator.V0 | Validator.V1 | Validator.V2 -> local_of state v
  | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7
  | Validator.V8 | Validator.V9 ->
      local_empty

(** Replace one validator's local by an update of it. *)
let update_local v f state =
  { state with locals = Validator_map.add v (f (local_of state v)) state.locals }

(** The genuine bindings the honest nodes sign and push at startup
    (consensus.rs:397-440): each honest validator binds its own committee
    key to its canonical peer id. *)
let honest_bindings =
  List.map (fun v -> { b_validator = v; b_peer = peer_of v }) honest

(** The signing act V3 performs under each strategy: only [Cooperate]
    actually signs (V3, p3). [Silent] and [Forge_record] never sign - the
    forged claim (V1, p3) is NOT a signing act by V1, which is exactly what
    BLS unforgeability (consensus.rs:534-535) guarantees. *)
let byz_signing = function
  | Strat_unchosen -> []
  | Cooperate -> [ { b_validator = byz; b_peer = P3 } ]
  | Silent -> []
  | Forge_record -> []

(** The record V3 broadcasts under each strategy: [Cooperate] pushes its
    genuine record; [Silent] pushes nothing; [Forge_record] pushes the
    unsigned record claiming V1's committee key at p3
    (source == advertised, so only the signature gate stands between it and
    confirmation). *)
let byz_push = function
  | Strat_unchosen -> []
  | Cooperate -> [ { b_validator = byz; b_peer = P3 } ]
  | Silent -> []
  | Forge_record -> [ { b_validator = Validator.V1; b_peer = P3 } ]

(** The startup transition out of {!Propose}: resolve the hidden strategy,
    perform the signing acts, and broadcast the NodeRecords - which stay in
    flight until {!Deliver}. *)
let startup strategy state =
  let add_all base bs = List.fold_left (fun acc b -> Binding_set.add b acc) base bs in
  {
    state with
    phase = Vote;
    strategy;
    signed = add_all state.signed (List.append honest_bindings (byz_signing strategy));
    pushed = add_all state.pushed (List.append honest_bindings (byz_push strategy));
  }

(** Gate deletion for the confirm-by-mutation test: {!Drop_record_verify}
    deletes the [NodeRecord::decode_and_verify] signature gate inside
    [peer_record_valid] (consensus.rs:534-535), so the forged record
    validates and an honest node confirms a binding nobody signed. *)
type mutation = Pristine | Drop_record_verify

(** The signature gate of [peer_record_valid] (consensus.rs:534-535),
    encoded as membership in the unforgeable [signed] set. The mutation
    deletes it; no sibling admission path re-checks the signature, so the
    deletion is a real refuter. *)
let verify_gate mut b state =
  match mut with
  | Pristine -> Binding_set.mem b state.signed
  | Drop_record_verify -> true

(** The admission-scope disjunct of record admission: the claimed key must
    be a committee key, or the record must come from its advertised subject
    (consensus.rs:1912-1944, add_self_advertised_peer
    all_peers.rs:213-256). Every record this model pushes satisfies it -
    honest records claim committee keys, and the forged record is pushed by
    its self-advertised subject - so the modeled confirm premise reduces to
    delivery plus the signature gate. *)
let committee_key_or_advertised b =
  List.exists (fun v -> Validator.equal v b.b_validator) roster

(** The confirm rule (manager.rs:799-838, 851-875): for each delivered
    record, admit the claimed binding into the node's confirmed map iff the
    signature gate and the admission scope both pass. Fold order over the
    ordered set is deterministic; no two pushed records ever claim one peer
    id, so the map writes never collide. *)
let confirm mut state l =
  Binding_set.fold
    (fun b acc ->
      if verify_gate mut b state && committee_key_or_advertised b then
        { acc with confirmed = Peer_map.add b.b_peer b.b_validator acc.confirmed }
      else acc)
    state.pushed l

(** The delivery transition out of {!Deliver}: every in-flight record
    reaches every honest node's store (bounded-delay fairness, kad record
    paths consensus.rs:1602-1613, 1744-1771, 2014-2024), and the confirm
    rule runs on each. *)
let deliver mut state =
  {
    (List.fold_left
       (fun acc v ->
         update_local v
           (fun l ->
             confirm mut acc { l with held = Binding_set.union acc.pushed l.held })
           acc)
       state honest)
    with phase = Done;
  }

(** The mutation-parameterized transition relation: the hidden strategy
    branches at {!Propose}; {!Vote} and {!Certify} are the in-flight window;
    {!Deliver} delivers and confirms; {!Done} is terminal (the kernel
    stutter-closes it). *)
let next_with mut state =
  match state.phase with
  | Propose ->
      List.map
        (fun strategy -> startup strategy state)
        [ Cooperate; Silent; Forge_record ]
  | Vote -> [ { state with phase = Certify } ]
  | Certify -> [ { state with phase = Deliver } ]
  | Deliver -> [ deliver mut state ]
  | Done -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The single initial state: startup, nothing signed, nothing pushed,
    every honest local empty, strategy unchosen. *)
let initial =
  {
    phase = Propose;
    strategy = Strat_unchosen;
    signed = Binding_set.empty;
    pushed = Binding_set.empty;
    locals =
      List.fold_left
        (fun acc v -> Validator_map.add v local_empty acc)
        Validator_map.empty honest;
  }

(** The atom vocabulary of the identity family. *)
type atom =
  | Confirmed of Validator.t * peer * Validator.t
      (** [Confirmed (i, p, v)]: honest i's peer-manager confirmed map binds
          peer id p to validator v (manager.rs:799-838,
          all_peers.rs:190-210) *)
  | Signed_binding of Validator.t * peer
      (** [(v, p)] is in the global signed set: validator v actually
          performed the private signing act binding its BLS key to peer id
          p - the unforgeable fact behind decode_and_verify
          (consensus.rs:534-535) *)
  | Provisioned of Validator.t * Validator.t * peer
      (** [Provisioned (i, v, p)]: node i holds the (v, p) binding by
          operator provisioning rather than record admission - in this
          model exactly its own binding (bootstrap/trusted provisioning
          start_epoch.rs:780-782, kad-DB restore all_peers.rs:823-829); a
          rigid atom, true independent of the run *)
  | First_connect of Validator.t * Validator.t
      (** the startup dial from i to v over the static committee mesh
          (consensus.rs:713-756, start_epoch.rs:780-782): true exactly at
          the {!Propose} instant for distinct endpoints - the single
          startup connect event of the card's leads_to *)

(** Atom valuation over global states. *)
let label a state =
  match a with
  | Confirmed (i, p, v) ->
      Option.fold ~none:false ~some:(Validator.equal v)
        (Peer_map.find_opt p (local_of state i).confirmed)
  | Signed_binding (v, p) ->
      Binding_set.mem { b_validator = v; b_peer = p } state.signed
  | Provisioned (i, v, p) -> Validator.equal i v && peer_equal p (peer_of i)
  | First_connect (i, v) -> (
      match state.phase with
      | Propose -> Bool.not (Validator.equal i v)
      | Vote | Certify | Deliver | Done -> false)

(** Render an atom with the surface names used in the statement docs. *)
let atom_to_string = function
  | Confirmed (i, p, v) ->
      "confirmed(" ^ Validator.to_string i ^ "," ^ peer_to_string p ^ "->"
      ^ Validator.to_string v ^ ")"
  | Signed_binding (v, p) ->
      "signed-binding(" ^ binding_to_string { b_validator = v; b_peer = p } ^ ")"
  | Provisioned (i, v, p) ->
      "provisioned(" ^ Validator.to_string i ^ ","
      ^ binding_to_string { b_validator = v; b_peer = p }
      ^ ")"
  | First_connect (i, v) ->
      "first-connect(" ^ Validator.to_string i ^ "," ^ Validator.to_string v ^ ")"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The spec under a mutation: single initial state, mutation-parameterized
    transitions, honest-local views, atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
