(** Finite interpreted system for the ADMISSION family (DESIGN family
    ADMISSION, statements #4 ban-is-local-enforcement-and-internode-opaque and
    #7 established-connection-implies-known-remote-admission). A joint graph of
    THREE independent directed ban-pairs, each a generic temp-ban mechanism
    abstracted from telcoin-network's libp2p peer manager. File citations refer
    to Telcoin-Association/telcoin-network.

    The modeled mechanism, per pair (banner b, subject s):
    - a connection [conn(b,s)] in {Up, Down}, and a banner-LOCAL one-tick
      temp-ban flag [ban_b(s)] in {Unbanned, Banned} - a boolean, NO counter
      (the excess-peer [temporarily_banned] cache, manager.rs:85 / :331-342);
    - SEED: the banner atomically temp-bans and disconnects the subject in ONE
      transition (Up,Unbanned) -> (Down,Banned), touching only banner-local
      state (apply_peer_action atomicity; the [DisconnectWithPX] analogue). The
      atomicity is load-bearing: a split ban-then-close would expose a transient
      (Up,Banned) admitted-while-banned state that refutes both statements'
      admission conjuncts;
    - EXPIRY: on the next heartbeat the flag clears (Down,Banned) ->
      (Down,Unbanned), touching only banner-local state and sending NOTHING to
      anyone ([unban_temp_banned_peers], manager.rs:599-603). Expiry is why the
      severance conjunct is a weak-until (bans expire), not an AG;
    - SILENT_DIAL_RETRY: the subject silently redials and the connection is
      re-admitted iff not banned (Down,Unbanned) -> (Up,Unbanned); the admission
      denial is the sole guard ([peer_banned], manager.rs:396-403, inbound gate
      behavior.rs:102-105). No failure is observed on the subject's side, so the
      denial leaks no ban information across nodes.

    A never-expiring ban is a legal path: the kernel stutter-closes terminals,
    and an infinite run that advances only the OTHER pairs holds any one pair at
    (Down,Banned) forever - the weak-until's "or forever" branch. CRITICALLY no
    phase / heartbeat-tick component appears in ANY view: a validator cannot
    clock the deterministic one-tick expiry timer, which is exactly what makes
    the post-expiry state view-collide with the still-banned state.

    The three pairs and their reachable per-pair values {(Up,Unbanned),
    (Down,Banned),(Down,Unbanned)} (the fourth, (Up,Banned), is unreachable in
    the pristine model precisely because the retry guard forbids it):
    - P1 = (V1 -> O): V1 temp-bans the phantom peer O;
    - P2 = (V2 -> O): V2 temp-bans O;
    - P3 = (V2 -> V1): V2 temp-bans committee validator V1.

    Role mapping (knowledge agents must be validators with a real, non-constant
    view; a blank-view party may never appear under K):
    - O is a phantom NON-COMMITTEE peer that exists only as the subject of P1
      and P2 - never a {!Validator.t}, never under K. Non-committee because a
      committee member is exempt from banning ([apply_penalty] TrustBasis
      exemption, peer.rs:209-237) and is purged from the temp-ban cache on
      rotation ([forgive_temporarily_banned], manager.rs:694-696 and :711); a
      ban on O can genuinely form and expire.
    - V1 is a knowledge agent (statement #7): its view is its own ban of O
      (P1, banner-local) plus the bare connection to V2 (P3's conn only - V1 is
      P3's subject, so it does NOT see V2's ban flag on it).
    - V2 is a knowledge agent (statement #4 opacity): its view is its bans of O
      and of V1 (P2 and P3, banner-local) plus their connections; V2 sees
      NOTHING of P1, so it cannot know whether V1 bans O.
    - V0 and V3 are idle here: constant blank view, never under K.

    Internode opacity (statement #4, conjunct B): a ban is peer-manager-local;
    [PeerEvent::Banned] / [Unbanned] are consumed locally
    (crates/network-libp2p/src/consensus.rs:1623-1630) and peer-exchange carries
    no ban information, so V2 learns of V1's ban of O only if V2 itself bans O -
    and the two bans are independent, so it never does by inference. *)

(** A connection leg of a directed pair: [Up] admitted, [Down] severed
    (swarm-level close after [apply_peer_action], manager.rs:331-342). *)
type conn = Up | Down

(** The banner-local one-tick temp-ban flag of a directed pair: [Banned] while
    the subject sits in [temporarily_banned] (manager.rs:85), [Unbanned] once
    the heartbeat clears it (manager.rs:599-603). No counter. *)
type ban = Unbanned | Banned

(** Total order index for {!conn}. *)
let conn_index = function Up -> 0 | Down -> 1

(** Total order on {!conn}. *)
let conn_compare a b = Int.compare (conn_index a) (conn_index b)

(** [true] iff the connection is admitted. *)
let conn_is_up = function Up -> true | Down -> false

(** Total order index for {!ban}. *)
let ban_index = function Unbanned -> 0 | Banned -> 1

(** Total order on {!ban}. *)
let ban_compare a b = Int.compare (ban_index a) (ban_index b)

(** [true] iff the banner-local temp-ban flag is set. *)
let ban_is_active = function Banned -> true | Unbanned -> false

(** One directed ban-pair's state: its connection leg and the banner's local
    temp-ban flag on the subject. *)
type pair = { conn : conn; ban : ban }

(** Total deterministic order over a pair's fields (connection, then flag). *)
let pair_compare pa pb =
  let c = conn_compare pa.conn pb.conn in
  if Bool.not (Int.equal c 0) then c else ban_compare pa.ban pb.ban

(** The joint global state: the three independent ban-pairs. [p1] = (V1 -> O),
    [p2] = (V2 -> O), [p3] = (V2 -> V1). There is no phase/tick field: nothing
    in the state (hence nothing in any view) clocks the one-tick expiry. *)
type state = { p1 : pair; p2 : pair; p3 : pair }

(** Total deterministic comparison over ALL state fields, pair by pair. *)
let state_compare s1 s2 =
  let c = pair_compare s1.p1 s2.p1 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = pair_compare s1.p2 s2.p2 in
    if Bool.not (Int.equal c1 0) then c1 else pair_compare s1.p3 s2.p3

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. [View_v1] is V1's projection - (conn(V1,O),
    ban_1(O), conn(V2,V1)): its own ban of O plus the bare connection to V2,
    WITHOUT V2's ban flag on it (V1 is P3's subject). [View_v2] is V2's
    projection - (conn(V2,O), ban_2(O), conn(V2,V1), ban_2(V1)): its two bans
    and their connections, with NO component of P1 (V2 cannot see V1's ban of
    O). [View_idle] is the constant blank view of the non-agents V0, V3. *)
type view =
  | View_v1 of conn * ban * conn
  | View_v2 of conn * ban * conn * ban
  | View_idle

(** Total deterministic order over ALL fields of V1's view. *)
let view_v1_compare (ca, ba, cc) (ca', ba', cc') =
  let c = conn_compare ca ca' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = ban_compare ba ba' in
    if Bool.not (Int.equal c1 0) then c1 else conn_compare cc cc'

(** Total deterministic order over ALL fields of V2's view. *)
let view_v2_compare (ca, ba, cc, bc) (ca', ba', cc', bc') =
  let c = conn_compare ca ca' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = ban_compare ba ba' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = conn_compare cc cc' in
      if Bool.not (Int.equal c2 0) then c2 else ban_compare bc bc'

(** Total order on views: [View_idle] < [View_v1] < [View_v2], with the
    field-wise order within each constructor. Every constructor is spelled: no
    wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_v1 _ | View_v2 _) -> -1
  | (View_v1 _ | View_v2 _), View_idle -> 1
  | View_v1 (ca, ba, cc), View_v1 (ca', ba', cc') ->
      view_v1_compare (ca, ba, cc) (ca', ba', cc')
  | View_v1 _, View_v2 _ -> -1
  | View_v2 _, View_v1 _ -> 1
  | View_v2 (ca, ba, cc, bc), View_v2 (ca', ba', cc', bc') ->
      view_v2_compare (ca, ba, cc, bc) (ca', ba', cc', bc')

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 and V2 are the knowledge agents (real, non-constant
    views); V0 and V3 are idle non-agents with the constant blank view and
    never appear under K. *)
let view v s =
  match v with
  | Validator.V1 -> View_v1 (s.p1.conn, s.p1.ban, s.p3.conn)
  | Validator.V2 -> View_v2 (s.p2.conn, s.p2.ban, s.p3.conn, s.p3.ban)
  | Validator.V0 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | No_admission_denial
      (** delete the [peer_banned] admission denial (manager.rs:403, the
          inbound-connection gate behavior.rs:102-105) so a silent dial-retry
          succeeds REGARDLESS of the ban on EVERY pair, adding the transition
          (Down,Banned) -> (Up,Banned): a connection re-forms while the ban is
          still active. On (V1 -> O) this makes conn(V1,O)=Up reachable while
          ban_1(O)=Banned before any unban, so the inner [Eu] of statement #4's
          severance conjunct becomes satisfiable (refuting it); on (V2 -> V1)
          it makes conn(V2,V1)=Up reachable while ban_2(V1)=Banned, an
          admitted-while-banned state that refutes statement #7. The ban=none
          guard is the SOLE gate on the retry, so no sibling path silently
          repairs the deletion; statement #4's opacity conjunct B is untouched,
          so #4's refutation is cleanly attributable to conjunct A. *)

(** One pair's enabled single-step transitions under a mutation. Pristine each
    pair value has exactly one move, giving the strongly connected 3-cycle
    (Up,Unbanned) -SEED-> (Down,Banned) -EXPIRY-> (Down,Unbanned) -RETRY->
    (Up,Unbanned); (Up,Banned) is unreachable pristine and has no move. Under
    [No_admission_denial] the deleted denial adds the retry (Down,Banned) ->
    (Up,Banned) alongside expiry. *)
let pair_next mut p =
  match (p.conn, p.ban) with
  | Up, Unbanned -> [ { conn = Down; ban = Banned } ]
  | Down, Banned -> (
      match mut with
      | Pristine -> [ { conn = Down; ban = Unbanned } ]
      | No_admission_denial ->
          [ { conn = Down; ban = Unbanned }; { conn = Up; ban = Banned } ])
  | Down, Unbanned -> [ { conn = Up; ban = Unbanned } ]
  | Up, Banned -> []

(** The transition relation: the three pairs advance independently, one pair
    per step, so each successor differs from [s] in exactly one pair. A state
    with no successor at all (only reachable under the mutation, all pairs at
    (Up,Banned)) is stutter-closed by the kernel. *)
let next_with mut s =
  List.concat
    [
      List.map (fun p -> { s with p1 = p }) (pair_next mut s.p1);
      List.map (fun p -> { s with p2 = p }) (pair_next mut s.p2);
      List.map (fun p -> { s with p3 = p }) (pair_next mut s.p3);
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: every pair admitted and unbanned (Up,Unbanned). *)
let initial =
  let up = { conn = Up; ban = Unbanned } in
  { p1 = up; p2 = up; p3 = up }

(** The atom vocabulary the two ADMISSION statements quantify over. [unbanned]
    and [ban_disconnect_in_flight] do not appear: ban_1(O)=None is
    [Not Ban_1o_active] and the atomic seed makes the in-flight window a
    non-state. *)
type atom =
  | Ban_1o_active
      (** ban_1(O) = Banned : V1's temp-ban of O is set (banned_1O) *)
  | Ban_2o_active
      (** ban_2(O) = Banned : V2's temp-ban of O is set (banned_2O) *)
  | Ban_2v1_active
      (** ban_2(V1) = Banned : V2's temp-ban of V1 is set - both the
          [tempban_window] antecedent and [banned_2V1] operand of #7 *)
  | Conn_v1o_up
      (** conn(V1,O) = Up : direct delivery O <-> V1 is possible
          (direct_delivery_O1) *)
  | Conn_v2v1_up
      (** conn(V2,V1) = Up : V1's connection to V2 is admitted (the
          admitted / connected_V1V2 predicate of #7) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Ban_1o_active -> ban_is_active s.p1.ban
  | Ban_2o_active -> ban_is_active s.p2.ban
  | Ban_2v1_active -> ban_is_active s.p3.ban
  | Conn_v1o_up -> conn_is_up s.p1.conn
  | Conn_v2v1_up -> conn_is_up s.p3.conn

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Ban_1o_active -> "banned_1(O)"
  | Ban_2o_active -> "banned_2(O)"
  | Ban_2v1_active -> "banned_2(V1)"
  | Conn_v1o_up -> "conn(V1,O)=up"
  | Conn_v2v1_up -> "conn(V2,V1)=up"

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
    parameterized transitions, the two-agent view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
