(** Finite interpreted system for the PEER_PRUNE_FAIRNESS family: ONE heartbeat
    connection-limit prune round at a single node, over five tracked peers. File
    citations refer to Telcoin-Association/telcoin-network at 0c59c15b, working
    tree as read.

    {1 The modeled mechanism}

    The heartbeat calls [PeerManager::prune_connected_peers]
    (crates/network-libp2p/src/peers/manager.rs:315, body :560-594). That
    function does exactly three things:

    - it asks [AllPeers::connected_peers_by_score_and_routability]
      (crates/network-libp2p/src/peers/all_peers.rs:965-978) for the connected
      peers in eviction order. That function SHUFFLES the vector
      (all_peers.rs:974, "shuffle here for unbiased tie-breakers") and then
      STABLE-sorts it by [(peer.score(), peer.is_routable())]
      (all_peers.rs:976, "lowest score first, then non-routable first"). The
      shuffle survives the sort exactly on ties, because [sort_by_key] is
      stable; the module doc states the intent verbatim: "The shuffle ensures
      peers with equal scores are sorted in a random order"
      (all_peers.rs:962-964). [Score] orders on [aggregate_score] alone
      (crates/network-libp2p/src/peers/score.rs:197-203);
    - it computes [excess_peer_count = connected_peers.len() -
      target_num_peers] over ALL connected peers, exempt ones included
      (manager.rs:564-565; [target_num_peers] is
      crates/config/src/network.rs:322), returning early at zero
      (manager.rs:566-569);
    - it filters the ordered vector to the prunable candidates -
      [if !self.is_peer_validator(peer_id) && !peer.is_operator_allowlisted()]
      (manager.rs:575, inside the order-preserving [filter_map] at :571-581) -
      and walks that candidate list dropping peers with
      [self.disconnect_peer(peer_id, true)] until the excess is exhausted
      (manager.rs:583-594).

    So the excess is computed over everybody but can only be paid out of the
    candidates. When the excess exceeds the candidate count the round evicts
    every candidate and STOPS, leaving the node still above target: the exempt
    peers are outside the pruning domain, not merely last in it.

    {1 Scope: exactly one round, and why that is faithful}

    Everything above happens inside one synchronous [&mut self] call with a
    plain [for] loop (manager.rs:583-594): no swarm event, no dial, no identify
    result and no committee update can interleave. Two consequences are
    modeled as frozen rather than omitted:

    - {b no reconnection.} A peer dropped here reaches
      [apply_peer_action]'s [PeerAction::DisconnectWithPX] arm
      (all_peers.rs:702-704 returns [DisconnectWithPX] for
      [Disconnecting { banned: false }] from [Connected]; manager.rs:340-345
      handles it) which does [self.temporarily_banned.insert(peer_id)] -
      "prevent immediate reconnection attempts" - and [peer_banned]
      (manager.rs:396-404) then denies re-admission until
      [unban_temp_banned_peers] (manager.rs:598-604) clears the entry a later
      heartbeat, after [excess_peers_reconnection_timeout]
      (crates/config/src/network.rs:350). Reconnection is therefore not a
      within-round repair path;
    - {b frozen identity map.} [is_peer_validator] resolves membership through
      [identity_for] and answers [false] for [PeerIdentity::Unidentified(_)]
      (all_peers.rs:836-845). Identities are confirmed by discovery/identify
      events processed outside this call, so within the round the recognition
      verdict is fixed;
    - {b no competing disconnect.} The other two routes by which a peer loses
      its connection are the reputation path - [AllPeers::process_penalty]
      (all_peers.rs:261-296) driving [Disconnecting { banned: true }] or
      [Banned], which [apply_peer_action] turns into [PeerAction::Disconnect] /
      [PeerAction::Ban] (manager.rs:327-338) - and the reciprocal disconnect a
      node issues after a peer-exchange goodbye
      ([disconnect_peer(peer, false)], consensus.rs:1139 and :1360). Both are
      driven by events the swarm delivers, so neither can fire inside this
      loop. Within the round [Dropped] therefore means EXACTLY "evicted for
      excess by this loop", which is what lets the statements below read
      [~connected(p)] as an eviction verdict. The reputation path cannot touch
      the two exempt peers in any case: [process_penalty] passes the peer's
      [TrustBasis] into [apply_penalty] (all_peers.rs:262-266,
      peer.rs:209-233), and an exempt peer "bypasses the score model entirely"
      there, so [TrustBasis::Validator] / [TrustBasis::Operator]
      (all_peers.rs:847-873) suppress the penalty outright.

    The round is decomposed into single-victim steps. That is equivalent to
    the real [for] loop and not weaker: scores do not change during the loop,
    so repeatedly evicting a current minimum evicts exactly the prefix of the
    sorted candidate list, and recomputing the excess after each step
    reproduces the [saturating_sub] countdown at manager.rs:587.

    {1 Components}

    Five tracked peers, all held equally routable so that the secondary sort
    key [is_routable] (crates/network-libp2p/src/peers/peer.rs:426-428) is
    constant and the key reduces to [Score]:

    - [Pa], [Pb]: ordinary peers in the LOW score bucket. They tie on both sort
      keys, so they are the shuffle's tie pair;
    - [Pc]: an ordinary peer in the HIGH score bucket;
    - [Px]: a peer whose committee status is the family's hidden fact. Its
      [trust] is [Confirmed_member] (identity confirmed AND in one of the three
      tracked committees, so [is_peer_validator] is true),
      [Unconfirmed_member] (genuinely in a committee but the node has no
      confirmed identity for it, so [is_peer_validator] is FALSE) or
      [Unconfirmed_outsider] (not in any committee). HIGH score bucket;
    - [Py]: an operator-allowlisted peer
      ([Peer::is_operator_allowlisted], peer.rs:401-403; construction-time and
      never touched by epoch rotation). HIGH score bucket.

    Both exempt classes sit in the HIGH bucket on purpose. A confirmed
    committee member is primed with [peer.reset_score_to_max()] on committee
    entry (all_peers.rs:1232, peer.rs:416-418) and an operator-allowlisted peer
    is exempt from the score model altogether ([TrustBasis::Operator],
    all_peers.rs:847-873), so neither decays. That priming is a REAL PARTIAL
    REPAIR of the exemption deletions: with a small excess the sort alone would
    keep an exempt peer alive even with the filter conjunct gone. The [Tight]
    capacity regime below is what defeats it.

    Two capacity regimes ([target_num_peers], config/src/network.rs:322):

    - [Slack]: target 4, five connected, excess 1. Exactly one peer is dropped
      and the argmin is the tie pair, so this is the tie-break regime;
    - [Tight]: target 1, five connected, excess 4. The excess is STRICTLY
      GREATER than the three ordinary candidates, so no sorting order can save
      an exempt peer once its filter conjunct is deleted, and the pristine
      round provably terminates above target.

    {1 Role mapping}

    - [Validator.V0] is the pruning node and the only knowledge agent. Its view
      is its own peer store as [prune_connected_peers] reads it: the capacity
      regime, the five connection statuses, and - for [Px] - the RECOGNITION
      TOKEN only. [Tok_validator] is [PeerIdentity::Confirmed] with the key in a
      tracked committee; [Tok_unidentified] is what the node sees for BOTH
      unconfirmed cases, because [identity_for] hands back
      [PeerIdentity::Unidentified] with no [BlsPublicKey] to test against the
      committee sets (all_peers.rs:836-845), and members whose libp2p id is not
      yet recoverable are skipped entirely when the committees are installed
      (all_peers.rs:1196-1235, "others are trusted lazily on discovery"). So
      [Unconfirmed_member] and [Unconfirmed_outsider] are view-identical to V0
      and differ only in the hidden ground truth - that is the family's
      ignorance witness;
    - [Validator.V1] .. [Validator.V9] are idle here: constant blank view, never
      under [K]. The tracked peers are deliberately NOT knowledge agents - a
      peer's own connection status is its own view, so any [K] on it would
      collapse.

    This family asserts NO positive [K]. Every candidate positive knowledge
    claim available in this slice is a projection of the pruning node's own
    peer store (V0 holds the committee sets, the allowlist flags and every
    score locally), which R1 rejects; the genuine epistemic content here is the
    node's INABILITY to tell a committee member it has not identified from an
    ordinary peer, and that is stated as ignorance. *)

(** Whether a tracked peer still holds a live connection to the pruning node.
    [Linked] is [ConnectionStatus::Connected]; [Dropped] is the
    [Disconnecting { banned: false }] state installed by
    [PeerManager::disconnect_peer(peer_id, true)] (manager.rs:472-489, called
    from the prune loop at manager.rs:586). *)
type link = Linked | Dropped

(** Total order index for {!link}. *)
let link_index = function Linked -> 0 | Dropped -> 1

(** Total order on {!link}. *)
let link_compare a b = Int.compare (link_index a) (link_index b)

(** [true] iff the peer is still connected, i.e. iff it is still counted by
    [connected_peers_by_score_and_routability] (all_peers.rs:967-971). *)
let link_is_up = function Linked -> true | Dropped -> false

(** The node's connection-limit regime, i.e. its [target_num_peers]
    (config/src/network.rs:322). [Slack] leaves an excess of one over the five
    tracked peers (the tie-break regime); [Tight] leaves an excess of four,
    strictly more than the three ordinary candidates. *)
type capacity = Slack | Tight

(** Total order index for {!capacity}. *)
let capacity_index = function Slack -> 0 | Tight -> 1

(** Total order on {!capacity}. *)
let capacity_compare a b = Int.compare (capacity_index a) (capacity_index b)

(** [target_num_peers] under a capacity regime (manager.rs:565). *)
let target = function Slack -> 4 | Tight -> 1

(** [Px]'s committee situation: the pair (ground-truth membership, whether the
    node has a confirmed identity for it). [Confirmed_member] is
    [PeerIdentity::Confirmed] with the key in a tracked committee, the only
    case for which [is_peer_validator] answers true (all_peers.rs:836-845);
    [Unconfirmed_member] is a genuine committee member the node has not
    identified, for which [is_peer_validator] answers FALSE via the
    [PeerIdentity::Unidentified(_)] arm; [Unconfirmed_outsider] is an ordinary
    unidentified peer. The last two are indistinguishable to the node. *)
type trust = Confirmed_member | Unconfirmed_member | Unconfirmed_outsider

(** Total order index for {!trust}. *)
let trust_index = function
  | Confirmed_member -> 0
  | Unconfirmed_member -> 1
  | Unconfirmed_outsider -> 2

(** Total order on {!trust}. *)
let trust_compare a b = Int.compare (trust_index a) (trust_index b)

(** [AllPeers::is_peer_validator] (all_peers.rs:836-845): true only when the
    identity is confirmed AND the key sits in a tracked committee. *)
let recognized_validator = function
  | Confirmed_member -> true
  | Unconfirmed_member | Unconfirmed_outsider -> false

(** Ground-truth committee membership, which the node cannot read off an
    unidentified peer. *)
let is_committee_member = function
  | Confirmed_member | Unconfirmed_member -> true
  | Unconfirmed_outsider -> false

(** The five tracked peers. [Pa] and [Pb] are the LOW-score ordinary tie pair,
    [Pc] a HIGH-score ordinary peer, [Px] the committee-status peer and [Py]
    the operator-allowlisted peer. The declaration order doubles as the fixed
    map-iteration order that the shuffle exists to hide (the peer store is a
    [HashMap<PeerIdentity, Peer>], all_peers.rs:44). *)
type peer = Pa | Pb | Pc | Px | Py

(** Total order index for {!peer}; also the deterministic tie order that
    survives when the shuffle is deleted. *)
let peer_index = function Pa -> 0 | Pb -> 1 | Pc -> 2 | Px -> 3 | Py -> 4

(** The roster in map-iteration order. *)
let all_tracked = [ Pa; Pb; Pc; Px; Py ]

(** The LOW score bucket: the value [Score::cmp] compares
    (score.rs:197-203). *)
let score_low = 0

(** The HIGH score bucket. *)
let score_high = 1

(** A peer's score bucket. [Pa] and [Pb] tie in the LOW bucket; [Pc], [Px] and
    [Py] sit in the HIGH bucket - the exempt peers because committee entry
    primes them to the maximum (all_peers.rs:1232) and operator trust exempts
    them from the score model (all_peers.rs:847-873), [Pc] because it is a
    well-behaved ordinary peer. *)
let score = function
  | Pa | Pb -> score_low
  | Pc | Px | Py -> score_high

(** The joint global state: the capacity regime, [Px]'s committee situation and
    the five connection statuses. Neither the regime nor the trust changes
    during a round (the loop at manager.rs:583-594 is synchronous), so they are
    per-run configuration carried in the state. *)
type state = {
  cap : capacity;
  xtrust : trust;
  la : link;
  lb : link;
  lc : link;
  lx : link;
  ly : link;
}

(** Total deterministic comparison over ALL state fields, in declaration
    order. *)
let state_compare s1 s2 =
  let c0 = capacity_compare s1.cap s2.cap in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = trust_compare s1.xtrust s2.xtrust in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = link_compare s1.la s2.la in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = link_compare s1.lb s2.lb in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = link_compare s1.lc s2.lc in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = link_compare s1.lx s2.lx in
            if Bool.not (Int.equal c5 0) then c5
            else link_compare s1.ly s2.ly

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** Read one peer's connection status out of the joint state. *)
let link_of s = function
  | Pa -> s.la
  | Pb -> s.lb
  | Pc -> s.lc
  | Px -> s.lx
  | Py -> s.ly

(** Rebuild the state with one peer's connection status replaced. *)
let set_link s p l =
  match p with
  | Pa -> { s with la = l }
  | Pb -> { s with lb = l }
  | Pc -> { s with lc = l }
  | Px -> { s with lx = l }
  | Py -> { s with ly = l }

(** [connected_peers.len()] at manager.rs:565: the count of ALL connected
    peers, exempt ones included. This is the whole reason a round can end above
    target. *)
let connected_count s =
  List.fold_left
    (fun n p -> if link_is_up (link_of s p) then n + 1 else n)
    0 all_tracked

(** [excess_peer_count > 0] at manager.rs:565 and :585. *)
let over_target s = connected_count s > target s.cap

(** What the pruning node's own peer store shows for [Px]: the recognition
    token, NOT the ground truth. [Tok_unidentified] is returned for BOTH
    unconfirmed cases because [identity_for] yields
    [PeerIdentity::Unidentified] with no [BlsPublicKey] to test against the
    committee sets (all_peers.rs:836-845). *)
type xtoken = Tok_validator | Tok_unidentified

(** Total order index for {!xtoken}. *)
let xtoken_index = function Tok_validator -> 0 | Tok_unidentified -> 1

(** Total order on {!xtoken}. *)
let xtoken_compare a b = Int.compare (xtoken_index a) (xtoken_index b)

(** The node's recognition verdict on [Px]. This is the projection that hides
    the ground truth: [Unconfirmed_member] and [Unconfirmed_outsider] both map
    to [Tok_unidentified]. *)
let xtoken_of = function
  | Confirmed_member -> Tok_validator
  | Unconfirmed_member | Unconfirmed_outsider -> Tok_unidentified

(** A validator's local view. [View_manager] is V0's projection - the capacity
    regime, its recognition token for [Px], and the five connection statuses,
    exactly the state [prune_connected_peers] reads (manager.rs:560-594). It
    carries NO component that distinguishes [Unconfirmed_member] from
    [Unconfirmed_outsider]. [View_idle] is the constant blank view of the
    non-agents V1..V9, which never appear under [K]. *)
type view =
  | View_manager of capacity * xtoken * link * link * link * link * link
  | View_idle

(** Total deterministic order over ALL fields of the pruning node's view. *)
let view_manager_compare (ca, ta, aa, ba, cc, xa, ya)
    (ca', ta', aa', ba', cc', xa', ya') =
  let c0 = capacity_compare ca ca' in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = xtoken_compare ta ta' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = link_compare aa aa' in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = link_compare ba ba' in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = link_compare cc cc' in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = link_compare xa xa' in
            if Bool.not (Int.equal c5 0) then c5 else link_compare ya ya'

(** Total order on views: [View_idle] < [View_manager], with the field-wise
    order within the manager constructor. Every constructor is spelled: no
    wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_manager _ -> -1
  | View_manager _, View_idle -> 1
  | ( View_manager (ca, ta, aa, ba, cc, xa, ya),
      View_manager (ca', ta', aa', ba', cc', xa', ya') ) ->
      view_manager_compare (ca, ta, aa, ba, cc, xa, ya)
        (ca', ta', aa', ba', cc', xa', ya')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 is the pruning node and the only knowledge agent;
    V1..V9 are idle non-agents with the constant blank view and never appear
    under [K]. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_manager (s.cap, xtoken_of s.xtrust, s.la, s.lb, s.lc, s.lx, s.ly)
  | Validator.V1 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. Each names the exact line
    it removes, the transitions that appear or disappear, and why no sibling
    path in the real code re-establishes the effect. *)
type mutation =
  | Pristine
  | No_score_sort
      (** delete [connected_peers.sort_by_key(|(_, peer)| (peer.score(),
          peer.is_routable()));] (all_peers.rs:976), leaving only the shuffle at
          :974. The eviction order becomes an arbitrary permutation of the
          candidates, so this ADDS the transitions that drop a HIGH-bucket
          candidate while a LOW-bucket one is still connected. No sibling
          repairs it: [prune_connected_peers] consumes the vector in the order
          it was handed - the candidate filter at manager.rs:571-581 is an
          order-preserving [filter_map] and the eviction loop at :583-594 is a
          plain [for] over its output with no re-sort - and
          [disconnect_peer] (manager.rs:472-489) takes the peer as given. The
          only other eviction-ordering machinery in the crate,
          [collect_excess_peers] (all_peers.rs:996-1034), orders BANNED and
          DISCONNECTED pruning by [Instant] and never touches the connected
          set. *)
  | No_tie_shuffle
      (** delete [connected_peers.shuffle(&mut rand::rng());]
          (all_peers.rs:974), leaving only the stable sort at :976. This
          REMOVES every tie-break branch: the surviving order is a
          deterministic function of the peer store's iteration order, so among
          equally scored candidates the same peer loses every time. No sibling
          repairs it: [sort_by_key] is Rust's STABLE sort, so it preserves
          whatever order it was given on ties and cannot re-randomise, and the
          candidate [filter_map] (manager.rs:571-581) preserves order exactly.
          The peer store is a [HashMap<PeerIdentity, Peer>] (all_peers.rs:44)
          whose [RandomState] is seeded once per map, so its order varies
          across processes but is FIXED within a run - which is precisely the
          starvation the shuffle exists to prevent. Modeled as the fixed
          {!peer_index} order. *)
  | No_validator_exemption
      (** delete the [!self.is_peer_validator(peer_id) &&] conjunct from the
          prune filter (manager.rs:575), leaving [!peer.is_operator_allowlisted()].
          This ADDS [Px] to the candidate list whenever it is a recognized
          committee member, so a validator can be evicted for excess. The known
          partial repair is REAL and is defeated by construction rather than
          ignored: committee entry primes a member's score to the maximum
          (all_peers.rs:1232), so with a small excess the sort alone would keep
          [Px] alive. The [Tight] regime makes the excess (4) strictly exceed
          the candidate count, so every candidate is evicted and no ordering
          can rescue [Px]. The other candidate repair, [peer_is_important]
          (manager.rs:665-668), guards only the connect-time limit check at
          behavior.rs:266-272 and never re-admits an already-pruned peer; and
          re-admission is itself blocked within the round by the
          [temporarily_banned] insert at manager.rs:342. *)
  | No_allowlist_exemption
      (** delete the [&& !peer.is_operator_allowlisted()] conjunct from the same
          filter (manager.rs:575), leaving [!self.is_peer_validator(peer_id)].
          This ADDS [Py] to the candidate list, so an operator-allowlisted peer
          can be evicted for excess. Same repair analysis: operator trust
          exempts the peer from the score model ([TrustBasis::Operator],
          all_peers.rs:847-873) so its score never decays, which is again only
          a sort-level rescue and is defeated by the [Tight] regime;
          [peer_is_important] again guards only behavior.rs:266-272. *)

(** Whether the prune filter at manager.rs:575 rejects a peer as a candidate.
    Every mutation arm is spelled for every peer: ordinary peers are never
    exempt, [Px] is exempt exactly when [is_peer_validator] holds, [Py] exactly
    when [is_operator_allowlisted] holds, and each deletion drops its own
    conjunct only. *)
let exempt mut s p =
  match p with
  | Pa | Pb | Pc -> false
  | Px -> (
      match mut with
      | Pristine | No_score_sort | No_tie_shuffle | No_allowlist_exemption ->
          recognized_validator s.xtrust
      | No_validator_exemption -> false)
  | Py -> (
      match mut with
      | Pristine | No_score_sort | No_tie_shuffle | No_validator_exemption ->
          true
      | No_allowlist_exemption -> false)

(** [ready_to_prune] at manager.rs:571-581: the connected, non-exempt peers, in
    map order. *)
let candidates mut s =
  List.filter
    (fun p -> link_is_up (link_of s p) && Bool.not (exempt mut s p))
    all_tracked

(** The candidates the sort puts first: those in the lowest occupied score
    bucket (all_peers.rs:976, "lowest score first"). On the empty list this is
    empty. *)
let lowest_scored ps =
  let best = List.fold_left (fun acc p -> Int.min acc (score p)) score_high ps in
  List.filter (fun p -> Int.equal (score p) best) ps

(** The peers that may be the next eviction, under a mutation. Pristine the
    shuffle-then-stable-sort leaves EVERY lowest-bucket candidate a legitimate
    victim, which is the nondeterminism this family is about;
    [No_score_sort] leaves every candidate a victim; [No_tie_shuffle] leaves
    exactly the first one in the fixed map order. The two exemption deletions
    change WHO is a candidate, not the order, so they keep the pristine
    selection rule. *)
let victims mut s =
  let cs = candidates mut s in
  match mut with
  | Pristine | No_validator_exemption | No_allowlist_exemption ->
      lowest_scored cs
  | No_score_sort -> cs
  | No_tie_shuffle -> (
      match lowest_scored cs with [] -> [] | p :: _ -> [ p ])

(** The transition relation: one eviction step of the round. The step is
    enabled iff the node is over target (manager.rs:565-569, :585) and a
    candidate exists (manager.rs:583-594); the successors are the legitimate
    victims. A round that has exhausted its candidates while still over target
    has no successor at all and is stutter-closed by the kernel - that terminal
    IS the "excess tolerated rather than resolved" outcome. *)
let next_with mut s =
  if over_target s then List.map (fun p -> set_link s p Dropped) (victims mut s)
  else []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The [Slack] initial state with [Px] a recognized committee member: five
    connected peers, target 4, excess 1. *)
let initial = {
  cap = Slack;
  xtrust = Confirmed_member;
  la = Linked;
  lb = Linked;
  lc = Linked;
  lx = Linked;
  ly = Linked;
}

(** The [Slack] initial state with [Px] an UNIDENTIFIED genuine committee
    member: the node cannot tell it from {!initial_slack_outsider}. *)
let initial_slack_unconfirmed_member =
  { initial with xtrust = Unconfirmed_member }

(** The [Slack] initial state with [Px] an unidentified NON-member: the
    view-identical sibling of {!initial_slack_unconfirmed_member}. *)
let initial_slack_outsider = { initial with xtrust = Unconfirmed_outsider }

(** The [Tight] initial state with [Px] a recognized committee member: target
    1, excess 4, strictly more than the three ordinary candidates. *)
let initial_tight = { initial with cap = Tight }

(** The [Tight] initial state with [Px] an unidentified genuine committee
    member: here the recognition gap actually costs a validator its slot. *)
let initial_tight_unconfirmed_member =
  { initial with cap = Tight; xtrust = Unconfirmed_member }

(** The [Tight] initial state with [Px] an unidentified non-member: the
    view-identical sibling of {!initial_tight_unconfirmed_member}. *)
let initial_tight_outsider =
  { initial with cap = Tight; xtrust = Unconfirmed_outsider }

(** The six initial states: both capacity regimes crossed with [Px]'s three
    committee situations. *)
let inits =
  [
    initial;
    initial_slack_unconfirmed_member;
    initial_slack_outsider;
    initial_tight;
    initial_tight_unconfirmed_member;
    initial_tight_outsider;
  ]

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Conn_a  (** [Pa] is still connected: the LOW-bucket tie peer *)
  | Conn_b  (** [Pb] is still connected: the other LOW-bucket tie peer *)
  | Conn_c  (** [Pc] is still connected: the HIGH-bucket ordinary peer *)
  | Conn_x  (** [Px] is still connected: the committee-status peer *)
  | Conn_y  (** [Py] is still connected: the operator-allowlisted peer *)
  | Cap_slack
      (** the excess is 1: exactly one peer is dropped this round
          (manager.rs:565) *)
  | X_recognized
      (** [is_peer_validator(Px)] holds (all_peers.rs:836-845), i.e. the node's
          prune filter sees [Px] as a validator *)
  | X_in_committee
      (** GROUND TRUTH: [Px] sits in one of the three tracked committees. Not a
          component of any view when the identity is unconfirmed *)
  | Over_target
      (** [connected_peers.len() > target_num_peers] (manager.rs:565): the node
          is still above its connection target *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Conn_a -> link_is_up s.la
  | Conn_b -> link_is_up s.lb
  | Conn_c -> link_is_up s.lc
  | Conn_x -> link_is_up s.lx
  | Conn_y -> link_is_up s.ly
  | Cap_slack -> (
      match s.cap with Slack -> true | Tight -> false)
  | X_recognized -> recognized_validator s.xtrust
  | X_in_committee -> is_committee_member s.xtrust
  | Over_target -> over_target s

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Conn_a -> "connected(a)"
  | Conn_b -> "connected(b)"
  | Conn_c -> "connected(c)"
  | Conn_x -> "connected(x)"
  | Conn_y -> "connected(y)"
  | Cap_slack -> "excess=1"
  | X_recognized -> "is_peer_validator(x)"
  | X_in_committee -> "committee_member(x)"
  | Over_target -> "over_target"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every
    reachable world by test/t_peer_prune_fairness_topos.ml. The transition
    relation only ever moves a peer from [Linked] to [Dropped] and never
    touches [cap] or [xtrust], so the reachability relation is ACYCLIC and the
    frame is a genuine finite poset. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the six initial states,
    mutation-parameterized transitions, the single-agent view, the atom
    valuation. *)
let spec_of mut = { Checker.init = inits; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
