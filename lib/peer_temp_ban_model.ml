(** Finite interpreted system for the PEER_TEMP_BAN family: the libp2p peer
    manager's temporary-ban cache, which is the crate's ONLY time-based
    exclusion. All file citations refer to Telcoin-Association/telcoin-network
    at 0c59c15b and were opened in that checkout.

    The modeled mechanism:
    - [BannedPeerCache] is a [HashSet] map plus a [VecDeque] list of
      [Element { key; inserted }] sorted by insertion instant, with ONE duration
      for every key ([BannedPeerCache::new(config.excess_peers_reconnection_timeout)],
      manager.rs:110; default 600s, crates/config/src/network.rs:350 and :372).
    - INSERT ([BannedPeerCache::insert], cache.rs:116-134) has two branches: a
      new key is [push_back]ed with the current instant (cache.rs:121-122), and
      a DUPLICATE key is removed from its position, re-stamped with
      [self.clock.now()] and [push_back]ed again (the refresh else-branch,
      cache.rs:123-128). Both branches are reached from exactly three call
      sites, all in [apply_peer_action] (manager.rs:331, :336, :342).
    - DRAIN ([BannedPeerCache::heartbeat], cache.rs:153-174) pops from the front
      and stops at the first element whose stamp has not aged out:
      [if element.inserted + self.duration > now { self.list.push_front(element);
      break; }] (cache.rs:162-165). Its single call site is
      [unban_temp_banned_peers] (manager.rs:599-603), called once per heartbeat
      (manager.rs:318 inside [PeerManager::heartbeat], manager.rs:289-322).
    - ENFORCEMENT ([PeerManager::peer_banned], manager.rs:396-404) is
      [self.temporarily_banned.contains(peer_id) || self.peers.peer_banned(...)],
      and [contains] reads the map ONLY - it never consults the clock
      (cache.rs:177-179). It gates the inbound admission (behavior.rs:102-105),
      the in-flight dial (behavior.rs:44-50) and [can_dial] (manager.rs:939-941).

    Components (a two-key cache over peers P1 and P2, both plain peers - not
    committee members, not operator-provisioned):
    - [entry1] / [entry2]: each peer's cache entry, carrying the age of ITS
      STAMP in heartbeat intervals. [Uncached] is [contains = false].
    - [since1]: a GHOST field - intervals since P1's LAST insertion. Nothing in
      [next_with] reads it and no view projects it; only [label] does. Under
      [Pristine] it equals P1's stamp age at every reachable state, and THAT
      agreement is precisely the content of the refresh else-branch; under
      {!No_reinsert_refresh} the two diverge, which is what makes statement S3
      separable from S1.
    - [reban1]: P1's second offence, still available. Offences are bounded at
      two so that liveness is honest: a peer that is re-banned forever really
      does stay excluded forever, and an unbounded re-ban would refute [Af] for
      a reason that has nothing to do with the drain.
    - [due]: a heartbeat interval has elapsed but has not yet been serviced.
      The model's time unit IS the heartbeat interval, so [Tick] is enabled only
      when [due = false] and [Drain] only when [due = true]: the manager drains
      on EVERY heartbeat (manager.rs:318), so no second interval can pass before
      the drain that follows the first. This alternation is the model's fairness
      assumption (the heartbeat fires infinitely often) and it is also what
      gives the window in which an entry has aged out but [contains] still
      refuses - the "resolution limited by the heartbeat interval" caveat
      documented at manager.rs:78-81.
    - [forgiven1]: P1 was lifted out of the cache by a forgive path. This is the
      REPAIR PATH the real code has and the model must not omit:
      [forgive_temporarily_banned] (manager.rs:737-745, fired from
      [update_committees] manager.rs:694-696 and :711) and
      [add_trusted_peer_and_dial] (manager.rs:145-147) both call
      [BannedPeerCache::remove] (cache.rs:139-147) with NO regard for the stamp,
      so a committee member or an operator-provisioned peer can leave the cache
      arbitrarily early. Every statement of this family is therefore conditioned
      on [Not Forgiven_1]. The forgive transition is enabled at EVERY live state
      (rotation and provisioning are not synchronised with the ban) and leads to
      a single absorbing state: post-forgiveness history is out of scope, and
      the sink deliberately keeps [since1 = Fresh_age], the worst case, so that
      the path is a genuine early release rather than a decorative flag.
      [BannedPeerCache::remove] and [heartbeat] are the ONLY removers: every
      occurrence of [temporarily_banned] in manager.rs (:85, :110, :124, :145,
      :299, :331, :336, :342, :401, :403, :600) was read.

    What is deliberately NOT modelled, and why each omission is conservative:
    - the second disjunct of [PeerManager::peer_banned] (manager.rs:403),
      [self.peers.peer_banned(peer_id)] (all_peers.rs:905-909), i.e. the
      reputation and IP ban. It can only keep a peer refused LONGER, so it
      cannot manufacture the liveness claim (which is stated about cache
      membership, not about admission overall), and including it would only
      REFINE V0's and V1's views, which can only strengthen a knowledge claim.
      It also cannot stand in for the cache after an early release: a capacity
      disconnect returns [PeerAction::Disconnect]/[DisconnectWithPX] without any
      [apply_penalty] ([handle_disconnecting_transition], all_peers.rs:679-712,
      the [banned] branch at :702-707), so the score is untouched.
    - a capacity bound on the cache. There is none: [BannedPeerCache] exposes
      only [insert], [remove], [heartbeat], [contains] and [len]
      (cache.rs:113-184) and nothing evicts on size. The [max_banned_peers]
      pruning that emits [PeerEvent::Unbanned] (manager.rs:552-553) prunes the
      score store, not this cache, and [PeerEvent::Unbanned] is consumed by
      dropping a gossipsub blacklist entry (consensus.rs:1630-1634) - it never
      re-enters the cache.
    - P2's own forgive path. Giving P2 one could only make [~contains(P2)] true
      EARLIER, which discharges S3's release-order weak-until sooner, so its
      absence is not what makes that statement true.

    Why the drain is "remove every entry whose stamp has aged out" rather than a
    front-stop loop: the list is maintained sorted by insertion instant (inserts
    only ever [push_back], cache.rs:122 and :127; asserted by [check_invariant],
    cache.rs:186-213), so "pop from the front, stop at the first unexpired" and
    "remove exactly the aged-out entries" agree. Both mutations preserve
    sortedness ({!No_reinsert_refresh} leaves the stale element in place with its
    old stamp), so the equivalence survives them and the abstraction is not
    doing any work the real loop would not do.

    Role mapping (only agents with a real, non-constant view may appear under K;
    idle validators get the constant blank view and never do):
    - V0 is the ADMISSION GATE, not the node: its entire input is the membership
      pair [(contains P1, contains P2)] (manager.rs:403 -> cache.rs:177-179).
      It sees no stamp and no clock, which is why it cannot tell an exclusion
      that is still running from one that has aged out but not yet been drained.
    - V1 is peer P1, the excluded peer: its view is the verdict the gate returns
      to it, [contains P1]. It sees neither the node's clock nor its own stamp
      nor P2. Modelling the peer as always able to retry (so the verdict is
      continuously visible) is deliberately generous: it makes the positive
      knowledge claim of S1 HARDER to satisfy, not easier.
    - V2 is peer P2, present so that release ORDER is expressible; its view is
      [contains P2]. It carries no K operand.
    - V3..V9 are idle: constant blank view, never under K.

    Reachability is a PREORDER, not a poset: the heartbeat keeps ticking after
    the cache has emptied, so [due] toggles between two distinct states forever.
    That is the "mechanism that undoes itself" case; a preorder is still a thin
    category, so presheaf restriction is still path-independent and the topos
    gate (test/t_peer_temp_ban_topos.ml) is unaffected. *)

(** Age of a stamp, in heartbeat intervals, saturating at the configured
    duration. [Full_duration] is exactly the drain's predicate
    [element.inserted + self.duration <= now] (the negation of the guard at
    cache.rs:162); the model fixes the duration at two heartbeat intervals, the
    smallest value at which "aged out" and "just inserted" are separated by an
    intermediate interval. *)
type age = Fresh_age | One_interval | Full_duration

(** Total order index for {!age}. *)
let age_index = function
  | Fresh_age -> 0
  | One_interval -> 1
  | Full_duration -> 2

(** Total order on {!age}. *)
let age_compare a b = Int.compare (age_index a) (age_index b)

(** One heartbeat interval later, saturating at {!Full_duration}. *)
let age_succ = function
  | Fresh_age -> One_interval
  | One_interval -> Full_duration
  | Full_duration -> Full_duration

(** [true] iff the full ban duration has elapsed for this age. *)
let age_is_full = function
  | Full_duration -> true
  | Fresh_age | One_interval -> false

(** Strictly younger: [a] is strictly fewer intervals old than [b]. Spelled out
    rather than derived from a comparison so no polymorphic compare is used. *)
let age_lt a b =
  match (a, b) with
  | Fresh_age, Fresh_age -> false
  | Fresh_age, (One_interval | Full_duration) -> true
  | One_interval, (Fresh_age | One_interval) -> false
  | One_interval, Full_duration -> true
  | Full_duration, (Fresh_age | One_interval | Full_duration) -> false

(** A peer's cache entry: [Uncached] is [contains key = false]
    (cache.rs:177-179), [Cached a] is an [Element] in the list whose stamp is
    [a] intervals old (cache.rs:64-69). *)
type slot = Uncached | Cached of age

(** Total order on {!slot}: every constructor pair spelled. *)
let slot_compare a b =
  match (a, b) with
  | Uncached, Uncached -> 0
  | Uncached, Cached _ -> -1
  | Cached _, Uncached -> 1
  | Cached x, Cached y -> age_compare x y

(** [true] iff the gate's [contains] returns true for this entry. *)
let slot_is_cached = function Uncached -> false | Cached _ -> true

(** [true] iff the entry exists AND its stamp has aged out, i.e. the drain's
    guard (cache.rs:162) would NOT push it back. *)
let slot_is_expired = function Uncached -> false | Cached a -> age_is_full a

(** The joint global state: the two cache entries, the ghost interval count
    since P1's last insertion, P1's remaining offence, the forgive flag and the
    unserviced-heartbeat flag. *)
type state = {
  entry1 : slot;  (** P1's entry, carrying its STAMP age *)
  since1 : age;  (** ghost: intervals since P1's LAST insertion *)
  reban1 : bool;  (** P1's second offence is still available *)
  entry2 : slot;  (** P2's entry, carrying its STAMP age *)
  forgiven1 : bool;  (** P1 was lifted by a forgive path *)
  due : bool;  (** an elapsed heartbeat interval awaits its drain *)
}

(** Total deterministic comparison over ALL state fields, in field order. *)
let state_compare s1 s2 =
  let c = slot_compare s1.entry1 s2.entry1 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = age_compare s1.since1 s2.since1 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Bool.compare s1.reban1 s2.reban1 in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = slot_compare s1.entry2 s2.entry2 in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.forgiven1 s2.forgiven1 in
          if Bool.not (Int.equal c4 0) then c4 else Bool.compare s1.due s2.due

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. [View_gate] is V0's projection, the admission
    gate's entire input: the two membership booleans and NOTHING else - no
    stamp, no clock, no forgive flag (manager.rs:403 -> cache.rs:177-179).
    [View_peer1] / [View_peer2] are the excluded peers' projections: the verdict
    the gate returns to that peer, and nothing about the other peer.
    [View_idle] is the constant blank view of the non-agents V3..V9. *)
type view =
  | View_gate of bool * bool
  | View_peer1 of bool
  | View_peer2 of bool
  | View_idle

(** Total order on views: [View_idle] < [View_gate] < [View_peer1] <
    [View_peer2], field-wise within each constructor. Every constructor pair is
    spelled: no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_gate _ | View_peer1 _ | View_peer2 _) -> -1
  | (View_gate _ | View_peer1 _ | View_peer2 _), View_idle -> 1
  | View_gate (x, y), View_gate (x', y') ->
      let c = Bool.compare x x' in
      if Bool.not (Int.equal c 0) then c else Bool.compare y y'
  | View_gate _, (View_peer1 _ | View_peer2 _) -> -1
  | (View_peer1 _ | View_peer2 _), View_gate _ -> 1
  | View_peer1 x, View_peer1 x' -> Bool.compare x x'
  | View_peer1 _, View_peer2 _ -> -1
  | View_peer2 _, View_peer1 _ -> 1
  | View_peer2 x, View_peer2 x' -> Bool.compare x x'

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 (the admission gate), V1 (peer P1) and V2 (peer P2) are
    the agents with a real, non-constant view; V3..V9 are idle non-agents with
    the constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V0 -> View_gate (slot_is_cached s.entry1, slot_is_cached s.entry2)
  | Validator.V1 -> View_peer1 (slot_is_cached s.entry1)
  | Validator.V2 -> View_peer2 (slot_is_cached s.entry2)
  | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7
  | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_expiry_guard
      (** delete the expiry guard of the drain loop,
          [if element.inserted + self.duration > now { self.list.push_front(element);
          break; }] (cache.rs:162-165). The [while let Some(element) =
          self.list.pop_front()] loop then pops the WHOLE list on the first
          heartbeat, so the drain transition removes every entry regardless of
          its stamp age - an exclusion is served early. No sibling path repairs
          it: [heartbeat] has one call site ([unban_temp_banned_peers],
          manager.rs:600) and nothing re-inserts a wrongly released peer, while
          the two paths that could hold it out anyway are excluded by
          hypothesis (forgive) or absent (a capacity disconnect never calls
          [apply_penalty] - it returns [PeerAction::Disconnect]/[DisconnectWithPX]
          from all_peers.rs:702-707 - so [AllPeers::peer_banned]
          (all_peers.rs:905-909) stays false and the second disjunct of
          manager.rs:403 cannot substitute for the cache). *)
  | No_heartbeat_drain
      (** delete [self.unban_temp_banned_peers();] from [PeerManager::heartbeat]
          (manager.rs:318). The heartbeat still runs (so [due] still clears) but
          the cache is never drained, so [contains] stays true forever and a
          rate limit becomes permanent exile. No sibling path repairs it:
          [BannedPeerCache::heartbeat] has exactly this one call site
          (manager.rs:600), and the only other removers - [forgive_temporarily_banned]
          (manager.rs:737-745) and [add_trusted_peer_and_dial] (manager.rs:145)
          - are MODELLED HERE and left enabled by this mutation; the statement
          still flips because it quantifies over all paths and the path that is
          never forgiven is one of them. *)
  | No_reinsert_refresh
      (** delete the duplicate-refresh else-branch of [BannedPeerCache::insert]
          (cache.rs:123-128), keeping only the [is_new] push. A re-inserted key
          then keeps its ORIGINAL stamp and position, so it is released a full
          duration after its FIRST offence rather than its last, and it can jump
          ahead of a peer inserted between the two. No sibling path repairs it:
          callers never remove-then-insert ([apply_peer_action] only ever
          inserts, manager.rs:331/:336/:342; [BannedPeerCache::remove] is called
          only from the two forgive paths, manager.rs:145 and :740), and the
          drain trusts the sorted-by-insertion invariant (cache.rs:186-213,
          itself [cfg(test)]) so nothing detects the stale stamp. *)

(** One interval later: every live stamp and the ghost counter age by one. *)
let slot_age = function Uncached -> Uncached | Cached a -> Cached (age_succ a)

(** The drain's effect on one entry under a mutation. [Pristine] and
    [No_reinsert_refresh] keep the expiry guard (aged-out entries leave, the
    rest are pushed back); [No_expiry_guard] pops the whole list;
    [No_heartbeat_drain] never runs the drain at all. *)
let slot_drain mut s =
  match mut with
  | Pristine | No_reinsert_refresh -> (
      match s with
      | Uncached -> Uncached
      | Cached a -> if age_is_full a then Uncached else Cached a)
  | No_expiry_guard -> Uncached
  | No_heartbeat_drain -> s

(** [BannedPeerCache::insert] on one entry under a mutation: the [is_new] branch
    (cache.rs:121-122) always stamps afresh; the duplicate branch
    (cache.rs:123-128) re-stamps under every mutation except
    {!No_reinsert_refresh}, which is the deletion of exactly that branch. *)
let slot_insert mut s =
  match (mut, s) with
  | (Pristine | No_expiry_guard | No_heartbeat_drain), Cached _ ->
      Cached Fresh_age
  | No_reinsert_refresh, Cached a -> Cached a
  | ( ( Pristine | No_expiry_guard | No_heartbeat_drain
      | No_reinsert_refresh ),
      Uncached ) ->
      Cached Fresh_age

(** The absorbing state reached by the forgive paths: P1 has left the cache
    with its timer not run ([since1 = Fresh_age], the worst case), and nothing
    downstream of forgiveness is in scope. *)
let forgiven_sink =
  {
    entry1 = Uncached;
    since1 = Fresh_age;
    reban1 = false;
    entry2 = Uncached;
    forgiven1 = true;
    due = false;
  }

(** The transition relation. From a live state: TICK (only while no heartbeat is
    outstanding) advances every stamp and the ghost counter and marks the
    heartbeat due; DRAIN (only while one is outstanding) applies
    {!slot_drain} and services it; REBAN spends P1's remaining offence through
    {!slot_insert}; FORGIVE goes to the absorbing {!forgiven_sink}. The sink has
    no successor and is stutter-closed by the kernel. *)
let next_with mut s =
  if s.forgiven1 then []
  else
    let ticked =
      if s.due then []
      else
        [
          {
            s with
            entry1 = slot_age s.entry1;
            entry2 = slot_age s.entry2;
            since1 = age_succ s.since1;
            due = true;
          };
        ]
    in
    let drained =
      if s.due then
        [
          {
            s with
            entry1 = slot_drain mut s.entry1;
            entry2 = slot_drain mut s.entry2;
            due = false;
          };
        ]
      else []
    in
    let rebanned =
      if s.reban1 then
        [
          {
            s with
            entry1 = slot_insert mut s.entry1;
            since1 = Fresh_age;
            reban1 = false;
          };
        ]
      else []
    in
    List.concat [ ticked; drained; rebanned; [ forgiven_sink ] ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** Initial state: P1 has just been inserted by [apply_peer_action]
    (manager.rs:331/:336/:342) and the cache holds nothing else. *)
let initial =
  {
    entry1 = Cached Fresh_age;
    since1 = Fresh_age;
    reban1 = true;
    entry2 = Uncached;
    forgiven1 = false;
    due = false;
  }

(** Second initial state: the two-entry queue, P1 inserted one heartbeat
    interval before P2 (P1's stamp is one interval old, P2's is fresh, and the
    interval between them has already been serviced). This is the configuration
    in which release ORDER is observable; P2 is never re-inserted, so its stamp
    age is always the true age of its last insertion. *)
let initial_staggered =
  {
    entry1 = Cached One_interval;
    since1 = One_interval;
    reban1 = true;
    entry2 = Cached Fresh_age;
    forgiven1 = false;
    due = false;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Cached_1
      (** [temporarily_banned.contains(P1)] - simultaneously the cache fact and
          the admission verdict, since the gate's entire input is [contains]
          (manager.rs:403 -> cache.rs:177-179, behavior.rs:102-105) *)
  | Cached_2  (** [temporarily_banned.contains(P2)] *)
  | Stamp_expired_1
      (** P1 is cached AND its stamp has aged out: the drain's guard
          (cache.rs:162) would not push it back *)
  | Duration_elapsed_1
      (** a full duration has elapsed since P1's LAST insertion - the ghost
          fact the refresh else-branch (cache.rs:123-128) is supposed to keep
          the stamp equal to *)
  | Forgiven_1
      (** P1 left the cache through a forgive path ([forgive_temporarily_banned]
          manager.rs:737-745, [add_trusted_peer_and_dial] manager.rs:145) *)
  | Younger_1
      (** both peers are cached and P1's LAST insertion is strictly more recent
          than P2's: P1 must therefore be released strictly later *)
  | Heartbeat_due
      (** an elapsed interval has not yet been serviced by the drain - the
          window in which [contains] still refuses an aged-out entry
          (manager.rs:78-81) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Cached_1 -> slot_is_cached s.entry1
  | Cached_2 -> slot_is_cached s.entry2
  | Stamp_expired_1 -> slot_is_expired s.entry1
  | Duration_elapsed_1 -> age_is_full s.since1
  | Forgiven_1 -> s.forgiven1
  | Younger_1 -> (
      match (s.entry1, s.entry2) with
      | Cached _, Cached a2 -> age_lt s.since1 a2
      | Cached _, Uncached | Uncached, Cached _ | Uncached, Uncached -> false)
  | Heartbeat_due -> s.due

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Cached_1 -> "contains(P1)"
  | Cached_2 -> "contains(P2)"
  | Stamp_expired_1 -> "stamp_expired(P1)"
  | Duration_elapsed_1 -> "duration_elapsed(P1)"
  | Forgiven_1 -> "forgiven(P1)"
  | Younger_1 -> "younger(P1,P2)"
  | Heartbeat_due -> "heartbeat_due"

(** The CTLK checker over this family's ordered state and view: the presheaf-
    topos denotation ({!Denote}, lib/internal/DESIGN.md), pinned to agree with
    {!System} at every reachable world by test/t_peer_temp_ban_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the two initial states, mutation-
    parameterized transitions, the three-agent view, the atom valuation. *)
let spec_of mut =
  {
    Checker.init = [ initial; initial_staggered ];
    next = next_with mut;
    view;
    label;
  }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
