(** The PEER_TEMP_BAN statement family, encoded over the
    {!Peer_temp_ban_model} interpreted system. What was mined: the temporary-ban
    cache of the libp2p peer manager
    (crates/network-libp2p/src/peers/cache.rs, driven from
    crates/network-libp2p/src/peers/manager.rs) is the crate's only time-based
    exclusion, and three separate lines of it carry the whole guarantee - the
    expiry comparison in the drain loop (cache.rs:162-165), the drain call in
    the heartbeat (manager.rs:318), and the duplicate-refresh else-branch of
    [insert] (cache.rs:123-128). One statement per line, one mutation per line.

    Reading guide for the K operands (why neither is a projection of its own
    knower's view, and why neither is rigid):

    - [K (V1, duration_elapsed(P1) \\/ forgiven(P1))] in S1. V1 is the excluded
      peer; its view is exactly the verdict the admission gate returns to it,
      [contains(P1)] (manager.rs:403 -> cache.rs:177-179, behavior.rs:102-105).
      The operand is about the node's HIDDEN state - the stamp the node wrote
      and the node's own forgive act - and is projected into no view at all.
      It is not rigid: it is false at every reachable state where P1 sits in the
      cache with a fresh stamp, so the knowledge is contingent, and it holds at
      the admitted states only because the drain's expiry guard is what let P1
      out. The disjunct [forgiven(P1)] is not decoration: the model HAS the
      committee/trusted forgive path (manager.rs:145, :737-745), which releases
      a peer with its timer unrun, so the peer's inference is genuinely
      "either my duration ran or I was forgiven" and nothing stronger.
    - [~K (V0, ~stamp_expired(P1))] in S2. V0 is the admission GATE, not the
      node: its whole input is the membership pair, because [contains] reads the
      map and never the clock (cache.rs:176-179). Two reachable states share
      that pair while disagreeing on whether P1's stamp has aged out, so the
      gate cannot tell an exclusion that is still running from one that has
      aged out and is waiting for the next heartbeat - the "resolution limited
      by the heartbeat interval" caveat of manager.rs:78-81. This is the
      epistemic reason release is LATE but never EARLY.

    Every statement is conditioned on [~forgiven(P1)] (directly, or through the
    weak-until's release disjunct), because the two forgive paths really do
    release a peer early and are modelled. *)

open Peer_temp_ban_model

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

(** [A[p W q]] by the kernel identity [A[p W q] = ~E[ ~q U (~p /\\ ~q) ]]:
    weak until is not a {!Formula.t} constructor. *)
let weak_until p q =
  Formula.Not
    (Formula.Eu (Formula.Not q, Formula.And (Formula.Not p, Formula.Not q)))

(** S1 - temp-ban-exclusion-is-never-served-early [safety]. The temporary-ban
    cache can be LATE but never EARLY, and that is exactly what makes an
    admission informative to the peer it excluded.

    (A) No early release. [BannedPeerCache::heartbeat] pops from the front and
    stops at the first element whose stamp has not aged out -
    [if element.inserted + self.duration > now { self.list.push_front(element);
    break; }] (cache.rs:162-165) - and the list is kept sorted by insertion
    instant (inserts only [push_back], cache.rs:122 and :127; [check_invariant],
    cache.rs:186-213), so an entry leaves the cache only through a state in
    which its own stamp has aged out:
    AG( contains(P1) /\\ ~forgiven(P1) -> A[ contains(P1) W (stamp_expired(P1)
    \\/ forgiven(P1)) ] ). Weak, not strong, until: a run that never reaches the
    next heartbeat keeps the peer excluded forever, which is a legal path here
    and is S2's business, not S1's. The [forgiven(P1)] release disjunct is the
    modelled repair path ([forgive_temporarily_banned] manager.rs:737-745,
    [add_trusted_peer_and_dial] manager.rs:145-147), which removes an entry with
    no regard for its stamp.

    (B) An admitted peer knows its timer ran. The peer sees only the gate's
    verdict on itself, never the stamp or the clock, yet at every reachable
    state in which it is not in the cache, every state sharing that view has
    either the full duration elapsed since its last insertion or the forgive
    flag set: AG( ~contains(P1) -> K_V1( duration_elapsed(P1) \\/ forgiven(P1) ) ).
    This is the epistemic content of conjunct (A): the expiry guard is what
    makes readmission EVIDENCE of elapsed time. The V1-view class at an admitted
    state is not a singleton - it contains states differing in whether the other
    peer P2 is still excluded and in whether the forgive path fired - and the
    operand is false at every freshly-inserted state, so the knowledge is
    contingent (both discharged in test/t_peer_temp_ban.ml, group "contingency").

    Mutation pin: {!Peer_temp_ban_model.No_expiry_guard} deletes the expiry
    comparison (cache.rs:162-165), so the drain loop pops the whole list on the
    first heartbeat: P1 leaves the cache from a state where its stamp is one
    interval old, refuting (A)'s weak-until, and the admitted-view class gains a
    state with the timer unrun and no forgiveness, refuting (B). No sibling path
    repairs the deletion - [BannedPeerCache::heartbeat] has a single call site
    (manager.rs:600), nothing re-inserts a wrongly released peer, and the
    reputation ban cannot substitute for the cache because a capacity disconnect
    returns [PeerAction::Disconnect]/[DisconnectWithPX] without any penalty
    (all_peers.rs:702-707), leaving [AllPeers::peer_banned] (all_peers.rs:905-909)
    false. Conjunct (B) additionally flips under
    {!Peer_temp_ban_model.No_reinsert_refresh}, which is honest: a stale stamp
    also destroys the peer's inference. *)
let s_never_early =
  let no_early_release =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Cached_1, Formula.Not (atom Forgiven_1)),
           weak_until (atom Cached_1)
             (Formula.Or (atom Stamp_expired_1, atom Forgiven_1)) ))
  in
  let admission_is_evidence =
    Formula.Ag
      (Formula.Implies
         ( Formula.Not (atom Cached_1),
           Formula.K
             ( Validator.V1,
               Formula.Or (atom Duration_elapsed_1, atom Forgiven_1) ) ))
  in
  {
    name = "temp-ban-exclusion-is-never-served-early";
    bucket = Statements.Safety;
    formula = Formula.And (no_early_release, admission_is_evidence);
    antecedent =
      Formula.And (atom Cached_1, Formula.Not (atom Duration_elapsed_1));
  }

(** S2 - temp-ban-exclusion-always-ends-at-a-heartbeat [liveness]. The
    "temporary" in temporary ban is enforced by exactly one periodic call, and
    the gate that enforces the ban is blind to the clock that ends it.

    (A) Every exclusion ends: leads_to( contains(P1), ~contains(P1) ). The
    manager's heartbeat calls [self.unban_temp_banned_peers();]
    (manager.rs:318, inside [PeerManager::heartbeat] manager.rs:289-322), which
    drains the cache and emits [PeerEvent::Unbanned] (manager.rs:599-603).
    Admission consults raw membership - [self.temporarily_banned.contains(peer_id)
    || self.peers.peer_banned(peer_id)] (manager.rs:403) - and [contains] does no
    expiry evaluation of its own (cache.rs:176-179), so the drain is the only
    enactor of expiry. Offences are bounded at two in the model: a peer that
    keeps re-offending really does stay excluded, so this liveness claim is
    about the mechanism, not about a peer's future behaviour. It is also a claim
    about THIS mechanism only: the target is [~contains(P1)], the cache's own
    membership, not "the peer is admitted". The other disjunct of manager.rs:403,
    [self.peers.peer_banned(peer_id)] (all_peers.rs:905-909), is the reputation
    and IP ban - a separate mechanism with its own decay - and is deliberately
    outside this family. Leaving it out is conservative in both directions: it
    can only keep a peer refused for longer, so it cannot manufacture this
    liveness, and it would only REFINE the gate's and the peer's views, which
    can only strengthen the knowledge claims.

    (B) The gate cannot see the clock: AG( contains(P1) /\\ ~stamp_expired(P1)
    -> ~K_V0( ~stamp_expired(P1) ) ). [contains] reads the map only
    (cache.rs:176-179), so for every membership pair the gate can observe there
    is a reachable state in which the entry has aged out and is merely waiting
    for the next heartbeat. That is why the documented ban duration has "a
    resolution limited by the heartbeat interval" (manager.rs:78-81) and why the
    guarantee is late-but-never-early rather than exact. The ignorance witness
    pair is asserted satisfiable in test/t_peer_temp_ban.ml.

    Mutation pin: {!Peer_temp_ban_model.No_heartbeat_drain} deletes
    [self.unban_temp_banned_peers();] from the heartbeat (manager.rs:318). The
    heartbeat still runs, so the model's interval still gets serviced, but the
    cache is never drained: [contains] stays true forever and a rate limit
    becomes permanent exile, refuting (A) on the path that is never forgiven.
    The sibling paths that could still remove the entry - the committee and
    trusted forgive routes (manager.rs:737-745, :145) - are present in the model
    and are NOT disabled by this mutation; the pin survives them because the
    claim quantifies over all paths. [BannedPeerCache::heartbeat] has exactly one
    call site (manager.rs:600), so no second drain repairs it. Conjunct (B) also
    flips under {!Peer_temp_ban_model.No_expiry_guard}, which collapses the
    gate's ignorance by emptying the cache before any entry can be observed
    aged-out in some membership class. *)
let s_always_ends =
  let exclusion_ends =
    Formula.leads_to (atom Cached_1) (Formula.Not (atom Cached_1))
  in
  let gate_is_clock_blind =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Cached_1, Formula.Not (atom Stamp_expired_1)),
           Formula.Not
             (Formula.K (Validator.V0, Formula.Not (atom Stamp_expired_1))) ))
  in
  {
    name = "temp-ban-exclusion-always-ends-at-a-heartbeat";
    bucket = Statements.Liveness;
    formula = Formula.And (exclusion_ends, gate_is_clock_blind);
    antecedent = atom Cached_1;
  }

(** S3 - temp-ban-reinsertion-restarts-the-uniform-clock [fairness]. One
    duration applies to every peer and it is measured from that peer's MOST
    RECENT insertion, because [BannedPeerCache::insert] re-stamps a duplicate
    key and pushes it to the back:
    [let position = self.list.iter().position(|e| e.key == key)...;
    element.inserted = self.clock.now(); self.list.push_back(element);]
    (cache.rs:123-128). The single duration comes from one constructor argument
    ([BannedPeerCache::new(config.excess_peers_reconnection_timeout)],
    manager.rs:110; crates/config/src/network.rs:350 and :372).

    (A) Measured from the LAST insertion: AG( contains(P1) /\\ ~forgiven(P1) ->
    A[ contains(P1) W (duration_elapsed(P1) \\/ forgiven(P1)) ] ). This is S1(A)
    with the cache's own stamp replaced by the ghost "intervals since P1's last
    insertion". On the pristine model the two agree at every reachable state -
    that agreement IS the content of the else-branch - so the separation between
    S1 and S3 is exactly what the refresh mutation exposes.

    (B) Release order is last-insertion order, so a re-offender cannot jump the
    queue: AG( younger(P1,P2) -> A[ contains(P1) W (~contains(P2) \\/
    forgiven(P1)) ] ). [younger(P1,P2)] holds where both peers are cached and
    P1's last insertion is strictly more recent than P2's; the drain releases
    strictly from the front of a list sorted by insertion instant
    (cache.rs:161-168, invariant cache.rs:186-213), so P1 cannot leave while P2
    is still held. P2 is a plain peer with no forgive path of its own: giving it
    one could only make [~contains(P2)] true EARLIER, which discharges the
    weak-until sooner, so its absence cannot be what makes (B) true.

    Mutation pin: {!Peer_temp_ban_model.No_reinsert_refresh} deletes the
    duplicate-refresh else-branch (cache.rs:123-128), keeping only the [is_new]
    push. The re-inserted key then keeps its original stamp and position: it is
    released a full duration after its FIRST offence, refuting (A), and it is
    released while a peer inserted between the two offences is still held,
    refuting (B). No sibling path repairs it: no caller does remove-then-insert
    ([apply_peer_action] only inserts, manager.rs:331/:336/:342;
    [BannedPeerCache::remove] is called only from the two forgive paths,
    manager.rs:145 and :740), and the drain trusts the sorted-by-insertion
    invariant, which the stale element does not violate, so nothing detects it.
    Conjunct (A) also flips under {!Peer_temp_ban_model.No_expiry_guard}, since a
    release with no expiry test at all is a fortiori early. *)
let s_reinsertion_restarts =
  let measured_from_last_insertion =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Cached_1, Formula.Not (atom Forgiven_1)),
           weak_until (atom Cached_1)
             (Formula.Or (atom Duration_elapsed_1, atom Forgiven_1)) ))
  in
  let no_queue_jump =
    Formula.Ag
      (Formula.Implies
         ( atom Younger_1,
           weak_until (atom Cached_1)
             (Formula.Or (Formula.Not (atom Cached_2), atom Forgiven_1)) ))
  in
  {
    name = "temp-ban-reinsertion-restarts-the-uniform-clock";
    bucket = Statements.Fairness;
    formula = Formula.And (measured_from_last_insertion, no_queue_jump);
    antecedent = atom Younger_1;
  }

(** The family's statements: one per deletable line of the temp-ban cache. *)
let all = [ s_never_early; s_always_ends; s_reinsertion_restarts ]

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
