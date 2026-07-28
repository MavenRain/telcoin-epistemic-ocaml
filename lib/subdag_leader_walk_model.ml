(** Finite interpreted system for the SUBDAG_LEADER_WALK family: ONE Bullshark
    commit walk over a four-round DAG window, abstracted from
    Telcoin-Association/telcoin-network (all citations re-opened in this
    checkout at git HEAD 0c59c15b).

    {1 The modeled mechanism}

    Committee of four with equal voting power, so f = 1, quorum (2f+1) = 3 and
    [validity_threshold] (f+1) = 2 - the last is [total.div_ceil 3] on a total
    voting power of 4 (crates/types/src/committee.rs:254-259). The window is:
    an even leader round r = 2 with leader certificate L, the vote round r+1 =
    3, and the next even leader round r' = 4 with leader certificate A (the
    "anchor"). Round-robin leader election is a pure function of the round and
    the swap table (leader_schedule.rs:285-303), and
    [LeaderSchedule::leader_certificate] does NO support filtering whatsoever
    (leader_schedule.rs:311-326).

    Three gates of [Bullshark] act on that window, and they are the whole
    content of this family:

    - DIRECT COMMIT (the f+1 support gate,
      crates/consensus/primary/src/consensus/bullshark.rs:194-206): a node sums
      the voting power of the round-3 certificates that name L among their
      parents and bails out with [Outcome::NotEnoughSupportForLeader] when
      [voting_power < self.committee.validity_threshold()]. Only a node that
      clears this gate commits L on its own initiative.
    - WALK-BACK INCLUSION (bullshark.rs:290-307): a node committing the anchor
      A from [committed_round] below r walks
      [(state.last_round.committed_round + 2 ..= leader.round() - 2).rev()] -
      with [committed_round = 0] and [leader.round() = 4] that range is exactly
      [[2]] - looks up L with [leader_certificate], and does
      [to_commit.push_front(prev_leader.clone())] {e iff}
      [self.linked(leader, prev_leader, &state.dag)] (bullshark.rs:301-305).
      The walk-back gate is LINKEDNESS, never support: an f-supported leader
      that happens to be an ancestor of the anchor is still included.
    - PER-LEADER SUBDAG (bullshark.rs:217-246): every queued leader is popped
      oldest-first, takes [let sub_dag_index = leader.nonce()] (bullshark.rs:218)
      and becomes its own [CommittedSubDag::new(sequence, leader.clone(),
      sub_dag_index, ...)] (bullshark.rs:240-246). Each subdag is a separate
      output: one [ConsensusHeader] number apiece downstream
      (executor/src/subscriber.rs:356-367, [number = last_number + 1] per
      subdag), and the reputation credit for a leader's supporters is awarded
      only against [state.last_committed_sub_dag.leader()]
      (bullshark.rs:81-89). So "L anchors its own subdag" is an observable
      consequence, not a modeling flourish.

    {1 The two objective globals, and why [High] forces [Linked]}

    [support] is the GLOBAL number of round-3 certificates naming L, collapsed
    to [Low] (<= f = 1) or [High] (>= f+1 = 2). [link] is the objective
    ancestry relation [linked(A, L)] (bullshark.rs:313-328): some round-3
    parent of A names L.

    Both are node-independent facts about certificates:
    - each authority contributes at most one round-3 certificate (the proposer
      aggregator refuses a second certificate from an authority already seen,
      aggregators/certificates.rs:75-102, and the dag insert rejects a
      conflicting certificate at the same (round, origin) with
      [ConsensusError::CertificateEquivocation], state.rs:145-157);
    - A carries >= 2f+1 = 3 round-3 parents, because a header is only proposed
      once its parent aggregator reaches [committee.quorum_threshold()]
      (aggregators/certificates.rs:92-99);
    - a node that holds A holds A's round-3 parents, and their round-2 parents,
      because [try_insert] runs [check_parents] (state.rs:114-122 passes
      [check_parents = true]; the check itself is state.rs:187-214). So
      [linked] evaluated anywhere equals the objective relation, and L's
      certificate is present at any node that holds a linked A.

    Quorum intersection, in the STAKE form the code actually uses: the
    supporter set carries at least [validity_threshold()] = [ceil(total/3)] and
    the anchor's parent set carries at least [quorum_threshold()] =
    [2*total/3 + 1] (committee.rs:254-259, :686-688), and those two sum to more
    than [total], so the two sets must share an authority. With four
    equal-power authorities that is the familiar count form: 2 supporters + 3
    anchor parents > 4 slots. Hence the world (High, Unlinked) does not exist
    and is not an initial state; the model has exactly three worlds, and this
    invariant is what makes the two knowledge claims below TRUE rather than
    merely stated.

    {1 Components and role mapping}

    - [support], [link]: the two objective globals above, fixed at the initial
      branch and never mutated (certificates are immutable).
    - [p0], [p3]: the commit progress of the two modeled nodes, V0 and V3.
    - [anchor_report]: whether V3's signed [ConsensusResult] gossip for its
      ANCHOR output has reached V0 (see below). This is the only cross-node
      information channel in the model and it is deliberately present rather
      than omitted.
    - V0 is the KNOWLEDGE AGENT of all three statements; its view is its own
      commit progress [p0] together with [anchor_report]. V3 is a modeled peer
      that also carries a real (non-constant) view of its own progress [p3],
      but does not appear under [K] in this family. V1, V2 and V4..V9 are idle
      non-agents with the constant blank view and NEVER appear under [K].

    {2 Why V0's view is [(p0, anchor_report)] and nothing more}

    A node's commit sequence is emitted on a purely LOCAL channel -
    [self.consensus_bus.sequence().send(committed_sub_dag)] (state.rs:456-460,
    inside [Consensus::new_certificate], state.rs:383-479) - so the commit act
    itself tells peers nothing. But it is NOT true that a peer's commits are
    invisible, and pretending so would be exactly the kind of omission that
    makes an ignorance claim cheap. After the subdag's batches are fetched, the
    executor publishes a SIGNED record of the output -
    [self.network_handle.publish_consensus(epoch, round, number, this_digest,
    public_key, sig)] (executor/src/subscriber.rs:296-316) - as
    [PrimaryGossip::Consensus(ConsensusResult { epoch, round, number, hash,
    validator, signature })] on the consensus-output topic
    (primary/src/network/mod.rs:431-452). A receiver checks
    [committee.contains(&key)] and [signature.verify_secure(...)]
    (primary/src/network/handler.rs:307-338), so an arriving record is an
    unforgeable attestation that that validator produced consensus output for
    that [round] - knowledge, not belief. [round] is
    [output.sub_dag().leader_round()] (subscriber.rs:297), so a round-4 record
    identifies an ANCHOR commit specifically.

    [anchor_report] models exactly that record's arrival: it can flip only once
    V3 has committed the anchor, and once flipped V0 KNOWS V3 committed it.
    Gossip is asynchronous, so the un-arrived state is equally real, and that
    is where V0's ignorance of the peer's occurrence lives. The peer's
    round-2 (L-subdag) record is deliberately NOT modeled, and it is safe to
    leave out precisely because it cannot discriminate: an L-led subdag is
    published both by a node that direct-committed L at [committed_round = 2]
    and by a node that reached L through the anchor's walk-back, so a round-2
    record alone never reveals an anchor commit.

    What V0 learns from its own progress is exactly what its own walk
    computed:
    - at [P_direct_l] it ran the support sum and the gate passed, so it knows
      [support = High];
    - at [P_walk_both] it ran [linked] and pushed L, so it knows
      [link = Linked] - and it did NOT run the support sum, because
      [order_leaders] contains no support check (bullshark.rs:290-307) and it
      never will: once [committed_round] passes r every later trigger
      short-circuits at [Outcome::LeaderBelowCommitRound]
      (bullshark.rs:135-138). A node that reaches L only through the walk-back
      genuinely does not know whether L had f+1 support;
    - at [P_anchor_only] it ran [linked] and got false, so it knows
      [link = Unlinked].
    Each of those is a function of [p0], so [p0] is the whole of V0's
    information about the globals.

    {1 Premises made explicit (rather than omitted)}

    - Both nodes start at [committed_round = 0], which is what puts r = 2 in
      the anchor's walk-back range at all; a node whose [committed_round] is
      already >= r skips L by range arithmetic, and that case is excluded by
      the statements' antecedents, not by the model pretending it cannot
      happen.
    - Both nodes agree on who the round-2 leader is. [leader] is a
      deterministic function of the round and the swap table
      (leader_schedule.rs:285-303), and the swap table is replaced only by
      [update_leader_schedule] AFTER a subdag has been popped
      (bullshark.rs:267-275, :333-351). Within this window both nodes enter
      with [committed_round = 0] and therefore with the same swap table, and
      [order_leaders] is called before any update in the same call
      (bullshark.rs:215), so the round-2 lookup agrees at both nodes.
    - The certificates that trigger a commit are eventually delivered: the
      model schedules the round-3 and round-5 triggers as a nondeterministic
      CHOICE (which arrives first) but not as a possible non-arrival. Bullshark
      needs that delivery assumption for any liveness at all; the liveness
      statement of this family is about what the walk is OBLIGED to do once the
      anchor commit fires, and its refuting mutation deletes that obligation,
      not the delivery.
    - Equivocation is excluded, as the code excludes it (state.rs:145-157,
      aggregators/certificates.rs:83-85). *)

(** The GLOBAL f+1 support level of the round-2 leader L: [Low] = at most
    f = 1 round-3 certificate names L, [High] = at least f+1 = 2 do. This is
    the quantity [commit_leader] sums and compares against
    [committee.validity_threshold()] (bullshark.rs:194-206). *)
type support = Low | High

(** Total order index for {!support}. *)
let support_index = function Low -> 0 | High -> 1

(** Total order on {!support}. *)
let support_compare a b = Int.compare (support_index a) (support_index b)

(** [true] iff L has f+1 support, i.e. the direct-commit gate can pass. *)
let support_is_high = function Low -> false | High -> true

(** The objective ancestry relation [linked(A, L)] of bullshark.rs:313-328:
    [Linked] iff some round-3 parent of the anchor A names L among its own
    parents. Node-independent, because [check_parents] (state.rs:187-214)
    guarantees any node holding A holds that whole two-round closure. *)
type link = Unlinked | Linked

(** Total order index for {!link}. *)
let link_index = function Unlinked -> 0 | Linked -> 1

(** Total order on {!link}. *)
let link_compare a b = Int.compare (link_index a) (link_index b)

(** [true] iff the anchor is linked to L, i.e. the walk-back inclusion gate
    (bullshark.rs:301) passes. *)
let link_is_linked = function Unlinked -> false | Linked -> true

(** One node's commit progress over this window. Monotone: certificates are
    only ever added and [committed_round] only ever rises. *)
type progress =
  | P_idle
      (** [committed_round = 0]; no subdag emitted yet. Neither trigger
          processed. *)
  | P_direct_l
      (** the round-3 trigger arrived first and the f+1 support gate PASSED
          (bullshark.rs:203-206), so this node committed L on its own
          initiative: one subdag with leader L and [sub_dag_index = L.nonce()]
          (bullshark.rs:218, :240-246). [committed_round = 2]. *)
  | P_walk_both
      (** the round-5 trigger arrived first from [committed_round = 0], the
          walk-back found L linked and pushed it (bullshark.rs:301-305), so
          this node emitted TWO subdags oldest-first (bullshark.rs:217): L's
          then A's. [committed_round = 4]. *)
  | P_anchor_only
      (** the round-5 trigger arrived first, the walk-back found L present but
          NOT linked, so nothing was pushed and only A's subdag was emitted.
          [committed_round = 4]. *)
  | P_direct_then_anchor
      (** L was direct-committed first, then the anchor: with
          [committed_round = 2] the walk-back range
          [(2 + 2 ..= 4 - 2)] is EMPTY, so the anchor commits alone on top of
          the already-emitted L subdag. [committed_round = 4]. *)

(** Total order index for {!progress}. *)
let progress_index = function
  | P_idle -> 0
  | P_direct_l -> 1
  | P_walk_both -> 2
  | P_anchor_only -> 3
  | P_direct_then_anchor -> 4

(** Total order on {!progress}. *)
let progress_compare a b = Int.compare (progress_index a) (progress_index b)

(** [true] iff this node cleared the f+1 support gate and direct-committed L
    itself. *)
let committed_l_directly = function
  | P_direct_l | P_direct_then_anchor -> true
  | P_idle | P_walk_both | P_anchor_only -> false

(** [true] iff this node has committed a subdag anchored at A. *)
let committed_anchor = function
  | P_walk_both | P_anchor_only | P_direct_then_anchor -> true
  | P_idle | P_direct_l -> false

(** [true] iff this node emitted a [CommittedSubDag] whose leader is L and
    whose [sub_dag_index] is [L.nonce()] - the leader-anchored subdag, not
    merely L's certificates somewhere in a closure. *)
let has_l_subdag = function
  | P_direct_l | P_walk_both | P_direct_then_anchor -> true
  | P_idle | P_anchor_only -> false

(** Arrival at V0 of the peer's signed [ConsensusResult] gossip for its ANCHOR
    output: [Unreported] while the record is still in flight (or was never
    produced), [Reported] once it has arrived and verified
    (subscriber.rs:296-316, network/mod.rs:431-452, handler.rs:307-338). *)
type report = Unreported | Reported

(** Total order index for {!report}. *)
let report_index = function Unreported -> 0 | Reported -> 1

(** Total order on {!report}. *)
let report_compare a b = Int.compare (report_index a) (report_index b)

(** [true] iff V0 has received and verified the peer's anchor-output record. *)
let report_seen = function Unreported -> false | Reported -> true

(** The joint global state: the two objective certificate facts, the two
    modeled nodes' commit progress, and the one cross-node channel. [p0] is V0
    (the knowledge agent), [p3] is the peer V3, [anchor_report] is V3's anchor
    [ConsensusResult] as seen by V0. *)
type state = {
  support : support;
  link : link;
  p0 : progress;
  p3 : progress;
  anchor_report : report;
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = support_compare s1.support s2.support in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = link_compare s1.link s2.link in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = progress_compare s1.p0 s2.p0 in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = progress_compare s1.p3 s2.p3 in
        if Bool.not (Int.equal c3 0) then c3
        else report_compare s1.anchor_report s2.anchor_report

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    [View_local_walk] is V0's projection: its own commit progress - which
    subdags it emitted and what its own walk computed - plus whether the peer's
    signed anchor record has arrived. It carries NO component of [p3] itself,
    because a commit act travels only on the local [consensus_bus.sequence()]
    channel (state.rs:456-460); the only thing that crosses the network is the
    published record, and that is [anchor_report].

    [View_peer_walk] is V3's projection: its own commit progress. V3 never
    appears under [K] in this family, but its view is real and non-constant
    rather than blank, because it is a committee member running the same code.

    [View_idle] is the constant blank view of the non-agents V1, V2 and
    V4..V9. *)
type view =
  | View_local_walk of progress * report
  | View_peer_walk of progress
  | View_idle

(** Total deterministic order over ALL fields of V0's view. *)
let view_local_compare (pa, ra) (pb, rb) =
  let c = progress_compare pa pb in
  if Bool.not (Int.equal c 0) then c else report_compare ra rb

(** Total order on views: [View_idle] < [View_local_walk] < [View_peer_walk],
    with the field-wise order within each constructor. Every constructor is
    spelled: no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_local_walk _ | View_peer_walk _) -> -1
  | (View_local_walk _ | View_peer_walk _), View_idle -> 1
  | View_local_walk (pa, ra), View_local_walk (pb, rb) ->
      view_local_compare (pa, ra) (pb, rb)
  | View_local_walk _, View_peer_walk _ -> -1
  | View_peer_walk _, View_local_walk _ -> 1
  | View_peer_walk pa, View_peer_walk pb -> progress_compare pa pb

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 is the knowledge agent of every statement in this
    family and V3 is the modeled peer; both have a real, non-constant view of
    their own commit progress. V1, V2 and V4..V9 are idle non-agents with the
    constant blank view and never appear under [K]. *)
let view v s =
  match v with
  | Validator.V0 -> View_local_walk (s.p0, s.anchor_report)
  | Validator.V3 -> View_peer_walk s.p3
  | Validator.V1 | Validator.V2 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine  (** the code as it stands at 0c59c15b *)
  | No_leader_support_gate
      (** delete the f+1 support gate bullshark.rs:203-206 -
          [if voting_power < self.committee.validity_threshold() { debug!(...);
          return Ok((Outcome::NotEnoughSupportForLeader, vec![])); }] - so
          [commit_leader] proceeds for ANY leader certificate it finds. This
          adds the transition [P_idle -> P_direct_l] in the [Low] worlds at
          BOTH nodes (the gate is in every node's copy of the code), so an
          unsupported L can be direct-committed while another node's walk-back
          skips it as unlinked.

          No sibling path repairs it. [commit_leader] (bullshark.rs:179-279)
          has exactly one threshold check, between the [leader_certificate]
          lookup and [order_leaders]; [leader_certificate]
          (leader_schedule.rs:311-326) does no support filtering at all - it
          returns whatever certificate sits at (round, leader) in the dag;
          [order_leaders]' gate (bullshark.rs:301) is LINKEDNESS and it applies
          only to PREVIOUS leaders, never to the leader that
          [commit_leader] was called with; and [process_certificate]
          (bullshark.rs:107-171) contains no second support check - its only
          guards are the dag insert, the odd-round bail-out and
          [LeaderBelowCommitRound]. *)
  | No_walk_back_inclusion
      (** delete the inclusion block bullshark.rs:300-306 -
          [if self.linked(leader, prev_leader, &state.dag) {
          to_commit.push_front(prev_leader.clone()); leader = prev_leader; }] -
          so [order_leaders] returns just [[anchor]]. This replaces
          [P_idle -> P_walk_both] with [P_idle -> P_anchor_only] in the
          [Linked] worlds: the anchor still commits, L's certificates are still
          sequenced, but L never becomes the leader of a subdag of its own.

          No sibling path repairs the LEADER-ANCHORED effect, and the model
          keeps the repair path that does exist so the difference is visible.
          [utils::order_dag] (utils.rs:10-57) walks the anchor's whole ancestor
          closure, so under this mutation L's CERTIFICATES are still committed
          inside A's subdag whenever L is an ancestor - that is why
          {!L_certs_sequenced_v0} stays true at [P_anchor_only] in a [Linked]
          world, and why the naive claim "L's certificates eventually commit"
          would be silently repaired. What [order_dag] cannot re-establish is a
          [CommittedSubDag] whose [leader] is L and whose [sub_dag_index] is
          [L.nonce()] (bullshark.rs:218, :240-246), hence a separate
          [ConsensusHeader] number downstream (subscriber.rs:363-367) and the
          reputation credit that is awarded only against
          [last_committed_sub_dag.leader()] (bullshark.rs:81-89). Nor does any
          later trigger recover it: once the anchor commits, [committed_round]
          is 4 and every later round-3 certificate short-circuits at
          [Outcome::LeaderBelowCommitRound] (bullshark.rs:135-138), while the
          [Outcome::ScheduleChanged] retry (bullshark.rs:141-152) re-runs
          [commit_leader] for the SAME anchor round with the new schedule and
          never fabricates a subdag for L. *)

(** The direct-commit move out of [P_idle]: the round-3 trigger arrives and the
    f+1 support gate (bullshark.rs:203-206) decides. {!No_leader_support_gate}
    deletes the comparison, so the move is enabled at [Low] too. *)
let direct_moves mut support =
  match (mut, support) with
  | Pristine, Low -> []
  | Pristine, High -> [ P_direct_l ]
  | No_walk_back_inclusion, Low -> []
  | No_walk_back_inclusion, High -> [ P_direct_l ]
  | No_leader_support_gate, Low -> [ P_direct_l ]
  | No_leader_support_gate, High -> [ P_direct_l ]

(** The anchor-commit move out of [P_idle] with [committed_round = 0]: the
    walk-back range is [[2]] and the inclusion gate (bullshark.rs:301) decides
    whether L is pushed. {!No_walk_back_inclusion} deletes the push, collapsing
    both branches onto [P_anchor_only]. *)
let anchor_moves mut link =
  match (mut, link) with
  | Pristine, Unlinked -> [ P_anchor_only ]
  | Pristine, Linked -> [ P_walk_both ]
  | No_leader_support_gate, Unlinked -> [ P_anchor_only ]
  | No_leader_support_gate, Linked -> [ P_walk_both ]
  | No_walk_back_inclusion, Unlinked -> [ P_anchor_only ]
  | No_walk_back_inclusion, Linked -> [ P_anchor_only ]

(** One node's enabled single-step moves. From [P_idle] the two triggers race;
    from [P_direct_l] the anchor commits alone (the walk-back range is empty at
    [committed_round = 2], so no mutation touches this arm); the three
    [committed_round = 4] states are terminal and stutter-closed by the
    kernel. *)
let progress_next mut support link p =
  match p with
  | P_idle -> direct_moves mut support @ anchor_moves mut link
  | P_direct_l -> [ P_direct_then_anchor ]
  | P_walk_both -> []
  | P_anchor_only -> []
  | P_direct_then_anchor -> []

(** Delivery of the peer's signed anchor [ConsensusResult] to V0. It becomes
    available only once V3 has actually committed an anchor subdag, because the
    record is published from [handle_consensus_output]
    (subscriber.rs:296-316), and it is monotone: gossip once verified is not
    forgotten. No mutation touches this channel - both gate deletions are
    inside [Bullshark], not in the executor or the network handler. *)
let report_next s =
  match s.anchor_report with
  | Reported -> []
  | Unreported ->
      if committed_anchor s.p3 then [ { s with anchor_report = Reported } ]
      else []

(** The transition relation: the two nodes advance independently, one node per
    step, and the peer's published anchor record may arrive at V0 as its own
    step. [support] and [link] are certificate facts and never change. *)
let next_with mut s =
  List.concat
    [
      List.map
        (fun p -> { s with p0 = p })
        (progress_next mut s.support s.link s.p0);
      List.map
        (fun p -> { s with p3 = p })
        (progress_next mut s.support s.link s.p3);
      report_next s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** Initial world 1 of 3: L has f+1 support, so by quorum intersection it is
    necessarily linked to the anchor. Both nodes idle at
    [committed_round = 0], nothing published yet. *)
let initial =
  {
    support = High;
    link = Linked;
    p0 = P_idle;
    p3 = P_idle;
    anchor_report = Unreported;
  }

(** Initial world 2 of 3: L has at most f support - so no node can ever
    direct-commit it - yet its single supporter happens to be an anchor parent,
    so the anchor's walk-back still includes it. This world is the whole reason
    the walk-back gate is linkedness and not support. *)
let initial_unsupported_linked =
  {
    support = Low;
    link = Linked;
    p0 = P_idle;
    p3 = P_idle;
    anchor_report = Unreported;
  }

(** Initial world 3 of 3: L has at most f support and is not an ancestor of the
    anchor, so every walk-back skips it. The excluded fourth world
    (High, Unlinked) is impossible by quorum intersection: the supporter stake
    and the anchor's parent stake together exceed the total. *)
let initial_unsupported_unlinked =
  {
    support = Low;
    link = Unlinked;
    p0 = P_idle;
    p3 = P_idle;
    anchor_report = Unreported;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Support_quorum_high
      (** L has >= f+1 = 2 round-3 supporters: the global quantity
          [commit_leader] compares against [validity_threshold()]
          (bullshark.rs:194-206) *)
  | Linked_anchor_l
      (** [linked(A, L)] holds: some round-3 parent of the anchor names L
          (bullshark.rs:313-328) *)
  | Direct_commit_l_v0
      (** V0 cleared the f+1 support gate and committed L on its own
          initiative *)
  | Direct_commit_l_v3  (** the same act at the peer V3 *)
  | Anchor_committed_v0
      (** V0 has committed a subdag anchored at A (leader round 4) *)
  | Anchor_committed_v3  (** the same at the peer V3 *)
  | L_subdag_v0
      (** V0 emitted a [CommittedSubDag] whose leader is L and whose
          [sub_dag_index] is [L.nonce()] (bullshark.rs:218, :240-246) *)
  | L_in_leaders_v3
      (** L appears in V3's committed leader sequence, i.e. V3 emitted an
          L-led subdag of its own *)
  | L_certs_sequenced_v0
      (** L's CERTIFICATE is inside some subdag V0 emitted - true also when V0
          committed only the anchor in a [Linked] world, because
          [utils::order_dag] (utils.rs:10-57) sweeps the anchor's whole
          ancestor closure. This atom exists so the model CARRIES the repair
          path that {!No_walk_back_inclusion} does not remove. *)
  | Peer_anchor_report_v0
      (** V0 has received and signature-verified the peer's published
          [ConsensusResult] for its anchor output (subscriber.rs:296-316,
          network/mod.rs:431-452, handler.rs:307-338) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Support_quorum_high -> support_is_high s.support
  | Linked_anchor_l -> link_is_linked s.link
  | Direct_commit_l_v0 -> committed_l_directly s.p0
  | Direct_commit_l_v3 -> committed_l_directly s.p3
  | Anchor_committed_v0 -> committed_anchor s.p0
  | Anchor_committed_v3 -> committed_anchor s.p3
  | L_subdag_v0 -> has_l_subdag s.p0
  | L_in_leaders_v3 -> has_l_subdag s.p3
  | L_certs_sequenced_v0 ->
      has_l_subdag s.p0 || (committed_anchor s.p0 && link_is_linked s.link)
  | Peer_anchor_report_v0 -> report_seen s.anchor_report

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Support_quorum_high -> "support(L) >= f+1"
  | Linked_anchor_l -> "linked(A,L)"
  | Direct_commit_l_v0 -> "direct_commit_V0(L)"
  | Direct_commit_l_v3 -> "direct_commit_V3(L)"
  | Anchor_committed_v0 -> "commit_anchor_V0(A)"
  | Anchor_committed_v3 -> "commit_anchor_V3(A)"
  | L_subdag_v0 -> "subdag_V0(leader=L)"
  | L_in_leaders_v3 -> "L in committed_leaders_V3"
  | L_certs_sequenced_v0 -> "certs(L) sequenced at V0"
  | Peer_anchor_report_v0 -> "anchor ConsensusResult(V3) seen by V0"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every
    reachable world by test/t_subdag_leader_walk_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation. The three initial states are the three
    possible (support, link) worlds; (High, Unlinked) is absent because quorum
    intersection forbids it. *)
let spec_of mut =
  {
    Checker.init =
      [ initial; initial_unsupported_linked; initial_unsupported_unlinked ];
    next = next_with mut;
    view;
    label;
  }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
