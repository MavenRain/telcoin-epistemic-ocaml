(** The SUBDAG_LEADER_WALK statement family: three statements about ONE
    Bullshark commit walk over the round-2 leader L, the round-3 vote layer and
    the round-4 anchor A, encoded over the {!Subdag_leader_walk_model}
    interpreted system. Citations refer to Telcoin-Association/telcoin-network
    at 0c59c15b and were re-opened in that checkout.

    {1 Reading guide for the [K] operands}

    The single knowledge agent is V0, and its view is its own commit progress
    plus whether the peer's signed anchor output record has arrived (see
    {!Subdag_leader_walk_model} for why that is the honest projection: the
    commit act itself goes out only on a local channel, state.rs:456-460, but
    a signed record of the OUTPUT is gossiped, subscriber.rs:296-316).

    - S1's positive operand is [AG( commit_anchor_V3(A) -> L in
      committed_leaders_V3 )]: a claim about what the PEER's future commit walk
      must contain. It is not a projection of V0's view - the peer's progress
      is never in V0's view, and the arrival bit says only THAT the peer
      committed an anchor, never what its walk contained - and it is not rigid:
      in the (Low, Unlinked) world the peer commits the anchor and excludes L,
      so the operand is FALSE at reachable states. V0 knows it after a direct
      commit only through quorum intersection: the gate it just cleared means
      the supporters carry at least [validity_threshold()], the anchor's
      parents carry at least [quorum_threshold()], and those two sum to more
      than the total voting power (committee.rs:254-259, :686-688), so some
      authority is both - hence [linked(A, L)], hence the peer's walk-back must
      push L.
    - S1's negative operand [~K_V0( commit_anchor_V3(A) )] is the matching
      ignorance, and it is CONDITIONED on the peer's signed output record not
      having arrived. Peers really do publish their commits - a signed
      [ConsensusResult] carrying the subdag's [leader_round]
      (subscriber.rs:296-316, network/mod.rs:431-452) - so an unconditional
      ignorance claim here would be true only by omitting that channel. The
      model carries the channel, the ignorance conjunct is guarded by its
      non-arrival, and the third conjunct states the positive half: once the
      record arrives and verifies against the committee
      (handler.rs:307-338), V0 KNOWS the peer committed. Content of the peer's
      future commit is known from the quorum-intersection lemma alone;
      occurrence is known only from an authenticated report.
    - S2's operand is [AG ~direct_commit_V3(L)], a universally quantified
      GLOBAL NEGATIVE about another node's acts, past and future. Not rigid:
      in the (High, Linked) world the peer does direct-commit L.
    - S3 carries no [K]. Its content is temporal: the walk-back's obligation to
      give a linked leader a subdag of its OWN, which downstream consumers
      (per-subdag [ConsensusHeader] numbering subscriber.rs:363-367, reputation
      credit bullshark.rs:81-89) depend on.

    Every positive [K] here is discharged against R2 in
    test/t_subdag_leader_walk.ml: for each of the three positive [K] operands
    an operative state is exhibited whose V0-view class contains at least two
    reachable states, and each operand is shown false somewhere reachable. *)

open Subdag_leader_walk_model

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

(** S1 - supported-leader-commit-implies-known-universal-inclusion [safety].

    [AG( direct_commit_V0(L) -> K_V0( AG( commit_anchor_V3(A) -> L in
    committed_leaders_V3 ) )
    /\\ (~report_V0(V3 anchor) -> ~K_V0( commit_anchor_V3(A) ))
    /\\ ( report_V0(V3 anchor) -> K_V0( commit_anchor_V3(A) )) )].

    Conjunct A (positive knowledge of the peer's future walk content). A direct
    commit of L happens only through the f+1 support gate
    [if voting_power < self.committee.validity_threshold()]
    (bullshark.rs:194-206), so V0 having direct-committed L means L has >= f+1
    = 2 round-3 supporters. Every certificate carries >= 2f+1 = 3 round-3
    parents (the proposer's parent aggregator releases only at
    [committee.quorum_threshold()], aggregators/certificates.rs:92-99) and each
    authority contributes at most one round-3 certificate
    (aggregators/certificates.rs:83-85, state.rs:145-157), so over 4 authority
    slots the supporter set and the anchor's parent set must intersect: the
    anchor is [linked] to L (bullshark.rs:313-328). Any peer that then commits
    that anchor from [committed_round] below 2 has r = 2 in its walk-back range
    [(committed_round + 2 ..= leader.round() - 2).rev()] (bullshark.rs:290),
    finds L's certificate present - [check_parents] at insert (state.rs:114-122,
    :187-214) guarantees a node holding the anchor holds its two-round ancestor
    closure - and pushes it (bullshark.rs:301-305). So the operand holds at
    every state of V0's view class, i.e. V0 KNOWS it.

    Conjunct B (ignorance of the peer's occurrence, before the report lands).
    Subdags are emitted only on the local [consensus_bus.sequence()] channel
    (state.rs:456-460), so the commit act itself is silent, and while the
    peer's published record is still in flight the two states "peer idle" and
    "peer already committed the anchor, record undelivered" share V0's whole
    view. That is the witness pair.

    Conjunct C (knowledge of the peer's occurrence, after the report lands).
    The record is not hearsay: the receiver requires
    [committee.contains(&key)] and [signature.verify_secure(...)]
    (handler.rs:307-338) before it counts, and it carries
    [round = output.sub_dag().leader_round()] (subscriber.rs:297), so a
    verified round-4 record is an unforgeable attestation that the peer
    committed an anchor. Every state in V0's view class where the record has
    arrived therefore has [commit_anchor_V3] true, which is knowledge in the
    exact sense of the semantics. This conjunct is what stops conjunct B from
    being an artefact of a missing channel.

    Mutation pins. {!No_walk_back_inclusion} deletes bullshark.rs:300-306, so
    the peer commits the anchor and returns [[anchor]] alone: a reachable state
    with [commit_anchor_V3] true and L absent from V3's leaders enters V0's
    class and the [K] fails. {!No_leader_support_gate} deletes
    bullshark.rs:203-206, so V0 can direct-commit an unsupported L in the
    (Low, Unlinked) world, where the peer's walk-back legitimately skips it -
    the quorum-intersection premise dies and the [K] fails. Neither is
    repaired: [order_leaders] is the only multi-leader path in [commit_leader]
    (bullshark.rs:179-279); after the peer's anchor commit [committed_round] is
    4 so every later trigger short-circuits at [LeaderBelowCommitRound]
    (bullshark.rs:135-138); [utils::order_dag] (utils.rs:10-57) sequences L's
    certificates under the anchor but never puts L in the leader sequence; and
    the [ScheduleChanged] retry (bullshark.rs:141-152) re-runs only the same
    anchor round. *)
let s1 =
  let peer_inclusion =
    Formula.Ag
      (Formula.Implies (atom Anchor_committed_v3, atom L_in_leaders_v3))
  in
  let known_inclusion = Formula.K (Validator.V0, peer_inclusion) in
  let knows_occurrence =
    Formula.K (Validator.V0, atom Anchor_committed_v3)
  in
  let unknown_before_report =
    Formula.Implies
      (Formula.Not (atom Peer_anchor_report_v0), Formula.Not knows_occurrence)
  in
  let known_after_report =
    Formula.Implies (atom Peer_anchor_report_v0, knows_occurrence)
  in
  {
    name = "supported-leader-commit-implies-known-universal-inclusion";
    bucket = Statements.Safety;
    formula =
      Formula.Ag
        (Formula.Implies
           ( atom Direct_commit_l_v0,
             Formula.And
               ( known_inclusion,
                 Formula.And (unknown_before_report, known_after_report) ) ));
    antecedent = atom Direct_commit_l_v0;
  }

(** S2 - unlinked-leader-skip-implies-known-global-no-direct-commit [security].

    [AG( (commit_anchor_V0(A) /\\ ~subdag_V0(leader=L)) -> K_V0( AG
    ~direct_commit_V3(L) ) )].

    The antecedent is V0's SKIP: it committed the anchor and L is not among its
    committed leaders. Pristine that state arises exactly one way - the
    walk-back found L's certificate at r = 2 (present, by [check_parents]
    closure) and [self.linked(leader, prev_leader, &state.dag)]
    (bullshark.rs:301) returned false, so nothing was pushed.

    Why the skip licenses a GLOBAL negative. [linked] is objective: the
    anchor's parent digests are fixed in the anchor certificate and any node
    holding it holds that closure (state.rs:114-122, :187-214), so unlinkedness
    is not an artefact of V0's partial view. Contrapositive of the pigeonhole
    used in S1: if f+1 = 2 round-3 certificates named L, one of them would be
    among the anchor's >= 3 round-3 parents and L would be linked. So unlinked
    means at most f = 1 supporter exists ANYWHERE - each authority having at
    most one round-3 certificate - and a peer's voting-power sum, which ranges
    over its own dag and is therefore no larger, can never reach
    [validity_threshold()]. The gate at bullshark.rs:203-206 can never pass at
    any node, past or future.

    R2 note: the operand is not rigid - in the (High, Linked) world the peer
    does direct-commit L - and V0's class at the skip state contains at least
    two reachable states, differing in whether the peer has committed its own
    anchor yet.

    Mutation pin. {!No_leader_support_gate} deletes bullshark.rs:203-206, so
    the peer direct-commits an unsupported L in the very (Low, Unlinked) world
    where V0 skipped it: a state with [direct_commit_V3(L)] enters V0's class
    and the [K] fails. No sibling repairs the deletion: that comparison is the
    ONLY support check between [leader_certificate]
    (leader_schedule.rs:311-326, which filters nothing) and [order_leaders],
    whose own gate is linkedness and applies only to previous leaders
    (bullshark.rs:301); [process_certificate] (bullshark.rs:107-171) adds no
    second check. {!No_walk_back_inclusion} also refutes it, for the different
    reason that a skip then carries no information at all - the walk is gone,
    so the skip state stops implying unlinkedness and V0's class grows to
    include the supported world. *)
let s2 =
  let skipped =
    Formula.And (atom Anchor_committed_v0, Formula.Not (atom L_subdag_v0))
  in
  let no_peer_direct_commit =
    Formula.Ag (Formula.Not (atom Direct_commit_l_v3))
  in
  {
    name = "unlinked-leader-skip-implies-known-global-no-direct-commit";
    bucket = Statements.Security;
    formula =
      Formula.Ag
        (Formula.Implies
           (skipped, Formula.K (Validator.V0, no_peer_direct_commit)));
    antecedent = skipped;
  }

(** S3 - linked-uncommitted-leader-eventually-anchors-its-own-subdag
    [liveness].

    [AG( (linked(A,L) /\\ ~subdag_V0(leader=L)) -> AF subdag_V0(leader=L) )].

    Whenever the anchor is linked to L and V0 has not yet given L a subdag of
    its own, it eventually does - either by clearing the f+1 gate itself
    (bullshark.rs:203-206) or, with no support at all, by the walk-back
    (bullshark.rs:301-305). The target is deliberately LEADER-ANCHORED: a
    [CommittedSubDag] whose [leader] is L and whose [sub_dag_index] is
    [leader.nonce()] (bullshark.rs:218, :240-246), which is what buys L its own
    [ConsensusHeader] number downstream ([number = last_number + 1] per subdag,
    subscriber.rs:363-367) and the reputation credit awarded only against
    [state.last_committed_sub_dag.leader()] (bullshark.rs:81-89).

    R8 / R5 note - this phrasing is forced by a repair path that really exists.
    The naive claim "a linked leader's certificates eventually commit" is
    SILENTLY REPAIRED by [utils::order_dag] (utils.rs:10-57), which walks the
    anchor's whole ancestor closure and sweeps L's certificates into A's subdag
    even with the walk-back deleted. The model carries that repair explicitly
    as {!Subdag_leader_walk_model.L_certs_sequenced_v0}, and
    test/t_subdag_leader_walk_mutation.ml asserts that the naive leads-to still
    HOLDS under the mutation while this statement flips - so the pin is not an
    artefact of an omitted path.

    Mutation pin. {!No_walk_back_inclusion} deletes bullshark.rs:300-306, so in
    the (Low, Linked) world - L linked but with only f supporters, hence
    ineligible for a direct commit - V0's only move from idle is a bare anchor
    commit and [subdag_V0(leader=L)] becomes unreachable, refuting the [AF].
    Nothing recovers it: [committed_round] is then 4, so a later round-3
    certificate short-circuits at [LeaderBelowCommitRound]
    (bullshark.rs:135-138), and the [ScheduleChanged] retry
    (bullshark.rs:141-152) re-elects only for the same anchor round.
    {!No_leader_support_gate} deliberately does NOT refute this statement: it
    only adds direct commits, which also produce an L-led subdag, so
    attribution stays clean. *)
let s3 =
  let pending =
    Formula.And (atom Linked_anchor_l, Formula.Not (atom L_subdag_v0))
  in
  {
    name = "linked-uncommitted-leader-eventually-anchors-its-own-subdag";
    bucket = Statements.Liveness;
    formula = Formula.leads_to pending (atom L_subdag_v0);
    antecedent = pending;
  }

(** The family's statements. *)
let all = [ s1; s2; s3 ]

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
