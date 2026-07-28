(** The PEER_PRUNE_FAIRNESS statement family, encoded over the
    {!Peer_prune_fairness_model} interpreted system: three properties of ONE
    heartbeat connection-limit prune round
    ([PeerManager::prune_connected_peers], manager.rs:560-594, fed by
    [AllPeers::connected_peers_by_score_and_routability], all_peers.rs:965-978).
    File citations refer to Telcoin-Association/telcoin-network at 0c59c15b.

    S1 is the ordering guarantee (who goes when scores differ), S2 the
    tie-break guarantee (nobody is starved when they do not) and S3 the
    exemption carve-out together with its recognition gap.

    {1 Reading guide for the epistemic operands}

    This family asserts NO positive [K]. The pruning node V0 holds the
    committee sets, the operator allowlist and every peer score in its own peer
    store, so every positive knowledge claim available in this slice would be a
    projection of V0's own view and R1 rejects it. What is genuinely hidden
    from V0 is the ground-truth committee membership of a peer it has not
    IDENTIFIED: [is_peer_validator] resolves through [identity_for] and answers
    [false] on the [PeerIdentity::Unidentified(_)] arm (all_peers.rs:836-845),
    and committee members whose libp2p id is not yet recoverable are skipped
    outright when the committees are installed (all_peers.rs:1196-1235,
    "others are trusted lazily on discovery").

    So the only [K] operands here are the two NEGATIVE ones in S3 conjunct D,
    and both are witnessed: [Unconfirmed_member] and [Unconfirmed_outsider]
    states with identical connection statuses and identical capacity are
    view-identical to V0 (the view carries [Tok_unidentified] for both,
    {!Peer_prune_fairness_model.xtoken_of}) and disagree on
    [committee_member(x)]. Each half of the conjunction is the non-trivial one
    at one member of that pair, so neither half is carried by the state that
    falsifies its operand. test/t_peer_prune_fairness.ml asserts both witness
    directions with [satisfiable]. *)

open Peer_prune_fairness_model

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

(** S1 - excess-prune-drops-the-lowest-scored-candidate-first [fairness].

    Heartbeat connection-limit pruning is a score-ordered discipline: while any
    LOW-bucket candidate is still connected, no HIGH-bucket peer has been
    dropped -

    AG( (connected(a) \/ connected(b)) ->
        connected(c) /\ connected(x) /\ connected(y) ).

    Grounding: [connected_peers_by_score_and_routability] hands
    [prune_connected_peers] a vector sorted by [(peer.score(),
    peer.is_routable())], "lowest score first"
    (all_peers.rs:976, doc at :961-964; [Score] orders on [aggregate_score]
    alone, score.rs:197-203). The candidate filter is an order-preserving
    [filter_map] (manager.rs:571-581) and the eviction loop is a plain [for]
    over its output (manager.rs:583-594), so the prefix that gets dropped is
    the lowest-scored prefix. The model holds [is_routable] equal across the
    roster (peer.rs:426-428) so the composite key reduces to the score, which
    is the conservative reading: with routability varying the order is
    refined, never reversed.

    A well-behaved peer therefore cannot be sacrificed while a worse-scored
    candidate keeps its slot. [~connected(p)] is an eviction verdict rather
    than a bare status because the round is one synchronous [&mut self] call:
    no reputation disconnect, no ban and no reconnection can interleave it (see
    the scope section of {!Peer_prune_fairness_model}), so the only thing that
    drops a peer here is this loop. The claim is stated over the whole HIGH bucket,
    including the two exempt peers, so it is also the statement that the
    exemption filter does not reorder anything: exempt peers are removed from
    the candidate list, not moved within it.

    Mutation pin: {!Peer_prune_fairness_model.No_score_sort} deletes
    [connected_peers.sort_by_key(...)] (all_peers.rs:976). The shuffle at :974
    survives, so the eviction order becomes an arbitrary permutation of the
    candidates and the ADDED transitions drop [Pc] (or an unrecognized [Px], or
    a de-exempted [Py]) while [Pa] and [Pb] are still connected - refuting the
    conjunct at every initial state. No sibling repairs it: nothing downstream
    re-orders the vector, and [collect_excess_peers] (all_peers.rs:996-1034),
    the crate's only other eviction-ordering code, orders BANNED and
    DISCONNECTED pruning by [Instant] and never touches the connected set.

    S1 is deliberately NOT pinned by the other three deletions and survives all
    of them: deleting the shuffle leaves a score-ordered (merely deterministic)
    walk, and the two exemption deletions change who is a candidate without
    touching the order. That is asserted in
    test/t_peer_prune_fairness_mutation.ml so the pin stays attributable. *)
let s1 =
  let score_ordered =
    Formula.Ag
      (Formula.Implies
         ( Formula.Or (atom Conn_a, atom Conn_b),
           Formula.And
             ( atom Conn_c,
               Formula.And (atom Conn_x, atom Conn_y) ) ))
  in
  {
    name = "excess-prune-drops-the-lowest-scored-candidate-first";
    bucket = Statements.Fairness;
    formula = score_ordered;
    antecedent =
      (* the ordering regime is really entered: a round reaches a state in
         which every ordinary peer, the HIGH-bucket one included, is gone *)
      Formula.And
        ( Formula.Not (atom Conn_c),
          Formula.And (Formula.Not (atom Conn_a), Formula.Not (atom Conn_b)) );
  }

(** S2 - tied-candidates-share-the-single-eviction-slot [fairness].

    In the single-excess regime the two candidates that tie on both sort keys
    have no deterministic victim, and exactly one of them goes:

    (A) no starvation - AG( excess=1 /\ everyone connected ->
        EF ~connected(a) /\ EF ~connected(b) );
    (B) exactly one - AG( excess=1 -> connected(a) \/ connected(b) ).

    Grounding: [connected_peers.shuffle(&mut rand::rng())]
    (all_peers.rs:974, "shuffle here for unbiased tie-breakers") runs BEFORE
    the stable [sort_by_key] at :976, and the module doc states the purpose
    verbatim - "The shuffle ensures peers with equal scores are sorted in a
    random order" (all_peers.rs:963-964). [Pa] and [Pb] tie on [Score]
    (score.rs:197-203) and on [is_routable] (peer.rs:426-428), so their
    relative order is exactly the shuffle's residue and either is a legitimate
    victim. Conjunct B is the excess countdown: [excess_peer_count] is
    [connected_peers.len().saturating_sub(target_num_peers)]
    (manager.rs:564-565) and is decremented once per disconnect
    (manager.rs:587), so an excess of one buys exactly one eviction.

    The two conjuncts are complementary and neither implies the other: A is
    about both branches existing, B about no branch dropping both.

    Mutation pin: {!Peer_prune_fairness_model.No_tie_shuffle} deletes the
    shuffle (all_peers.rs:974). [sort_by_key] is Rust's STABLE sort, so with
    the shuffle gone the surviving relative order of tied peers is the peer
    store's iteration order - a [HashMap] whose [RandomState] is seeded per map
    (all_peers.rs:44), hence fixed for the life of the process. The tie-break
    branch is REMOVED, [Pb] is never selected in the single-excess regime, and
    [EF ~connected(b)] fails at the operative state: the same peer loses at
    every heartbeat, which is the starvation the shuffle exists to prevent. No
    sibling repairs it: the sort cannot re-randomise what it is stable over,
    and the candidate [filter_map] (manager.rs:571-581) preserves order
    exactly.

    S2 survives the other three deletions and that is asserted: deleting the
    sort leaves both tie peers reachable victims (it only adds more), and the
    exemption deletions do not change the argmin in the single-excess
    regime. *)
let s2 =
  let all_connected =
    Formula.And
      ( atom Conn_a,
        Formula.And
          ( atom Conn_b,
            Formula.And (atom Conn_c, Formula.And (atom Conn_x, atom Conn_y)) )
      )
  in
  let no_starvation =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Cap_slack, all_connected),
           Formula.And
             ( Formula.Ef (Formula.Not (atom Conn_a)),
               Formula.Ef (Formula.Not (atom Conn_b)) ) ))
  in
  let exactly_one =
    Formula.Ag
      (Formula.Implies
         (atom Cap_slack, Formula.Or (atom Conn_a, atom Conn_b)))
  in
  {
    name = "tied-candidates-share-the-single-eviction-slot";
    bucket = Statements.Fairness;
    formula = Formula.And (no_starvation, exactly_one);
    antecedent = Formula.And (atom Cap_slack, all_connected);
  }

(** S3 - recognized-exemption-is-the-only-prune-carve-out [security].

    The excess-prune loop can never select a peer the node RECOGNIZES as
    consensus-critical, the excess is then tolerated rather than resolved, and
    the word "recognizes" is load-bearing:

    (A) validator carve-out - AG( is_peer_validator(x) -> connected(x) );
    (B) operator carve-out - AG( connected(y) );
    (C) the excess is tolerated, not resolved - AG( is_peer_validator(x) /\
        ~excess=1 /\ ~connected(a) /\ ~connected(b) /\ ~connected(c) ->
        over_target );
    (D) the recognition gap - AG( ~is_peer_validator(x) /\ ~connected(x) ->
        ~K_V0(committee_member(x)) /\ ~K_V0(~committee_member(x)) ).

    Grounding for A and B: the single filter
    [if !self.is_peer_validator(peer_id) && !peer.is_operator_allowlisted()]
    (manager.rs:575) is the only thing that removes a connected peer from the
    eviction list. [is_peer_validator] spans the previous, current and next
    committee slots (all_peers.rs:836-845); [is_operator_allowlisted] is
    construction-time operator trust that epoch rotation never touches
    (peer.rs:401-403). Neither is a score comparison, so the carve-out holds at
    hypothetically low scores too - that is why the two exempt peers here are
    NOT rescued by the sort in the [Tight] regime.

    Grounding for C: [excess_peer_count] is computed over ALL connected peers
    (manager.rs:564-565) but can only be paid out of the filtered candidates
    (manager.rs:571-581), and the loop simply ends when they run out
    (manager.rs:583-594). In the [Tight] regime the excess is 4 and there are
    three ordinary candidates, so the round drops all three and STOPS with the
    node still over target. Consensus-critical links are outside the pruning
    domain, not merely last inside it.

    Grounding for D: the carve-out is keyed on RECOGNITION, not on membership.
    [is_peer_validator] answers [false] for [PeerIdentity::Unidentified(_)]
    (all_peers.rs:836-845), and installing the committees skips members whose
    libp2p id is not yet recoverable - "others are trusted lazily on
    discovery" (all_peers.rs:1196-1235). So an unidentified genuine committee
    member is pruned as an ordinary peer, and at the moment the node prunes it
    the node can neither confirm nor rule out that it just evicted a validator:
    the [Unconfirmed_member] and [Unconfirmed_outsider] states with the same
    connection statuses are view-identical to V0. D is the family's only
    epistemic conjunct and it is an IGNORANCE claim; there is no positive [K]
    here, because everything else the node could know is a projection of its
    own peer store.

    Mutation pins. {!Peer_prune_fairness_model.No_validator_exemption} deletes
    the [!self.is_peer_validator(peer_id) &&] conjunct at manager.rs:575 and
    refutes A (and, one step later, C). The known partial repair is handled
    rather than ignored: committee entry primes the member's score to the
    maximum ([peer.reset_score_to_max()], all_peers.rs:1232, peer.rs:416-418),
    so under a SMALL excess the sort alone would keep [Px] alive even with the
    conjunct gone - the model therefore states A in a system whose [Tight]
    regime has excess 4 against 4 candidates, where every candidate is evicted
    and no ordering can rescue anyone. The other candidate repair,
    [peer_is_important] (manager.rs:665-668), guards only the connect-time
    limit at behavior.rs:266-272 and never re-admits a pruned peer; within the
    round re-admission is blocked anyway by the [temporarily_banned] insert on
    the [DisconnectWithPX] arm (manager.rs:340-345, gate at :396-404).

    {!Peer_prune_fairness_model.No_allowlist_exemption} deletes the
    [&& !peer.is_operator_allowlisted()] conjunct at the same line and refutes
    B (and C). Same repair analysis: operator trust exempts the peer from the
    score model ([TrustBasis::Operator], all_peers.rs:847-873) so its score
    never decays, which is again only a sort-level rescue and is again defeated
    by the [Tight] regime.

    Conjunct D is stated because it is TRUE and is the security content of the
    slice, not because a mutation refutes it: neither exemption deletion
    changes the view classes of the unidentified pair. S3 survives
    {!Peer_prune_fairness_model.No_score_sort} and
    {!Peer_prune_fairness_model.No_tie_shuffle}, which is asserted so that the
    two exemption pins stay attributable. *)
let s3 =
  let validator_carve_out =
    Formula.Ag (Formula.Implies (atom X_recognized, atom Conn_x))
  in
  let operator_carve_out = Formula.Ag (atom Conn_y) in
  let excess_tolerated =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             ( atom X_recognized,
               Formula.And
                 ( Formula.Not (atom Cap_slack),
                   Formula.And
                     ( Formula.Not (atom Conn_a),
                       Formula.And
                         ( Formula.Not (atom Conn_b),
                           Formula.Not (atom Conn_c) ) ) ) ),
           atom Over_target ))
  in
  let recognition_gap =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             (Formula.Not (atom X_recognized), Formula.Not (atom Conn_x)),
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom X_in_committee)),
               Formula.Not
                 (Formula.K
                    (Validator.V0, Formula.Not (atom X_in_committee))) ) ))
  in
  {
    name = "recognized-exemption-is-the-only-prune-carve-out";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( validator_carve_out,
          Formula.And
            (operator_carve_out, Formula.And (excess_tolerated, recognition_gap))
        );
    antecedent =
      (* an unidentified peer really is evicted, so the recognition gap is not
         asserted over an empty set of states *)
      Formula.And
        (Formula.Not (atom X_recognized), Formula.Not (atom Conn_x));
  }

(** The family's statements: two fairness properties of the eviction order and
    one security property of the carve-out that bounds it. *)
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
