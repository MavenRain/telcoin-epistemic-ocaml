(** The ROUND_WEIGHT_CAP statement family, encoded over the
    {!Round_weight_cap_model} interpreted system: the per-identity voting-power
    cap that [CertificatesAggregator::append] enforces on the round-parent
    quorum, the threshold gate that reads the capped weight, and what a node
    that emitted a round-[r] parent batch does and does not thereby know. All
    three statements were re-grounded line by line against the working tree of
    telcoin-network at git HEAD 0c59c15b.

    READING GUIDE FOR THE K OPERANDS. There are exactly two positive knowledge
    conjuncts and two negative ones, over two agents.

    - [Remote_quorum_certified] (S2 conjunct A, positive, agent V0) = "at least
      2f+1 = 3 DISTINCT committee members have had a round-[r] header
      certified". This is a fact about that many REMOTE nodes' completed
      proposal rounds - each of them collected 2f+1 votes from yet other nodes
      - never about V0's own act. It is NOT a projection of V0's view: V0's
      view carries [|authorities_seen|] and [weight], and the model's
      [certified] field is set by an environment step that V0 never observes,
      so at every state where V0 has appended fewer than [quorum_threshold]
      distinct origins its view is compatible with both truth values. It is
      NOT rigid: it is false at every initial state and at every state before
      the certification step fires. The inference from V0's local observation
      to this global fact is sound ONLY because of the distinctness guard
      (certificates.rs:83-85) TOGETHER WITH the threshold comparison (:91-92) -
      delete either and the same local observation stops entailing it, which is
      why both mutations refute this conjunct.
    - [Origin_equivocated] (S3 conjunct B, positive, agent V0) = "the origin V3
      really did get two distinct round-[r] headers certified". A fact about
      V3's acts. It is not a view projection globally - at every state where no
      duplicate reached V0, V0's view is identical in the equivocating and the
      honest world - and it is not rigid, being false throughout the
      [Refetched_copy] cone. What makes it KNOWN at the operative states is
      possession: V0 holds both digests, so a re-delivered copy of a
      certificate it already accepted and a second distinct header from a
      counted author are different observations to it.
    - [Peer_reached_quorum] (S2 conjunct B, negative, agent V0) = "the peer
      primary's own round-[r] aggregator fired". No message on this route
      carries a peer's aggregator weight, so V0's view is compatible with both.
    - [Origin_equivocated] again (S3 conjunct C, negative, agent V1). V1's view
      is its own aggregator status plus the verdict it computed as a voter on
      V0's round-[r+1] header. The drop of the duplicate is a bare [return
      None] at certificates.rs:83-85 - no log, no metric, no error, no fault
      attribution, and nothing on the wire - so V1's view is identical in the
      equivocating and the honest world. The ABSENCE of any attribution
      transition in the model is exactly the modelling of that silence; the
      sibling vote aggregator does raise [DagError::AuthorityReuse] on the same
      condition (votes.rs:42-45), and the certificate route deliberately does
      not.

    FAITHFULNESS (R5). The one real repair for a parent set that double-counts
    an identity is remote and one round later: each voter re-inserts every
    parent author into a [BTreeSet] and fails with
    [HeaderError::DuplicateParents] on a repeat (handler.rs:700, :725-728), and
    re-sums [voting_power_by_id(parent.origin())] against
    [quorum_threshold()], failing with [CertificateError::Inquorate]
    (:730, :733-738). That repair is MODELLED as the [header] field, it stays
    LIVE under both mutations, and S1 conjunct (C) asserts it explicitly. Every
    claim this family makes is therefore anchored on the LOCAL emission event,
    which the repair does not touch. *)

open Round_weight_cap_model

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

(** S1 - per-origin-round-weight-cap-is-exactly-one [safety]. No knowledge
    operator: this is the quota invariant the whole family rests on.

    (A) THE CAP - AG( ~(weight_0(r) > |authorities_seen_0(r)|) ). The round-[r]
    aggregator adds voting power once per distinct origin and never again, so
    the accumulated weight is exactly the count of distinct committee origins
    appended for that round, no matter how many certificates an identity
    issues or how many times one is re-delivered. Grounding:
    aggregators/certificates.rs:80 takes the origin, :82-85 refuses an origin
    already in [authorities_seen], and only afterwards :87-89 pushes the
    certificate and does [self.weight += committee.voting_power_by_id(&origin)].
    The per-identity unit is fixed at [EQUAL_VOTING_POWER = 1]
    (types/src/committee.rs:25, :511-513), so the cap is enforced BY IDENTITY
    and not by message count.

    (B) THE HAZARD IS REAL - EF( duplicate_offered_0(r) ). Asserted, not
    assumed, so that (A) cannot be true merely because no duplicate ever
    reaches [append]. Two routes do: a re-delivered copy on the catch-up
    ingress, where [process_fetched_certificates_in_parallel]
    (cert_validator.rs:235-243) runs [verify_collection] (:246-268) and
    [forward_verified_certs] (:133) without either consulting the certificate
    store, so the single-certificate digest dedup at :93-98 is bypassed and
    cert_manager.rs:74-135 -> :189-220 calls [append_certificate] a second
    time; and a second distinct header from a Byzantine origin, which the
    digest dedup could not see in any case and which the vote-once rule permits
    while no certificate is yet stored for that author and round
    (handler.rs:824-839).

    (C) THE DISCLOSED DOWNSTREAM REPAIR - AG( header_accepted_0(r+1) ->
    distinct_0(r) >= 2f+1 ). Even if the local cap were gone, a parent set that
    double-counts an identity does not survive the network: each voter of the
    round-[r+1] header inserts every parent author into a [BTreeSet] and fails
    with [HeaderError::DuplicateParents] on a repeat (handler.rs:700, :725-728)
    and re-sums the stake against [quorum_threshold()], failing with
    [CertificateError::Inquorate] (:730, :733-738). This conjunct is stated so
    the family cannot be accused of proving (A) by omitting the repair; it
    survives BOTH mutations, which is the evidence that the repair is genuinely
    modelled and genuinely live.

    MUTATION PIN. {!Round_weight_cap_model.No_distinct_origin_guard} deletes
    certificates.rs:83-85, so the [deliver_duplicate] transition falls through
    to :88-89 and increments [weight] without incrementing [origins]: conjunct
    (A) fails at the very first duplicate. Sibling-repair hunt for that
    deletion: cert_validator.rs:93-98 dedups exact retransmissions only and is
    bypassed by the fetch route; cert_manager.rs:74-135 never checks
    [(round, origin)] uniqueness; [save_cert]
    (certificate_store.rs:128-147) OVERWRITES the [(round, origin)] index at
    :137-138 rather than flagging a conflict; [append_certificate]
    (certificates.rs:24-44) has no error arm but the channel send; the proposer
    never re-derives distinctness (proposer.rs:384-467, :338-365, :751); and
    [DagError::AuthorityReuse] lives in the VOTE aggregator (votes.rs:42-45),
    a different aggregator on a different message type. The only repair is the
    remote one, and it is conjunct (C). {!Round_weight_cap_model
    .No_quorum_threshold_gate} leaves all three conjuncts standing, so the flip
    is cleanly attributable. *)
let s1 =
  let cap = Formula.Ag (Formula.Not (atom Weight_exceeds_origins)) in
  let hazard_is_real = Formula.Ef (atom Duplicate_appended) in
  let remote_repair =
    Formula.Ag
      (Formula.Implies (atom Header_accepted, atom Distinct_quorum_appended))
  in
  {
    name = "per-origin-round-weight-cap-is-exactly-one";
    bucket = Statements.Safety;
    formula = Formula.And (cap, Formula.And (hazard_is_real, remote_repair));
    antecedent = atom Duplicate_appended;
  }

(** S2 - round-quorum-emission-implies-known-distinct-supermajority [security].

    (A) KNOWN SUPERMAJORITY - AG( emitted_0(r) ->
    K_V0( certified(r) >= 2f+1 ) ). When the local round-[r] aggregator fires,
    the node KNOWS that a supermajority of DISTINCT validators each got a
    header certified at round [r] - a fact about 2f+1 REMOTE nodes' completed
    proposal rounds, hence (with f = 1) about at least f+1 honest nodes having
    finished round [r]. The entailment runs through both gates and only both:
    the distinctness guard (certificates.rs:82-85) makes [weight] a count of
    distinct identities, and the threshold comparison (:91-92) against
    [quorum_threshold()] = [2 * total_votes / 3 + 1] = 3
    (types/src/committee.rs:247-252, :516-518, :261-263) makes firing equal to
    "that count reached 2f+1". Delete either and the same local observation
    stops entailing the global fact - which is precisely what both mutations
    demonstrate.

    (B) THE KNOWLEDGE IS ONE-SIDED - AG( emitted_0(r) ->
    ( ~K_V0(emitted_1(r)) /\\ ~K_V0(~emitted_1(r)) ) ). Emission says nothing
    about any particular peer, because each node's aggregator fires on its own
    local arrival order: [CertificatesAggregatorManager] holds a private
    [BTreeMap<Round, Box<CertificatesAggregator>>] (certificates.rs:10-15,
    :32-36) and nothing on the wire reports another node's [weight] or
    [authorities_seen].

    R2 NON-DEGENERACY for (A). At the operative states V0's view class is not a
    singleton: [certified] and [peer] are both invisible to V0, so a state with
    the same [(origins, weight, emitted, observation, header)] and the peer
    still idle is reachable alongside one with the peer fired - which is
    exactly what conjunct (B) asserts and what
    [k-remote-quorum-class-nonsingleton] in the test suite checks. And the
    operand is genuinely contingent: it is false at every state before the
    certification step, witnessed by [k-remote-quorum-contingent].

    R3 IGNORANCE WITNESS for (B). Two reachable states with an identical V0
    view - same [|authorities_seen|], same [weight], same emission latch, same
    duplicate observation, same header verdict - one with [peer = P_idle] and
    one with [peer = P_quorum]. Both directions are asserted satisfiable in the
    test suite.

    MUTATION PIN. {!Round_weight_cap_model.No_quorum_threshold_gate} deletes
    certificates.rs:91-92, so every successful append forwards a
    one-certificate parent batch to the proposer: the node emits with a single
    distinct origin appended, at which point its view class contains states
    where the supermajority is NOT yet certified and (A) dies. Sibling-repair
    hunt for that deletion: on the emitting node nothing re-derives the round
    quorum - [process_parents] (proposer.rs:384-467) only warns on a round
    mismatch (:385-390) and extends [last_parents] (:447); [ready] (:374-379)
    delegates to [update_leader] (:319-327) / [enough_votes] (:338-365), which
    tallies stake over [last_parents] purely to set [advance_round]; and the
    propose gate is the bare [!self.last_parents.is_empty()] (:751). The remote
    voters DO reject the resulting inquorate header (handler.rs:733-738) and
    that repair is modelled and stays live, which is why this statement is
    anchored on the local emission event. Conjunct (B) survives the mutation,
    so the refutation is cleanly attributable to (A). NOTE, so it is never
    mistaken for a second pin: (A) also dies under
    {!Round_weight_cap_model.No_distinct_origin_guard}, because a
    double-counted identity lets the node emit with only two distinct origins.
    That is the intended reading - the entailment needs BOTH gates - and it is
    reported rather than hidden. *)
let s2 =
  let known_supermajority =
    Formula.Ag
      (Formula.Implies
         ( atom Emitted_round_quorum,
           Formula.K (Validator.V0, atom Remote_quorum_certified) ))
  in
  let one_sided =
    Formula.Ag
      (Formula.Implies
         ( atom Emitted_round_quorum,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom Peer_reached_quorum)),
               Formula.Not
                 (Formula.K
                    (Validator.V0, Formula.Not (atom Peer_reached_quorum))) )
         ))
  in
  {
    name = "round-quorum-emission-implies-known-distinct-supermajority";
    bucket = Statements.Security;
    formula = Formula.And (known_supermajority, one_sided);
    antecedent = atom Emitted_round_quorum;
  }

(** S3 - equivocating-origin-drop-is-silent-and-unattributable [security].

    (A) CONTAINMENT AT EMISSION - AG( ( emitted_0(r) /\\
    duplicate_offered_0(r) ) -> distinct_0(r) >= 2f+1 ). A node that is
    holding a duplicate round-[r] certificate for an identity it already
    counted still fires only on 2f+1 DISTINCT origins: the second certificate
    is refused at certificates.rs:82-85 before it can reach the accumulation at
    :87-89, so it can never be the marginal unit that trips the threshold at
    :91-92. Byzantine equivocation at the certificate layer is therefore
    CONTAINED.

    (B) THE HOLDER CAN ATTRIBUTE - AG( ( duplicate_offered_0(r) /\\
    equivocated(V3,r) ) -> K_V0( equivocated(V3,r) ) ). A node that personally
    received the second header knows it: it holds both digests, and
    [Certificate::digest()] is the header digest, so two certified round-[r]
    headers from one author are two distinct objects in its own store. This is
    a positive claim about ANOTHER node's act, not about V0's own.

    (C) NOBODY ELSE CAN - AG( emitted_1(r) -> ( ~K_V1( equivocated(V3,r) ) /\\
    ~K_V1( ~equivocated(V3,r) ) ) ). A peer that reached its own round-[r]
    quorum cannot tell whether an equivocation happened, because the drop is
    invisible outside the dropping node: certificates.rs:83-85 is a bare
    [return None] with no log, no metric, no error and no fault attribution,
    the emitted batch is [self.certificates.drain(..)] (:98) and therefore
    contains only the certificates that were counted, and [save_cert]
    (certificate_store.rs:128-147) silently OVERWRITES the [(round, origin)]
    index at :137-138 instead of flagging a conflict. The ban machinery is
    unreachable from this route - [append_certificate]
    (certificates.rs:24-44) returns [CertManagerResult<()>] whose only error
    arm is the channel send - and the [DagError::AuthorityReuse] that the VOTE
    aggregator raises on exactly this condition (votes.rs:42-45) is a different
    aggregator on a different message type and is not consulted here. So the
    equivocation is contained but never punished, and the containment leaves no
    evidence for anyone but the node that happened to receive both. The only
    metric anywhere on this ingress is [certificates_received_total], which
    [process_peer_certificate] increments on ANY [Ok] return
    (cert_validator.rs:75-77) - including the digest-dedup early return at
    :93-98 - so it counts receipts rather than appends and cannot distinguish a
    certificate that was counted from one that was dropped. Not even the local
    operator gets a trace.

    R2 NON-DEGENERACY for (B). The V0-view class at an operative state is not a
    singleton: [certified] and [peer] are invisible to V0, so states differing
    in the peer's aggregator status share the view; the test
    [k-equivocation-class-nonsingleton] asserts that at such a state V0 cannot
    rule out that the peer has fired. And the operand is contingent: throughout
    the [Refetched_copy] cone [equivocated(V3,r)] is false, witnessed by
    [k-equivocation-contingent].

    R3 IGNORANCE WITNESS for (C). Two reachable states with an identical V1
    view - same [peer] status, same header verdict - one in the [Second_header]
    cone and one in the [Refetched_copy] cone. Both directions are asserted
    satisfiable in the test suite.

    MUTATION PIN. {!Round_weight_cap_model.No_distinct_origin_guard} deletes
    certificates.rs:83-85, so the duplicate falls through to :88-89 and adds a
    unit of voting power: the node reaches the threshold with only two distinct
    origins appended and conjunct (A) fails - the containment is gone and an
    equivocating identity IS the marginal vote. The sibling-repair hunt for
    that deletion is the one recorded on S1: no local route re-derives
    distinctness, and the only repair (handler.rs:725-728, :733-738) is remote,
    one round later, modelled, and left live by the mutation, so it cannot
    rescue conjunct (A), which is about the local emission. Conjuncts (B) and
    (C) survive the mutation, so the refutation is cleanly attributable to (A).
    NOTE: (A) also dies under
    {!Round_weight_cap_model.No_quorum_threshold_gate}, which lets the node
    emit on its first append; that is reported rather than hidden. *)
let s3 =
  let containment =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Emitted_round_quorum, atom Duplicate_appended),
           atom Distinct_quorum_appended ))
  in
  let holder_attributes =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Duplicate_appended, atom Origin_equivocated),
           Formula.K (Validator.V0, atom Origin_equivocated) ))
  in
  let peer_cannot_attribute =
    Formula.Ag
      (Formula.Implies
         ( atom Peer_reached_quorum,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom Origin_equivocated)),
               Formula.Not
                 (Formula.K (Validator.V1, Formula.Not (atom Origin_equivocated)))
             ) ))
  in
  {
    name = "equivocating-origin-drop-is-silent-and-unattributable";
    bucket = Statements.Security;
    formula =
      Formula.And
        (containment, Formula.And (holder_attributes, peer_cannot_attribute));
    antecedent =
      Formula.And (atom Emitted_round_quorum, atom Duplicate_appended);
  }

(** The family's statements: the per-identity quota, what emission proves about
    remote certification rounds, and the silence of the equivocation drop. *)
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
