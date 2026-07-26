(** The GOSSIP_REJECT statement family, encoded over the
    {!Gossip_reject_model} interpreted system. Mined from telcoin-network,
    re-grounded line by line against the checkout at HEAD 0c59c15b, and stated
    here in the form that survived both the code skeptic and the
    finite-model-semantics skeptic. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide. The family has ONE idea: the reject path splits
    accountability two ways at consensus.rs:2090-2097, and the split is an
    EPISTEMIC one.
    - The size bound is a compile-time protocol CONSTANT, identical on every
      node (config/network.rs:98-112 says so, and says why a per-node bound
      would be unsound), enforced both on origination (consensus.rs:782-798)
      and on receipt (consensus.rs:1491-1497). So visible evidence ENTAILS the
      hidden fact and the relayer is knowably guilty - S1.
    - The publisher set is per-node, epoch-scoped state installed by each
      node's own [Subscribe] (consensus.rs:800-805, start_epoch.rs:505-524).
      So the SAME visible evidence entails nothing about the relayer and it is
      unjudgeable - S2.
    - The residual mis-attribution risk this creates on the author side is
      absorbed by the peer manager's [TrustBasis] exemption - S3.

    The three K operands are three genuinely DIFFERENT hidden facts, none of
    them a function of V0's own view (R1): the relayer's deviation [rdev], the
    relayer's private publisher verdict [rmap], and the author's intent (the
    honest/Byzantine split that [Cls_denied_committee] merges away). *)

open Gossip_reject_model

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

(** The operative antecedent of S1: V0 has taken delivery of an oversized
    payload. Reachable at 24 of the 49 pristine states (the three non-[Quiet]
    stages x 4 author standings x 2 hidden relayer maps). *)
let oversized_receipt =
  Formula.And (atom Msg_inbound, atom Payload_over)

(** The operative antecedent of S2: V0 has taken delivery of an in-bounds
    message whose author its own map denies. Reachable at 18 of the 49 pristine
    states (3 non-[Quiet] stages x 3 denied author standings x 2 relayer
    maps). *)
let denied_in_bounds_receipt =
  Formula.conj
    [ atom Msg_inbound; Formula.Not (atom Payload_over); atom Authz_denied ]

(** The operative antecedent of S3: the author was made the penalty target and
    sits in a tracked committee slot. Reachable at 8 of the 49 pristine states
    ([Within] payload, author in {Auth_stale_honest, Auth_stale_byz}, stages
    [Settled] and [Rotated], both relayer maps). *)
let charged_committee_author =
  Formula.And (atom Charged_author, atom Author_in_committee)

(** S1 - oversized-gossip-receipt-implies-known-relayer-deviation [security].
    Once V0 has taken delivery of a gossip payload larger than
    [MAX_GOSSIP_MESSAGE_SIZE], V0 KNOWS the delivering peer itself broke
    protocol - and it knows this while remaining wholly ignorant of that
    relayer's internal publisher map - and the message's author is never
    charged on that branch.

    (A) attributable: AG( (inbound /\\ oversized) -> K_V0(deviated(R)) ). The
    bound is a compile-time protocol CONSTANT, not a tunable
    (crates/config/src/network.rs:98-112, [pub const MAX_GOSSIP_MESSAGE_SIZE:
    usize = 12_000] plus the network-wide-identical-bound rationale at
    :100-110). It is enforced on origination (consensus.rs:782-798, the
    [msg.len() > MAX_GOSSIP_MESSAGE_SIZE => Err(PublishError::MessageTooLarge)]
    arm) and on receipt (consensus.rs:1491-1497); gossipsub runs
    [ValidationMode::Strict] with [validate_messages()]
    (consensus.rs:342-362), and only the [Accept] arm of
    [report_message_validation_result] forwards. So a peer that delivers an
    oversized payload either published one (violating the origination guard) or
    forwarded one its own [verify_gossip] must have Rejected. The code asserts
    exactly this at consensus.rs:2047-2052. R1/R2: [deviated(R)] is the hidden
    field [rdev], never in any view and NOT a function of V0's view - at
    [Within] states it is decided entirely by the hidden [rmap], so two
    view-identical worlds disagree on it - and not rigid, being false at every
    reachable ([Within], [Map_permits]) state.

    (B) opaque_relayer_map: AG( (inbound /\\ oversized) ->
    (~K_V0(relayer_map_forbids(A)) /\\ ~K_V0(~relayer_map_forbids(A))) ).
    [authorized_publishers] is per-node state installed by that node's own
    [Subscribe] (consensus.rs:800-805) with the current epoch's committee keys
    (start_epoch.rs:517-524, worker topic at :697-705); V0 sees bytes and a
    [PeerId], never the relayer's map. This conjunct is what makes conjunct (A)
    demonstrably non-degenerate: it proves the operative view class holds at
    least two reachable worlds, namely the [Map_permits] and [Map_forbids]
    siblings of every oversized state.

    (C) author_spared: AG( (inbound /\\ oversized) -> ~charged(A) ).
    [RejectReason::TooLarge] maps only to [FatalRelayer] or [Skip], never
    [FatalAuthor] (consensus.rs:2092-2093), and the [FatalAuthor] arm at
    consensus.rs:1075-1088 is the sole call of [process_penalty] on the author
    in the reject path.

    Mutation pin: {!Gossip_reject_model.No_receive_size_gate} deletes the
    receive-side size check (consensus.rs:1491-1497) from the SHARED binary, so
    an honest node no longer Rejects an oversized payload - it Accepts, and
    [Accept] is the only arm that forwards. [deviation_of] at ([Oversized],
    [Map_permits]) flips to [Dev_none], putting a non-deviating world into the
    oversized view class and killing conjunct (A) at that state outright; and
    the verdict falls through from [TooLarge] to the publisher check, so
    oversized deliveries from denied authors carry [charged(A)] and conjunct
    (C) fails too. Conjunct (B) is untouched. No sibling repairs the deletion:
    libp2p's own [max_transmit_size] default of 65536 is above this model's
    [Oversized] band and TN never sets it, the origination guard never runs on
    a forward, and [TNCodec]'s bound governs request/response only. *)
let s1 =
  let attributable =
    Formula.Ag
      (Formula.Implies
         (oversized_receipt, Formula.K (Validator.V0, atom Relayer_deviated)))
  in
  let opaque_relayer_map =
    Formula.Ag
      (Formula.Implies
         ( oversized_receipt,
           Formula.And
             ( Formula.Not
                 (Formula.K (Validator.V0, atom Relayer_map_forbids)),
               Formula.Not
                 (Formula.K
                    ( Validator.V0,
                      Formula.Not (atom Relayer_map_forbids) )) ) ))
  in
  let author_spared =
    Formula.Ag
      (Formula.Implies (oversized_receipt, Formula.Not (atom Charged_author)))
  in
  {
    name = "oversized-gossip-receipt-implies-known-relayer-deviation";
    bucket = Statements.Security;
    formula = Formula.conj [ attributable; opaque_relayer_map; author_spared ];
    antecedent = oversized_receipt;
  }

(** S2 - unauthorized-author-reject-spares-and-cannot-judge-the-forwarder
    [fairness]. When V0 rejects an in-bounds message because its author is not
    an authorized publisher, the forwarding peer is never made the penalty
    target, and V0 can neither convict nor exonerate that forwarder - it cannot
    tell an epoch-skewed honest relayer from a Byzantine amplifier.

    (A) forwarder_spared: AG( (inbound /\\ ~oversized /\\ unauthorized_author)
    -> ~charged(R) ). consensus.rs:2094-2095 maps [UnauthorizedAuthor] to
    [FatalAuthor] (author resolved) or [Skip], never [FatalRelayer]; the
    dispatch at consensus.rs:1063-1099 calls
    [process_penalty(propagation_source, Fatal)] only inside the
    [FatalRelayer] arm (:1064-1074). The variant doc states the intent verbatim
    at consensus.rs:2054-2060.

    (B) forwarder_unjudged: AG( (inbound /\\ ~oversized /\\
    unauthorized_author) -> (~K_V0(deviated(R)) /\\ ~K_V0(~deviated(R))) ). The
    relayer's verdict is computed against ITS OWN [authorized_publishers]
    (consensus.rs:1499-1513 run on the relayer's copy), installed per-node
    per-epoch by its own [Subscribe] (consensus.rs:800-805 with
    start_epoch.rs:517-524), so two honest nodes straddling an epoch edge
    legitimately disagree. V0 holds only its own map; nothing on the wire
    carries the relayer's verdict. R3 witness: wA = ([Settled], [Within],
    [Auth_stale_honest], [Map_permits], rdev=[Dev_none], [Charge_author],
    [Rep_trusted]) - the honest epoch-skewed forwarder - and wB = the same
    world with [Map_forbids] and rdev=[Dev_relay] - the Byzantine amplifier.
    Both reachable, identical V0-view ([Settled], [Within],
    [Cls_denied_committee], [Charge_author], [Rep_trusted]), disagreeing on
    [deviated(R)].

    Mutation pin: {!Gossip_reject_model.No_reject_attribution_split} deletes
    the two [UnauthorizedAuthor] arms (consensus.rs:2094-2095), so every reject
    falls through to [FatalRelayer] and each denied scenario's [Settled] and
    [Rotated] states carry [charged(R)]: conjunct (A) is false. Conjunct (B) is
    untouched - both [rmap] worlds still collide - so the refutation is cleanly
    attributable to (A), the same shape the frozen ADMISSION exemplar documents
    for its severance conjunct. No sibling repairs the deletion: gossipsub
    internal peer scoring is not configured at all, rejects never reach the
    application layer, the committee exemption suppresses a score effect but
    not the charge (and this conjunct's atom is the [RejectPenalty] TARGET, not
    the ban), and [SlowPeer] fires on a different event. *)
let s2 =
  let forwarder_spared =
    Formula.Ag
      (Formula.Implies
         (denied_in_bounds_receipt, Formula.Not (atom Charged_relayer)))
  in
  let forwarder_unjudged =
    Formula.Ag
      (Formula.Implies
         ( denied_in_bounds_receipt,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom Relayer_deviated)),
               Formula.Not
                 (Formula.K
                    (Validator.V0, Formula.Not (atom Relayer_deviated))) ) ))
  in
  {
    name = "unauthorized-author-reject-spares-and-cannot-judge-the-forwarder";
    bucket = Statements.Fairness;
    formula = Formula.And (forwarder_spared, forwarder_unjudged);
    antecedent = denied_in_bounds_receipt;
  }

(** S3 - committee-author-charged-under-ignorance-is-never-banned [safety]. V0
    Fatal-charges the author of an unauthorized message without being able to
    tell an epoch-skewed honest validator from a tracked committee member
    deliberately publishing outside its authorization - and that is safe
    precisely because the peer manager's [TrustBasis] exemption means a peer in
    any tracked committee slot is never actually banned by the charge.

    (A) never_banned: AG( ~(committee(A) /\\ banned(A)) ).
    [AllPeers::process_penalty] resolves the identity, computes the exemption
    and forwards it (all_peers.rs:258-303, especially :262-266); [exemption]
    returns [Some(TrustBasis::Validator)] for any [Confirmed] key in the
    previous/current/next slots (all_peers.rs:847-873, slots maintained at
    :1102-1122); [Peer::apply_penalty] then bypasses the score model entirely
    for an exempt peer (peer.rs:209-237, the [if let Some(basis) = exemption {
    warn } else { self.score.apply_penalty(penalty) }] at :218-233). Without
    the exemption a [Fatal] sets the score to [min_score] (score.rs:84-100),
    which is at or below [min_score_before_ban] (config/network.rs:446-465), so
    [reputation_for] returns [Banned] (score.rs:157-187). NON-VACUOUS: banned
    IS reachable - the [Auth_rogue] scenario sits in no tracked slot, is not
    allowlisted, and reaches [Rep_banned] at [Settled] and stays banned at
    [Rotated].

    (B) intent_opaque: AG( (charged(A) /\\ committee(A)) ->
    (~K_V0(deviates(A)) /\\ ~K_V0(~deviates(A))) ). V0's reject decision reads
    only [authorized_publishers] for the topic (consensus.rs:1499-1513), which
    [start_epoch] installs with the CURRENT committee only
    (start_epoch.rs:517-524), while the exemption spans previous/current/next
    (all_peers.rs:831-873). So "denied by [authorized_publishers] but inside a
    tracked slot" is ONE observation class covering both an honest validator
    publishing under its own epoch view and a tracked member deliberately
    publishing unauthorized content; consensus.rs:2054-2060 names the first
    case explicitly. R3 witness: wC = ([Settled], [Within],
    [Auth_stale_honest], [Map_permits], [Charge_author], [Rep_trusted]) and wD
    = the same world with [Auth_stale_byz]. Both reachable, identical V0-view
    ([Settled], [Within], [Cls_denied_committee], [Charge_author],
    [Rep_trusted]), disagreeing on [deviates(A)].

    Mutation pin: {!Gossip_reject_model.No_committee_exemption} deletes the
    [TrustBasis] bypass (peer.rs:218-233), so [exempt] is false for every peer
    and the [Charge_author] of the in-bounds [Auth_stale_honest] and
    [Auth_stale_byz] scenarios, under either relayer map, drives the reputation to
    [Rep_banned] at [Settled]: [committee(A)] and [banned(A)] hold together and
    conjunct (A) is false. Conjunct (B) is untouched (both intents still
    collide, now both banned). The real sibling repair - the [Rotated] step's
    [apply_committee_membership] unban and [reset_score_to_max]
    (all_peers.rs:1180-1239) - is MODELLED and stays LIVE under the mutation;
    it restores [Rep_trusted] one step later, which is exactly why the
    statement is an AG-never-both invariant rather than an eventual-recovery
    claim, and the [Settled] state still violates it.

    NOTE: {!Gossip_reject_model.No_reject_attribution_split} also errors this
    statement, but through [Vacuous_antecedent] (it removes every author
    charge, so [charged(A)] becomes unreachable). That is NOT a pin and is not
    presented as one. *)
let s3 =
  let never_banned =
    Formula.Ag
      (Formula.Not
         (Formula.And (atom Author_in_committee, atom Author_banned)))
  in
  let intent_opaque =
    Formula.Ag
      (Formula.Implies
         ( charged_committee_author,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom Author_deviates)),
               Formula.Not
                 (Formula.K
                    (Validator.V0, Formula.Not (atom Author_deviates))) ) ))
  in
  {
    name = "committee-author-charged-under-ignorance-is-never-banned";
    bucket = Statements.Safety;
    formula = Formula.And (never_banned, intent_opaque);
    antecedent = charged_committee_author;
  }

(** The family's statements: the knowably-guilty relayer (security), the
    unjudgeable forwarder (fairness), and the ignorance-absorbing committee
    exemption (safety). Each is pinned by its own gate. *)
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
