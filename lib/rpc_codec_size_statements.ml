(** The RPC_CODEC_SIZE statements (S1, S2, S3) over {!Rpc_codec_size_model}.

    What was mined. The length-prefixed snappy codec of [network-libp2p]
    (codec.rs:32-105) raises exactly two shapes of io error - the three
    [std::io::Error::other] size rejections (:51-54, :61-67, :96-101) and the
    [ErrorKind::UnexpectedEof] truncation (:78-83) - and the inbound failure
    classifier (consensus.rs:1279-1314) turns that one-bit distinction into two
    opposite verdicts: [Penalty::Medium] for the former, no penalty at all for
    the latter. A second, independent filter then decides whether the levied
    penalty reaches the score at all: the trust basis
    ([Peer::apply_penalty], peer.rs:213-233, resolved at all_peers.rs:261-263
    from the three committee slots and the operator allowlist, :847-873). The
    family reads the same exchange three ways: who actually pays and on what
    evidence (S1), the asymmetry between the two error shapes (S2), and the one
    gate that bounds the buffer the read loop fills (S3).

    READING GUIDE FOR THE K OPERANDS. There is exactly ONE positive knowledge
    conjunct in this family and two ignorance conjuncts, and all three take V0 -
    the reading node - as the knower.

    - [K_V0(deviated(B))] in S1 conjunct D is NOT a projection of V0's own view.
      V0's view is [(obs, settlement, charge, trust)]: the codec verdict,
      whether the classifier has run, what reached B's score, and whether B is
      inside V0's own trust basis. [deviated(B)] is a fact about B's hidden
      [plan]. It is not rigid either: it is FALSE at reachable states
      ([Plan_honest_large_cap], [Plan_honest_flap]) and TRUE at others, and V0's
      ignorance of it is precisely what S1 conjunct B asserts on the RPC path.
      The knowledge holds on the gossip path only because the bound there is
      network-wide (config/network.rs:98-112), so no honest branch can produce
      that observation at all. Its view class is a genuine doubleton - B's own
      configured cap still varies invisibly across it - and t_rpc_codec_size.ml
      proves that.
    - [~K_V0(deviated(B))] in S1 conjunct B: the witness pair is
      [Plan_honest_large_cap] (honest, 2 MiB cap, sends a message legal under
      its own bound) against [Plan_spam_oversize] (Byzantine, same declaration
      to burn V0). Both trip codec.rs:51-54 with the identical error, so V0's
      view is identical and [deviated(B)] differs.
    - [~K_V0(deliberate_truncation(B))] in S2 conjunct B: the witness pair is
      [Plan_honest_flap] against [Plan_grief_truncate]. Both raise the identical
      [UnexpectedEof] at codec.rs:78-83 and both take the exemption at
      consensus.rs:1284, so V0's view is identical and the intent differs.

    [K_V1(..)] never appears: V1 is B, and any fact about B's own plan, cap or
    committee standing is a projection of B's own view (R1). [penalty_exempt(B)]
    never appears under [K] either, in the other direction: V0 computes it
    itself, so knowing it would be trivial. *)

open Rpc_codec_size_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** The reading node, and the only knowledge agent this family quantifies
    over. *)
let reader = Validator.V0

(** The [ErrorKind::Other] refusal of an oversized declaration
    (codec.rs:51-54): the antecedent both S1 and S2 build their charge conjunct
    on. *)
let rpc_reject = Formula.Atom Rpc_prefix_size_reject

(** A refusal of a peer the trust basis does NOT exempt (all_peers.rs:847-873):
    the only case in which a levied penalty reaches the score at all. *)
let scored_rpc_reject =
  Formula.And (rpc_reject, Formula.Not (Formula.Atom Penalty_exempt))

(** The charge conjunct shared by S1 conjunct A and S2 conjunct C: a size
    refusal of a scored peer inevitably costs it a Medium penalty. *)
let scored_reject_is_charged =
  Formula.Ag
    (Formula.Implies
       (scored_rpc_reject, Formula.Af (Formula.Atom Charged_medium)))

(** S1 - oversize-rpc-charge-is-levied-under-peer-config-ignorance [security].

    CONJUNCT A, the charge. Everywhere V0's codec has refused a request because
    the declared uncompressed length exceeds V0's own [max_rpc_message_size]
    (codec.rs:51-54) AND the sender is not inside V0's trust basis, the refusal
    inevitably costs the sender a Medium penalty. [std::io::Error::other]
    carries [ErrorKind::Other], so the inbound classifier falls past the
    transport-flap exemption (consensus.rs:1281-1286) into the catch-all at
    :1289-1299, which calls [process_penalty(peer, Penalty::Medium)];
    [Penalty::Medium => self.add(-5.0)] (peers/score.rs:89-94). [AF] rather than
    a plain conjunction because the classifier is a separate swarm event from
    the codec error, and the model keeps that step separate.

    CONJUNCT B, the ignorance - and this one is NOT scoped by the trust basis,
    because ignorance is symmetric across it. Everywhere that refusal happens,
    V0 does not know that the sender deviated. The cap is per-node operator
    config - [pub max_rpc_message_size: usize] inside a [#[serde(default)]]
    struct (config/network.rs:115-119), default [1024 * 1024] (:188), wired at
    consensus.rs:364-365 - and the repo's own test asserts a 2 MiB value parses
    (config/network.rs:509, :525). An honest peer configured at 2 MiB emits a
    message its own [encode_message] accepts (codec.rs:133-136) and V0's decoder
    refuses, and V0 sees exactly what it sees for a spammer.

    CONJUNCT C, the exemption. Everywhere the SAME refusal comes from a peer
    inside V0's trust basis, nothing is ever charged. [AllPeers::process_penalty]
    resolves the basis before touching the peer -
    [let exemption = self.trust_basis_for(&id);] (all_peers.rs:261-263) - and
    [Peer::apply_penalty] short-circuits on it (peer.rs:218-233): a committee
    member (previous, current or next slot) or an operator-allowlisted peer
    bypasses the score model entirely. So the -5 that conjunct A promises lands
    on exactly the peers V0 has the least independent information about, and
    never on the ones it does.

    CONJUNCT D, the contrast case in the same repo. Everywhere V0 has rejected a
    GOSSIP payload for size, [K_V0(deviated(B))] does hold. The gossip bound is
    a protocol constant (config/network.rs:112) whose doc comment (:98-111)
    states the attribution argument outright: it is "not a per-node tunable",
    the reject path Fatal-bans the relayer, and "that attribution is sound only
    if every honest node applies the identical bound". The bound is enforced
    symmetrically on publish and receive, so no honest branch produces that
    observation. The RPC path has no such constant, and that is the whole
    content of the statement.

    MUTATION PINS. {!No_inbound_catchall_penalty} deletes consensus.rs:1289-1299
    and refutes conjunct A: the classify transition settles a scored peer at
    [Charge_none], so the [AF] fails, while B, C and D all still hold.
    {!No_trust_exemption} deletes the short-circuit at peer.rs:218-233 and
    refutes conjunct C from the other side: the exempt peer is now scored like
    anyone else. Two independent gates, two independent refutations of the same
    statement, neither of which disturbs the epistemic conjuncts. No sibling
    path repairs either: for the catch-all, the outbound mirror (:1241-1251) is
    a different event on a different initiator, the gossip route (:1063-1073) is
    left LIVE in the mutated model and is the witness that charging did not
    simply vanish, the application route (:894-901) cannot fire for a message
    that never decoded, and every other inbound arm (:1307-1313) is explicitly
    no-penalty; for the exemption, [Peer::apply_penalty] is the sole caller of
    [Score::apply_penalty] and the ban path keys off [Reputation] alone
    (all_peers.rs:264-284). *)
let s_1 =
  let conjunct_a = scored_reject_is_charged in
  let conjunct_b =
    Formula.Ag
      (Formula.Implies
         (rpc_reject, Formula.Not (Formula.K (reader, atom Deviated))))
  in
  let conjunct_c =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (rpc_reject, atom Penalty_exempt),
           Formula.Ag (Formula.Not (atom Charged_any)) ))
  in
  let conjunct_d =
    Formula.Ag
      (Formula.Implies
         (atom Gossip_size_reject, Formula.K (reader, atom Deviated)))
  in
  {
    name = "oversize-rpc-charge-is-levied-under-peer-config-ignorance";
    bucket = Statements.Security;
    formula =
      Formula.And
        (Formula.And (conjunct_a, conjunct_b), Formula.And (conjunct_c, conjunct_d));
    antecedent = Formula.Or (rpc_reject, atom Gossip_size_reject);
  }

(** S2 - truncated-body-is-penalty-exempt-while-an-oversize-declaration-is-not
    [security].

    CONJUNCT A. Everywhere B declared a body and delivered less of it, so that
    V0's read loop saw [read == 0] with [remaining > 0] (codec.rs:78-83), B is
    never charged, at any severity, from that state onward - and this holds
    WITHOUT any trust-basis scope, because the exemption at consensus.rs:1284
    fires before the trust basis is ever consulted. The error carries
    [ErrorKind::UnexpectedEof], which is one alternative of the inbound
    exemption chain at :1281-1286, whose body is the bare comment "transport
    flap on WAN - no penalty" (:1287). The [AG] is inside the implication on
    purpose: the classifier runs one step after the codec error, so a conjunct
    that only looked at the truncation instant would be satisfied by a model
    that charges immediately afterwards.

    CONJUNCT B. At every such state [~K_V0(deliberate_truncation(B))]: V0 cannot
    tell a griefing peer from a reset stream. Both branches raise the identical
    error at the identical line and both take the identical exemption arm, so
    V0's whole view - [(obs, settlement, charge, trust)] - is the same on both.

    Together: truncation is a free action against this node, free for scored and
    exempt peers alike, and the freeness is not compensated by attribution,
    because there is no attribution to be had.

    CONJUNCT C, the asymmetry that makes A worth stating. Everywhere the SAME
    peer instead declares an oversized body and is not trust-exempt, the charge
    is levied (the conjunct A of S1). One malformed-input outcome is free for
    everyone and the other costs -5 to everyone outside the committee, and the
    codec chooses between them by which [std::io::Error] constructor it happens
    to call.

    MUTATION PINS. {!No_inbound_eof_exemption} deletes
    [ErrorKind::UnexpectedEof] from the exemption list (consensus.rs:1284, one
    alternative of the [|] chain at :1281-1286). Truncation then falls into the
    catch-all at :1289-1299 and the classify transition ADDS a [Charge_medium]
    on the truncation branch of a scored peer, so A fails while B survives (the
    two truncation branches remain indistinguishable, they are merely both
    charged now). Nothing repairs the pristine exemption from elsewhere: the
    outbound classifier carries the same list at :1236 and is a different event,
    [Timeout | ConnectionClosed] (:1310-1312) and [ResponseOmission] (:1313) are
    explicit no-penalty arms, [peers/manager.rs:429-443] is the sole route into
    [Score::apply_penalty], and the application route (:894-901) cannot see a
    message that never decoded. S2 is ALSO refuted by
    {!No_inbound_catchall_penalty} through conjunct C, and that cross pin is
    asserted in the mutation suite; it is NOT refuted by {!No_trust_exemption},
    because scoring exempt peers cannot create a charge the classifier never
    levied. *)
let s_2 =
  let truncated = atom Body_truncated in
  let conjunct_a =
    Formula.Ag
      (Formula.Implies
         (truncated, Formula.Ag (Formula.Not (atom Charged_any))))
  in
  let conjunct_b =
    Formula.Ag
      (Formula.Implies
         ( truncated,
           Formula.Not (Formula.K (reader, atom Deliberate_truncation)) ))
  in
  let conjunct_c = scored_reject_is_charged in
  {
    name =
      "truncated-body-is-penalty-exempt-while-an-oversize-declaration-is-not";
    bucket = Statements.Security;
    formula =
      Formula.And (Formula.And (conjunct_a, conjunct_b), conjunct_c);
    antecedent = Formula.Or (truncated, rpc_reject);
  }

(** S3 - compressed-body-accumulation-is-bounded-by-the-declared-uncompressed-
    length [safety].

    CONJUNCT A - [AG ~buffer_amplified]. The peak resident size of
    [compressed_buffer] never exceeds
    [snap::raw::max_compress_len(uncompressed_len)]. The buffer is filled by the
    unbounded-in-total loop at codec.rs:73-86 - [while remaining > 0 { let want
    = remaining.min(chunk.len()); let read = io.read(&mut chunk[..want]).await?;
    .. compressed_buffer.extend_from_slice(&chunk[..read]); remaining -= read;
    }] - where the 8 KiB [BODY_READ_CHUNK_SIZE] (:16-21) bounds each individual
    read and nothing else. The only thing standing between a peer and an
    arbitrarily large resident allocation is the compressed-length gate at
    :61-67.

    CONJUNCT B - [AG (inflated_compressed_declaration(B) -> AG ~body_read_ran)].
    That gate fires BEFORE a single body byte is read: it sits at :61-67 and the
    loop starts at :73. So a peer that declares a compressed length above the
    snappy maximum for its own declared uncompressed length costs V0 nothing at
    all, not even a partial buffer.

    Why this is not the covered prefix-gate statement restated. The
    uncompressed-prefix gate (:51-54) bounds [uncompressed_len] and therefore
    [decode_buffer]; it says nothing about how many COMPRESSED bytes are
    accumulated. Neither do the output bounds: [.take(decode_limit)] (:91-93)
    and the equality check (:96-101) both constrain [decode_buffer] and both run
    only after the whole compressed body is already resident. The model carries
    that equality check on a pristine branch ([Plan_snappy_short]) precisely so
    the claim cannot be read as pretending it away.

    MUTATION PIN. {!No_compressed_length_gate} deletes codec.rs:61-67. The
    inflated declaration then passes into the read loop, so the codec transition
    yields [Peak_amplified] and [body_read_ran], refuting both conjuncts. The
    surviving repair paths are modelled and do NOT rescue the bound: the mutated
    branch still fails the equality check at :96-101 and a scored sender is
    still charged Medium, and [TNCodec::new]'s [Vec::with_capacity] (:205-218)
    is an initial capacity that [extend_from_slice] grows past and
    [compressed_buffer.clear()] (:44) keeps resident. QUIC flow control
    (consensus.rs:447-455, config/network.rs:292-296, :309-310) throttles
    unacknowledged data rather than capping the total, so the residual bound
    after the deletion is the 4-byte [compressed_len] prefix itself
    (codec.rs:56-59) - a refutation of the stated bound, not a claim of
    unboundedness. Neither penalty mutation touches this statement, which is the
    evidence that the codec gate and the two accountability gates are
    independent. *)
let s_3 =
  let inflated = atom Inflated_compressed_declaration in
  let conjunct_a = Formula.Ag (Formula.Not (atom Buffer_amplified)) in
  let conjunct_b =
    Formula.Ag
      (Formula.Implies (inflated, Formula.Ag (Formula.Not (atom Body_read_ran))))
  in
  {
    name =
      "compressed-body-accumulation-is-bounded-by-the-declared-uncompressed-length";
    bucket = Statements.Safety;
    formula = Formula.And (conjunct_a, conjunct_b);
    antecedent = inflated;
  }

(** The family's statements. *)
let all = [ s_1; s_2; s_3 ]

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
