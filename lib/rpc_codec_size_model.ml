(** Finite interpreted system for the RPC_CODEC_SIZE family: the length-prefixed
    snappy request/response codec of [network-libp2p], the inbound failure
    classifier that decides whether the sending peer is charged for what the
    codec refused, and the trust-basis exemption that decides whether the charge
    reaches the score at all. File citations refer to
    Telcoin-Association/telcoin-network at git HEAD [0c59c15b]; every line range
    below was opened in that checkout.

    SCOPE. Exactly ONE inbound exchange: a remote peer [B] is the REQUESTER and
    the local node [V0] is the RESPONDER reading [B]'s request off the wire with
    [TNCodec::read_request] (codec.rs:231-246 -> [decode_message], :32-105). The
    direction is fixed by every antecedent in this family, and it matters: the
    failure classifier has two mirrored halves, [ReqResEvent::InboundFailure]
    (consensus.rs:1276-1320) and [ReqResEvent::OutboundFailure] (:1203-1275),
    and only the inbound half can fire for a request this node is reading. The
    one gossip branch is carried deliberately as the contrast case for S1 and is
    labelled as such throughout. Only exchanges the codec or the gossip size
    check REFUSES are modelled: a message that decodes leaves the network layer
    entirely and its accountability is the application's, through
    [NetworkCommand::ReportPenalty] (consensus.rs:894-901), which by
    construction cannot fire for a message that never decoded.

    THE MODELLED MECHANISM, gate by gate, in source order.

    - The UNCOMPRESSED-PREFIX gate, codec.rs:51-54:
      [if uncompressed_len > max_message_size { return Err(
      std::io::Error::other("prefix indicates message size is too large")); }].
      [max_message_size] is [TNCodec::new]'s [max_chunk_size]
      (codec.rs:203-219), wired from per-node operator config at
      consensus.rs:364-365 [TNCodec::<Req, Res>::new(
      network_config.libp2p_config().max_rpc_message_size)]. The field is
      [pub max_rpc_message_size: usize] (config/network.rs:117-119) inside a
      [#[serde(default)]] struct (:115-117), defaulting to [1024 * 1024]
      (:188). It is NOT a protocol constant: the repo's own test asserts a
      2 MiB value round-trips through partial YAML (config/network.rs:507-509,
      :525).
    - The COMPRESSED-LENGTH gate, codec.rs:61-67:
      [let max_compress_len = snap::raw::max_compress_len(uncompressed_len);
      if compressed_len > max_compress_len { return Err(
      std::io::Error::other("compressed size exceeds max for reported
      uncompressed size")); }]. This is the ONLY bound on the streaming
      accumulation that follows.
    - The STREAMING READ LOOP, codec.rs:69-86: [let mut remaining =
      compressed_len; let mut chunk = [0u8; BODY_READ_CHUNK_SIZE]; while
      remaining > 0 { .. compressed_buffer.extend_from_slice(&chunk[..read]);
      remaining -= read; }]. [BODY_READ_CHUNK_SIZE] is 8 KiB (codec.rs:16-21)
      and bounds each individual read, not the total. A short read raises
      [std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "compressed body
      shorter than reported compressed size")] (codec.rs:78-83).
    - The OUTPUT bounds, codec.rs:88-101: [let decode_limit =
      u64::try_from(uncompressed_len)..; FrameDecoder::new(reader)
      .take(decode_limit)] and then [if decode_buffer.len() != uncompressed_len
      { return Err(std::io::Error::other("decompressed size does not match
      reported uncompressed size")); }]. Both constrain [decode_buffer], and
      both run only AFTER the whole compressed body has been accumulated.
    - The INBOUND FAILURE CLASSIFIER, consensus.rs:1279-1314. [Io(e)] splits on
      [e.kind()]: the exemption chain [ConnectionReset | ConnectionAborted |
      TimedOut | UnexpectedEof | BrokenPipe | Interrupted] (:1281-1286) is a
      documented no-penalty arm ("transport flap on WAN", :1287; rationale at
      :1223-1226 on the outbound mirror), and the adjacent catch-all
      (:1289-1299) warns "inbound IO failure (likely codec violation)" and calls
      [process_penalty(peer, Penalty::Medium)]. Every [std::io::Error::other]
      the codec raises carries [ErrorKind::Other] and therefore lands in the
      catch-all; the truncation error carries [ErrorKind::UnexpectedEof] and
      therefore lands in the exemption.
    - The TRUST-BASIS EXEMPTION, which decides whether the levied penalty ever
      reaches the score. [AllPeers::process_penalty] resolves it first -
      [let exemption = self.trust_basis_for(&id);] (all_peers.rs:261-263) - and
      [Peer::apply_penalty] short-circuits on it: [if let Some(basis) =
      exemption { .. warn on Severe/Fatal .. } else { self.score.apply_penalty(
      penalty); }] (peer.rs:213-233). [AllPeers::exemption] (:847-873) grants it
      to any peer whose confirmed BLS key is in the previous, current or next
      committee ([TrustBasis::Validator]) and to any operator-allowlisted peer
      ([TrustBasis::Operator]). [Penalty::Medium => self.add(-5.0)] and
      [Penalty::Fatal => config.min_score] (peers/score.rs:89-94) therefore
      apply to SCORED peers only. Modelling this is not optional: without it
      "the refusal costs B five points" would be true only because the model
      omitted the branch on which it costs nothing.
    - The GOSSIP contrast, consensus.rs:1491-1497: [if gossip.data.len() >
      MAX_GOSSIP_MESSAGE_SIZE { return GossipAcceptance::Reject(
      RejectReason::TooLarge); }] -> [RejectPenalty::FatalRelayer] ->
      [process_penalty(propagation_source, Penalty::Fatal)] (:1063-1073).
      [MAX_GOSSIP_MESSAGE_SIZE = 12_000] (config/network.rs:112) is documented
      at :98-111 as "a protocol constant, not a per-node tunable ... that
      attribution is sound only if every honest node applies the identical bound
      ... A per-node bound would instead let an honest relayer configured with a
      larger limit be Fatal-banned". That comment is the whole point of S1: the
      RPC path has no such constant.

    COMPONENTS (seven fields; the pristine reachable graph is exactly 53 states
    = 1 initial + 26 codec-resolved + 26 classified, where 26 = 13 admissible
    (plan, config) pairs x 2 trust bases).
    - [plan] : B's hidden intent for this exchange, fixed by the first step.
    - [cfg] : B's own [max_rpc_message_size], invisible to V0 at every step.
    - [trust] : whether B is exempt from the score model (all_peers.rs:847-873).
      VISIBLE to V0: it is computed from V0's own committee slots and its own
      operator allowlist, not from anything B sends.
    - [obs] : what V0's codec (or gossip check) reported - the io error kind AND
      its message, since V0 logs [?e] at consensus.rs:1290-1294.
    - [peak] : the peak resident size class of [compressed_buffer] relative to
      [snap::raw::max_compress_len(uncompressed_len)].
    - [settlement] : whether V0's classifier has run for this exchange.
    - [charge] : the penalty that actually reached B's score, latched. A latch
      is the honest encoding of the EVENT [Score::apply_penalty]: the score
      itself decays exponentially afterwards (peers/score.rs:108-119), but the
      charge having been levied is not undone by that decay.

    B's plan and V0's codec verdict are one atomic step, because
    [decode_message] is a single await on the inbound stream and no swarm event
    is emitted between B's first prefix byte and the codec's verdict. The
    classification is the SECOND step, because it is a separate swarm event
    ([ReqResEvent::InboundFailure]) processed by a different function.

    ROLE MAPPING.
    - V0 is THE READING NODE and the only knowledge agent under [K]. Its view is
      [(obs, settlement, charge, trust)]: the codec's error kind and text,
      whether the failure classifier has run, what reached B's score, and
      whether B is inside V0's trust basis. It does NOT see [plan] (B's intent
      is not on the wire), it does NOT see [cfg] (no field of any request
      carries the sender's configured cap, and the codec reads only two length
      prefixes), and it does NOT see [peak]: no branch anywhere reads
      [compressed_buffer.len()] as a decision input and no metric records it -
      the only consumers of those buffers are the four [Codec] methods
      (codec.rs:231-300) and [sync/frame.rs:76-103], all of which pass them
      through by reference.
    - V1 is THE SENDING PEER B, an agent with a real non-constant view
      [(plan, cfg, trust, disconnected)]: B knows its own intent, its own
      configured cap and its own committee membership, and observes a
      disconnect exactly when a Fatal penalty actually reached its score
      (peers/manager.rs:429-443, ban path :448-461). B is deliberately NEVER an
      operand of [K] in this family: [K_V1(deviated(B))] would be a projection
      of V1's own view and therefore collapsed under R1.
    - V2..V9 are idle non-agents with the constant blank view and never appear
      under K. *)

(** B's hidden plan for this one exchange. Each constructor is a distinct wire
    behaviour with a distinct place in the codec's gate order. *)
type bplan =
  | Plan_undecided
      (** the pre-choice marker of the single initial state: B has not yet
          committed to a behaviour *)
  | Plan_honest_large_cap
      (** B is honest but runs [max_rpc_message_size = 2097152]
          (config/network.rs:509, :525) and sends a message legal under its own
          bound and over V0's default 1 MiB (:188). Admissible only with
          [Cfg_large]: [encode_message] refuses to originate a message above the
          sender's OWN cap (codec.rs:133-136), so a default-configured honest
          node cannot take this branch. *)
  | Plan_spam_oversize
      (** B deliberately declares [uncompressed_len > max_message_size] to make
          V0 do work, tripping codec.rs:51-54 with the identical error the
          honest-config-skew branch produces *)
  | Plan_honest_flap
      (** B is honest and its stream is reset mid-body by the network, so the
          read loop sees [read == 0] and raises [UnexpectedEof]
          (codec.rs:78-83) *)
  | Plan_grief_truncate
      (** B deliberately declares a body, delivers part of it and half-closes,
          producing the identical [UnexpectedEof] at codec.rs:78-83 *)
  | Plan_spam_inflate
      (** B declares a legal [uncompressed_len] together with an inflated
          [compressed_len], tripping codec.rs:61-67 *)
  | Plan_snappy_short
      (** B declares two legal lengths and delivers a well-formed but SHORT
          snappy frame, so the whole body is accumulated and the post-decode
          equality check at codec.rs:96-101 rejects it. This branch is what puts
          the "sibling" output bound of S3 into the pristine model. *)
  | Plan_spam_gossip
      (** the contrast branch: B relays a gossip payload above
          [MAX_GOSSIP_MESSAGE_SIZE] (config/network.rs:112), rejected at
          consensus.rs:1495-1497 and charged [Penalty::Fatal] at :1063-1073 *)

(** Total order index for {!bplan}. *)
let bplan_index = function
  | Plan_undecided -> 0
  | Plan_honest_large_cap -> 1
  | Plan_spam_oversize -> 2
  | Plan_honest_flap -> 3
  | Plan_grief_truncate -> 4
  | Plan_spam_inflate -> 5
  | Plan_snappy_short -> 6
  | Plan_spam_gossip -> 7

(** Total order on {!bplan}. *)
let bplan_compare a b = Int.compare (bplan_index a) (bplan_index b)

(** B's own [max_rpc_message_size] (config/network.rs:117-119). Per-node
    operator config, never on the wire, never visible to V0. *)
type bcfg =
  | Cfg_default  (** the [1024 * 1024] default of config/network.rs:188 *)
  | Cfg_large
      (** the 2 MiB value the repo's own partial-YAML test exercises
          (config/network.rs:509, asserted at :525) *)

(** Total order index for {!bcfg}. *)
let bcfg_index = function Cfg_default -> 0 | Cfg_large -> 1

(** Total order on {!bcfg}. *)
let bcfg_compare a b = Int.compare (bcfg_index a) (bcfg_index b)

(** Whether B is inside V0's trust basis (all_peers.rs:847-873). Computed by V0
    from its own three committee slots and its own operator allowlist, so it is
    VISIBLE to V0 and says nothing about what B sent. *)
type trust =
  | Trust_scored
      (** [trust_basis_for] returned [None]: B is subject to the normal score
          model (all_peers.rs:875-895) *)
  | Trust_exempt
      (** [Some TrustBasis::Validator] (B's confirmed BLS key is in the
          previous, current or next committee) or [Some TrustBasis::Operator]
          (B is operator-allowlisted); [Peer::apply_penalty] then bypasses the
          score model entirely (peer.rs:213-233) *)

(** Total order index for {!trust}. *)
let trust_index = function Trust_scored -> 0 | Trust_exempt -> 1

(** Total order on {!trust}. *)
let trust_compare a b = Int.compare (trust_index a) (trust_index b)

(** What V0's codec (or gossip size check) reported for this exchange. V0
    observes the io [ErrorKind] AND the error text, because the catch-all logs
    the whole error [?e] (consensus.rs:1290-1294); the three
    [std::io::Error::other] sites are therefore distinguishable to V0 even
    though the classifier treats them alike. *)
type obs =
  | Obs_pending  (** the exchange has not started; nothing reported yet *)
  | Obs_size_prefix
      (** [Error::other("prefix indicates message size is too large")],
          codec.rs:51-54 *)
  | Obs_size_compressed
      (** [Error::other("compressed size exceeds max for reported uncompressed
          size")], codec.rs:61-67 *)
  | Obs_size_mismatch
      (** [Error::other("decompressed size does not match reported uncompressed
          size")], codec.rs:96-101 *)
  | Obs_truncated
      (** [Error::new(ErrorKind::UnexpectedEof, "compressed body shorter than
          reported compressed size")], codec.rs:78-83 *)
  | Obs_gossip_too_large
      (** [GossipAcceptance::Reject(RejectReason::TooLarge)],
          consensus.rs:1495-1497 *)

(** Total order index for {!obs}. *)
let obs_index = function
  | Obs_pending -> 0
  | Obs_size_prefix -> 1
  | Obs_size_compressed -> 2
  | Obs_size_mismatch -> 3
  | Obs_truncated -> 4
  | Obs_gossip_too_large -> 5

(** Total order on {!obs}. *)
let obs_compare a b = Int.compare (obs_index a) (obs_index b)

(** The peak resident size class of [compressed_buffer] (codec.rs:73-86),
    measured against the bound the compressed-length gate is supposed to
    enforce, [snap::raw::max_compress_len(uncompressed_len)]. *)
type peak =
  | Peak_none
      (** the read loop at codec.rs:73-86 never ran: the exchange was rejected
          by a prefix gate, or it is not an RPC at all *)
  | Peak_bounded
      (** peak occupancy is within [max_compress_len(uncompressed_len)], the
          bound codec.rs:61-67 establishes *)
  | Peak_amplified
      (** peak occupancy is ABOVE that bound: [extend_from_slice] at
          codec.rs:84 grew the buffer past the capacity [TNCodec::new] reserved
          (:205-218), and [compressed_buffer.clear()] at :44 keeps that capacity
          resident on the per-behaviour codec instance for its lifetime *)

(** Total order index for {!peak}. *)
let peak_index = function
  | Peak_none -> 0
  | Peak_bounded -> 1
  | Peak_amplified -> 2

(** Total order on {!peak}. *)
let peak_compare a b = Int.compare (peak_index a) (peak_index b)

(** Whether V0's failure classifier (consensus.rs:1276-1320) or gossip reject
    handler (:1049-1074) has run for this exchange. *)
type settlement =
  | Unsettled  (** the swarm event has not been processed yet *)
  | Settled  (** it has, and {!charge} is final *)

(** Total order index for {!settlement}. *)
let settlement_index = function Unsettled -> 0 | Settled -> 1

(** Total order on {!settlement}. *)
let settlement_compare a b =
  Int.compare (settlement_index a) (settlement_index b)

(** The penalty that actually reached B's score, latched. A penalty that
    [Peer::apply_penalty] suppressed for an exempt peer (peer.rs:218-230) never
    becomes anything other than [Charge_none] here, which is the whole point of
    S1's exemption conjunct. *)
type charge =
  | Charge_none
      (** no [Score::apply_penalty] ran: either no penalty was levied, or the
          trust basis suppressed it *)
  | Charge_medium
      (** [Penalty::Medium => self.add(-5.0)] reached the score
          (consensus.rs:1295-1298, peers/score.rs:91) *)
  | Charge_fatal
      (** [Penalty::Fatal => config.min_score] reached the score and the peer is
          banned (consensus.rs:1070-1073, peers/score.rs:93,
          peers/manager.rs:448-461) *)

(** Total order index for {!charge}. *)
let charge_index = function
  | Charge_none -> 0
  | Charge_medium -> 1
  | Charge_fatal -> 2

(** Total order on {!charge}. *)
let charge_compare a b = Int.compare (charge_index a) (charge_index b)

(** The joint global state of one inbound exchange. *)
type state = {
  plan : bplan;  (** B's hidden intent, fixed by the first transition *)
  cfg : bcfg;  (** B's own configured [max_rpc_message_size] *)
  trust : trust;  (** whether B is inside V0's trust basis *)
  obs : obs;  (** what V0's codec or gossip check reported *)
  peak : peak;  (** peak resident [compressed_buffer] class *)
  settlement : settlement;  (** has V0's classifier run *)
  charge : charge;  (** the penalty that reached B's score *)
}

(** Total deterministic comparison over ALL state fields, in field order
    [plan, cfg, trust, obs, peak, settlement, charge]. *)
let state_compare s1 s2 =
  let c0 = bplan_compare s1.plan s2.plan in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = bcfg_compare s1.cfg s2.cfg in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = trust_compare s1.trust s2.trust in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = obs_compare s1.obs s2.obs in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = peak_compare s1.peak s2.peak in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = settlement_compare s1.settlement s2.settlement in
            if Bool.not (Int.equal c5 0) then c5
            else charge_compare s1.charge s2.charge

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view; see the header for the full role mapping.

    [View_reader] is V0, the node reading B's request:
    [(obs, settlement, charge, trust)]. It EXCLUDES [plan] (intent is not on the
    wire), [cfg] (no request field carries the sender's cap; the codec reads two
    length prefixes and nothing else, codec.rs:46-59) and [peak] (no branch
    reads [compressed_buffer.len()] and no metric records it). It INCLUDES
    [trust], because V0 computes it itself from its own committee slots and
    allowlist (all_peers.rs:847-873).

    [View_sender] is V1, the peer B: [(plan, cfg, trust, disconnected)]. B knows
    its own intent, its own cap and its own committee membership, and observes a
    disconnect exactly when a Fatal penalty reached its score
    (peers/manager.rs:429-443, :448-461). It EXCLUDES [obs], [settlement] and
    any Medium charge: nothing is sent back to a peer when a sub-fatal penalty
    is applied.

    [View_idle] is the constant blank view of the non-agents V2..V9. *)
type view =
  | View_reader of obs * settlement * charge * trust  (** V0: the reading node *)
  | View_sender of bplan * bcfg * trust * bool  (** V1: the sending peer B *)
  | View_idle  (** the constant blank view of the non-agents V2..V9 *)

(** Total deterministic order over ALL fields of the reader's view. *)
let view_reader_compare (o, s, c, t) (o', s', c', t') =
  let c0 = obs_compare o o' in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = settlement_compare s s' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = charge_compare c c' in
      if Bool.not (Int.equal c2 0) then c2 else trust_compare t t'

(** Total deterministic order over ALL fields of the sender's view. *)
let view_sender_compare (p, g, t, d) (p', g', t', d') =
  let c0 = bplan_compare p p' in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = bcfg_compare g g' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = trust_compare t t' in
      if Bool.not (Int.equal c2 0) then c2 else Bool.compare d d'

(** Total order on views: [View_idle] < [View_reader] < [View_sender], with the
    field-wise order within each constructor. Every constructor pair is spelled:
    no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_reader _ | View_sender _) -> -1
  | (View_reader _ | View_sender _), View_idle -> 1
  | View_reader (o, s, c, t), View_reader (o', s', c', t') ->
      view_reader_compare (o, s, c, t) (o', s', c', t')
  | View_reader _, View_sender _ -> -1
  | View_sender _, View_reader _ -> 1
  | View_sender (p, g, t, d), View_sender (p', g', t', d') ->
      view_sender_compare (p, g, t, d) (p', g', t', d')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** Has a Fatal penalty actually reached B's score, and therefore banned and
    disconnected it? Only [Charge_fatal] reaches [config.min_score]
    (peers/score.rs:93) and the ban path (peers/manager.rs:448-461); a Medium
    charge is silent to the peer, and a suppressed penalty is no charge at
    all. *)
let disconnected s =
  match s.charge with
  | Charge_fatal -> true
  | Charge_none | Charge_medium -> false

(** View projection. V0 is the reading node and the only agent that appears
    under [K]; V1 is the sending peer B, an agent with a real view that is never
    an operand of [K] (R1: it would be a projection of its own view); V2..V9 are
    idle non-agents with the constant blank view. *)
let view v s =
  match v with
  | Validator.V0 -> View_reader (s.obs, s.settlement, s.charge, s.trust)
  | Validator.V1 -> View_sender (s.plan, s.cfg, s.trust, disconnected s)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at HEAD [0c59c15b] *)
  | No_inbound_catchall_penalty
      (** delete the catch-all arm of the inbound [Io] classifier -
          [_ => { warn!(.. "inbound IO failure (likely codec violation)"); self
          .swarm.behaviour_mut().peer_manager.process_penalty(peer,
          Penalty::Medium); }] (consensus.rs:1289-1299). REMOVES the charge on
          the classify transition for every [ErrorKind::Other] observation, so
          [Obs_size_prefix], [Obs_size_compressed] and [Obs_size_mismatch]
          settle at [Charge_none] instead of [Charge_medium].

          Why no sibling path repairs it, hunted in the real code. (a) The
          outbound mirror (consensus.rs:1241-1251) has the identical arm, but it
          fires on [ReqResEvent::OutboundFailure] - this node reading a
          RESPONSE to a request it issued - a different event with a different
          initiator, and the scope of this family is the inbound direction
          throughout. (b) [verify_gossip] (:1491-1497 -> :1063-1073) charges
          [Penalty::Fatal], but that is the gossipsub behaviour; the model keeps
          it LIVE under this mutation, which is exactly why S1's gossip conjunct
          survives here while its RPC conjunct falls, and it is the witness that
          the deletion did not simply disable all charging. (c) The application
          route [NetworkCommand::ReportPenalty] (:894-901) is driven from the
          consensus crates only after a message has DECODED
          (worker/src/network/mod.rs:490-498, :527-535, :596-604, :659-665) and
          so cannot fire for a codec error. (d) Every remaining inbound arm is
          explicitly no-penalty: [UnsupportedProtocols] (:1307-1309),
          [Timeout | ConnectionClosed] (:1310-1312), [ResponseOmission] (:1313).
          (e) [peers/manager.rs:429-443] is the sole entry into
          [AllPeers::process_penalty] (all_peers.rs:261-266) and there is no
          failure-count escalation anywhere on this path. *)
  | No_inbound_eof_exemption
      (** delete [ErrorKind::UnexpectedEof] from the inbound exemption chain -
          one alternative of the [|] list at consensus.rs:1281-1286, namely
          :1284. A truncated body then falls through to the catch-all at
          :1289-1299, so the classify transition ADDS a [Charge_medium] on the
          [Obs_truncated] branch of a SCORED peer where the pristine model has
          [Charge_none].

          Why no sibling path repairs it: this mutation ADDS a charge rather
          than removing one, so the question is instead whether the pristine
          no-charge is itself repaired elsewhere, and it is not. (a) The
          outbound classifier carries the same exemption (:1236) and is a
          different event anyway. (b) [Timeout | ConnectionClosed] (:1310-1312)
          and [ResponseOmission] (:1313) are explicit no-penalty arms. (c) The
          peer manager's only route into [Score::apply_penalty] is
          [process_penalty] (peers/manager.rs:429-443 -> all_peers.rs:261-266 ->
          peer.rs:213-233); connection bookkeeping does not touch score. (d) The
          application route cannot see a message that never decoded. *)
  | No_trust_exemption
      (** delete the trust-basis short-circuit in [Peer::apply_penalty] -
          [if let Some(basis) = exemption { .. } else { self.score
          .apply_penalty(penalty); }] (peer.rs:218-233), i.e. score every peer.
          A [Trust_exempt] peer then takes the SAME charge a [Trust_scored] peer
          takes, so the classify transition ADDS a [Charge_medium] on the
          exempt prefix-rejection branch where the pristine model has
          [Charge_none].

          Why no sibling path repairs it. (a) [Peer::apply_penalty] is the only
          caller of [Score::apply_penalty] (peer.rs:232); the exemption is
          resolved once at all_peers.rs:261-263 and threaded through, and the
          only other consumer is [Peer::ensure_banned] (peer.rs:244-252), which
          forwards the same argument to the same function - deleting the
          short-circuit disables both together. (b) There is no second
          allowlist check at the network-layer call sites: the penalty call
          sites in consensus.rs pass a bare [(peer_id, penalty)] and know
          nothing about trust. (c) The ban path keys off [Reputation] alone
          (all_peers.rs:264-284), so with the short-circuit gone an exempt peer
          bans exactly like any other. *)
  | No_compressed_length_gate
      (** delete the compressed-length gate - [let max_compress_len =
          snap::raw::max_compress_len(uncompressed_len); if compressed_len >
          max_compress_len { return Err(std::io::Error::other(..)); }]
          (codec.rs:61-67). B may then declare a legal [uncompressed_len]
          together with an inflated [compressed_len] and the loop at
          codec.rs:73-86 accumulates every delivered byte, so the
          [Plan_spam_inflate] codec transition CHANGES from
          [(Obs_size_compressed, Peak_none)] to
          [(Obs_size_mismatch, Peak_amplified)].

          Why no sibling path repairs it, hunted in the real code and MODELLED.
          (a) codec.rs:51-54 bounds only [uncompressed_len]; it stays live under
          this mutation and the mutated branch still passes it. (b) The output
          bounds - [.take(decode_limit)] (:91-93) and the equality check
          (:96-101) - constrain [decode_buffer] and run only after the whole
          compressed body has been accumulated. The model HAS this repair: the
          mutated branch still ends in [Obs_size_mismatch] and still settles at
          [Charge_medium] for a scored peer, and the pristine
          [Plan_snappy_short] branch exercises the same equality check with a
          bounded buffer. It rejects the message; it does not bound the
          accumulation, which is precisely what S3 asserts. (c) [TNCodec::new]
          (:205-218) does [Vec::with_capacity(max_compress_len)] - an initial
          capacity, not a cap; [extend_from_slice] grows past it and
          [compressed_buffer.clear()] (:44) preserves the grown capacity on the
          per-behaviour codec instance (:189-201, reused by all four [Codec]
          methods at :231-300). (d) QUIC flow control (consensus.rs:447-455 <-
          config/network.rs:292-296, defaults 50 MiB per stream and 100 MiB per
          connection at :309-310) bounds UNACKNOWLEDGED data, and the read loop
          acknowledges as it consumes, so it throttles the accumulation without
          capping it; the residual cap is the 4-byte [compressed_len] prefix
          itself (codec.rs:56-59). The refutation is therefore of the stated
          bound, not a claim of unboundedness. *)

(** [xs] if [cond], otherwise no successor. Keeps every transition a total
    function into a successor list with no loop keyword. *)
let enabled_list cond xs = if cond then xs else []

(** Has B not yet committed to a plan (i.e. is this the initial state)? *)
let is_undecided p =
  match p with
  | Plan_undecided -> true
  | Plan_honest_large_cap | Plan_spam_oversize | Plan_honest_flap
  | Plan_grief_truncate | Plan_spam_inflate | Plan_snappy_short
  | Plan_spam_gossip ->
      false

(** Has V0's classifier not yet run for this exchange? *)
let is_unsettled st = match st with Unsettled -> true | Settled -> false

(** Every plan B can commit to, in {!bplan_index} order; [Plan_undecided] is the
    pre-choice marker and is not a choice. *)
let all_plans =
  [
    Plan_honest_large_cap;
    Plan_spam_oversize;
    Plan_honest_flap;
    Plan_grief_truncate;
    Plan_spam_inflate;
    Plan_snappy_short;
    Plan_spam_gossip;
  ]

(** Both operator settings of [max_rpc_message_size] this family carries. *)
let all_cfgs = [ Cfg_default; Cfg_large ]

(** Both sides of the trust basis (all_peers.rs:847-873). *)
let all_trusts = [ Trust_scored; Trust_exempt ]

(** Is [(plan, cfg)] an admissible pair? Only [Plan_honest_large_cap] is
    constrained: an HONEST node cannot originate a message above its own cap
    because [encode_message] refuses it - [if encode_buffer.len() >
    max_message_size { return Err(std::io::Error::other("encode data >
    max_message_size")); }] (codec.rs:133-136) - so the honest-config-skew
    branch exists only for a peer configured above V0. A Byzantine sender is
    under no such constraint, which is why every spam branch takes both
    settings. The trust basis is orthogonal to both: committee membership and
    the operator allowlist say nothing about what a peer sends. *)
let plan_admits_cfg plan cfg =
  match plan with
  | Plan_honest_large_cap -> (
      match cfg with Cfg_default -> false | Cfg_large -> true)
  | Plan_undecided | Plan_spam_oversize | Plan_honest_flap | Plan_grief_truncate
  | Plan_spam_inflate | Plan_snappy_short | Plan_spam_gossip ->
      true

(** Which [(obs, peak)] pair V0's codec produces for a given plan, in the gate
    order of codec.rs:51-101. Only [Plan_spam_inflate] is mutation-sensitive:
    with codec.rs:61-67 deleted its body is accumulated instead of refused, and
    the failure surfaces later at the equality check (:96-101) with the buffer
    already amplified. *)
let codec_outcome mut plan =
  match plan with
  | Plan_undecided -> []
  | Plan_honest_large_cap | Plan_spam_oversize ->
      [ (Obs_size_prefix, Peak_none) ]
  | Plan_honest_flap | Plan_grief_truncate -> [ (Obs_truncated, Peak_bounded) ]
  | Plan_snappy_short -> [ (Obs_size_mismatch, Peak_bounded) ]
  | Plan_spam_gossip -> [ (Obs_gossip_too_large, Peak_none) ]
  | Plan_spam_inflate -> (
      match mut with
      | Pristine | No_inbound_catchall_penalty | No_inbound_eof_exemption
      | No_trust_exemption ->
          [ (Obs_size_compressed, Peak_none) ]
      | No_compressed_length_gate -> [ (Obs_size_mismatch, Peak_amplified) ])

(** T1 - B opens the exchange with a hidden plan, carrying its own operator
    config and its own standing in V0's trust basis, and V0's codec resolves it
    in the same step: the two prefix gates (codec.rs:51-54, :61-67), the
    streaming read loop (:73-86) and the output bounds (:88-101) run in source
    order inside one [decode_message] await, or the gossip size check
    (consensus.rs:1495-1497) does for the contrast branch. No swarm event is
    emitted in between, which is why the codec verdict is atomic here and the
    classification below is not. *)
let t_exchange mut s =
  enabled_list (is_undecided s.plan)
    (List.concat_map
       (fun plan ->
         List.concat_map
           (fun cfg ->
             enabled_list (plan_admits_cfg plan cfg)
               (List.concat_map
                  (fun trust ->
                    List.map
                      (fun (o, p) ->
                        { s with plan; cfg; trust; obs = o; peak = p })
                      (codec_outcome mut plan))
                  all_trusts))
           all_cfgs)
       all_plans)

(** Does this observation generate an event V0's penalty logic processes? Every
    codec failure surfaces as [ReqResEvent::InboundFailure]
    (consensus.rs:1276-1320) and the gossip reject as a [GossipAcceptance]
    verdict (:1049-1074); only the pre-exchange state generates nothing. *)
let settles o =
  match o with
  | Obs_pending -> false
  | Obs_size_prefix | Obs_size_compressed | Obs_size_mismatch | Obs_truncated
  | Obs_gossip_too_large ->
      true

(** The penalty V0's classifier LEVIES for an observation, before the trust
    basis decides whether it reaches the score. The three [Error::other] sites
    share the [ErrorKind::Other] catch-all (consensus.rs:1289-1299); the
    truncation carries [ErrorKind::UnexpectedEof] and takes the transport-flap
    exemption (:1284); the gossip reject is Fatal (:1063-1073). *)
let levied mut o =
  match o with
  | Obs_pending -> Charge_none
  | Obs_size_prefix | Obs_size_compressed | Obs_size_mismatch -> (
      match mut with
      | Pristine | No_inbound_eof_exemption | No_trust_exemption
      | No_compressed_length_gate ->
          Charge_medium
      | No_inbound_catchall_penalty -> Charge_none)
  | Obs_truncated -> (
      match mut with
      | Pristine | No_inbound_catchall_penalty | No_trust_exemption
      | No_compressed_length_gate ->
          Charge_none
      | No_inbound_eof_exemption -> Charge_medium)
  | Obs_gossip_too_large -> Charge_fatal

(** What actually reaches B's score: [Peer::apply_penalty] runs
    [self.score.apply_penalty(penalty)] only when the resolved [TrustBasis] is
    [None] (peer.rs:218-233), so an exempt peer's penalty is suppressed whatever
    its severity - the Severe/Fatal case is merely logged (:223-230). *)
let charge_of mut trust o =
  match trust with
  | Trust_scored -> levied mut o
  | Trust_exempt -> (
      match mut with
      | No_trust_exemption -> levied mut o
      | Pristine | No_inbound_catchall_penalty | No_inbound_eof_exemption
      | No_compressed_length_gate ->
          Charge_none)

(** T2 - V0 classifies the exchange: the inbound failure match
    (consensus.rs:1279-1314) or the gossip reject handler (:1049-1074) levies a
    penalty, and [Peer::apply_penalty] (peer.rs:213-233) decides whether it
    reaches the score. This is the step all three penalty mutations edit. *)
let t_classify mut s =
  enabled_list
    (is_unsettled s.settlement && settles s.obs)
    [ { s with settlement = Settled; charge = charge_of mut s.trust s.obs } ]

(** The transition relation: the two phases unioned, one step per successor.
    Every step strictly advances the exchange (undecided -> resolved, unsettled
    -> settled), so the reachable graph is acyclic. A state with no successor is
    stutter-closed by the kernel, which is what makes the [Af] in S1 honest. *)
let next_with mut s = List.concat [ t_exchange mut s; t_classify mut s ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: a connection is up and no exchange has started. [cfg] and
    [trust] carry placeholder values here because B has committed to nothing
    yet; the first transition sets all three together. *)
let initial =
  {
    plan = Plan_undecided;
    cfg = Cfg_default;
    trust = Trust_scored;
    obs = Obs_pending;
    peak = Peak_none;
    settlement = Unsettled;
    charge = Charge_none;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Rpc_prefix_size_reject
      (** V0's codec refused the request on the declared uncompressed length:
          [uncompressed_len > max_message_size] (codec.rs:51-54) *)
  | Gossip_size_reject
      (** V0 rejected a gossip payload above the network-wide
          [MAX_GOSSIP_MESSAGE_SIZE] (consensus.rs:1495-1497,
          config/network.rs:98-112) *)
  | Body_truncated
      (** V0's read loop hit [read == 0] before [remaining] reached zero
          (codec.rs:78-83) *)
  | Inflated_compressed_declaration
      (** B declared a [compressed_len] above
          [snap::raw::max_compress_len(uncompressed_len)] - the condition
          codec.rs:61-67 exists to refuse *)
  | Deviated
      (** B's plan is a deliberate protocol deviation, as opposed to honest
          behaviour under a different operator config or a genuine WAN flap.
          A fact about [plan], hidden from V0 at every step. *)
  | Deliberate_truncation
      (** B withheld the declared body ON PURPOSE, as opposed to a middlebox
          resetting the stream. Hidden from V0: both branches raise the
          identical [UnexpectedEof] at codec.rs:78-83. *)
  | Penalty_exempt
      (** B is inside V0's trust basis - a peer whose confirmed BLS key is in
          the previous, current or next committee, or an operator-allowlisted
          peer (all_peers.rs:847-873) - so [Peer::apply_penalty] bypasses the
          score model (peer.rs:218-233). Computed by V0, hence visible to it. *)
  | Charged_medium
      (** a [Penalty::Medium] reached B's score: [self.add(-5.0)]
          (peers/score.rs:91) *)
  | Charged_any
      (** some penalty reached B's score in this exchange, at any severity *)
  | Peer_cap_above_ours
      (** B runs [max_rpc_message_size] above V0's - the 2 MiB operator setting
          of config/network.rs:509. Never on the wire, never visible to V0. *)
  | Body_read_ran
      (** the streaming read loop at codec.rs:73-86 executed at least one
          [extend_from_slice] for this exchange *)
  | Buffer_amplified
      (** [compressed_buffer]'s peak occupancy exceeded
          [snap::raw::max_compress_len(uncompressed_len)] *)
  | Exchange_settled
      (** V0's classifier has run for this exchange (consensus.rs:1276-1320 or
          :1049-1074) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Rpc_prefix_size_reject -> (
      match s.obs with
      | Obs_size_prefix -> true
      | Obs_pending | Obs_size_compressed | Obs_size_mismatch | Obs_truncated
      | Obs_gossip_too_large ->
          false)
  | Gossip_size_reject -> (
      match s.obs with
      | Obs_gossip_too_large -> true
      | Obs_pending | Obs_size_prefix | Obs_size_compressed | Obs_size_mismatch
      | Obs_truncated ->
          false)
  | Body_truncated -> (
      match s.obs with
      | Obs_truncated -> true
      | Obs_pending | Obs_size_prefix | Obs_size_compressed | Obs_size_mismatch
      | Obs_gossip_too_large ->
          false)
  | Inflated_compressed_declaration -> (
      match s.plan with
      | Plan_spam_inflate -> true
      | Plan_undecided | Plan_honest_large_cap | Plan_spam_oversize
      | Plan_honest_flap | Plan_grief_truncate | Plan_snappy_short
      | Plan_spam_gossip ->
          false)
  | Deviated -> (
      match s.plan with
      | Plan_spam_oversize | Plan_grief_truncate | Plan_spam_inflate
      | Plan_snappy_short | Plan_spam_gossip ->
          true
      | Plan_undecided | Plan_honest_large_cap | Plan_honest_flap -> false)
  | Deliberate_truncation -> (
      match s.plan with
      | Plan_grief_truncate -> true
      | Plan_undecided | Plan_honest_large_cap | Plan_spam_oversize
      | Plan_honest_flap | Plan_spam_inflate | Plan_snappy_short
      | Plan_spam_gossip ->
          false)
  | Penalty_exempt -> (
      match s.trust with Trust_exempt -> true | Trust_scored -> false)
  | Charged_medium -> (
      match s.charge with
      | Charge_medium -> true
      | Charge_none | Charge_fatal -> false)
  | Charged_any -> (
      match s.charge with
      | Charge_medium | Charge_fatal -> true
      | Charge_none -> false)
  | Peer_cap_above_ours -> (
      match s.cfg with Cfg_large -> true | Cfg_default -> false)
  | Body_read_ran -> (
      match s.peak with
      | Peak_bounded | Peak_amplified -> true
      | Peak_none -> false)
  | Buffer_amplified -> (
      match s.peak with
      | Peak_amplified -> true
      | Peak_none | Peak_bounded -> false)
  | Exchange_settled -> (
      match s.settlement with Settled -> true | Unsettled -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Rpc_prefix_size_reject -> "rpc_prefix_size_reject(V0, B)"
  | Gossip_size_reject -> "gossip_size_reject(V0, B)"
  | Body_truncated -> "body_truncated(B)"
  | Inflated_compressed_declaration -> "inflated_compressed_declaration(B)"
  | Deviated -> "deviated(B)"
  | Deliberate_truncation -> "deliberate_truncation(B)"
  | Penalty_exempt -> "penalty_exempt(B)"
  | Charged_medium -> "charged_medium(B)"
  | Charged_any -> "charged_any(B)"
  | Peer_cap_above_ours -> "peer_cap_above_ours(B)"
  | Body_read_ran -> "body_read_ran"
  | Buffer_amplified -> "buffer_amplified"
  | Exchange_settled -> "exchange_settled"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation ({!Denote}, lib/internal/DESIGN.md), pinned to
    agree with {!System} at every reachable world by
    test/t_rpc_codec_size_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state, mutation-
    parameterized transitions, the two-agent view and the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
