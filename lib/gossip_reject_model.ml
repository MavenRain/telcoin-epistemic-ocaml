(** Finite interpreted system for the GOSSIP_REJECT family: how
    telcoin-network's gossip reject path attributes accountability, and what a
    receiving node can and cannot KNOW about the two candidate culprits. File
    citations refer to Telcoin-Association/telcoin-network (HEAD 0c59c15b).

    The modeled mechanism. A single gossip message is delivered to V0 by a
    relaying peer R and was authored by a distinct peer A. [verify_gossip]
    (crates/network-libp2p/src/consensus.rs:1491-1514) runs two checks in
    order: a size check against the compile-time protocol constant
    [MAX_GOSSIP_MESSAGE_SIZE] (crates/config/src/network.rs:98-112,
    consensus.rs:1495-1497), then an authorized-publisher check against V0's
    OWN per-topic [authorized_publishers] map (consensus.rs:1499-1513). The
    resulting [RejectReason] decides who is charged
    (consensus.rs:2040-2098): [TooLarge] -> [FatalRelayer],
    [UnauthorizedAuthor] -> [FatalAuthor], never the reverse. The dispatch at
    consensus.rs:1049-1101 calls [process_penalty] on exactly one of the two
    peers. [process_penalty] resolves the identity, computes the committee
    exemption and forwards it (crates/network-libp2p/src/peers/all_peers.rs:258-303,
    :847-873); an exempt peer bypasses the score model entirely
    (crates/network-libp2p/src/peers/peer.rs:209-237, the [if let Some(basis) =
    exemption] bypass at :218-233), while a non-exempt [Penalty::Fatal] sets the
    score to [min_score] (crates/network-libp2p/src/peers/score.rs:84-100) which
    is at or below [min_score_before_ban], so [reputation_for] returns [Banned]
    (score.rs:157-187, thresholds at crates/config/src/network.rs:446-465).

    The family's ONE idea: the split at consensus.rs:2090-2097 is an EPISTEMIC
    one. The size bound is a compile-time constant identical on every node (the
    doc comment at config/network.rs:100-110 says so, and says why a per-node
    bound would be unsound), so visible evidence ENTAILS the hidden fact and
    the relayer is knowably guilty. The publisher set is per-node epoch-scoped
    state installed by each node's own [Subscribe] (consensus.rs:800-805,
    crates/node/src/manager/node/start_epoch.rs:505-524), so the same visible
    evidence entails NOTHING about the relayer and it is unjudgeable. The
    residual mis-attribution risk on the author side is absorbed by the peer
    manager's [TrustBasis] exemption.

    Components (all four sampled once, at delivery time, then carried through
    the pipeline):
    - the payload size class {!payload}, measured against the protocol
      constant;
    - the author's standing {!authorship} as V0's two local lookups see it,
      with the honest/Byzantine intent split inside the "denied but tracked"
      class;
    - the relaying peer's OWN publisher verdict {!relayer_map} - HIDDEN;
    - the derived relayer-deviation flag {!deviation} - HIDDEN, functionally
      determined by the two above, so it adds no branching.
    Carried through a 4-stage pipeline {!stage}: [Quiet] (nothing in flight) ->
    [Inbound] (gossipsub delivered; the verdict not yet acted on) -> [Settled]
    ([RejectReason::penalty] chosen and the peer manager applied it) ->
    [Rotated] (the next [update_committees] ran [apply_committee_membership],
    all_peers.rs:1102-1122 / :1180-1239).

    Role mapping. V0 is the SOLE knowledge agent: it is the receiving node, and
    its view is exactly what it locally computed - its own pipeline stage, the
    byte-length class it measured (consensus.rs:1495), the author class its own
    two maps yield (consensus.rs:1502-1508 plus the committee slots at
    all_peers.rs:847-873), the penalty target it itself selected
    (consensus.rs:1063), and the author's reputation in its own peer record.
    V1, V2 and V3 are idle: constant blank view, never under K. R and A are
    PHANTOM peers - never a {!Validator.t}, never under K - exactly as the
    frozen [Admission_model] treats its phantom peer O.

    What V0 does NOT see, and why each omission is real:
    (1) [rmap], the relaying peer's own [authorized_publishers] verdict on this
    author. That map is per-node state installed by that node's own [Subscribe]
    (consensus.rs:800-805) with its own epoch's committee keys
    (start_epoch.rs:517-524); nothing on the wire carries it.
    (2) [rdev], whether the relayer itself broke protocol. On the [Within]
    branch this is decided entirely by (1).
    (3) the split of [Cls_denied_committee] into [Auth_stale_honest] and
    [Auth_stale_byz] - the remote author's intent, i.e. which committee view it
    published under. consensus.rs:2054-2060 names the honest case explicitly.
    Those three omissions are the only hidden state and each is the operand of
    exactly one K family.

    Scoping, fixed and documented, none of it load-bearing for any statement:
    the relayer and the author are DISTINCT peers (A <> R, so the first-hop
    originator case is out of scope); both BLS identities are resolved, i.e.
    [penalty(relayer_resolved = true, author_resolved = true)], so the two
    [Skip] arms at consensus.rs:2093 and :2095 are not enumerated - they only
    ever weaken the charge, so their absence cannot make a statement true; the
    relayer is a non-exempt, non-allowlisted peer; [Auth_rogue] is not
    operator-allowlisted; app-layer penalties after [Accept]
    (consensus.rs:1027-1041, issue #819) are omitted because rejects never
    reach the consumer - only the [Accept] arm calls [try_send] at :1039-1041 -
    and because such a penalty would route through the same exempt-aware
    [process_penalty] anyway; the [Oversized] class denotes the 12_001..65_535
    byte band, where libp2p's own untouched default [max_transmit_size] of
    65536 does not fire. *)

(** Payload size class of the delivered gossip message, measured against the
    compile-time protocol constant [MAX_GOSSIP_MESSAGE_SIZE]
    (config/network.rs:98-112, consensus.rs:1495). *)
type payload =
  | Within  (** at or under the 12,000-byte protocol bound *)
  | Oversized
      (** in the 12_001..65_535 band: above the TN bound, below libp2p's own
          untouched default [max_transmit_size] of 65536
          (libp2p-gossipsub config default; TN's [ConfigBuilder] at
          consensus.rs:342-362 never calls [.max_transmit_size]) *)

(** Total order index for {!payload}. *)
let payload_index = function Within -> 0 | Oversized -> 1

(** Total order on {!payload}. *)
let payload_compare a b = Int.compare (payload_index a) (payload_index b)

(** [true] iff the payload exceeds [MAX_GOSSIP_MESSAGE_SIZE]. *)
let payload_is_over = function Within -> false | Oversized -> true

(** The author's standing, as V0's own two local lookups see it, plus the
    hidden intent split inside the denied-but-tracked class. *)
type authorship =
  | Auth_current
      (** in V0's per-topic [authorized_publishers] map
          (consensus.rs:1502-1508): the message is Accepted *)
  | Auth_stale_honest
      (** absent from V0's [authorized_publishers] but present in a tracked
          previous/current/next committee slot (all_peers.rs:836-845,
          :860-868), publishing honestly under its OWN epoch view - the case
          consensus.rs:2057-2059 names *)
  | Auth_stale_byz
      (** the SAME observable class as {!Auth_stale_honest}, but deliberately
          publishing outside its authorization *)
  | Auth_rogue
      (** in no tracked committee slot and not operator-allowlisted, so
          [exemption] returns [None] (all_peers.rs:865-872) *)

(** Total order index for {!authorship}. *)
let authorship_index = function
  | Auth_current -> 0
  | Auth_stale_honest -> 1
  | Auth_stale_byz -> 2
  | Auth_rogue -> 3

(** Total order on {!authorship}. *)
let authorship_compare a b =
  Int.compare (authorship_index a) (authorship_index b)

(** [true] iff V0's own [authorized_publishers] map denies this author, i.e.
    [verify_gossip] falls to the [UnauthorizedAuthor] branch
    (consensus.rs:1509-1513). *)
let author_is_denied = function
  | Auth_current -> false
  | Auth_stale_honest | Auth_stale_byz | Auth_rogue -> true

(** [true] iff the author holds a [Confirmed] key in one of the three tracked
    committee slots, so [exemption] returns [Some TrustBasis::Validator]
    (all_peers.rs:847-873). *)
let author_in_committee = function
  | Auth_current | Auth_stale_honest | Auth_stale_byz -> true
  | Auth_rogue -> false

(** [true] iff the author really did publish outside its authorization on
    purpose. PARTLY HIDDEN: {!Auth_stale_honest} and {!Auth_stale_byz} collapse
    into one observable class. *)
let author_deviates = function
  | Auth_current | Auth_stale_honest -> false
  | Auth_stale_byz | Auth_rogue -> true

(** HIDDEN. The relaying peer's OWN [authorized_publishers] verdict on this
    author - per-node state installed by that peer's own [Subscribe]
    (consensus.rs:800-805) with its own epoch's committee keys
    (start_epoch.rs:517-524). Never in any view. *)
type relayer_map =
  | Map_permits  (** the relayer's own map authorizes this author *)
  | Map_forbids
      (** the relayer's own map denies this author, so an honest relayer's
          [verify_gossip] would have Rejected and never forwarded *)

(** Total order index for {!relayer_map}. *)
let relayer_map_index = function Map_permits -> 0 | Map_forbids -> 1

(** Total order on {!relayer_map}. *)
let relayer_map_compare a b =
  Int.compare (relayer_map_index a) (relayer_map_index b)

(** [true] iff the relayer's own publisher map denies this author. *)
let relayer_map_is_forbid = function Map_permits -> false | Map_forbids -> true

(** HIDDEN. Whether the relaying peer itself broke protocol in delivering this
    message: it either published a payload the origination guard forbids
    (consensus.rs:790-791), or forwarded one its own [verify_gossip] must have
    Rejected - under [ValidationMode::Strict] + [validate_messages]
    (consensus.rs:342-362) only the [Accept] arm of
    [report_message_validation_result] forwards. *)
type deviation =
  | Dev_none  (** the relayer behaved as an honest node running this binary *)
  | Dev_relay  (** the relaying peer itself misbehaved *)

(** Total order index for {!deviation}. *)
let deviation_index = function Dev_none -> 0 | Dev_relay -> 1

(** Total order on {!deviation}. *)
let deviation_compare a b =
  Int.compare (deviation_index a) (deviation_index b)

(** [true] iff the relaying peer itself broke protocol. *)
let deviation_is_relay = function Dev_none -> false | Dev_relay -> true

(** Which peer the reject path selected as the penalty target - the
    [RejectPenalty] decision and its [process_penalty] call, NOT its score
    effect (consensus.rs:1063-1099). *)
type charge =
  | Charge_none  (** Accepted, or the verdict not yet acted on *)
  | Charge_relayer
      (** [RejectPenalty::FatalRelayer]: [process_penalty(propagation_source,
          Penalty::Fatal)] at consensus.rs:1070-1073 *)
  | Charge_author
      (** [RejectPenalty::FatalAuthor]: [process_penalty(author_id,
          Penalty::Fatal)] at consensus.rs:1084-1087 *)

(** Total order index for {!charge}. *)
let charge_index = function
  | Charge_none -> 0
  | Charge_relayer -> 1
  | Charge_author -> 2

(** Total order on {!charge}. *)
let charge_compare a b = Int.compare (charge_index a) (charge_index b)

(** [true] iff the forwarding peer was made the penalty target. *)
let charge_is_relayer = function
  | Charge_none | Charge_author -> false
  | Charge_relayer -> true

(** [true] iff the message author was made the penalty target. *)
let charge_is_author = function
  | Charge_none | Charge_relayer -> false
  | Charge_author -> true

(** The author's reputation inside V0's peer manager, as [reputation_for] maps
    the aggregate score (score.rs:181-187). [Disconnected] is not modeled: a
    [Penalty::Fatal] jumps straight to [min_score] (score.rs:93), which is at
    or below [min_score_before_ban], so the intermediate band is unreachable on
    this path. *)
type rep =
  | Rep_trusted  (** score strictly above [min_score_before_disconnect] *)
  | Rep_banned
      (** [aggregate_score <= min_score_before_ban] (score.rs:158-161,
          :183) *)

(** Total order index for {!rep}. *)
let rep_index = function Rep_trusted -> 0 | Rep_banned -> 1

(** Total order on {!rep}. *)
let rep_compare a b = Int.compare (rep_index a) (rep_index b)

(** [true] iff the peer manager actually banned the author. *)
let rep_is_banned = function Rep_trusted -> false | Rep_banned -> true

(** Pipeline position of the single modeled gossip delivery. *)
type stage =
  | Quiet  (** nothing in flight *)
  | Inbound
      (** gossipsub delivered the message to V0's [GossipEvent::Message] arm
          (consensus.rs:989-1002); [verify_gossip]'s verdict is not yet acted
          on *)
  | Settled
      (** [RejectReason::penalty] chosen and [process_penalty] applied
          (consensus.rs:1049-1099) *)
  | Rotated
      (** the next [update_committees] ran [apply_committee_membership]
          (all_peers.rs:1102-1122, :1180-1239) *)

(** Total order index for {!stage}. *)
let stage_index = function
  | Quiet -> 0
  | Inbound -> 1
  | Settled -> 2
  | Rotated -> 3

(** Total order on {!stage}. *)
let stage_compare a b = Int.compare (stage_index a) (stage_index b)

(** [true] iff V0 has taken delivery of the gossip message. *)
let stage_is_delivered = function
  | Quiet -> false
  | Inbound | Settled | Rotated -> true

(** The joint global state. [rdev], [charge] and [arep] are SET by the
    transitions from the three sampled components, not sampled themselves, so
    they add no branching. *)
type state = {
  stage : stage;  (** pipeline position *)
  payload : payload;  (** size class of the delivered payload *)
  author : authorship;  (** the author's standing plus its hidden intent *)
  rmap : relayer_map;  (** HIDDEN: the relayer's own publisher verdict *)
  rdev : deviation;  (** HIDDEN: whether the relayer itself misbehaved *)
  charge : charge;  (** which peer the reject path charged *)
  arep : rep;  (** the author's reputation in V0's peer manager *)
}

(** Total deterministic comparison over ALL seven state fields. *)
let state_compare s1 s2 =
  let c = stage_compare s1.stage s2.stage in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = payload_compare s1.payload s2.payload in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = authorship_compare s1.author s2.author in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = relayer_map_compare s1.rmap s2.rmap in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = deviation_compare s1.rdev s2.rdev in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = charge_compare s1.charge s2.charge in
            if Bool.not (Int.equal c5 0) then c5 else rep_compare s1.arep s2.arep

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** What V0 observes of the author: exactly its two LOCAL lookups - the
    per-topic [authorized_publishers] membership (consensus.rs:1502-1508) and
    the previous/current/next committee membership used by [exemption]
    (all_peers.rs:847-873). It deliberately MERGES {!Auth_stale_honest} with
    {!Auth_stale_byz}: those two differ only in the remote author's intent,
    which no local lookup reveals. *)
type author_class =
  | Cls_authorized  (** in V0's [authorized_publishers] for the topic *)
  | Cls_denied_committee
      (** denied by [authorized_publishers], yet in a tracked committee slot *)
  | Cls_denied_outsider  (** denied and in no tracked slot *)

(** Total order index for {!author_class}. *)
let author_class_index = function
  | Cls_authorized -> 0
  | Cls_denied_committee -> 1
  | Cls_denied_outsider -> 2

(** Total order on {!author_class}. *)
let author_class_compare a b =
  Int.compare (author_class_index a) (author_class_index b)

(** The observable author class of an {!authorship}: the merge of the honest
    and Byzantine stale authors is the model's single intent-hiding step. *)
let author_class_of = function
  | Auth_current -> Cls_authorized
  | Auth_stale_honest | Auth_stale_byz -> Cls_denied_committee
  | Auth_rogue -> Cls_denied_outsider

(** A validator's local view. [View_v0] is the receiving node's projection -
    its own pipeline stage, the byte-length class it measured, the author class
    its two local maps yield, the penalty target it itself selected, and the
    author's reputation in its own peer record. Everything in it is V0-local,
    which is what keeps the model honest. [View_idle] is the constant blank
    view of the non-agents V1, V2, V3. *)
type view =
  | View_v0 of stage * payload * author_class * charge * rep
  | View_idle

(** Total deterministic order over ALL five fields of V0's view. *)
let view_v0_compare (sa, pa, ca, ga, ra) (sb, pb, cb, gb, rb) =
  let c = stage_compare sa sb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = payload_compare pa pb in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = author_class_compare ca cb in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = charge_compare ga gb in
        if Bool.not (Int.equal c3 0) then c3 else rep_compare ra rb

(** Total order on views: [View_idle] < [View_v0], with the field-wise order
    within the agent constructor. Every constructor pair is spelled: no
    wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_v0 _ -> -1
  | View_v0 _, View_idle -> 1
  | View_v0 (sa, pa, ca, ga, ra), View_v0 (sb, pb, cb, gb, rb) ->
      view_v0_compare (sa, pa, ca, ga, ra) (sb, pb, cb, gb, rb)

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 is the SOLE knowledge agent (the receiving node); V1,
    V2 and V3 are idle non-agents with the constant blank view and never appear
    under K. The relayer R and the author A are phantom peers, not
    {!Validator.t} at all. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_v0 (s.stage, s.payload, author_class_of s.author, s.charge, s.arep)
  | Validator.V1
  | Validator.V2
  | Validator.V3
  | Validator.V4
  | Validator.V5
  | Validator.V6
  | Validator.V7
  | Validator.V8
  | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_receive_size_gate
      (** delete the receive-side size check at the head of [verify_gossip]
          (consensus.rs:1491-1497, the [if gossip.data.len() >
          MAX_GOSSIP_MESSAGE_SIZE { return
          GossipAcceptance::Reject(RejectReason::TooLarge); }]). The deletion
          is in the SHARED binary, so it is gone at the relaying peer too -
          which is exactly the point: the [FatalRelayer] attribution at
          consensus.rs:2092 is sound ONLY because every honest node runs this
          same check. Effect: an honest node no longer Rejects an oversized
          payload, so it Accepts it, and [Accept] is the only
          [report_message_validation_result] arm that forwards - so
          [deviation_of] at ([Oversized], [Map_permits]) flips from
          [Dev_relay] to [Dev_none]; and [verdict_of] falls through from
          [Too_large] to the publisher check, so an oversized delivery from a
          denied author now charges the AUTHOR. SIBLING HUNT: (1) libp2p's own
          [max_transmit_size] defaults to 65536 and TN's [ConfigBuilder] never
          sets it (consensus.rs:342-362; a repo-wide search for
          [max_transmit_size] has no hits), so the 12_001..65_535 band this
          model's [Oversized] denotes is completely unguarded; (2) the
          origination guard at consensus.rs:782-798 stops honest PUBLISHING
          but never runs on the forward path, so it cannot repair a relayer
          that is not the originator; (3) [TNCodec]'s [max_rpc_message_size]
          (consensus.rs:364-365) governs request/response only. No repair. *)
  | No_reject_attribution_split
      (** delete the two [RejectReason::UnauthorizedAuthor] arms of
          [RejectReason::penalty] (consensus.rs:2094-2095), so every reject
          falls through to the relayer branch. Effect: [charge_of] returns
          [Charge_relayer] instead of [Charge_author] for every
          [Unauthorized_author] verdict, so the forwarder IS made the penalty
          target. SIBLING HUNT: (1) gossipsub-internal peer scoring is not
          configured at all - a repo-wide search for [with_peer_score],
          [PeerScoreParams], [PeerScoreThresholds] and [gossip_threshold] has
          no hits - so reporting [MessageAcceptance::Reject] applies no
          internal penalty of its own, it only drops the message from the
          mcache; (2) rejects never reach the application layer, since only
          the [Accept] arm calls [event_stream.try_send]
          (consensus.rs:1039-1047), so the consumer cannot re-charge or
          un-charge; (3) the committee exemption (peer.rs:218-233) suppresses
          the score EFFECT for an exempt relayer but not the charge itself,
          and this family's atom is the [RejectPenalty] target - the
          [process_penalty] call at consensus.rs:1070-1073 - chosen precisely
          so that sibling cannot silently repair the deletion; (4) [SlowPeer]
          and [GossipsubNotSupported] (consensus.rs:1109-1116) fire on
          different events. No repair. *)
  | No_committee_exemption
      (** delete the [TrustBasis] bypass inside [Peer::apply_penalty]
          (peer.rs:209-237, the [if let Some(basis) = exemption { warn } else {
          self.score.apply_penalty(penalty) }] at :218-233), reached from
          [AllPeers::process_penalty] at all_peers.rs:262-266. Effect: the
          [Fatal] lands on every peer regardless of [TrustBasis], so
          [arep_of] drives every [Charge_author] to [Rep_banned] - including
          the stale-but-tracked committee authors, whose [Settled] state then
          satisfies [Author_in_committee] and [Author_banned] together.
          SIBLING HUNT: (1) [apply_committee_membership] (all_peers.rs:1180-1239)
          unbans the member and calls [reset_score_to_max] on every
          [update_committees] (all_peers.rs:1102-1122) and lazily on discovery
          via [apply_membership_if_committee] - this IS a real sibling, so it
          is MODELLED as the mandatory {!Rotated} step and is left LIVE under
          every mutation; it repairs only AFTER the ban, which is why the
          safety statement is phrased as "never both at once" rather than as
          eventual recovery, and the [Settled] state still flips; (2)
          [prepare_committee_dial] / [forgive_temporarily_banned] touch only
          the temporarily-banned excess-connection cache, never [Score] - same
          later-repair shape, folded into the same {!Rotated} step; (3)
          heartbeat score decay (score.rs:123-136) is likewise a later repair,
          is itself skipped for exempt peers, and banned peers are locked out
          for [banned_before_decay] (score.rs:149-154); (4)
          [process_penalty]'s [NoAction] early return (all_peers.rs:269-271)
          does not fire, since Trusted -> Banned is a reputation CHANGE. No
          path prevents the ban. *)

(** Whether the relaying peer itself broke protocol, given the payload class
    and the relayer's own publisher verdict. [Map_forbids] is a deviation under
    any mutation: forwarding a message your own map denies means your own
    [verify_gossip] Rejected it, and only [Accept] forwards
    (consensus.rs:1499-1513 run on the relayer's copy). On [Map_permits] an
    oversized payload is a deviation only while the shared binary still carries
    the receive-side size gate. Every mutation constructor is spelled. *)
let deviation_of mut payload rmap =
  match rmap with
  | Map_forbids -> Dev_relay
  | Map_permits -> (
      match (payload, mut) with
      | Oversized, Pristine -> Dev_relay
      | Oversized, No_reject_attribution_split -> Dev_relay
      | Oversized, No_committee_exemption -> Dev_relay
      | Oversized, No_receive_size_gate -> Dev_none
      | Within, Pristine -> Dev_none
      | Within, No_receive_size_gate -> Dev_none
      | Within, No_reject_attribution_split -> Dev_none
      | Within, No_committee_exemption -> Dev_none)

(** The outcome of V0's [verify_gossip] (consensus.rs:1491-1514). *)
type verdict =
  | Accept_msg  (** [GossipAcceptance::Accept] (consensus.rs:1510) *)
  | Too_large
      (** [GossipAcceptance::Reject(RejectReason::TooLarge)]
          (consensus.rs:1496) *)
  | Unauthorized_author
      (** [GossipAcceptance::Reject(RejectReason::UnauthorizedAuthor)]
          (consensus.rs:1512) *)

(** The publisher check alone (consensus.rs:1499-1513), run against V0's OWN
    per-topic [authorized_publishers] map. *)
let authz_verdict_of author =
  match author with
  | Auth_current -> Accept_msg
  | Auth_stale_honest | Auth_stale_byz | Auth_rogue -> Unauthorized_author

(** V0's [verify_gossip] verdict: the size gate first, then the publisher
    check. Under {!No_receive_size_gate} the size gate is gone and an oversized
    payload falls through to the publisher check. Every mutation constructor is
    spelled. *)
let verdict_of mut s =
  match (s.payload, mut) with
  | Oversized, Pristine -> Too_large
  | Oversized, No_reject_attribution_split -> Too_large
  | Oversized, No_committee_exemption -> Too_large
  | Oversized, No_receive_size_gate -> authz_verdict_of s.author
  | Within, Pristine -> authz_verdict_of s.author
  | Within, No_receive_size_gate -> authz_verdict_of s.author
  | Within, No_reject_attribution_split -> authz_verdict_of s.author
  | Within, No_committee_exemption -> authz_verdict_of s.author

(** Which peer the reject path charges ([RejectReason::penalty],
    consensus.rs:2090-2097, with both identities resolved). Under
    {!No_reject_attribution_split} the two [UnauthorizedAuthor] arms are gone
    and every reject falls through to [FatalRelayer]. Every mutation
    constructor is spelled. *)
let charge_of mut s =
  match verdict_of mut s with
  | Accept_msg -> Charge_none
  | Too_large -> Charge_relayer
  | Unauthorized_author -> (
      match mut with
      | Pristine -> Charge_author
      | No_receive_size_gate -> Charge_author
      | No_committee_exemption -> Charge_author
      | No_reject_attribution_split -> Charge_relayer)

(** Whether the author bypasses the score model - [exemption] returning
    [Some TrustBasis::Validator] for a [Confirmed] key in a tracked slot
    (all_peers.rs:847-873), honoured by the bypass at peer.rs:218-233. Under
    {!No_committee_exemption} the bypass is deleted, so nobody is exempt. Every
    mutation constructor is spelled. *)
let exempt_of mut author =
  match mut with
  | Pristine -> author_in_committee author
  | No_receive_size_gate -> author_in_committee author
  | No_reject_attribution_split -> author_in_committee author
  | No_committee_exemption -> false

(** The author's reputation after the charge lands. Only a [Charge_author] can
    touch the author's score, and a non-exempt [Penalty::Fatal] sets it to
    [min_score] (score.rs:93), which is at or below [min_score_before_ban], so
    [reputation_for] returns [Banned] (score.rs:158-161, :183). *)
let arep_of mut s =
  match charge_of mut s with
  | Charge_none -> Rep_trusted
  | Charge_relayer -> Rep_trusted
  | Charge_author ->
      if exempt_of mut s.author then Rep_trusted else Rep_banned

(** The committee rotation repair: [apply_committee_membership] forgives the
    ban and calls [reset_score_to_max] for every tracked member
    (all_peers.rs:1191-1239, driven from :1102-1122). MUTATION-INDEPENDENT ON
    PURPOSE - this is the R4 sibling path and it stays live under every
    mutation, so no statement is true merely because the model omits it. *)
let rotate_of s = if author_in_committee s.author then Rep_trusted else s.arep

(** The 16 possible deliveries out of {!Quiet}: two payload classes x four
    author standings x two hidden relayer maps, each carrying the derived
    hidden deviation flag, no charge yet and an untouched author reputation. *)
let inbound_states mut =
  List.concat_map
    (fun payload ->
      List.concat_map
        (fun author ->
          List.map
            (fun rmap ->
              {
                stage = Inbound;
                payload;
                author;
                rmap;
                rdev = deviation_of mut payload rmap;
                charge = Charge_none;
                arep = Rep_trusted;
              })
            [ Map_permits; Map_forbids ])
        [ Auth_current; Auth_stale_honest; Auth_stale_byz; Auth_rogue ])
    [ Within; Oversized ]

(** The transition relation: {!Quiet} branches once into the 16 deliveries,
    then the pipeline is deterministic - {!Inbound} applies
    [RejectReason::penalty] and the peer manager's response, {!Settled} applies
    the next [update_committees], and {!Rotated} is terminal (the kernel
    stutter-closes it). *)
let next_with mut s =
  match s.stage with
  | Quiet -> inbound_states mut
  | Inbound ->
      [ { s with stage = Settled; charge = charge_of mut s; arep = arep_of mut s } ]
  | Settled -> [ { s with stage = Rotated; arep = rotate_of s } ]
  | Rotated -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: no gossip in flight, canonical scenario fields, so
    [Payload_over] and [Authz_denied] are FALSE at {!Quiet} and every operative
    antecedent is genuinely stage-gated rather than holding at the root. *)
let initial =
  {
    stage = Quiet;
    payload = Within;
    author = Auth_current;
    rmap = Map_permits;
    rdev = Dev_none;
    charge = Charge_none;
    arep = Rep_trusted;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Msg_inbound
      (** stage <> Quiet: V0 has taken delivery of the gossip message from the
          relaying peer (consensus.rs:989-1002) *)
  | Payload_over
      (** payload = Oversized: [gossip.data.len() > MAX_GOSSIP_MESSAGE_SIZE]
          (consensus.rs:1495, config/network.rs:112) *)
  | Authz_denied
      (** author <> Auth_current: the source is not an authorized publisher for
          the topic in V0's OWN map (consensus.rs:1502-1512) *)
  | Relayer_deviated
      (** rdev = Dev_relay: the relaying peer itself broke protocol in
          delivering this message. HIDDEN - never in any view *)
  | Relayer_map_forbids
      (** rmap = Map_forbids: the relaying peer's own
          [authorized_publishers] denies this author. HIDDEN - never in any
          view *)
  | Charged_relayer
      (** charge = Charge_relayer: [RejectPenalty::FatalRelayer] taken, i.e.
          [process_penalty(propagation_source, Fatal)]
          (consensus.rs:1064-1074) *)
  | Charged_author
      (** charge = Charge_author: [RejectPenalty::FatalAuthor] taken, i.e.
          [process_penalty(author_id, Fatal)] (consensus.rs:1075-1088) *)
  | Author_in_committee
      (** author holds a [Confirmed] key in a tracked previous/current/next
          slot (all_peers.rs:836-845, :860-868) *)
  | Author_deviates
      (** the author really did publish outside its authorization. Merged with
          its honest sibling inside [Cls_denied_committee], so PARTLY HIDDEN *)
  | Author_banned
      (** arep = Rep_banned: the score model actually banned the author
          (score.rs:158-161, :181-187) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Msg_inbound -> stage_is_delivered s.stage
  | Payload_over -> payload_is_over s.payload
  | Authz_denied -> author_is_denied s.author
  | Relayer_deviated -> deviation_is_relay s.rdev
  | Relayer_map_forbids -> relayer_map_is_forbid s.rmap
  | Charged_relayer -> charge_is_relayer s.charge
  | Charged_author -> charge_is_author s.charge
  | Author_in_committee -> author_in_committee s.author
  | Author_deviates -> author_deviates s.author
  | Author_banned -> rep_is_banned s.arep

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Msg_inbound -> "inbound(msg)"
  | Payload_over -> "oversized(msg)"
  | Authz_denied -> "unauthorized_author(msg)"
  | Relayer_deviated -> "deviated(R)"
  | Relayer_map_forbids -> "relayer_map_forbids(A)"
  | Charged_relayer -> "charged(R)"
  | Charged_author -> "charged(A)"
  | Author_in_committee -> "committee(A)"
  | Author_deviates -> "deviates(A)"
  | Author_banned -> "banned(A)"

(** The exact CTLK checker over this family's ordered state and view. *)
module Checker = System.Make (State) (View)

(** The checker spec under a mutation: single initial state,
    mutation-parameterized transitions, the single-agent view, the atom
    valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
