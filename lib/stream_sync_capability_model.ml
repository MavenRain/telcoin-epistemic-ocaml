(** Finite interpreted system for the STREAM_SYNC_CAPABILITY family: the
    per-peer epoch-pack sync-capability cache of [PrimaryNetworkHandle], the
    outbound stream-upgrade classification that feeds it, and the epoch-boundary
    clear that empties it. File citations refer to
    Telcoin-Association/telcoin-network at git HEAD [0c59c15b]; every line range
    below was opened in that checkout's working tree.

    THE MODELLED MECHANISM. A primary keeps
    [sync_capability : Arc<Mutex<HashMap<BlsPublicKey, bool>>>] on its network
    handle (mod.rs:365-381). Its documented meaning is at mod.rs:371-379: absent
    = not yet probed, [false] = "the peer did not answer a sync open (a
    pre-cutover peer that fails negotiation, OR one that negotiated but never
    [Ack]ed), so it is skipped on later probes this epoch", [true] = the peer
    served or is serving. Three things decide what lands in it.

    - THE OUTBOUND UPGRADE CLASSIFICATION. [classify_outbound]
      (network-libp2p/src/stream/handler.rs:142-152) splits the swarm's
      [StreamUpgradeError] three ways: [NegotiationFailed] becomes
      [StreamError::UpgradeFailed] (:145-147), [Io(e)] becomes
      [StreamError::UpgradeIo] (:148), [Timeout] becomes [StreamError::Timeout]
      (:144). The public error type states why the split exists
      (stream/upgrade.rs:82-89): [UpgradeIo] is "Distinct from
      [StreamError::UpgradeFailed]: the peer may well speak the protocol, so a
      caller probing protocol support should treat this as transient rather than
      as 'unsupported'". The outbound open advertises exactly ONE protocol
      (handler.rs:244-250, [TNStreamProtocol::new(vec![self.protocol_for(
      open.kind)], self.sync.clone())]), which is what makes a
      [NegotiationFailed] on a sync open unambiguous.
    - THE CONSUMER THAT TURNS AN ERROR INTO A CACHE WRITE.
      [try_sync_epoch_pack_exchange] maps ONLY [UpgradeFailed] to
      [EpochPackAttempt::Unsupported] and every other open error to
      [EpochPackAttempt::Failed] (mod.rs:1173-1181). Two FURTHER routes reach
      [Unsupported] after a SUCCESSFUL negotiation: the [SYNC_ACK_TIMEOUT]
      elapsing on the first frame (mod.rs:1210-1220) and a read error whose kind
      is [UnexpectedEof | ConnectionReset | BrokenPipe] (mod.rs:1221-1228).
      [request_epoch_pack_sync] then writes: [Imported] -> [insert(peer, true)]
      (mod.rs:1073-1074), [Failed] -> [insert(peer, true)] (mod.rs:1102-1105,
      "the peer speaks sync but this exchange failed; keep it sync-capable"),
      and [Unsupported] -> [insert(peer, false)] ONLY behind the guard
      [if last_consensus_number.is_none()] (mod.rs:1091-1093), whose comment
      states the ambiguity verbatim: "Only a FULL-pack [Unsupported]
      authoritatively proves the peer does not speak [/tn-primary-sync]. A
      PARTIAL [Unsupported] is ambiguous: the peer may be on an earlier item
      that serves full packs but cannot decode the newer [EpochPackPartial]
      variant, so it must not cache [false] and hide that peer from full-pack
      sync." The two request variants are
      network-libp2p/src/sync/request.rs:43-46 ([EpochPack]) and :67-72
      ([EpochPackPartial]); the caller selects between them on the [Option] at
      mod.rs:1188-1192.
    - THE ELIGIBILITY FILTER AND THE EPOCH CLEAR. Both sync probe loops drop a
      peer cached [false] BEFORE any probe is attempted - mod.rs:1066-1069 in
      the epoch-pack path and mod.rs:626-629 in the consensus-output path - and
      each takes at most [MAX_EPOCH_SYNC_PROBES = 3] peers (mod.rs:148, :630,
      :1070). The only route back to eligibility is
      [PrimaryNetworkHandle::clear_sync_capability] (mod.rs:409-416), called at
      exactly one site, [network_handle.clear_sync_capability();]
      (node/src/manager/node/start_epoch.rs:547-550).

    THE THIRD [Unsupported] ROUTE IS MODELLED ON PURPOSE, AND IT IS WHY THE
    KNOWLEDGE CLAIM IS SHAPED AS IT IS. The [Io] / [NegotiationFailed] split
    exists at the OPEN but is NOT applied at the READ. mod.rs:1221-1228 maps
    [UnexpectedEof | ConnectionReset | BrokenPipe] to [Unsupported] - a
    peer-attributable verdict that caches [false] - while the very same three
    kinds are classified as not the peer's fault by the stream layer's own
    penalty taxonomy, [StreamFailure::Io(kind)] -> [None] under the comment
    "transport flaps on WAN are not faults" (stream/upgrade.rs:149-156). So a
    connection that dies between a successful negotiation and the first frame
    caches [false] against a peer that answers full-pack opens perfectly well. A
    model that left that route out would make "a cached [false] means the peer
    does not answer" come out TRUE when the real code does not support it; this
    model carries it as {!Link_cut_after_open}, and S1's knowledge operand is
    the disjunction that survives it.

    COMPONENTS (four; the pristine reachable graph is exactly 34 states).
    - [cap] : the HIDDEN disposition of the one candidate peer [w] toward this
      epoch's sync opens. Four values, spelled at {!capability}. This is the
      operand of the family's knowledge claims and is never in the prober's
      view.
    - [entry] : [v]'s map slot for [w], carrying the PROVENANCE of a negative
      verdict - which probe kind wrote it and which of the three [Unsupported]
      routes produced it - so S1 and S2 can talk about it. The real map holds
      only a [bool] (mod.rs:380), which is exactly why [v]'s view collapses
      every negative variant to one answer.
    - [recent] : the classification of [v]'s most recent probe, at the
      [EpochPackAttempt] granularity the code itself branches on
      (mod.rs:1072-1115). Only "a PARTIAL request came back [Unsupported]" is
      distinguished, because that is the one case the guard at :1091 turns on.
    - [probes] : how many sync opens [v] has spent on [w] this epoch, capped at
      {!max_probes} = 2. This is the model's shrunk stand-in for
      [MAX_EPOCH_SYNC_PROBES = 3] (mod.rs:148, whose doc at :141-145 confirms it
      counts stream opens, not peers examined); two is the smallest budget that
      still lets a peer left eligible by an ambiguous partial verdict be probed
      AGAIN inside the same epoch, which is the whole point of the :1091 guard.

    ROLE MAPPING.
    - V0 is [v], THE PROBER, and is a knowledge agent. Its view is
      [(cache answer, recent, probes)]: the map slot as the code stores it - a
      bare three-way answer with NO provenance, because
      [HashMap<BlsPublicKey, bool>] has none (mod.rs:380) - plus the
      classification of its last probe and its own probe bookkeeping. It does
      NOT see [cap] and it does NOT see which route produced a negative verdict.
      Those exclusions are the substance of the family: the transient
      [EpochPackAttempt] is consumed inside the probe closure
      (mod.rs:1071-1116), the [debug!] at :1094-1099 is a log line rather than
      state, and only the [bool] survives into the map.
    - V1 is [w], THE CANDIDATE PEER, and is a knowledge agent. Its view is
      [(cap, probes)]: its own disposition and how many inbound sync opens it
      has been offered - deliberately generous, since [w]'s swarm does see
      inbound opens. It does NOT see [entry]: the capability map is a private
      field of [v]'s handle (mod.rs:380), never serialized into any frame
      ([PrimarySyncRequest], request.rs:38-84) and never reported back, and the
      sync probe is penalty-exempt on the [UnsupportedProtocol] branch
      (handler.rs:211-220), so not even [w]'s peer score carries the verdict.
    - V2..V9 are idle: constant blank view, never under K.

    WHY [Pre_cutover] AND [Negotiates_mute] ARE BOTH PRESENT. The code collapses
    them on purpose: a [NegotiationFailed] open (mod.rs:1176-1178) and an [Ack]
    timeout (mod.rs:1220) both produce the SAME [EpochPackAttempt::Unsupported]
    value, both are penalty-exempt or produce no [StreamFailure] at all, and
    both write the SAME [false]. Nothing downstream of :1091 can tell them
    apart. They differ on a hidden fact - whether [w] advertises
    [/tn-primary-sync] at all - and S1 conjunct B is precisely the statement
    that a cached [false] does NOT license that stronger reading. Modelling only
    one of them would have made S1 conjunct A say something the real code does
    not support.

    DELIBERATE SCOPE NOTES, stated so they are not mistaken for omissions.
    (i) The consensus-output path (mod.rs:617-670) is a third probe route. It
    filters on [Some(false)] identically (:626-629) and writes [true] on
    [Fetched] (:634) and on [Failed] (:658) but NEVER writes [false] - its
    [Unsupported] arm is a bare [debug!] (:643-653). It can therefore neither
    poison the map nor repair a poisoned entry, so it is carried in the prose of
    the sibling hunts rather than as a third probe kind; adding it would enlarge
    the state space without changing a single verdict.
    (ii) There is no epoch COUNTER component. The boundary
    (start_epoch.rs:547-550) returns [v]'s per-epoch state to its cleared start,
    and no statement quantifies over which epoch it is in, so numbering epochs
    would double the state space for no content. The boundary transition is
    still present and is what S3 is about.
    (iii) [cap] is held fixed across the boundary even though a binary upgrade
    there is the documented reason for the clear (start_epoch.rs:547-549). That
    is the HARDER case for S3: the peer that is still incapable is re-probed
    anyway. Letting [cap] improve at the boundary could only make the fairness
    claim easier.
    (iv) The epoch boundary is modelled as always enabled, i.e. epochs are
    assumed to end. S3's [AF] is therefore a claim about what the boundary DOES,
    not about whether it arrives; the mutation that pins it deletes the clear,
    not the boundary. *)

(** The hidden disposition of the candidate peer [w] toward a sync open this
    epoch. The classification is operational - it is exactly what the exchange
    at mod.rs:1154-1288 can distinguish - not a claim about [w]'s source code. *)
type capability =
  | Pre_cutover
      (** [w] does not advertise [/tn-primary-sync]: the single-protocol
          outbound upgrade (handler.rs:244-250) fails multistream-select, the
          swarm reports [NegotiationFailed], [classify_outbound] returns
          [StreamError::UpgradeFailed] (handler.rs:145-147) and the consumer
          maps it to [EpochPackAttempt::Unsupported] (mod.rs:1176-1178). *)
  | Negotiates_mute
      (** [w] DOES advertise the protocol - negotiation succeeds - but it never
          puts an opening frame on the wire within [SYNC_ACK_TIMEOUT]
          (mod.rs:1210-1220). Downstream of :1091 this is indistinguishable from
          {!Pre_cutover}: same attempt value, same cache write, same peer
          score. *)
  | Full_only
      (** [w] answers a FULL-pack open ([PrimarySyncRequest::EpochPack],
          request.rs:43-46) but is on an earlier item that cannot decode the
          newer [EpochPackPartial] variant (request.rs:67-72), so a partial open
          gets no [Ack] and comes back [Unsupported]. This is exactly the
          population the guard at mod.rs:1091 is written for. *)
  | Full_and_partial
      (** [w] answers both request variants: a probe of either kind reaches
          [EpochPackAttempt::Imported] (mod.rs:1073) absent a transport
          fault. *)

(** Total order index for {!capability}. *)
let capability_index = function
  | Pre_cutover -> 0
  | Negotiates_mute -> 1
  | Full_only -> 2
  | Full_and_partial -> 3

(** Total order on {!capability}. *)
let capability_compare a b =
  Int.compare (capability_index a) (capability_index b)

(** Does [w] advertise the sync protocol, i.e. would the single-protocol
    outbound upgrade negotiate (handler.rs:244-250)? Everything except
    {!Pre_cutover} does; this is what decides whether the exchange can even
    reach the read stage that {!Link_cut_after_open} models. *)
let advertises = function
  | Pre_cutover -> false
  | Negotiates_mute | Full_only | Full_and_partial -> true

(** Which request variant [v] put in the opening frame (mod.rs:1188-1192). *)
type probe_kind =
  | Full_probe
      (** [last_consensus_number = None] -> [PrimarySyncRequest::EpochPack]
          (mod.rs:1189, request.rs:43-46). This is the only kind the guard at
          mod.rs:1091 lets write a negative entry. *)
  | Partial_probe
      (** [last_consensus_number = Some(n)] ->
          [PrimarySyncRequest::EpochPackPartial] (mod.rs:1190,
          request.rs:67-72). Its [Unsupported] is ambiguous, so it must not
          cache [false]. *)

(** What the transport did under this open, an environment choice independent of
    {!capability}. *)
type transport =
  | Link_ok  (** no transport fault: the outcome is [w]'s to decide *)
  | Link_open_fault
      (** a transport I/O fault AT THE OPEN, before negotiation completes. The
          swarm reports [StreamUpgradeError::Io], [classify_outbound] returns
          [StreamError::UpgradeIo] (handler.rs:148) and the consumer's catch-all
          arm makes it [EpochPackAttempt::Failed] (mod.rs:1179), which caches
          [true] (:1105). The other non-negotiation open errors ([Timeout] at
          handler.rs:144, [NotConnected], [TooManyPending]) take the same
          catch-all arm and are folded into this branch. *)
  | Link_cut_after_open
      (** the connection dies AFTER a successful negotiation and before the
          first frame arrives. [read_frame] yields an I/O error whose kind is
          [ConnectionReset] or [BrokenPipe] (or [UnexpectedEof] on a clean
          teardown), and mod.rs:1221-1228 classifies exactly those three kinds
          as [EpochPackAttempt::Unsupported] - a peer-attributable verdict -
          even though the stream layer's own taxonomy scores those same kinds as
          not the peer's fault ("transport flaps on WAN are not faults",
          stream/upgrade.rs:149-156). Enabled only when {!advertises} holds,
          since the exchange has to negotiate to reach the read at all. *)

(** Why an exchange came back [EpochPackAttempt::Unsupported]. The prober never
    sees this: the three routes produce one and the same attempt value. *)
type unsupported_cause =
  | Peer_did_not_answer
      (** negotiation failed (mod.rs:1176-1178) or the [Ack] timed out
          (mod.rs:1220) - the peer's own doing *)
  | Post_negotiation_cut
      (** the read after a successful negotiation hit
          [UnexpectedEof | ConnectionReset | BrokenPipe] (mod.rs:1221-1228) *)
  | Pre_negotiation_fault
      (** a transport fault at the open reached the consumer as [UpgradeFailed].
          UNREACHABLE on the pristine model - the [Io] arm at handler.rs:148
          keeps it [UpgradeIo] - and reachable exactly under
          {!No_io_classification_split}. *)

(** Total order index for {!unsupported_cause}. *)
let unsupported_cause_index = function
  | Peer_did_not_answer -> 0
  | Post_negotiation_cut -> 1
  | Pre_negotiation_fault -> 2

(** The flattened per-exchange outcome the cache writer branches on
    (mod.rs:1072-1115). *)
type attempt =
  | Imported  (** the pack streamed and imported (mod.rs:1073) *)
  | Unsupported of unsupported_cause
      (** [w] did not answer the open (mod.rs:1083), by one of three routes *)
  | Failed
      (** the exchange failed for a reason that is not proof of absence
          (mod.rs:1102) *)

(** [v]'s map slot for [w], with the provenance of a negative verdict attached.
    The real map is [HashMap<BlsPublicKey, bool>] (mod.rs:380) and carries NO
    provenance; it is tracked here only so the statements can talk about which
    probe and which route wrote a [false], and {!cache_answer_of} strips it back
    out for [v]'s view. *)
type entry =
  | Entry_absent  (** not yet probed this epoch (mod.rs:373) *)
  | Entry_capable  (** [insert(peer, true)] (mod.rs:1074 or :1105) *)
  | Entry_unsyncable_peer
      (** [insert(peer, false)] from a FULL probe whose [Unsupported] was the
          peer's own doing (mod.rs:1176-1178 or :1220) *)
  | Entry_unsyncable_link_cut
      (** [insert(peer, false)] from a FULL probe cut by the transport after
          negotiation (mod.rs:1221-1228). Reachable on the PRISTINE model: this
          is the leak scope note in the header. *)
  | Entry_unsyncable_open_fault
      (** [insert(peer, false)] from a FULL probe whose transport fault at the
          open was misclassified as a negotiation failure. UNREACHABLE on the
          pristine model and reachable exactly under
          {!No_io_classification_split}. *)
  | Entry_unsyncable_by_partial
      (** [insert(peer, false)] written by a PARTIAL-pack probe. UNREACHABLE on
          the pristine model - the guard at mod.rs:1091 forbids it - and
          reachable exactly under {!No_partial_probe_guard}. *)

(** Total order index for {!entry}. *)
let entry_index = function
  | Entry_absent -> 0
  | Entry_capable -> 1
  | Entry_unsyncable_peer -> 2
  | Entry_unsyncable_link_cut -> 3
  | Entry_unsyncable_open_fault -> 4
  | Entry_unsyncable_by_partial -> 5

(** Total order on {!entry}. *)
let entry_compare a b = Int.compare (entry_index a) (entry_index b)

(** What [v] can read back out of the map: a three-way answer with no
    provenance, exactly [HashMap::get] on a [bool] map (mod.rs:1067). *)
type cache_answer =
  | Answer_absent  (** [get(peer) == None] *)
  | Answer_capable  (** [get(peer) == Some(&true)] *)
  | Answer_unsyncable  (** [get(peer) == Some(&false)] - what :1067 filters on *)

(** Total order index for {!cache_answer}. *)
let cache_answer_index = function
  | Answer_absent -> 0
  | Answer_capable -> 1
  | Answer_unsyncable -> 2

(** Total order on {!cache_answer}. *)
let cache_answer_compare a b =
  Int.compare (cache_answer_index a) (cache_answer_index b)

(** The map read [v] actually gets: all four negative variants collapse to one
    answer, because the stored value is a [bool] (mod.rs:380). *)
let cache_answer_of = function
  | Entry_absent -> Answer_absent
  | Entry_capable -> Answer_capable
  | Entry_unsyncable_peer | Entry_unsyncable_link_cut
  | Entry_unsyncable_open_fault | Entry_unsyncable_by_partial ->
      Answer_unsyncable

(** The classification of [v]'s most recent probe, at the [EpochPackAttempt]
    granularity of mod.rs:1072-1115. *)
type recent =
  | Recent_none  (** no probe yet this epoch *)
  | Recent_partial_verdict
      (** the last probe sent [EpochPackPartial] and came back [Unsupported] -
          the ambiguous case the guard at mod.rs:1091 refuses to cache *)
  | Recent_other  (** any other last-probe outcome *)

(** Total order index for {!recent}. *)
let recent_index = function
  | Recent_none -> 0
  | Recent_partial_verdict -> 1
  | Recent_other -> 2

(** Total order on {!recent}. *)
let recent_compare a b = Int.compare (recent_index a) (recent_index b)

(** The probe budget per epoch: the model's shrunk [MAX_EPOCH_SYNC_PROBES]
    (mod.rs:148, applied at :630 and :1070). Two is the smallest budget under
    which a peer left eligible by an ambiguous partial verdict can still be
    probed again inside the same epoch. *)
let max_probes = 2

(** The joint global state: [w]'s hidden disposition, [v]'s map slot for it, the
    classification of [v]'s last probe, and [v]'s probe budget spend this
    epoch. *)
type state = {
  cap : capability;
      (** [w]'s hidden disposition toward a sync open; never in [v]'s view *)
  entry : entry;  (** [v]'s [sync_capability] slot for [w] (mod.rs:380) *)
  recent : recent;  (** the classification of [v]'s last probe this epoch *)
  probes : int;  (** sync opens spent on [w] this epoch, in [0, {!max_probes}] *)
}

(** Total deterministic comparison over ALL state fields, in field order
    [cap, entry, recent, probes]. *)
let state_compare s1 s2 =
  let c0 = capability_compare s1.cap s2.cap in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = entry_compare s1.entry s2.entry in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = recent_compare s1.recent s2.recent in
      if Bool.not (Int.equal c2 0) then c2 else Int.compare s1.probes s2.probes

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view; see the header for the full role mapping and the
    grounding of every exclusion.

    [View_prober] is V0, the probing primary: [(cache answer, recent, probes)].
    The cache answer carries NO provenance because the stored value is a [bool]
    (mod.rs:380), and [cap] is absent because nothing in [v]'s persistent state
    records it - the [EpochPackAttempt] dies inside the probe closure
    (mod.rs:1071-1116).

    [View_peer] is V1, the candidate peer: [(cap, probes)]. It knows its own
    disposition and can count inbound sync opens, but the capability map is a
    private field of [v]'s handle and is never on the wire.

    [View_idle] is the constant blank view of the non-agents V2..V9. *)
type view =
  | View_prober of cache_answer * recent * int
      (** V0: (map answer, last-probe classification, probes spent) *)
  | View_peer of capability * int
      (** V1: (own disposition, inbound sync opens offered) *)
  | View_idle  (** the constant blank view of the non-agents V2..V9 *)

(** Total deterministic order over ALL fields of the prober's view. *)
let view_prober_compare (a, r, p) (a', r', p') =
  let c0 = cache_answer_compare a a' in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = recent_compare r r' in
    if Bool.not (Int.equal c1 0) then c1 else Int.compare p p'

(** Total deterministic order over ALL fields of the candidate peer's view. *)
let view_peer_compare (c, p) (c', p') =
  let c0 = capability_compare c c' in
  if Bool.not (Int.equal c0 0) then c0 else Int.compare p p'

(** Total order on views: [View_idle] < [View_prober] < [View_peer], with the
    field-wise order within each constructor. Every constructor pair is spelled:
    no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_prober _ | View_peer _) -> -1
  | (View_prober _ | View_peer _), View_idle -> 1
  | View_prober (x, r, p), View_prober (x', r', p') ->
      view_prober_compare (x, r, p) (x', r', p')
  | View_prober _, View_peer _ -> -1
  | View_peer _, View_prober _ -> 1
  | View_peer (c, p), View_peer (c', p') -> view_peer_compare (c, p) (c', p')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 (the prober) and V1 (the candidate peer) are the
    knowledge agents with real, non-constant views; V2..V9 are idle non-agents
    with the constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V0 -> View_prober (cache_answer_of s.entry, s.recent, s.probes)
  | Validator.V1 -> View_peer (s.cap, s.probes)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at HEAD [0c59c15b] *)
  | No_io_classification_split
      (** delete the distinct [Io] arm of [classify_outbound]
          (network-libp2p/src/stream/handler.rs:148), mapping
          [StreamUpgradeError::Io(e)] to
          [(StreamFailure::UnsupportedProtocol, StreamError::UpgradeFailed)]
          like the [NegotiationFailed] arm above it. A transport fault at the
          open then reaches the consumer as [UpgradeFailed], so mod.rs:1176-1178
          turns it into [EpochPackAttempt::Unsupported] and a FULL probe writes
          [false] (mod.rs:1092) against a peer that answers perfectly well. In
          the model this replaces the [Link_open_fault -> Failed] arm of
          {!classify} with [Link_open_fault -> Unsupported Pre_negotiation_fault].

          WHY NO SIBLING PATH REPAIRS IT. (a) The [Failed] arm's own
          [insert(peer, true)] (mod.rs:1102-1105) is the repair the pristine
          code uses, and it is exactly what this deletion disables - it is
          modelled, and the mutation removes it rather than the model omitting
          it. (b) A second probe inside the epoch cannot correct the entry: both
          probe loops drop [Some(false)] peers BEFORE probing (mod.rs:1066-1069
          and :626-629), so no later exchange runs against a poisoned peer. (c)
          The consensus-output path can neither poison nor correct: it filters
          identically (:626-629) and its [Unsupported] arm is a bare [debug!]
          with no write (:643-653). (d) There is no legacy [/tn-stream] fallback
          for these exchanges post-#739 - mod.rs:1053-1055 and :607-608 both say
          so. (e) The epoch clear (mod.rs:409-416, start_epoch.rs:547-550) IS a
          genuine repair, but only at the NEXT boundary; it is modelled, and S1
          is refuted at a state strictly before it. *)
  | No_partial_probe_guard
      (** delete the guard [if last_consensus_number.is_none()] at
          crates/consensus/primary/src/network/mod.rs:1091, so that EVERY
          [EpochPackAttempt::Unsupported] runs
          [self.sync_capability.lock().insert(peer, false);] (:1092). An
          ambiguous PARTIAL verdict then caches [false] against a peer that
          serves full packs and cannot decode [EpochPackPartial] only. In the
          model this replaces the [Partial_probe -> entry unchanged] arm of
          {!write_entry} with [Partial_probe -> Entry_unsyncable_by_partial].

          WHY NO SIBLING PATH REPAIRS IT. (a) The repair the guard preserves is
          a LATER FULL PROBE inside the same epoch, and the eligibility filter
          at mod.rs:1066-1069 destroys it: once [Some(false)] is in the map the
          peer is dropped before any probe. The model carries that later full
          probe explicitly ({!max_probes} = 2), so S2 conjunct C witnesses the
          repair on the pristine model and its disappearance under the
          mutation. (b) The consensus-output path filters on the same
          [Some(false)] (:626-629) and never writes [false] (:643-653), so it
          routes around nothing. (c) [MAX_EPOCH_SYNC_PROBES = 3] (mod.rs:148)
          bounds the fan-out - and its own doc at :141-145 confirms it counts
          stream OPENS, so a poisoned peer is skipped for free rather than
          making room for a better one. (d) The epoch clear repairs it only at
          the next boundary (mod.rs:409-416, start_epoch.rs:547-550) - and a
          node that needs an epoch pack needs it inside this epoch. *)
  | No_epoch_clear
      (** delete [network_handle.clear_sync_capability();]
          (crates/node/src/manager/node/start_epoch.rs:550). The boundary then
          resets [v]'s probe bookkeeping but leaves the map untouched, so a
          [false] survives every boundary and the peer is excluded from every
          sync path for the life of the process. In the model this replaces the
          [entry = Entry_absent] reset of {!t2_boundary} with
          [entry = s.entry].

          WHY NO SIBLING PATH REPAIRS IT. (a) There is no TTL and no eviction:
          the map has no timestamps and the ONLY writers in the tree are the
          [insert] sites (mod.rs:634, :658, :1074, :1092, :1105) and this clear
          - searching crates/ for [clear_sync_capability] returns exactly the
          definition (mod.rs:414), its doc reference (:378) and this one call
          site. (b) A fresh handle each epoch would reset the map incidentally
          and make the clear dead code; it does not happen.
          [PrimaryNetworkHandle::new] is called once, inside
          [spawn_node_networks] (node.rs:1117-1143), which [run] invokes once
          before the epoch loop (node.rs:877); every epoch then CLONES the
          stored handle (start_epoch.rs:326-330) and the map lives behind an
          [Arc] (mod.rs:380), so all clones share one map. (c) No path ignores
          the filter: both probe loops test [Some(&false)] identically
          (:626-629, :1066-1069). (d) There is no legacy fallback route that
          would serve the peer anyway (mod.rs:607-608, :1053-1055). *)

(** [enabled_list cond succs] is [succs] when the transition guard holds and the
    empty list otherwise. Every transition family below is one guard and one
    successor list, so no loop keyword and no mutable accumulator appears. *)
let enabled_list cond succs = if cond then succs else []

(** Is [w] still a probe candidate for [v] this epoch? The eligibility filter
    drops a peer whose map slot reads [Some(&false)] (mod.rs:1066-1069, and
    identically :626-629); an absent slot or a [true] leaves it eligible. *)
let eligible s =
  match s.entry with
  | Entry_absent | Entry_capable -> true
  | Entry_unsyncable_peer | Entry_unsyncable_link_cut
  | Entry_unsyncable_open_fault | Entry_unsyncable_by_partial ->
      false

(** Which transport outcomes an open against this peer can have. A cut after
    negotiation (mod.rs:1221-1228) presupposes that negotiation succeeded, so it
    is offered only against a peer that advertises the protocol. *)
let links_for cap =
  enabled_list true [ Link_ok; Link_open_fault ]
  @ enabled_list (advertises cap) [ Link_cut_after_open ]

(** What [w] itself does with an open of this kind when the transport holds up:
    the responder half of [try_sync_epoch_pack_exchange] (mod.rs:1154-1288). *)
let responder_verdict cap kind =
  match (cap, kind) with
  | Pre_cutover, (Full_probe | Partial_probe) -> Unsupported Peer_did_not_answer
  | Negotiates_mute, (Full_probe | Partial_probe) ->
      Unsupported Peer_did_not_answer
  | Full_only, Full_probe -> Imported
  | Full_only, Partial_probe -> Unsupported Peer_did_not_answer
  | Full_and_partial, (Full_probe | Partial_probe) -> Imported

(** The flattened [EpochPackAttempt] for one exchange. A transport fault at the
    open takes the catch-all arm at mod.rs:1179 and becomes [Failed] because
    [classify_outbound] gave it [UpgradeIo] rather than [UpgradeFailed]
    (handler.rs:148); under {!No_io_classification_split} that split is gone and
    the same fault becomes [Unsupported]. A cut AFTER negotiation is
    [Unsupported] under every mutation - no gate here touches mod.rs:1221-1228.
    Mutation-exhaustive, no wildcard arm. *)
let classify mut cap kind link =
  match link with
  | Link_open_fault -> (
      match mut with
      | Pristine | No_partial_probe_guard | No_epoch_clear -> Failed
      | No_io_classification_split -> Unsupported Pre_negotiation_fault)
  | Link_cut_after_open -> Unsupported Post_negotiation_cut
  | Link_ok -> responder_verdict cap kind

(** The negative slot a FULL probe writes, tagged with the route that produced
    it (mod.rs:1092). *)
let negative_entry_of_cause = function
  | Peer_did_not_answer -> Entry_unsyncable_peer
  | Post_negotiation_cut -> Entry_unsyncable_link_cut
  | Pre_negotiation_fault -> Entry_unsyncable_open_fault

(** The cache write this attempt performs (mod.rs:1073-1074, :1091-1093,
    :1102-1105). [Imported] and [Failed] both write [true]; [Unsupported] writes
    [false] only from a FULL probe, and a PARTIAL [Unsupported] leaves the slot
    alone unless {!No_partial_probe_guard} has deleted the guard.
    Mutation-exhaustive, no wildcard arm. *)
let write_entry mut current att kind =
  match att with
  | Imported -> Entry_capable
  | Failed -> Entry_capable
  | Unsupported cause -> (
      match kind with
      | Full_probe -> negative_entry_of_cause cause
      | Partial_probe -> (
          match mut with
          | Pristine | No_io_classification_split | No_epoch_clear -> current
          | No_partial_probe_guard -> Entry_unsyncable_by_partial))

(** The classification [v] carries forward from this probe. Only the ambiguous
    case - a PARTIAL request answered [Unsupported] - is distinguished, because
    that is the one the guard at mod.rs:1091 turns on; the three [Unsupported]
    routes are NOT distinguished, because the code flattens them into one
    attempt value. *)
let recent_of att kind =
  match (att, kind) with
  | Unsupported _, Partial_probe -> Recent_partial_verdict
  | Unsupported _, Full_probe -> Recent_other
  | Imported, (Full_probe | Partial_probe) -> Recent_other
  | Failed, (Full_probe | Partial_probe) -> Recent_other

(** One probe of the given kind under the given transport outcome. *)
let probe_result mut s kind link =
  let att = classify mut s.cap kind link in
  {
    cap = s.cap;
    entry = write_entry mut s.entry att kind;
    recent = recent_of att kind;
    probes = s.probes + 1;
  }

(** T1 - [v] spends one sync open on [w]. Enabled only while the peer is
    eligible (mod.rs:1066-1069) and the epoch's probe budget is unspent
    (mod.rs:1070, [MAX_EPOCH_SYNC_PROBES]). Both request variants and every
    admissible transport outcome branch. *)
let t1_probe mut s =
  enabled_list
    (eligible s && Bool.not (Int.equal s.probes max_probes))
    (List.concat_map
       (fun kind ->
         List.map (fun link -> probe_result mut s kind link) (links_for s.cap))
       [ Full_probe; Partial_probe ])

(** T2 - the epoch boundary. [start_epoch] resets [v]'s probe bookkeeping and
    calls [clear_sync_capability] (start_epoch.rs:547-550 -> mod.rs:409-416),
    emptying the map; under {!No_epoch_clear} the call is gone and the slot
    survives. [w]'s disposition is held fixed across the boundary - see scope
    note (iii) in the header. Mutation-exhaustive, no wildcard arm. *)
let t2_boundary mut s =
  [
    {
      cap = s.cap;
      entry =
        (match mut with
        | Pristine | No_io_classification_split | No_partial_probe_guard ->
            Entry_absent
        | No_epoch_clear -> s.entry);
      recent = Recent_none;
      probes = 0;
    };
  ]

(** The transition relation: one probe, or the epoch boundary. *)
let next_with mut s = t1_probe mut s @ t2_boundary mut s

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state for a pre-cutover peer: a fresh epoch, an empty map slot,
    no probe spent. *)
let initial =
  { cap = Pre_cutover; entry = Entry_absent; recent = Recent_none; probes = 0 }

(** The same fresh start against a peer that negotiates but never answers. *)
let initial_mute = { initial with cap = Negotiates_mute }

(** The same fresh start against a peer that serves full packs but cannot decode
    [EpochPackPartial] (request.rs:67-72). *)
let initial_full_only = { initial with cap = Full_only }

(** The same fresh start against a fully upgraded peer. *)
let initial_full_and_partial = { initial with cap = Full_and_partial }

(** Every initial state: [w]'s disposition is chosen by the environment and is
    never observed by [v], so each of the four is its own initial world. *)
let inits =
  [ initial; initial_mute; initial_full_only; initial_full_and_partial ]

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Cached_unsyncable
      (** [v]'s map slot for [w] reads [Some(&false)]: the state the eligibility
          filter at mod.rs:1067 drops *)
  | Cached_by_full_probe
      (** the negative slot was written by a FULL-pack probe, the only write the
          guard at mod.rs:1091 admits *)
  | Cached_capable
      (** the slot reads [Some(&true)], written either by [Imported]
          (mod.rs:1074) or by [Failed] (mod.rs:1105) *)
  | Entry_unwritten  (** the slot is absent: [w] has not been probed this epoch *)
  | Answers_full_open
      (** HIDDEN: [w] answers a full-pack open within the exchange deadline - it
          negotiates, [Ack]s and streams (mod.rs:1236-1273). False exactly for
          {!Pre_cutover} and {!Negotiates_mute}. Never in [v]'s view. *)
  | Advertises_sync
      (** HIDDEN: [w] advertises [/tn-primary-sync] at all, i.e. the outbound
          upgrade would negotiate (handler.rs:244-250). False exactly for
          {!Pre_cutover}. This is STRICTLY WEAKER than answering: a
          {!Negotiates_mute} peer advertises and still gets cached [false]
          through mod.rs:1220. Never in [v]'s view. *)
  | Verdict_from_a_post_negotiation_cut
      (** HIDDEN: the negative slot was produced by a transport cut AFTER a
          successful negotiation (mod.rs:1221-1228), not by anything [w] did.
          The map holds a bare [bool] (mod.rs:380), so this provenance is not in
          [v]'s view either. *)
  | Recent_partial_unsupported
      (** [v]'s last probe sent [EpochPackPartial] and came back [Unsupported] -
          the ambiguous verdict of mod.rs:1084-1090 *)
  | Probe_budget_spent
      (** [v] has spent this epoch's probe budget on [w] ({!max_probes}, the
          model's [MAX_EPOCH_SYNC_PROBES], mod.rs:148) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Cached_unsyncable -> (
      match s.entry with
      | Entry_unsyncable_peer | Entry_unsyncable_link_cut
      | Entry_unsyncable_open_fault | Entry_unsyncable_by_partial ->
          true
      | Entry_absent | Entry_capable -> false)
  | Cached_by_full_probe -> (
      match s.entry with
      | Entry_unsyncable_peer | Entry_unsyncable_link_cut
      | Entry_unsyncable_open_fault ->
          true
      | Entry_absent | Entry_capable | Entry_unsyncable_by_partial -> false)
  | Cached_capable -> (
      match s.entry with
      | Entry_capable -> true
      | Entry_absent | Entry_unsyncable_peer | Entry_unsyncable_link_cut
      | Entry_unsyncable_open_fault | Entry_unsyncable_by_partial ->
          false)
  | Entry_unwritten -> (
      match s.entry with
      | Entry_absent -> true
      | Entry_capable | Entry_unsyncable_peer | Entry_unsyncable_link_cut
      | Entry_unsyncable_open_fault | Entry_unsyncable_by_partial ->
          false)
  | Answers_full_open -> (
      match s.cap with
      | Full_only | Full_and_partial -> true
      | Pre_cutover | Negotiates_mute -> false)
  | Advertises_sync -> advertises s.cap
  | Verdict_from_a_post_negotiation_cut -> (
      match s.entry with
      | Entry_unsyncable_link_cut -> true
      | Entry_absent | Entry_capable | Entry_unsyncable_peer
      | Entry_unsyncable_open_fault | Entry_unsyncable_by_partial ->
          false)
  | Recent_partial_unsupported -> (
      match s.recent with
      | Recent_partial_verdict -> true
      | Recent_none | Recent_other -> false)
  | Probe_budget_spent -> Int.equal s.probes max_probes

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Cached_unsyncable -> "cached_unsyncable(w)"
  | Cached_by_full_probe -> "cached_by_full_probe(w)"
  | Cached_capable -> "cached_capable(w)"
  | Entry_unwritten -> "entry_unwritten(w)"
  | Answers_full_open -> "answers_full_open(w)"
  | Advertises_sync -> "advertises_sync(w)"
  | Verdict_from_a_post_negotiation_cut -> "verdict_from_post_negotiation_cut(w)"
  | Recent_partial_unsupported -> "recent_partial_unsupported"
  | Probe_budget_spent -> "probe_budget_spent"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation ({!Denote}, lib/internal/DESIGN.md), pinned to
    agree with {!System} at every reachable world by
    test/t_stream_sync_capability_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the four hidden-disposition initial
    worlds, mutation-parameterized transitions, the two-agent view, the atom
    valuation. *)
let spec_of mut = { Checker.init = inits; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
