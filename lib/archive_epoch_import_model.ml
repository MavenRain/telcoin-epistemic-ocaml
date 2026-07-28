(** The ARCHIVE-EPOCH-IMPORT family: one pass of [ConsensusChain::stream_import]
    (crates/storage/src/consensus.rs:441-541) over a peer-supplied epoch pack,
    from the already-held short circuit through the streamed batch bound and the
    publish-time final-header equality to the remove+rename that installs the
    pack for readers.

    {b Mechanism.} Four gates sit on that one function and this family is three
    of them plus the reader path they race:

    + the idempotency / anti-truncation short circuit
      (consensus.rs:450-465): [get_static(epoch)] then
      [pack.consensus_header_by_number(final.number)] then
      [have.digest() == epoch_final_hash] returns [Ok(())] with nothing
      touched, so a node that already holds the requested final header never
      re-enters the install window;
    + the per-output batch bound (consensus_pack.rs:1451-1468): in the v1
      stream the consensus header is read FIRST (:1428-1440 rejects a leading
      [Batch] record), its sub-dag's payload digests are counted into
      [expected_digest_count] (:1451-1459), and
      [if expected_digest_count > MAX_BATCHES_PER_OUTPUT] rejects with
      [TooManyBatches] (:1466-1468) BEFORE the batch-reading loop at :1477
      inserts anything into [available_batches]. [MAX_BATCHES_PER_OUTPUT] is
      1_000 (:1371-1372), 50 under [cfg(test)] (:1375-1376). The legacy v0
      decoder is a different function with its OWN running counter
      ([batch_records += 1; if batch_records > MAX_BATCHES_PER_OUTPUT],
      :1575/:1587-1590) and it buffers up to the cap before tripping;
      [stream_import] picks between the two on [stream_iter.version() == 0]
      (:960-974), i.e. the sending peer chooses which gate it faces;
    + the publish-time final-header equality (consensus.rs:487-497): the chain
      is verified link by link while it streams
      ([output.parent_hash() != parent_digest -> InvalidConsensusChain],
      [consensus_number > final_consensus_number -> InvalidConsensusNumber],
      [parent_digest = output.digest()], consensus_pack.rs:975-986), anchored
      at the previous epoch's final hash (:952-956) behind
      [verify_epoch_meta] (:932, definition :1318), so
      [epoch_record.final_consensus.number != last_header.number ||
      epoch_final_hash != last_header.digest() -> InvalidImport] is what turns
      a verified gapless PREFIX into a verified gapless WHOLE epoch;
    + the install itself (consensus.rs:509-532): take [pack_install], drop the
      handle, [if std::fs::exists(&base_dir) { remove_dir_all(&base_dir) }]
      (:513-519), [rename] (:520), purge [recent_packs] of this epoch (:526),
      [rename_err?] (:527), [fsync_directory] (:532). The remove leaves a
      window in which [epoch-{N}] does not exist, and the source says so
      in-line at :514-517.

    {b The reader that races it, and the repair path it has.} A reader goes
    through [ConsensusChain::get_static] (consensus.rs:1067-1088), which takes
    NO [pack_install] lock: it checks [current_pack], then scans the
    [recent_packs] FIFO and returns a clone on a hit, and only on a miss calls
    [ConsensusPack::open_static(&self.base_path, epoch)] - the one step that
    touches the directory and therefore the one step the window can fail. The
    cache hit is a genuine repair and is modelled: a cached [ConsensusPack]
    keeps its file descriptors, so it still answers while the directory entry
    is unlinked, and the installer's purge at :526 happens AFTER the rename at
    :520, not inside the window. What defeats the repair is equally real: the
    FIFO is capped at [PACK_CACHE_SIZE = 10] (:323) and [get_static] evicts
    with [pop_front] before every push (:1080-1083), so ten opens of other
    epochs flush our entry. The model therefore carries a cache that starts
    warm, can be evicted at any point, and is purged on install.

    {b Components.} What the serving peer [w] actually possesses of the epoch
    ({!hold}, hidden from the importer), the stream format the peer chose
    ({!fmt}), the batch-digest count its output declares ({!decl}), what the
    importer already held when it started ({!have}), the pipeline position
    ({!stage}), how much has been buffered ({!buf}), the FIFO cache
    ({!cache}) and one in-process reader ({!reader}).

    {b Scope.} The reader/cache sub-model is live only in the already-held
    branch ([have = Have_final]), because that is the branch statement S2 is
    about. The model is NOT rigged to make the window exclusive to a mutation:
    two pristine initial states ([initial_incomplete_pack],
    [initial_incomplete_pack_ahead]) hold an incomplete [epoch-{N}] directory,
    take the [std::fs::exists] branch at :513 and pass through
    {!St_unlinked} on the pristine model - that is exactly the case the
    source's own comment at :514-517 warns about, and
    test/t_archive_epoch_import.ml asserts it is reachable.

    {b Role mapping.} [V0] is the importing node [v]: a knowledge agent whose
    view is its own pipeline position, the stream version and declared count it
    read, its own buffer and whether its own [consensus_header_by_number]
    lookup found the final header. NOT in [V0]'s view: what the peer's archive
    actually holds (the whole point of the linkage gate), and the reader/cache
    race - [get_static] takes the [recent_packs] lock, reads and drops it
    (:1073-1084) and there is no handshake with a concurrent reader. [V1] is
    the serving peer [w]; its view is exactly its own possession, because the
    epoch-pack exchange is one-directional bytes with no receipt of the
    importer's verdict (crates/consensus/primary/src/network/mod.rs:1243-1273
    awaits only its own local [import] future). [V2]..[V9] are idle non-agents
    with the constant blank view and never appear under [K].

    Every citation in this module was opened in the working tree of
    Telcoin-Association/telcoin-network at git 0c59c15b while writing it. *)

(** What the serving peer [w] actually possesses of epoch [e]. The importer
    asks for everything up to [epoch_record.final_consensus] and the responder
    streams what it has, so the peer's archive - not the request - decides how
    long the chain on the wire is. *)
type hold =
  | Peer_prefix
      (** [w] holds start..final-1 only: a gapless but SHORT chain, the case
          consensus.rs:492-497 exists to reject *)
  | Peer_exact  (** [w] holds exactly start..final *)
  | Peer_ahead
      (** [w] holds start..final and the first output of epoch [e+1]; the
          responder still streams only up to the requested final number, so the
          bytes are identical to {!Peer_exact} *)

(** Total order index for {!hold}. *)
let hold_index = function Peer_prefix -> 0 | Peer_exact -> 1 | Peer_ahead -> 2

(** Total order on {!hold}. *)
let hold_compare a b = Int.compare (hold_index a) (hold_index b)

(** The pack stream version, which the SENDER picks and [stream_import]
    dispatches on ([stream_iter.version() == 0], consensus_pack.rs:960-974). *)
type fmt =
  | Fmt_legacy
      (** v0: batches arrive before the terminating consensus record and
          [iter_to_output_legacy] bounds them with its own running counter
          (consensus_pack.rs:1575, :1587-1590) *)
  | Fmt_v1
      (** v1: the consensus header arrives first (:1428-1440) and its declared
          digest count is checked before any batch is buffered (:1466-1468) *)

(** Total order index for {!fmt}. *)
let fmt_index = function Fmt_legacy -> 0 | Fmt_v1 -> 1

(** Total order on {!fmt}. *)
let fmt_compare a b = Int.compare (fmt_index a) (fmt_index b)

(** How many batch digests the streamed output declares, relative to
    [MAX_BATCHES_PER_OUTPUT] (consensus_pack.rs:1371-1376). The count comes out
    of the header's sub-dag, which is attacker-controlled and bounded only by
    [MAX_RECORD_SIZE] (archive/pack_iter.rs:25, :100-102, :120-123). *)
type decl =
  | Decl_ok  (** [expected_digest_count <= MAX_BATCHES_PER_OUTPUT] *)
  | Decl_flood  (** [expected_digest_count > MAX_BATCHES_PER_OUTPUT] *)

(** Total order index for {!decl}. *)
let decl_index = function Decl_ok -> 0 | Decl_flood -> 1

(** Total order on {!decl}. *)
let decl_compare a b = Int.compare (decl_index a) (decl_index b)

(** What the importer already had on disk for this epoch when [stream_import]
    was entered - the outcome of the [get_static] plus
    [consensus_header_by_number] plus digest comparison at
    consensus.rs:450-464. *)
type have =
  | Have_none
      (** no [epoch-{N}] directory at all, so the [std::fs::exists] test at
          :513 is false and the install is a bare rename with no window *)
  | Have_partial
      (** an [epoch-{N}] directory exists but does not resolve the requested
          final number, so the lookup at :458-459 errors, the import proceeds
          and the install DOES take the remove+rename window *)
  | Have_final
      (** the requested final header resolves by number and its digest matches,
          which is exactly the short circuit's condition at :461-462 *)

(** Total order index for {!have}. *)
let have_index = function Have_none -> 0 | Have_partial -> 1 | Have_final -> 2

(** Total order on {!have}. *)
let have_compare a b = Int.compare (have_index a) (have_index b)

(** The importer's position in [stream_import]. *)
type stage =
  | St_idle  (** [stream_import] entered, the short circuit not yet evaluated *)
  | St_shorted
      (** the short circuit fired: [return Ok(())] at consensus.rs:462 with the
          canonical directory untouched *)
  | St_header
      (** v1 only: the epoch meta was verified (:932) and the output's
          consensus header was read, so [expected_digest_count] is known
          (consensus_pack.rs:1451-1459) and nothing has been buffered *)
  | St_capped
      (** rejected with [TooManyBatches]: v1 at :1466-1468 before buffering, v0
          at :1587-1590 after buffering up to the cap *)
  | St_batches
      (** the batch records have been buffered into [available_batches]
          (:1477-1505) and the streamed chain was link-verified as it went
          (:975-986) *)
  | St_link_rejected
      (** the publish-time equality failed: [InvalidImport] at
          consensus.rs:492-497, [ImportPath]'s [Drop] removes the staging dir
          (:1331-1335) and the canonical directory is untouched *)
  | St_unlinked
      (** [remove_dir_all(&base_dir)] has run and [rename] has not: the window
          the source comment at consensus.rs:514-517 describes *)
  | St_published
      (** [rename] (:520), [recent_packs] purge (:526) and
          [fsync_directory] (:532) are done; the pack is now what every reader
          of this epoch gets *)

(** Total order index for {!stage}. *)
let stage_index = function
  | St_idle -> 0
  | St_shorted -> 1
  | St_header -> 2
  | St_capped -> 3
  | St_batches -> 4
  | St_link_rejected -> 5
  | St_unlinked -> 6
  | St_published -> 7

(** Total order on {!stage}. *)
let stage_compare a b = Int.compare (stage_index a) (stage_index b)

(** How much of one output's batch set has been buffered in
    [available_batches]. *)
type buf =
  | Buf_none  (** nothing inserted yet *)
  | Buf_capped  (** at most [MAX_BATCHES_PER_OUTPUT] records held *)
  | Buf_flood  (** more than the cap: the state the bound exists to forbid *)

(** Total order index for {!buf}. *)
let buf_index = function Buf_none -> 0 | Buf_capped -> 1 | Buf_flood -> 2

(** Total order on {!buf}. *)
let buf_compare a b = Int.compare (buf_index a) (buf_index b)

(** The [recent_packs] FIFO's entry for this epoch (consensus.rs:303,
    :1073-1086). *)
type cache =
  | Cache_warm
      (** an open [ConsensusPack] for this epoch sits in the FIFO; its file
          descriptors survive an unlink, so it answers inside the window *)
  | Cache_evicted
      (** the entry is gone - either flushed by the [pop_front] at :1081-1083
          once ten other epochs have been opened, or purged by the installer
          at :526 *)

(** Total order index for {!cache}. *)
let cache_index = function Cache_warm -> 0 | Cache_evicted -> 1

(** Total order on {!cache}. *)
let cache_compare a b = Int.compare (cache_index a) (cache_index b)

(** One in-process reader of this epoch going through
    [ConsensusChain::get_static] (consensus.rs:1067-1088). *)
type reader =
  | Rd_idle  (** has not asked yet *)
  | Rd_waiting  (** inside [get_static], not yet resolved *)
  | Rd_served  (** got a [ConsensusPack], from the cache or from [open_static] *)
  | Rd_failed
      (** [open_static] returned [Err]: the directory entry was not there *)

(** Total order index for {!reader}. *)
let reader_index = function
  | Rd_idle -> 0
  | Rd_waiting -> 1
  | Rd_served -> 2
  | Rd_failed -> 3

(** Total order on {!reader}. *)
let reader_compare a b = Int.compare (reader_index a) (reader_index b)

(** The joint global state: the peer's hidden possession, the stream the peer
    chose, the importer's prior contents, its pipeline position and buffer, the
    FIFO cache and the racing reader. *)
type state = {
  hold : hold;  (** what [w] possesses; never in [V0]'s view *)
  fmt : fmt;  (** the stream version [w] sent *)
  decl : decl;  (** the batch-digest count the output declares *)
  have : have;  (** what [v] held on entry (consensus.rs:450-464) *)
  stage : stage;  (** where [v] is inside [stream_import] *)
  buf : buf;  (** [available_batches] occupancy *)
  cache : cache;  (** the [recent_packs] entry for this epoch *)
  reader : reader;  (** the in-process reader racing the install *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = hold_compare s1.hold s2.hold in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = fmt_compare s1.fmt s2.fmt in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = decl_compare s1.decl s2.decl in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = have_compare s1.have s2.have in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = stage_compare s1.stage s2.stage in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = buf_compare s1.buf s2.buf in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = cache_compare s1.cache s2.cache in
              if Bool.not (Int.equal c6 0) then c6
              else reader_compare s1.reader s2.reader

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    [View_node] is what the importing node [v] can actually see: its own
    position in [stream_import], the stream version it dispatched on
    (consensus_pack.rs:960), the digest count the header declared (:1459), its
    own [available_batches] occupancy and the outcome of its own
    [consensus_header_by_number] lookup (consensus.rs:458-462). It deliberately
    omits {!hold} - the peer's archive is exactly the fact the linkage gate
    lets [v] infer rather than observe - and it omits {!cache}/{!reader},
    because [get_static] takes the [recent_packs] lock, reads and drops it
    (:1073-1084) and the import task never learns whether a reader was in
    flight.

    [View_peer] is the serving peer's own possession and nothing else: the
    exchange is one-directional bytes and the importer's verdict never travels
    back (crates/consensus/primary/src/network/mod.rs:1243-1273). *)
type view =
  | View_idle  (** the constant blank view of the non-agents [V2]..[V9] *)
  | View_peer of hold
  | View_node of stage * fmt * decl * buf * have

(** Total order index for {!view}. *)
let view_index = function
  | View_idle -> 0
  | View_peer _ -> 1
  | View_node _ -> 2

(** Total order on the importing node's five visible components. *)
let view_node_compare (g1, f1, d1, b1, h1) (g2, f2, d2, b2, h2) =
  let c = stage_compare g1 g2 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = fmt_compare f1 f2 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = decl_compare d1 d2 in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = buf_compare b1 b2 in
        if Bool.not (Int.equal c3 0) then c3 else have_compare h1 h2

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_peer _ | View_node _) -> -1
  | (View_peer _ | View_node _), View_idle -> 1
  | View_peer h1, View_peer h2 -> hold_compare h1 h2
  | View_peer _, View_node _ -> -1
  | View_node _, View_peer _ -> 1
  | View_node (g1, f1, d1, b1, h1), View_node (g2, f2, d2, b2, h2) ->
      view_node_compare (g1, f1, d1, b1, h1) (g2, f2, d2, b2, h2)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. [V0] is the importing node [v] and [V1] is the serving
    peer [w]; [V2]..[V9] are idle non-agents with the constant blank view and
    never appear under [K]. *)
let view v s =
  match v with
  | Validator.V0 -> View_node (s.stage, s.fmt, s.decl, s.buf, s.have)
  | Validator.V1 -> View_peer s.hold
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_final_header_link
      (** delete the [if epoch_record.final_consensus.number !=
          last_header.number || epoch_final_hash != last_header.digest() {
          return Err(ConsensusChainError::InvalidImport); }] block
          (crates/storage/src/consensus.rs:492-497). That REMOVES the
          {!St_batches} -> {!St_link_rejected} transition for a {!Peer_prefix}
          sender and ADDS {!St_batches} -> {!St_published} in its place, so a
          verified-but-SHORT chain is renamed over [epoch-{N}] and served as
          authoritative. No sibling path repairs it at publish time: the
          streamed linkage checks (consensus_pack.rs:975-986) certify only that
          what arrived is gapless from the previous epoch's final hash, never
          that it REACHED the requested final number; [ConsensusPack::open_static]
          -> [files_consistent] (consensus_pack.rs:894-902) passes on a
          truncated-but-cleanly-closed pack because the three sidecars agree
          with the short data file; [ImportPath] only removes the staging
          directory (consensus.rs:1331-1335); and
          [pack_validate::validate_pack_file] is an offline tool with no call
          site on this path. Two partial, LATER repairs exist and neither
          touches the publish-time claim: [is_epoch_complete]
          (consensus.rs:922-930) re-resolves the final number and would let a
          caller re-stream, but never un-publishes; and [get_epoch_stream]
          (:543-576) re-checks [final_consensus.number == last_header.number &&
          hash == last_header.digest()] before serving the pack ONWARD to a
          peer, which limits propagation but not local trust - the sibling
          [get_partial_epoch_stream] (:587-602) deliberately does not require
          completeness, and the node's own read path just uses whatever is
          published ([get_static] then [get_consensus_output_bytes], :906-918).
          Pins S1. *)
  | No_already_held_shortcircuit
      (** delete the [if let Ok(have) =
          pack.consensus_header_by_number(epoch_record.final_consensus.number)
          .await { if have.digest() == epoch_final_hash { return Ok(()); } }]
          guard (crates/storage/src/consensus.rs:458-464). That REMOVES the
          {!St_idle} -> {!St_shorted} transition for [have = Have_final] and
          ADDS the full pipeline in its place, so a node that already holds the
          epoch runs the remove+rename and passes through {!St_unlinked}. No
          sibling path repairs it: [ImportPath::new] refuses only a SECOND
          concurrent import of the same epoch in this process
          ([if proc_path.exists() { return Ok(None) }], :1305-1308) and never
          considers what is already held; the [pack_install] mutex (:509,
          declared :305-311) serialises installers against [new_epoch] but
          readers never take it ([get_static], :1067-1088); the [recent_packs]
          cache DOES answer inside the window and IS modelled here, but it is a
          ten-entry FIFO that [get_static] evicts from with [pop_front]
          (:323, :1080-1083), so ten opens of other epochs strip the repair;
          and [import_partial_to_staging] (:312-318, call site
          crates/consensus/primary/src/network/mod.rs:1249-1256) diverts only
          PARTIAL sync prefixes into [staging-{epoch}] - the full-pack branch
          at network/mod.rs:1264-1265 still calls [stream_import]. Nor does any
          caller retry: every [get_static] call site is
          [if let Ok(pack) = self.get_static(epoch).await { .. } else { .. }]
          with a give-up arm ([Ok(None)], [StreamUnavailable], or the staging
          fallback, which covers only the in-progress epoch in
          {!ConsensusChain}'s staging slot) - consensus.rs:549, 593, 762, 800,
          839, 869, 906-918, 968, 984, 1000, 1037 - which is why {!Rd_failed}
          is a sink here. Pins S2. *)
  | No_batch_count_cap
      (** delete [if expected_digest_count > MAX_BATCHES_PER_OUTPUT { return
          Err(PackError::TooManyBatches(MAX_BATCHES_PER_OUTPUT)); }]
          (crates/storage/src/consensus_pack.rs:1466-1468). That REMOVES the
          {!St_header} -> {!St_capped} transition for a v1 stream declaring
          more than the cap and ADDS {!St_header} -> {!St_batches} with
          {!Buf_flood}, i.e. the importer buffers an attacker-declared number
          of batch records. No sibling path repairs the v1 stream:
          [MAX_RECORD_SIZE] bounds each record but not how many are named
          (archive/pack_iter.rs:100-102, :120-123), and one 16MiB sub-dag can
          name hundreds of thousands of digests; the terminating condition
          [if digest_count == expected_digest_count { break; }] (:1496-1499)
          is derived from the same unbounded count; the per-record
          [tokio::time::timeout] (:1409-1419) bounds latency, not memory; and
          the legacy v0 counter (:1575, :1587-1590) lives in a different
          function that [stream_import] reaches only when
          [stream_iter.version() == 0] (:960-974) - the sender chooses the
          version, so it is not a repair. The model keeps the v0 branch live
          precisely so this can be checked: under this mutation the v0 branch
          is still bounded and only the v1 branch floods. Pins S3. *)

(** Does the short circuit at consensus.rs:458-464 fire in this state under
    this mutation? *)
let short_circuits mut s =
  match s.have with
  | Have_final -> (
      match mut with
      | Pristine | No_final_header_link | No_batch_count_cap -> true
      | No_already_held_shortcircuit -> false)
  | Have_none | Have_partial -> false

(** Does the v1 declared-count check at consensus_pack.rs:1466-1468 reject
    before any batch is buffered? *)
let cap_rejects_v1 mut s =
  match s.decl with
  | Decl_flood -> (
      match mut with
      | Pristine | No_final_header_link | No_already_held_shortcircuit -> true
      | No_batch_count_cap -> false)
  | Decl_ok -> false

(** Does the legacy v0 running counter at consensus_pack.rs:1587-1590 trip?
    It is independent of every mutation in this family: those delete gates in
    [stream_import] and in the v1 decoder only. *)
let legacy_counter_trips s =
  match s.fmt with
  | Fmt_legacy -> ( match s.decl with Decl_flood -> true | Decl_ok -> false)
  | Fmt_v1 -> false

(** Does the publish-time final-header equality at consensus.rs:492-497 reject
    this stream under this mutation? *)
let link_rejects mut s =
  match s.hold with
  | Peer_prefix -> (
      match mut with
      | Pristine | No_already_held_shortcircuit | No_batch_count_cap -> true
      | No_final_header_link -> false)
  | Peer_exact | Peer_ahead -> false

(** How full [available_batches] gets once the batch loop at
    consensus_pack.rs:1477-1505 has run for a v1 stream. *)
let buf_after_v1 s =
  match s.decl with Decl_ok -> Buf_capped | Decl_flood -> Buf_flood

(** Does the install have to unlink [epoch-{N}] first - the
    [if std::fs::exists(&base_dir)] test at consensus.rs:513? *)
let unlink_needed s =
  match s.have with
  | Have_partial | Have_final -> true
  | Have_none -> false

(** Is the reader/cache sub-model live here? It is scoped to the already-held
    branch, the branch statement S2 speaks about; see the module header. *)
let availability_live s =
  match s.have with
  | Have_final -> true
  | Have_none | Have_partial -> false

(** The importer's own step: one move down [stream_import]. *)
let stage_steps mut s =
  match s.stage with
  | St_idle ->
      if short_circuits mut s then [ { s with stage = St_shorted } ]
      else (
        match s.fmt with
        | Fmt_v1 -> [ { s with stage = St_header } ]
        | Fmt_legacy -> [ { s with stage = St_batches; buf = Buf_capped } ])
  | St_header ->
      if cap_rejects_v1 mut s then [ { s with stage = St_capped } ]
      else [ { s with stage = St_batches; buf = buf_after_v1 s } ]
  | St_batches ->
      if legacy_counter_trips s then [ { s with stage = St_capped } ]
      else if link_rejects mut s then [ { s with stage = St_link_rejected } ]
      else if unlink_needed s then [ { s with stage = St_unlinked } ]
      else [ { s with stage = St_published; cache = Cache_evicted } ]
  | St_unlinked -> [ { s with stage = St_published; cache = Cache_evicted } ]
  | St_shorted | St_capped | St_link_rejected | St_published -> []

(** The FIFO's step: ten opens of other epochs flush this epoch's entry
    (consensus.rs:323, :1080-1083). One-way; a re-open would re-warm it, but a
    re-open DURING the window fails on the same missing directory, and [Af]
    quantifies over all paths, so the eviction path is the one that matters. *)
let cache_steps s =
  if availability_live s then
    match s.cache with
    | Cache_warm -> [ { s with cache = Cache_evicted } ]
    | Cache_evicted -> []
  else []

(** How [get_static] resolves for the racing reader: cache hit first
    (consensus.rs:1074-1079), otherwise [ConsensusPack::open_static] at :1085,
    which is the only step the unlink window can fail. *)
let reader_answer s =
  match s.cache with
  | Cache_warm -> Rd_served
  | Cache_evicted -> (
      match s.stage with
      | St_unlinked -> Rd_failed
      | St_idle | St_shorted | St_header | St_capped | St_batches
      | St_link_rejected | St_published ->
          Rd_served)

(** The reader's step: arrive, then resolve. *)
let reader_steps s =
  if availability_live s then
    match s.reader with
    | Rd_idle -> [ { s with reader = Rd_waiting } ]
    | Rd_waiting -> [ { s with reader = reader_answer s } ]
    | Rd_served | Rd_failed -> []
  else []

(** The transition relation: the importer, the cache and the reader advance
    independently, one component per step. *)
let next_with mut s = stage_steps mut s @ cache_steps s @ reader_steps s

(** The pristine transition relation. *)
let next = next_with Pristine

(** The honest full-epoch import: the peer holds exactly the requested epoch,
    sends a v1 stream declaring a legal batch count, and the importer holds no
    [epoch-{N}] directory at all. *)
let initial =
  {
    hold = Peer_exact;
    fmt = Fmt_v1;
    decl = Decl_ok;
    have = Have_none;
    stage = St_idle;
    buf = Buf_none;
    cache = Cache_warm;
    reader = Rd_idle;
  }

(** The same import from a peer that holds only start..final-1: the chain on
    the wire is gapless but short, which is what consensus.rs:492-497 rejects. *)
let initial_peer_prefix = { initial with hold = Peer_prefix }

(** The same import from a peer that is AHEAD of the epoch boundary. The
    responder streams only up to the requested final number, so the bytes and
    every outcome are identical to {!initial} - this is the twin that makes
    [V0]'s view class at a published state non-singleton. *)
let initial_peer_ahead = { initial with hold = Peer_ahead }

(** The importer already has an [epoch-{N}] directory but it does not resolve
    the requested final number, so the short circuit does not fire and the
    install must remove before it renames: the PRISTINE unlink window. *)
let initial_incomplete_pack = { initial with have = Have_partial }

(** The incomplete-pack import from an ahead peer; the second member of the
    published-state view class in that branch. *)
let initial_incomplete_pack_ahead =
  { initial with have = Have_partial; hold = Peer_ahead }

(** A v1 stream whose header declares more batch digests than
    [MAX_BATCHES_PER_OUTPUT]. *)
let initial_flood_v1 = { initial with decl = Decl_flood }

(** The same flood over the legacy v0 stream, where the bound is the running
    counter at consensus_pack.rs:1587-1590 instead. Kept live so the v1 gate
    deletion can be seen NOT to be repaired by the v0 sibling. *)
let initial_flood_legacy =
  { initial with decl = Decl_flood; fmt = Fmt_legacy }

(** A redundant import: the node already holds the requested final consensus
    header by number and digest, so the short circuit at consensus.rs:461-462
    must fire. This is the only initial state where the reader/cache
    sub-model is live. *)
let initial_already_held = { initial with have = Have_final }

(** Every initial state, in the order [spec_of] lists them. *)
let inits =
  [
    initial;
    initial_peer_prefix;
    initial_peer_ahead;
    initial_incomplete_pack;
    initial_incomplete_pack_ahead;
    initial_flood_v1;
    initial_flood_legacy;
    initial_already_held;
  ]

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Published
      (** the imported pack has been renamed over [epoch-{N}] and fsynced
          (consensus.rs:520-532) *)
  | Peer_holds_full_epoch
      (** [w] possessed every consensus output of the epoch from start through
          [final_consensus] *)
  | Peer_holds_beyond_epoch
      (** [w] additionally possesses an output past the epoch boundary *)
  | Redundant_import
      (** the importer already held the requested final consensus header
          (consensus.rs:458-462) *)
  | Epoch_dir_absent
      (** [epoch-{N}] has been removed and not yet renamed back
          (consensus.rs:513-520) *)
  | Reader_waiting  (** an in-process reader is inside [get_static] *)
  | Reader_served  (** that reader got a [ConsensusPack] *)
  | Reader_failed  (** that reader got an open error instead *)
  | Stream_in_progress
      (** a peer stream is being decoded: the header has been read or the batch
          loop is running *)
  | Stream_is_v1
      (** the sender chose the v1 format, so the v1 decoder is the one running
          (consensus_pack.rs:960-974) *)
  | Declares_over_cap
      (** the output declares more batch digests than
          [MAX_BATCHES_PER_OUTPUT] *)
  | Batches_buffered  (** at least one batch record sits in [available_batches] *)
  | Buffer_over_cap
      (** more than [MAX_BATCHES_PER_OUTPUT] records are buffered *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Published -> (
      match s.stage with
      | St_published -> true
      | St_idle | St_shorted | St_header | St_capped | St_batches
      | St_link_rejected | St_unlinked ->
          false)
  | Peer_holds_full_epoch -> (
      match s.hold with
      | Peer_exact | Peer_ahead -> true
      | Peer_prefix -> false)
  | Peer_holds_beyond_epoch -> (
      match s.hold with
      | Peer_ahead -> true
      | Peer_prefix | Peer_exact -> false)
  | Redundant_import -> (
      match s.have with
      | Have_final -> true
      | Have_none | Have_partial -> false)
  | Epoch_dir_absent -> (
      match s.stage with
      | St_unlinked -> true
      | St_idle | St_shorted | St_header | St_capped | St_batches
      | St_link_rejected | St_published ->
          false)
  | Reader_waiting -> (
      match s.reader with
      | Rd_waiting -> true
      | Rd_idle | Rd_served | Rd_failed -> false)
  | Reader_served -> (
      match s.reader with
      | Rd_served -> true
      | Rd_idle | Rd_waiting | Rd_failed -> false)
  | Reader_failed -> (
      match s.reader with
      | Rd_failed -> true
      | Rd_idle | Rd_waiting | Rd_served -> false)
  | Stream_in_progress -> (
      match s.stage with
      | St_header | St_batches -> true
      | St_idle | St_shorted | St_capped | St_link_rejected | St_unlinked
      | St_published ->
          false)
  | Stream_is_v1 -> ( match s.fmt with Fmt_v1 -> true | Fmt_legacy -> false)
  | Declares_over_cap -> (
      match s.decl with Decl_flood -> true | Decl_ok -> false)
  | Batches_buffered -> (
      match s.buf with Buf_capped | Buf_flood -> true | Buf_none -> false)
  | Buffer_over_cap -> (
      match s.buf with Buf_flood -> true | Buf_none | Buf_capped -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Published -> "published(v, e)"
  | Peer_holds_full_epoch -> "holds(w, start..final)"
  | Peer_holds_beyond_epoch -> "holds(w, final+1)"
  | Redundant_import -> "already_held(v, e)"
  | Epoch_dir_absent -> "epoch_dir_absent"
  | Reader_waiting -> "reader_waiting"
  | Reader_served -> "reader_answered"
  | Reader_failed -> "reader_errored"
  | Stream_in_progress -> "importing(v, w)"
  | Stream_is_v1 -> "stream_v1"
  | Declares_over_cap -> "declared > MAX_BATCHES_PER_OUTPUT"
  | Batches_buffered -> "buffered > 0"
  | Buffer_over_cap -> "buffered > MAX_BATCHES_PER_OUTPUT"

(** The CTLK checker over this family's ordered state and view: the presheaf-
    topos denotation, pinned to agree with {!System} by
    test/t_archive_epoch_import_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation. *)
let spec_of mut = { Checker.init = inits; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
