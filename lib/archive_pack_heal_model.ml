(** The ARCHIVE-PACK-HEAL family: one epoch pack's data file and its three
    sidecar indexes across a failed append, a crash and a reopen.

    {b Mechanism.} A [ConsensusPack] is a background thread owning an [Inner]
    made of four separately buffered, separately synced files
    (crates/storage/src/consensus_pack.rs:1126-1134 syncs them in the order
    data, position index, consensus digests, batch digests):

    - the data pack [Pack<PackRecord>] (crates/storage/src/archive/pack.rs),
      an append-only log of length-prefixed CRC'd records;
    - [consensus_pos_idx], a dense position index whose entry [j] records the
      post-append file length as [output_end] (consensus_pack.rs:1059-1062);
    - [consensus_digests] and [batch_digests], two hash indexes each carrying
      a [data_file_length] field the pack keeps in step
      (consensus_pack.rs:1011-1012, :1063-1064,
      archive/digest_index/index.rs:405-420).

    Three gates sit on that pipeline and this family is exactly those three:

    + the write-failure latch [PackInner.failed] (archive/pack.rs:165, set at
      :269 in the [AppendError::WriteDataError] arm, read at :262 and :299);
    + the append-open repair [Inner::trunc_and_heal]
      (consensus_pack.rs:664-728), called from [open_append]
      (:809-814) and [open_append_exists] (:852-857), whose phase B walk-back
      is clamped shrink-only at :713-716;
    + the read-only-open agreement gate [Inner::files_consistent]
      (:640-662), enforced only from [open_static] (:894-902), which is the
      mode behind [ConsensusChain::get_static] (consensus.rs:1067-1088) and
      therefore behind every peer-facing read of a past epoch.

    {b Components.} Lengths are counted in whole consensus-output records past
    the epoch-meta header, so [L0] is the length of a freshly created pack
    (consensus_pack.rs:802-807) and [L1]/[L2] add one record each. The state
    carries the data length [plen], the two tracked lengths [ctrack]/[btrack],
    the position-index entry count [pidx], the latch, the error-watch/observed
    signal, one remote-holder bit, the lifecycle phase and the three
    heal-outcome markers.

    {b Role mapping.} [V0] is the node that owns the pack: it is a knowledge
    agent with a genuinely partial view - while the thread runs it sees only
    the error watch ([ConsensusPack::get_error], :356-363) and the indexed
    output count ([contains_consensus_header_number], :1070-1072), never the
    data-file length, the tracked lengths or the latch; after a reopen it sees
    the healed file lengths but NOT what the heal trimmed, because
    [trunc_and_heal] returns [Result<(), PackError>] (:665-670) and reports
    nothing. [V1] is the remote peer [w] that may have been served this
    epoch's bytes over [get_partial_epoch_stream] (consensus.rs:587-602); its
    view is exactly its own possession. [V2]..[V9] are idle non-agents with
    the constant blank view and never appear under [K].

    Every citation in this module was opened in the working tree of
    Telcoin-Association/telcoin-network at git 0c59c15b while writing it. *)

(** Data-file length, in whole consensus-output records past the epoch-meta
    header. [L0] is what a fresh pack reports once [EpochMeta] is appended
    (consensus_pack.rs:802-807), i.e. the [DATA_HEADER_BYTES] boundary the
    heal's phase-A guards compare against (:675, :677). *)
type len = L0 | L1 | L2

(** Total order index for {!len}. *)
let len_index = function L0 -> 0 | L1 -> 1 | L2 -> 2

(** Total order on {!len}. *)
let len_compare a b = Int.compare (len_index a) (len_index b)

(** [a <= b] on {!len}, without polymorphic comparison. *)
let len_le a b = Int.equal (Int.min (len_index a) (len_index b)) (len_index a)

(** [a < b] on {!len}. *)
let len_lt a b = Bool.not (len_le b a)

(** The smaller of two lengths - the [min] of consensus_pack.rs:716. *)
let min_len a b = if len_le a b then a else b

(** One record longer, saturating at [L2] (the model's scope bound). *)
let succ_len = function L0 -> L1 | L1 -> L2 | L2 -> L2

(** One record shorter, saturating at [L0]: a crash that loses the last
    unsynced record's bytes. *)
let pred_len = function L0 -> L0 | L1 -> L0 | L2 -> L1

(** Position-index entry count. Entry [j] (1-based) carries
    [output_end = L_j], because [save_consensus_output] stores the file length
    taken AFTER the data append (consensus_pack.rs:1059-1062). *)
type pidx = P0 | P1 | P2

(** Total order index for {!pidx}. *)
let pidx_index = function P0 -> 0 | P1 -> 1 | P2 -> 2

(** Total order on {!pidx}. *)
let pidx_compare a b = Int.compare (pidx_index a) (pidx_index b)

(** One more indexed output, saturating at [P2]. *)
let succ_pidx = function P0 -> P1 | P1 -> P2 | P2 -> P2

(** One fewer indexed output: a crash losing the unsynced index tail. *)
let pred_pidx = function P0 -> P0 | P1 -> P0 | P2 -> P1

(** The [output_end] of the LAST entry, i.e. the file length the position
    index believes in; [L0] when the index is empty (consensus_pack.rs:653-658
    skips the check in that case). *)
let pidx_end = function P0 -> L0 | P1 -> L1 | P2 -> L2

(** The [output_end] of the FIRST entry - the value the walk-back ends up
    holding when it falls all the way through to [idx = 0]
    (consensus_pack.rs:705-710). [L0] for an empty index, which the walk-back
    never sees. *)
let pidx_first_end = function P0 -> L0 | P1 -> L1 | P2 -> L1

(** What the walk-back leaves behind when NO entry fits inside the surviving
    data. Both of its index truncations are guarded by [idx != start_idx]
    (consensus_pack.rs:695 and :706), so a single-entry index - where
    [start_idx] is already 0 - is left completely untouched: the stale entry
    survives claiming an [output_end] past the clamped file. With two or more
    entries the walk reaches [idx = 0] with [idx != start_idx] and
    [truncate_all] empties the index (:707). *)
let pidx_after_total_miss = function P0 -> P0 | P1 -> P1 | P2 -> P0

(** The index entries, NEWEST FIRST, paired with the entry count that
    [truncate_to_index] would leave behind (position_index/index.rs:227-237
    keeps entries [0..=key], i.e. [key + 1] of them). *)
let pidx_entries = function
  | P0 -> []
  | P1 -> [ (P1, L1) ]
  | P2 -> [ (P2, L2); (P1, L1) ]

(** [PackInner.failed] (archive/pack.rs:165): [Lt_failed] refuses every later
    [append] (:262-263) and every [commit] (:299-301). *)
type latch = Lt_ok | Lt_failed

(** Total order index for {!latch}. *)
let latch_index = function Lt_ok -> 0 | Lt_failed -> 1

(** Total order on {!latch}. *)
let latch_compare a b = Int.compare (latch_index a) (latch_index b)

(** The error watch of consensus_pack.rs:135/142 together with what [V0] has
    actually read out of it. [Sg_raised] is an error published by
    [tx_error.send_replace] (:142) that the node has not yet collected;
    [Sg_seen] is one it has collected through [get_error] (:358-363), which is
    the only way the node ever learns of a background failure. *)
type signal = Sg_clean | Sg_raised | Sg_seen

(** Total order index for {!signal}. *)
let signal_index = function Sg_clean -> 0 | Sg_raised -> 1 | Sg_seen -> 2

(** Total order on {!signal}. *)
let signal_compare a b = Int.compare (signal_index a) (signal_index b)

(** Publish an error on the watch. [send_replace] overwrites, so a second
    failure is indistinguishable from the first and an already-observed error
    stays observed (the node short-circuits at :368 before sending again). *)
let raise_signal = function
  | Sg_clean -> Sg_raised
  | Sg_raised -> Sg_raised
  | Sg_seen -> Sg_seen

(** Whether the peer [w] holds this epoch's second output, i.e. whether the
    node already streamed those bytes out over
    [ConsensusChain::get_partial_epoch_stream] (consensus.rs:587-602). *)
type holder = Hd_no | Hd_yes

(** Total order index for {!holder}. *)
let holder_index = function Hd_no -> 0 | Hd_yes -> 1

(** Total order on {!holder}. *)
let holder_compare a b = Int.compare (holder_index a) (holder_index b)

(** Did the reopen repair make the data file LONGER than it found it - the
    zero-extension the clamp at consensus_pack.rs:713-716 exists to prevent
    ([Pack::truncate] is [DataFile::set_len], which extends as readily as it
    truncates: archive/pack.rs:424-427, archive/data_file.rs:134-166). *)
type grew = Gr_no | Gr_yes

(** Total order index for {!grew}. *)
let grew_index = function Gr_no -> 0 | Gr_yes -> 1

(** Total order on {!grew}. *)
let grew_compare a b = Int.compare (grew_index a) (grew_index b)

(** Did the repair discard a position-index entry, i.e. lose an output the
    index had already committed to (consensus_pack.rs:696-699, :705-708). *)
type dropped = Dp_no | Dp_yes

(** Total order index for {!dropped}. *)
let dropped_index = function Dp_no -> 0 | Dp_yes -> 1

(** Total order on {!dropped}. *)
let dropped_compare a b = Int.compare (dropped_index a) (dropped_index b)

(** Was the batch digest index's tracked length still above the bare header
    when the repair started - the [batch_final > DATA_HEADER_BYTES as u64]
    guard of consensus_pack.rs:675. Below it, phase A falls through to the
    [else if consensus_final > DATA_HEADER_BYTES] branch at :677 and truncates
    to a length that is NOT bounded by the surviving data, which is the one
    reachable way the pristine repair grows a file. *)
type bguard = Bg_below | Bg_above

(** Total order index for {!bguard}. *)
let bguard_index = function Bg_below -> 0 | Bg_above -> 1

(** Total order on {!bguard}. *)
let bguard_compare a b = Int.compare (bguard_index a) (bguard_index b)

(** The pack's lifecycle position. The three post-crash phases are terminal:
    the family is about one open decision, not a sequence of them. *)
type phase =
  | Ph_run  (** the append thread is live ([run_pack_loop], :132-193) *)
  | Ph_down  (** the process died; the four files sit at rest *)
  | Ph_healed  (** reopened with [open_append]/[open_append_exists]: the
                   repair of :664-728 has run *)
  | Ph_static  (** reopened with [open_static] (:862-904): the agreement gate
                   let the pack through and it may now be served *)

(** Total order index for {!phase}. *)
let phase_index = function
  | Ph_run -> 0
  | Ph_down -> 1
  | Ph_healed -> 2
  | Ph_static -> 3

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The joint global state: the four file lengths, the writer's latch and
    signal, the peer's possession, the lifecycle phase and the three
    heal-outcome markers (which are [Gr_no]/[Dp_no]/[Bg_below] outside
    {!Ph_healed}). *)
type state = {
  plen : len;  (** [Pack::file_len] (archive/pack.rs:209-212) *)
  ctrack : len;  (** [consensus_digests.data_file_length()] (:648) *)
  btrack : len;  (** [batch_digests.data_file_length()] (:649) *)
  pidx : pidx;  (** [consensus_pos_idx.len()] *)
  latch : latch;  (** [PackInner.failed] *)
  signal : signal;  (** the error watch plus what [V0] read from it *)
  holder : holder;  (** whether [w] holds output 2's bytes *)
  phase : phase;
  grew : grew;  (** the repair extended the data file *)
  dropped : dropped;  (** the repair discarded an indexed output *)
  bguard : bguard;  (** the batch index still tracked a real length *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = len_compare s1.plen s2.plen in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = len_compare s1.ctrack s2.ctrack in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = len_compare s1.btrack s2.btrack in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = pidx_compare s1.pidx s2.pidx in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = latch_compare s1.latch s2.latch in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = signal_compare s1.signal s2.signal in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = holder_compare s1.holder s2.holder in
              if Bool.not (Int.equal c6 0) then c6
              else
                let c7 = phase_compare s1.phase s2.phase in
                if Bool.not (Int.equal c7 0) then c7
                else
                  let c8 = grew_compare s1.grew s2.grew in
                  if Bool.not (Int.equal c8 0) then c8
                  else
                    let c9 = dropped_compare s1.dropped s2.dropped in
                    if Bool.not (Int.equal c9 0) then c9
                    else bguard_compare s1.bguard s2.bguard

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    [View_node_run] is what the pack's owner can actually observe while the
    background thread is alive: the collected error signal and the number of
    outputs the position index has committed to
    ([contains_consensus_header_number], consensus_pack.rs:1070-1072). It does
    NOT carry [plen], [ctrack], [btrack] or [latch]: no API on
    [ConsensusPack] exposes the data-file length or the [failed] flag.

    [View_node_down] is the blank view of a dead process.

    [View_node_open_*] are what the owner sees after a reopen: the four
    lengths, which it can read back. They do NOT carry [grew] or [dropped] -
    [trunc_and_heal] reports neither (consensus_pack.rs:665-670, it returns
    [Result<(), PackError>] and the only trace it leaves is the trimmed files
    themselves).

    [View_peer] is the remote holder's own possession and nothing else: the
    epoch-pack stream is one-directional bytes with no receipt back
    (consensus.rs:587-602). *)
type view =
  | View_idle  (** the constant blank view of the non-agents [V2]..[V9] *)
  | View_peer of holder
  | View_node_down
  | View_node_run of signal * pidx
  | View_node_healed of len * len * len * pidx
  | View_node_static of len * len * len * pidx

(** Total order index for {!view}. *)
let view_index = function
  | View_idle -> 0
  | View_peer _ -> 1
  | View_node_down -> 2
  | View_node_run _ -> 3
  | View_node_healed _ -> 4
  | View_node_static _ -> 5

(** Total order on the running node's view payload. *)
let view_run_compare (s1, p1) (s2, p2) =
  let c = signal_compare s1 s2 in
  if Bool.not (Int.equal c 0) then c else pidx_compare p1 p2

(** Total order on a reopened pack's four visible lengths. *)
let view_files_compare (a1, b1, c1, n1) (a2, b2, c2, n2) =
  let c = len_compare a1 a2 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1' = len_compare b1 b2 in
    if Bool.not (Int.equal c1' 0) then c1'
    else
      let c2' = len_compare c1 c2 in
      if Bool.not (Int.equal c2' 0) then c2' else pidx_compare n1 n2

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | ( View_idle,
      ( View_peer _ | View_node_down | View_node_run _ | View_node_healed _
      | View_node_static _ ) ) ->
      -1
  | ( ( View_peer _ | View_node_down | View_node_run _ | View_node_healed _
      | View_node_static _ ),
      View_idle ) ->
      1
  | View_peer h1, View_peer h2 -> holder_compare h1 h2
  | ( View_peer _,
      (View_node_down | View_node_run _ | View_node_healed _ | View_node_static _)
    ) ->
      -1
  | ( ( View_node_down | View_node_run _ | View_node_healed _
      | View_node_static _ ),
      View_peer _ ) ->
      1
  | View_node_down, View_node_down -> 0
  | View_node_down, (View_node_run _ | View_node_healed _ | View_node_static _)
    ->
      -1
  | (View_node_run _ | View_node_healed _ | View_node_static _), View_node_down
    ->
      1
  | View_node_run (g1, q1), View_node_run (g2, q2) ->
      view_run_compare (g1, q1) (g2, q2)
  | View_node_run _, (View_node_healed _ | View_node_static _) -> -1
  | (View_node_healed _ | View_node_static _), View_node_run _ -> 1
  | View_node_healed (a1, b1, c1, n1), View_node_healed (a2, b2, c2, n2) ->
      view_files_compare (a1, b1, c1, n1) (a2, b2, c2, n2)
  | View_node_healed _, View_node_static _ -> -1
  | View_node_static _, View_node_healed _ -> 1
  | View_node_static (a1, b1, c1, n1), View_node_static (a2, b2, c2, n2) ->
      view_files_compare (a1, b1, c1, n1) (a2, b2, c2, n2)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. [V0] owns the pack and [V1] is the remote holder [w];
    [V2]..[V9] are idle non-agents with the constant blank view and never
    appear under [K]. *)
let view v s =
  match v with
  | Validator.V0 -> (
      match s.phase with
      | Ph_run -> View_node_run (s.signal, s.pidx)
      | Ph_down -> View_node_down
      | Ph_healed -> View_node_healed (s.plen, s.ctrack, s.btrack, s.pidx)
      | Ph_static -> View_node_static (s.plen, s.ctrack, s.btrack, s.pidx))
  | Validator.V1 -> View_peer s.holder
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_shrink_clamp
      (** delete [let new_pack_len = new_pack_len.min(pack_len);]
          (crates/storage/src/consensus_pack.rs:716), so the repair's phase-B
          walk-back writes its raw [output_end] straight into
          [data.truncate] (:717-719). That ADDS a heal transition which
          zero-extends the pack to a stale position-index entry's claimed end
          instead of leaving the surviving bytes alone. No sibling path
          repairs it: [Pack::truncate] is [DataFile::set_len], documented
          "truncating or extending" with no shrink-only assertion
          (archive/pack.rs:424-427, archive/data_file.rs:134-166) - the
          neighbouring [PositionIndex::truncate_to_index] DOES carry exactly
          such a defensive guard (position_index/index.rs:227-233) but it
          protects the .pdx file, not the data file; [files_consistent] is
          called only from [open_static] (:894) and never on either append
          path (:809-814, :852-857); and the repair's own epilogue then
          BLESSES the new length by writing it into both digest indexes
          (:721-726), so a later [open_static] sees three agreeing files.
          Downstream, the extension re-enables the [pos < self.data.file_len()]
          guards (:1080-1084, :1097-1099, :1240-1244, :1254-1256) for records
          that do not exist; the per-record CRC (archive/pack.rs:346-365) only
          fires on a read that actually reaches the zero region. Pins S1. *)
  | No_static_consistency_gate
      (** delete the [if !Self::files_consistent(..) { return
          Err(PackError::CorruptPack); }] block
          (crates/storage/src/consensus_pack.rs:894-902), so a read-only open
          succeeds on a pack whose data length disagrees with either digest
          index's tracked length or with the last position-index entry's
          [output_end]. That ADDS an [open_static] transition out of every
          damaged at-rest configuration. No sibling path repairs it for the
          consumers this statement is about: [ConsensusChain::get_static]
          caches the opened pack with no further validation
          (consensus.rs:1067-1088) and is the entry point of a dozen read
          paths (consensus.rs:450, 549, 593, 762, 800, 839, 869, 906, 968,
          984, 1000, 1037); [get_partial_epoch_stream] (consensus.rs:587-602)
          resolves an [output_end] and streams the prefix with no completeness
          check at all; and the per-record CRC (archive/pack.rs:346-365)
          cannot see a record the indexes never learned about. The ONE partial
          sibling is [get_epoch_stream] (consensus.rs:543-576), which
          additionally requires the pack's latest header to match the epoch
          record - that repairs the full-epoch-stream consumer only, and this
          statement is about the open itself, which every other consumer
          trusts. Pins S2. *)
  | No_write_failure_latch
      (** delete the [AppendError::WriteDataError(_io_err) => self.failed =
          true] arm (crates/storage/src/archive/pack.rs:269), so a torn data
          write leaves the pack unlatched. That REMOVES the [Lt_failed]
          successor of a torn save, collapsing the torn and index-error
          routes into one. No sibling path re-establishes the latch:
          [run_pack_loop] owns [inner] for the life of the thread and never
          rebuilds it on error (consensus_pack.rs:132-193,
          certificate_pack.rs:53-86), [DataFile::write] has no latch of its
          own (archive/data_file.rs:334-358), and [Drop for PackInner] turns
          [commit] into a no-op precisely BECAUSE of this flag
          (archive/pack.rs:175-179, :299-301). Two genuine repairs of the
          neighbouring INTERLEAVING hazard do exist and are modelled rather
          than omitted - the caller short-circuits on the watch before it ever
          sends again ([save_consensus_output], :367-368) and the pack refuses
          any output whose number is not the next one ([save_consensus_output],
          :1034-1043) - which is exactly why S3 claims only the epistemic
          content of the latch and not "no record follows a torn one". The
          repair across a restart (a fresh [PackInner] has [failed: false],
          archive/pack.rs:202) is modelled too, as the crash erasing the
          latch. Pins S3. *)

(** Damage a crash can do to the four files. Each pattern is a real window in
    [Inner::persist], which commits the data first and then syncs the position
    index, the consensus digests and the batch digests in that order
    (consensus_pack.rs:1126-1134); ordinary saves never fsync at all
    ([flush_data], :1137-1142, is flush-without-sync), so any of the four can
    be behind after a power loss. *)
type damage =
  | Dm_clean  (** a clean shutdown: [PackMessage::Shutdown] persisted (:184-187) *)
  | Dm_data_tail  (** the last record's bytes were never fsynced and are lost *)
  | Dm_data_all  (** the whole unsynced data tail is lost *)
  | Dm_index_tail
      (** the index tail is lost: the position index and both tracked lengths
          fall back one record, the shape the restart test at
          consensus.rs:1554-1560 constructs *)
  | Dm_data_and_batch
      (** the data tail is lost AND the batch digest index is back at the bare
          header, the shape produced by a crash between
          [consensus_digests.sync()] and [batch_digests.sync()]
          (consensus_pack.rs:1130-1131) on a pack whose batch index had not
          yet been written *)

(** Every damage pattern, for the crash transition's fan-out. *)
let all_damage =
  [ Dm_clean; Dm_data_tail; Dm_data_all; Dm_index_tail; Dm_data_and_batch ]

(** Apply one damage pattern to the four at-rest lengths. *)
let apply_damage d (p, c, b, n) =
  match d with
  | Dm_clean -> (p, c, b, n)
  | Dm_data_tail -> (pred_len p, c, b, n)
  | Dm_data_all -> (L0, c, b, n)
  | Dm_index_tail -> (p, pred_len c, pred_len b, pred_pidx n)
  | Dm_data_and_batch -> (pred_len p, c, L0, n)

(** The first half of [Inner::files_consistent] (consensus_pack.rs:647-652):
    the data length equals BOTH digest indexes' tracked lengths. This is the
    half the repair's epilogue re-establishes unconditionally (:721-726). *)
let digest_lengths_match s =
  Int.equal 0 (len_compare s.plen s.ctrack)
  && Int.equal 0 (len_compare s.plen s.btrack)

(** [Inner::files_consistent] in full (consensus_pack.rs:640-662): the digest
    halves plus - unless the position index is empty - the last entry's
    [output_end]. *)
let files_agree s =
  digest_lengths_match s
  && (match s.pidx with
     | P0 -> true
     | P1 | P2 -> Int.equal 0 (len_compare (pidx_end s.pidx) s.plen))

(** Phase A of the repair (consensus_pack.rs:671-685): if the data file is
    longer than either tracked length, truncate to the smaller surviving
    tracked length - but only through guards that both require the chosen
    length to be above the bare header. When [batch_final] is AT the header
    the first branch is skipped and the second truncates to [consensus_final]
    with nothing bounding it by the data we actually have, which is the one
    way the pristine repair extends a file. *)
let heal_phase_a s =
  if len_lt s.ctrack s.plen || len_lt s.btrack s.plen then
    if len_lt s.btrack s.ctrack && len_lt L0 s.btrack then s.btrack
    else if len_lt L0 s.ctrack then s.ctrack
    else s.plen
  else s.plen

(** Phase B's walk-back (consensus_pack.rs:687-712): starting at the newest
    entry, step back to the newest one whose [output_end] fits inside the
    surviving data, keeping that many entries. If none fits, the candidate
    length is the FIRST entry's [output_end] - above the data by construction,
    which is what the clamp at :716 then has to catch - and the index is left
    as {!pidx_after_total_miss} says, which for a single-entry index is
    UNTOUCHED because both truncations are guarded by [idx != start_idx]. *)
let heal_walk_back p plen =
  let fits = List.filter (fun (_, e) -> len_le e plen) (pidx_entries p) in
  match fits with
  | (j, e) :: _ -> (j, e)
  | [] -> (pidx_after_total_miss p, pidx_first_end p)

(** The shrink clamp of consensus_pack.rs:713-716, and its deletion. *)
let clamp_new_len mut raw plen =
  match mut with
  | Pristine | No_static_consistency_gate | No_write_failure_latch ->
      min_len raw plen
  | No_shrink_clamp -> raw

(** Whether a torn data write latches the pack shut (archive/pack.rs:269). *)
let latch_after_tear mut =
  match mut with
  | Pristine | No_shrink_clamp | No_static_consistency_gate -> Lt_failed
  | No_write_failure_latch -> Lt_ok

(** Whether [open_static] admits this at-rest configuration
    (consensus_pack.rs:894-902). *)
let static_admits mut s =
  match mut with
  | Pristine | No_shrink_clamp | No_write_failure_latch -> files_agree s
  | No_static_consistency_gate -> true

(** [Inner::trunc_and_heal] end to end (consensus_pack.rs:664-728): phase A,
    then the clamped walk-back, then the epilogue that writes the healed
    length into both digest indexes (:721-726). *)
let heal mut s =
  let pre = s.plen in
  let after_a = heal_phase_a s in
  let entries_left, new_len =
    match s.pidx with
    | P0 -> (P0, after_a)
    | P1 | P2 ->
        let j, raw = heal_walk_back s.pidx after_a in
        (j, clamp_new_len mut raw after_a)
  in
  {
    plen = new_len;
    ctrack = new_len;
    btrack = new_len;
    pidx = entries_left;
    latch = Lt_ok;
    signal = Sg_clean;
    holder = s.holder;
    phase = Ph_healed;
    grew = (if len_lt pre new_len then Gr_yes else Gr_no);
    dropped =
      (if Int.equal 0 (pidx_compare entries_left s.pidx) then Dp_no else Dp_yes);
    bguard = (if len_lt L0 s.btrack then Bg_above else Bg_below);
  }

(** Is the position index caught up with the data file - the precondition the
    consensus-number check enforces (consensus_pack.rs:1034-1043): an output
    whose index is not exactly [consensus_pos_idx.len()] is refused before a
    single byte is written. *)
let index_caught_up s = Int.equal 0 (len_compare (pidx_end s.pidx) s.plen)

(** Can the pack accept another output. Three independent gates say no after a
    failure: the caller short-circuits on the watch (:367-368), the pack
    refuses an out-of-order number (:1034-1043), and a latched [PackInner]
    refuses the append itself (archive/pack.rs:262-263). A refused save
    changes no file and re-publishes an error the watch already holds, so it
    is a self-loop and is omitted rather than modelled as a transition. *)
let can_save s =
  (match s.latch with Lt_ok -> true | Lt_failed -> false)
  && index_caught_up s
  && Bool.not (Int.equal 0 (len_compare s.plen L2))

(** The four outcomes of one [save_consensus_output] the thread processes
    (consensus_pack.rs:1018-1067).

    + It lands: data appended (:1048-1051), digests and position index saved
      (:1056-1062), both tracked lengths advanced (:1063-1064).
    + Its data append tears mid-record: the [?] at :1051 (or at :1003 inside
      the batch loop) returns before any index is touched, and the
      [AppendError::WriteDataError] arm latches the pack
      (archive/pack.rs:269). The tracked lengths stay where the previous save
      left them.
    + The data lands and an index save fails with the tracked lengths still
      behind - the digest save at :1056-1058 on an output with no batches, so
      the batch loop's :1010-1012 never ran. Published on the same watch and
      NOT latching, because [IndexAppend] is not [AppendError::WriteDataError]
      (archive/pack.rs:270-274).
    + The data lands and the POSITION index save fails at :1060-1062 after the
      batch loop already advanced both tracked lengths at :1010-1012, so the
      digests are caught up with the data and only the position index is
      short. Also non-latching, and it leaves a different at-rest shape, so it
      is a separate successor rather than a duplicate of the previous one. *)
let save_steps mut s =
  if can_save s then
    [
      {
        s with
        plen = succ_len s.plen;
        ctrack = succ_len s.plen;
        btrack = succ_len s.plen;
        pidx = succ_pidx s.pidx;
      };
      {
        s with
        plen = succ_len s.plen;
        latch = latch_after_tear mut;
        signal = raise_signal s.signal;
      };
      { s with plen = succ_len s.plen; signal = raise_signal s.signal };
      {
        s with
        plen = succ_len s.plen;
        ctrack = succ_len s.plen;
        btrack = succ_len s.plen;
        signal = raise_signal s.signal;
      };
    ]
  else []

(** Streaming this epoch's prefix to the peer [w]
    ([ConsensusChain::get_partial_epoch_stream], consensus.rs:587-602). It
    needs the output resolvable in the position index (:594) and flushes the
    data first (:598), so it is enabled only once output 2 is both written and
    indexed. *)
let serve_steps s =
  match (s.pidx, s.holder) with
  | P2, Hd_no ->
      if Int.equal 0 (len_compare s.plen L2) then [ { s with holder = Hd_yes } ]
      else []
  | P2, Hd_yes -> []
  | (P0 | P1), (Hd_no | Hd_yes) -> []

(** The node collecting a published error ([get_error], consensus_pack.rs:
    356-363, called at the head of every request at :368, :378). *)
let read_steps s =
  match s.signal with
  | Sg_raised -> [ { s with signal = Sg_seen } ]
  | Sg_clean | Sg_seen -> []

(** The process dying. The in-memory latch and the watch die with it (both are
    fields of structures the thread owns), the files keep whatever survived,
    and the peer keeps whatever it was already sent. *)
let crash_steps s =
  List.map
    (fun d ->
      let p, c, b, n = apply_damage d (s.plen, s.ctrack, s.btrack, s.pidx) in
      {
        plen = p;
        ctrack = c;
        btrack = b;
        pidx = n;
        latch = Lt_ok;
        signal = Sg_clean;
        holder = s.holder;
        phase = Ph_down;
        grew = Gr_no;
        dropped = Dp_no;
        bguard = Bg_below;
      })
    all_damage

(** The reopen decision: append mode always opens and repairs
    (consensus_pack.rs:809-814, :852-857), read-only mode opens only if the
    agreement gate lets it (:894-902). *)
let open_steps mut s =
  heal mut s :: (if static_admits mut s then [ { s with phase = Ph_static } ] else [])

(** The transition relation: the writer runs, crashes, and the files are
    reopened exactly once. *)
let next_with mut s =
  match s.phase with
  | Ph_run -> save_steps mut s @ serve_steps s @ read_steps s @ crash_steps s
  | Ph_down -> open_steps mut s
  | Ph_healed -> []
  | Ph_static -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: a freshly created epoch pack, header and [EpochMeta]
    only, both digest indexes seeded to that length
    (consensus_pack.rs:802-807), nothing served. *)
let initial =
  {
    plen = L0;
    ctrack = L0;
    btrack = L0;
    pidx = P0;
    latch = Lt_ok;
    signal = Sg_clean;
    holder = Hd_no;
    phase = Ph_run;
    grew = Gr_no;
    dropped = Dp_no;
    bguard = Bg_below;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Heal_ran  (** the pack was reopened for append, so [trunc_and_heal] ran *)
  | Heal_extended
      (** the repair left the data file LONGER than it found it *)
  | Heal_dropped_output
      (** the repair discarded a position-index entry, i.e. an output the
          index had committed to is gone *)
  | Batch_index_survived
      (** the batch digest index still tracked a length above the bare header
          when the repair started (the [batch_final > DATA_HEADER_BYTES] guard
          of consensus_pack.rs:675) *)
  | Peer_holds_epoch_bytes
      (** the peer [w] was streamed this epoch's second output *)
  | Static_open_served
      (** the pack was opened read-only and may now be served to peers *)
  | Files_agree
      (** [files_consistent] holds of the current four files (:640-662) *)
  | Digest_lengths_match
      (** the data length equals both digest indexes' tracked lengths - the
          half of [files_consistent] the repair's epilogue restores
          unconditionally (:647-652 checked, :721-726 restored) *)
  | Error_seen
      (** the node has collected a published [PackError] off the watch *)
  | Data_ahead_of_index
      (** the data file holds bytes past the last indexed record's
          [output_end] - the hidden condition the [pos < file_len] guards at
          :1081, :1097, :1241, :1254 exist for *)
  | Pack_latched  (** [PackInner.failed] is set (archive/pack.rs:165, :269) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Heal_ran -> (
      match s.phase with
      | Ph_healed -> true
      | Ph_run | Ph_down | Ph_static -> false)
  | Heal_extended -> ( match s.grew with Gr_yes -> true | Gr_no -> false)
  | Heal_dropped_output -> (
      match s.dropped with Dp_yes -> true | Dp_no -> false)
  | Batch_index_survived -> (
      match s.bguard with Bg_above -> true | Bg_below -> false)
  | Peer_holds_epoch_bytes -> (
      match s.holder with Hd_yes -> true | Hd_no -> false)
  | Static_open_served -> (
      match s.phase with
      | Ph_static -> true
      | Ph_run | Ph_down | Ph_healed -> false)
  | Files_agree -> files_agree s
  | Digest_lengths_match -> digest_lengths_match s
  | Error_seen -> (
      match s.signal with
      | Sg_seen -> true
      | Sg_clean | Sg_raised -> false)
  | Data_ahead_of_index -> len_lt (pidx_end s.pidx) s.plen
  | Pack_latched -> ( match s.latch with Lt_failed -> true | Lt_ok -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Heal_ran -> "heal_ran"
  | Heal_extended -> "heal_extended"
  | Heal_dropped_output -> "heal_dropped(n)"
  | Batch_index_survived -> "batch_final > header"
  | Peer_holds_epoch_bytes -> "holds(w, n)"
  | Static_open_served -> "open_static_ok"
  | Files_agree -> "files_consistent"
  | Digest_lengths_match -> "digest_lengths_match"
  | Error_seen -> "error_seen(v)"
  | Data_ahead_of_index -> "data_ahead_of_index"
  | Pack_latched -> "pack_latched"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} by
    test/t_archive_pack_heal_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
