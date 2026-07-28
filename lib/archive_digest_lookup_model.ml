(** Finite interpreted system for the ARCHIVE_DIGEST_LOOKUP family: the
    by-digest read pipeline of the consensus archive, from the in-memory bloom
    filter at the front, through the hash-bucket lookup and the file-length
    bounds test in the middle, to the digest recheck at the end, and out onto
    the wire where the requesting worker re-validates what it received. File
    citations refer to Telcoin-Association/telcoin-network at 0c59c15b (working
    tree).

    THE PIPELINE, stage by stage, with the site each stage is abstracted from:

    - [HdxIndex::load] consults the in-memory bloom filter FIRST and returns
      [FetchError::NotFound] without touching a bucket when the filter says
      absent; only if the filter admits does it run the authoritative bucket
      scan [fetch_position] (archive/digest_index/index.rs:775-782,
      :612-647). The single writer of a bloom bit is [Index::save]
      (:762-772, the [self.bloom.accrue(key)] at :770); [Bloom::contains] is
      a conjunction over the bit positions [Bloom::accrue] sets, and there is
      no clear or delete (archive/digest_index/bloom.rs:65-95). The filter is
      persisted beside the header by [write_header] (:449-454) and reloaded
      from disk on open - it is NEVER recomputed from the buckets (:363-366).
    - [ConsensusPack::Inner::contains_batch] answers a possession question
      from the index answer and ONE bounds test, and never reads the data
      file: [if let Ok(pos) = self.batch_digests.load(digest) { pos <
      self.data.file_len() } else { false }] (consensus_pack.rs:1236-1245).
    - [ConsensusPack::Inner::batch] adds two gates the advertisement does not
      have: the same bounds test as an early return (:1249-1256) and then,
      after the fetch, the content recheck [if batch.digest() != digest {
      return None; }] (:1257-1263). The identical asymmetric pair exists for
      consensus headers (:1076-1085 vs :1088-1108) and for certificates
      (certificate_pack.rs:291-297 vs :299-312).
    - The pack service is ONE thread draining [PackMessage] sequentially
      ([run_pack_loop] :132-192, [ContainsBatch] :172-174, [Batch] :175-177),
      which is why the model freezes the archive for the duration of an
      exchange. That freeze is the one modelling assumption S1's [AF] leans
      on: it is what makes a single exchange atomic with respect to appends
      and repairs. It applies identically to the pristine and the mutated
      runs, so the pin it supports is not an artefact of it.
    - On the wire, [get_batches] hands the archive's answers back with no
      digest comparison at the storage boundary (consensus.rs:1031-1045,
      trait types/src/consensus_chain_traits.rs:119-123), the responder
      streams them ([get_batches_local], worker/src/batch_fetcher.rs:73-111,
      used by network/stream_codec.rs:108 and :171), and the REQUESTER
      re-hashes every batch it reads and rejects the WHOLE exchange when one
      was not requested: [let batch_digest = batch.digest(); if
      !requested_digests.contains(&batch_digest) { return
      Err(NetworkError::ProtocolError(...)) }]
      (worker/src/network/handle.rs:754-761). The purely local path re-keys
      the same way ([fetched_batches.extend(local_batches.into_iter().map(|b|
      (b.digest(), b)))] then [missing_digests.retain(...)],
      batch_fetcher.rs:229-232).

    WHY THE RECYCLED OFFSET IS REACHABLE. The repair path truncates the data
    file and deliberately leaves the digest indexes alone: "Note we leave the
    digest indexes with potentially some missing digests. This should be OK
    since they will have to be overwritten with same digests when they are
    readded and lookups should handle this" (consensus_pack.rs:680-684).
    [contains_batch]'s own comment names the resulting state - "in a very rare
    case of repairing a damaged pack we might have something in the index not
    in the pack file (yet)" (:1237-1239) - and [batch]'s recheck comment names
    the next one - "a repaired DB could write a new batch to the same location
    as an old batch" (:1258-1260). There is no repair for that: the index has
    no delete API at all ([Index for HdxIndex] exposes save/load/sync only,
    index.rs:761-797), nothing anywhere rebuilds an index from the data file
    ([validate_pack_file] opens the data file read-only, reports issues and
    never touches the hdx/pdx sidecars, pack_validate.rs:183-238), and a
    duplicate key simply overwrites the stored position in place ("We just
    overwrite a duplicate.", index.rs:695-700). The per-record CRC validates
    whichever record occupies the offset just as happily as the right one
    (archive/pack.rs:346-365).

    COMPONENTS. Three modelled payloads over two offsets: [Rec_d] (the
    preimage of digest d) and [Rec_e] (the preimage of a different digest e)
    compete for offset p0, and [Rec_g] (the preimage of digest g) lives at
    offset p1. [live] is the pack's tracked length as a count of readable
    records, so "pos < file_len" is [entry_in_bounds]. [idx_d], [idx_e],
    [idx_g] are the digest index's bucket entries, which survive a repair.
    [bit_x] and [bit_y] are bloom bit positions: d accrues {x,y}, e and g
    accrue {y}, and the never-saved probe digest q needs {y} alone - q's bit
    set is a strict subset of d's, the minimal faithful witness of the
    union-coverage that produces a real false positive in a filter whose
    [contains] is a conjunction over 8 positions per item. [healed] records
    that the single modelled repair episode has happened. [exch] is one
    request/response round of the batch fetcher: ask, then the archive's local
    [contains] advertisement, then the archive's fetch and the requester's
    validation of what came back.

    ROLE MAPPING (knowledge agents must have a real, non-constant view; idle
    validators carry the blank view and never appear under K):
    - V0 is the ARCHIVE node. Its view is exactly the two values the answering
      procedures read before they answer: the digest index's answer for d
      ([load] - the bloom verdict composed with the bucket entry) and the
      pack's file length, plus its own trace of the exchange (what it
      advertised and which slots its fetch filled). V0 does NOT see the bytes
      at an offset it has not fetched - reading them is precisely what
      [batch()] does - and it cannot tell a served preimage from a served
      substitute, because telling them apart is the very comparison
      :1261-1263 makes.
    - V1 is the REQUESTING worker. Its view is its request phase and the set
      of batches its own digest validation kept. It does NOT see V0's pack,
      index, bloom, offsets or repair history, and it cannot see V0's internal
      [contains] advertisement at all ([contains_current_batch] is a local
      API, consensus.rs:1026-1028): the advertise step leaves V1 waiting.
    - V2..V9 are idle: constant blank view, never under K. *)

(** The byte content of one modelled offset. [Vacant] is "no readable record
    here" (either never written, or truncated away by the repair). *)
type cell =
  | Vacant  (** nothing readable at this offset *)
  | Rec_d  (** the preimage of digest d *)
  | Rec_e  (** the preimage of digest e - the record that recycles p0 *)
  | Rec_g  (** the preimage of digest g *)

(** Total order index for {!cell}. *)
let cell_index = function Vacant -> 0 | Rec_d -> 1 | Rec_e -> 2 | Rec_g -> 3

(** Total order on {!cell}. *)
let cell_compare a b = Int.compare (cell_index a) (cell_index b)

(** [true] iff this cell holds d's preimage. *)
let cell_is_d = function Rec_d -> true | Vacant | Rec_e | Rec_g -> false

(** [true] iff this cell holds g's preimage. *)
let cell_is_g = function Rec_g -> true | Vacant | Rec_d | Rec_e -> false

(** [true] iff this cell holds a readable record at all. *)
let cell_is_record = function
  | Vacant -> false
  | Rec_d | Rec_e | Rec_g -> true

(** The pack's tracked data-file length, as a count of readable records:
    [L0] holds neither offset, [L1] holds p0, [L2] holds p0 and p1. This is
    [Pack::file_len] (archive/pack.rs:210-212) as consumed by the
    [pos < self.data.file_len()] tests. *)
type live =
  | L0  (** file_len covers no modelled record *)
  | L1  (** file_len covers p0 only *)
  | L2  (** file_len covers p0 and p1 *)

(** Total order index for {!live}. *)
let live_index = function L0 -> 0 | L1 -> 1 | L2 -> 2

(** Total order on {!live}. *)
let live_compare a b = Int.compare (live_index a) (live_index b)

(** [true] iff offset p0 is inside the data file. *)
let live_covers_p0 = function L0 -> false | L1 | L2 -> true

(** [true] iff offset p1 is inside the data file. *)
let live_covers_p1 = function L0 | L1 -> false | L2 -> true

(** A digest index bucket entry: absent, or the stored record position. A
    repair never removes one (consensus_pack.rs:680-684) and there is no
    delete API (index.rs:761-797). *)
type entry =
  | No_entry  (** no bucket element carries this key *)
  | At_p0  (** the stored position is offset p0 *)
  | At_p1  (** the stored position is offset p1 *)

(** Total order index for {!entry}. *)
let entry_index = function No_entry -> 0 | At_p0 -> 1 | At_p1 -> 2

(** Total order on {!entry}. *)
let entry_compare a b = Int.compare (entry_index a) (entry_index b)

(** [true] iff the bucket scan would return a position for this key. *)
let entry_present = function No_entry -> false | At_p0 | At_p1 -> true

(** The [pos < self.data.file_len()] test (consensus_pack.rs:1241 for the
    advertisement, :1254-1256 for the fetch's early return). *)
let entry_in_bounds e l =
  match e with
  | No_entry -> false
  | At_p0 -> live_covers_p0 l
  | At_p1 -> live_covers_p1 l

(** The answer [ConsensusPack::Inner::contains_batch] produced for digest d. *)
type adv =
  | Adv_yes  (** the archive advertised possession of d *)
  | Adv_no  (** the archive denied possession of d *)

(** Total order index for {!adv}. *)
let adv_index = function Adv_yes -> 0 | Adv_no -> 1

(** Total order on {!adv}. *)
let adv_compare a b = Int.compare (adv_index a) (adv_index b)

(** What the archive's fetch put in the d slot of its answer. *)
type d_slot =
  | D_nothing  (** [batch(d)] returned [None] *)
  | D_preimage  (** it returned d's preimage, as the contract requires *)
  | D_substitute
      (** it returned the record that now occupies d's indexed offset, which
          is NOT d's preimage - only reachable with the recheck deleted *)

(** The archive's answer to one two-digest request {d, g}. *)
type serve =
  | Serve_nothing  (** neither slot delivered a record *)
  | Serve_d  (** d's preimage only *)
  | Serve_sub  (** a substituted record in the d slot only *)
  | Serve_g  (** g's preimage only *)
  | Serve_d_g  (** both preimages *)
  | Serve_sub_g  (** a substituted record in the d slot, plus g's preimage *)

(** Total order index for {!serve}. *)
let serve_index = function
  | Serve_nothing -> 0
  | Serve_d -> 1
  | Serve_sub -> 2
  | Serve_g -> 3
  | Serve_d_g -> 4
  | Serve_sub_g -> 5

(** Total order on {!serve}. *)
let serve_compare a b = Int.compare (serve_index a) (serve_index b)

(** What the requester kept after re-hashing everything it read. A batch whose
    digest was not requested aborts the WHOLE exchange with a
    [ProtocolError], so nothing at all is kept (handle.rs:754-761). *)
type keep =
  | Keep_nothing  (** the exchange completed and delivered nothing *)
  | Keep_d  (** d's preimage was validated and kept *)
  | Keep_g  (** g's preimage was validated and kept *)
  | Keep_d_g  (** both were validated and kept *)
  | Keep_poisoned
      (** an unrequested digest arrived, so the exchange errored and NOTHING
          was kept - including the honestly served batches *)

(** Total order index for {!keep}. *)
let keep_index = function
  | Keep_nothing -> 0
  | Keep_d -> 1
  | Keep_g -> 2
  | Keep_d_g -> 3
  | Keep_poisoned -> 4

(** Total order on {!keep}. *)
let keep_compare a b = Int.compare (keep_index a) (keep_index b)

(** The requester's validation of an archive answer: the digest of every batch
    read is compared against the requested set, and one miss voids everything
    (handle.rs:754-761; the local path re-keys by [b.digest()] to the same
    effect, batch_fetcher.rs:229-232). *)
let keep_of = function
  | Serve_nothing -> Keep_nothing
  | Serve_d -> Keep_d
  | Serve_g -> Keep_g
  | Serve_d_g -> Keep_d_g
  | Serve_sub -> Keep_poisoned
  | Serve_sub_g -> Keep_poisoned

(** One request/response round of the batch fetcher over the digests {d, g}. *)
type exch =
  | X_idle  (** no request in flight; the archive may advance *)
  | X_asked  (** the requester sent {d, g} *)
  | X_advertised of adv  (** the archive answered [contains_batch(d)] *)
  | X_served of adv * serve
      (** the archive answered the fetch and the requester validated it *)

(** Total order index for {!exch}. *)
let exch_index = function
  | X_idle -> 0
  | X_asked -> 1
  | X_advertised _ -> 2
  | X_served (_, _) -> 3

(** Total order on {!exch}: every constructor pair is spelled, no wildcard
    arm. *)
let exch_compare a b =
  match (a, b) with
  | X_idle, X_idle -> 0
  | X_asked, X_asked -> 0
  | X_advertised x, X_advertised y -> adv_compare x y
  | X_served (ax, sx), X_served (ay, sy) ->
      let c = adv_compare ax ay in
      if Bool.not (Int.equal c 0) then c else serve_compare sx sy
  | ( (X_idle | X_asked | X_advertised _ | X_served _),
      (X_idle | X_asked | X_advertised _ | X_served _) ) ->
      Int.compare (exch_index a) (exch_index b)

(** The joint global state: the archive's two offsets, its tracked length, its
    three index entries, its two bloom bits, whether the single modelled
    repair episode has run, and the in-flight exchange. *)
type state = {
  cell0 : cell;  (** byte content at offset p0 *)
  cell1 : cell;  (** byte content at offset p1 *)
  live : live;  (** the pack's tracked data-file length *)
  idx_d : entry;  (** the digest index's bucket entry for d *)
  idx_e : entry;  (** the digest index's bucket entry for e *)
  idx_g : entry;  (** the digest index's bucket entry for g *)
  bit_x : bool;  (** bloom bit position x - accrued by d alone *)
  bit_y : bool;  (** bloom bit position y - accrued by d, e and g *)
  healed : bool;  (** the damaged-and-repaired episode has run *)
  exch : exch;  (** the in-flight request/response round *)
}

(** Total order index for a boolean field. *)
let flag_index = function true -> 1 | false -> 0

(** Total order on a boolean field. *)
let flag_compare a b = Int.compare (flag_index a) (flag_index b)

(** Total deterministic comparison over ALL ten state fields. *)
let state_compare a b =
  let c0 = cell_compare a.cell0 b.cell0 in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = cell_compare a.cell1 b.cell1 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = live_compare a.live b.live in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = entry_compare a.idx_d b.idx_d in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = entry_compare a.idx_e b.idx_e in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = entry_compare a.idx_g b.idx_g in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = flag_compare a.bit_x b.bit_x in
              if Bool.not (Int.equal c6 0) then c6
              else
                let c7 = flag_compare a.bit_y b.bit_y in
                if Bool.not (Int.equal c7 0) then c7
                else
                  let c8 = flag_compare a.healed b.healed in
                  if Bool.not (Int.equal c8 0) then c8
                  else exch_compare a.exch b.exch

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** [Bloom::contains] for digest d, a conjunction over d's two accrued bit
    positions {x, y} (bloom.rs:65-80). *)
let filter_admits_d s = Bool.( && ) s.bit_x s.bit_y

(** [Bloom::contains] for the probe digest q, whose single bit position {y} is
    a strict subset of d's {x, y} and is shared with e and g. q is never
    saved, so whenever y is set the filter admits a key the buckets do not
    hold - a false positive, eliminated by the authoritative scan. *)
let filter_admits_q s = s.bit_y

(** [HdxIndex::load] for digest d: the filter first, then the bucket scan
    (index.rs:775-782). *)
let lookup_ok_d s = Bool.( && ) (filter_admits_d s) (entry_present s.idx_d)

(** [HdxIndex::load] for digest g, whose accrued bit set is {y}. *)
let lookup_ok_g s = Bool.( && ) s.bit_y (entry_present s.idx_g)

(** The pack really holds d's preimage at a readable offset. Hidden from V0
    until it fetches, and never visible to V1. *)
let holds_d s = Bool.( && ) (live_covers_p0 s.live) (cell_is_d s.cell0)

(** The pack really holds g's preimage at a readable offset. *)
let holds_g s = Bool.( && ) (live_covers_p1 s.live) (cell_is_g s.cell1)

(** The byte content the index entry points at. *)
let record_at e s =
  match e with No_entry -> Vacant | At_p0 -> s.cell0 | At_p1 -> s.cell1

(** The index answer V0 observes for digest d - the only thing
    [contains_batch] learns about d before it answers. *)
type load_answer =
  | Load_missing  (** [load] returned [FetchError::NotFound] *)
  | Load_at_p0  (** [load] returned offset p0 *)
  | Load_at_p1  (** [load] returned offset p1 *)

(** Total order index for {!load_answer}. *)
let load_answer_index = function
  | Load_missing -> 0
  | Load_at_p0 -> 1
  | Load_at_p1 -> 2

(** Total order on {!load_answer}. *)
let load_answer_compare a b =
  Int.compare (load_answer_index a) (load_answer_index b)

(** What [load(d)] hands the caller. *)
let load_answer_of s =
  if lookup_ok_d s then
    match s.idx_d with
    | No_entry -> Load_missing
    | At_p0 -> Load_at_p0
    | At_p1 -> Load_at_p1
  else Load_missing

(** Which slots of its own answer the archive saw filled. A substituted record
    is indistinguishable from a preimage here: telling them apart is exactly
    the deleted comparison (consensus_pack.rs:1261-1263). *)
type served_by_v0 =
  | Sv_none  (** the fetch filled neither slot *)
  | Sv_d  (** the fetch returned a record for d *)
  | Sv_g  (** the fetch returned a record for g *)
  | Sv_dg  (** the fetch returned a record for both *)

(** Total order index for {!served_by_v0}. *)
let served_by_v0_index = function
  | Sv_none -> 0
  | Sv_d -> 1
  | Sv_g -> 2
  | Sv_dg -> 3

(** Total order on {!served_by_v0}. *)
let served_by_v0_compare a b =
  Int.compare (served_by_v0_index a) (served_by_v0_index b)

(** The archive's own reading of its answer. *)
let served_by_v0_of = function
  | Serve_nothing -> Sv_none
  | Serve_d -> Sv_d
  | Serve_sub -> Sv_d
  | Serve_g -> Sv_g
  | Serve_d_g -> Sv_dg
  | Serve_sub_g -> Sv_dg

(** V0's trace of the exchange: it sees the request, its own advertisement and
    which slots its fetch filled. *)
type v0_exch =
  | V0_idle  (** no request in flight *)
  | V0_asked  (** a request arrived *)
  | V0_adv of adv  (** it answered [contains_batch(d)] *)
  | V0_served of adv * served_by_v0  (** it answered the fetch *)

(** Total order index for {!v0_exch}. *)
let v0_exch_index = function
  | V0_idle -> 0
  | V0_asked -> 1
  | V0_adv _ -> 2
  | V0_served (_, _) -> 3

(** Total order on {!v0_exch}: every constructor pair spelled. *)
let v0_exch_compare a b =
  match (a, b) with
  | V0_idle, V0_idle -> 0
  | V0_asked, V0_asked -> 0
  | V0_adv x, V0_adv y -> adv_compare x y
  | V0_served (ax, sx), V0_served (ay, sy) ->
      let c = adv_compare ax ay in
      if Bool.not (Int.equal c 0) then c else served_by_v0_compare sx sy
  | ( (V0_idle | V0_asked | V0_adv _ | V0_served (_, _)),
      (V0_idle | V0_asked | V0_adv _ | V0_served (_, _)) ) ->
      Int.compare (v0_exch_index a) (v0_exch_index b)

(** V0's projection of the exchange. *)
let v0_exch_of = function
  | X_idle -> V0_idle
  | X_asked -> V0_asked
  | X_advertised a -> V0_adv a
  | X_served (a, sv) -> V0_served (a, served_by_v0_of sv)

(** V1's trace of the exchange. The archive's [contains] advertisement is a
    local API call (consensus.rs:1026-1028), so from V1's side the advertise
    step is indistinguishable from still waiting. *)
type v1_exch =
  | V1_idle  (** it has not asked *)
  | V1_waiting  (** it asked and has no answer yet *)
  | V1_answered of keep  (** it validated an answer and kept this much *)

(** Total order index for {!v1_exch}. *)
let v1_exch_index = function
  | V1_idle -> 0
  | V1_waiting -> 1
  | V1_answered _ -> 2

(** Total order on {!v1_exch}: every constructor pair spelled. *)
let v1_exch_compare a b =
  match (a, b) with
  | V1_idle, V1_idle -> 0
  | V1_waiting, V1_waiting -> 0
  | V1_answered x, V1_answered y -> keep_compare x y
  | ( (V1_idle | V1_waiting | V1_answered _),
      (V1_idle | V1_waiting | V1_answered _) ) ->
      Int.compare (v1_exch_index a) (v1_exch_index b)

(** V1's projection of the exchange. *)
let v1_exch_of = function
  | X_idle -> V1_idle
  | X_asked -> V1_waiting
  | X_advertised _ -> V1_waiting
  | X_served (_, sv) -> V1_answered (keep_of sv)

(** A validator's local view.

    [View_archive] is V0's: the index answer for d, the pack's file length,
    and its own exchange trace - exactly the inputs of [contains_batch]
    (consensus_pack.rs:1236-1245) plus what it answered. It carries NO cell
    contents: the bytes at an offset are readable only by fetching, and a
    substitute is indistinguishable from a preimage without the recheck.

    [View_requester] is V1's: its request phase and the batches its own digest
    validation kept (handle.rs:754-761). Nothing of V0's disk appears in it.

    [View_idle] is the constant blank view of the non-agents V2..V9. *)
type view =
  | View_archive of load_answer * live * v0_exch
  | View_requester of v1_exch
  | View_idle

(** Total deterministic order over ALL fields of V0's view. *)
let view_archive_compare (la, lva, xa) (lb, lvb, xb) =
  let c = load_answer_compare la lb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = live_compare lva lvb in
    if Bool.not (Int.equal c1 0) then c1 else v0_exch_compare xa xb

(** Total order on views: [View_idle] < [View_archive] < [View_requester],
    with the field-wise order within each constructor. Every constructor pair
    is spelled: no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_archive (_, _, _) | View_requester _) -> -1
  | (View_archive (_, _, _) | View_requester _), View_idle -> 1
  | View_archive (la, lva, xa), View_archive (lb, lvb, xb) ->
      view_archive_compare (la, lva, xa) (lb, lvb, xb)
  | View_archive (_, _, _), View_requester _ -> -1
  | View_requester _, View_archive (_, _, _) -> 1
  | View_requester xa, View_requester xb -> v1_exch_compare xa xb

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 (the archive) and V1 (the requesting worker) are the
    knowledge agents; V2..V9 are idle non-agents with the constant blank view
    and never appear under K. *)
let view v s =
  match v with
  | Validator.V0 -> View_archive (load_answer_of s, s.live, v0_exch_of s.exch)
  | Validator.V1 -> View_requester (v1_exch_of s.exch)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_digest_recheck
      (** delete [if batch.digest() != digest { return None; }] from
          [ConsensusPack::Inner::batch] (consensus_pack.rs:1261-1263), so the
          record occupying d's recycled offset leaves the archive under d's
          name. This ADDS the [Serve_sub] / [Serve_sub_g] answers at the
          states where the repair stranded d's index entry and a later append
          reused p0.

          Sibling-repair hunt, and why each candidate fails to repair it: the
          [pos >= self.data.file_len()] early return at :1249-1256 is a
          DIFFERENT gate, is kept under this mutation, and cannot help because
          the recycled offset is in range by construction; the per-record CRC
          validates the substituted record as happily as the right one
          (archive/pack.rs:346-365); the storage boundary [get_batches]
          compares no digests (consensus.rs:1031-1045); the epoch stream
          importer's own recheck (:1486-1492) is a different route and is not
          on the by-digest service path ([PackMessage::Batch] ->
          [inner.batch], :175-177). The two repairs that DO exist - the
          requester's re-hash of every batch it reads (handle.rs:754-761) and
          the local path's re-keying by [b.digest()]
          (batch_fetcher.rs:229-232) - are MODELLED, in [keep_of]: they
          convert a substituted record into a [ProtocolError] that voids the
          entire exchange, so the honestly served batch for g is discarded
          too. That is the harm this mutation exposes, and it is precisely
          what those repairs cannot undo. *)
  | No_bloom_accrue
      (** delete [self.bloom.accrue(key);] from [Index::save]
          (archive/digest_index/index.rs:770), so no save ever sets a bloom
          bit and every later [load] of a saved key short-circuits to
          [NotFound] at :777-778. This REMOVES the bit-setting effect of the
          save transitions.

          Sibling-repair hunt: [fetch_position] is private and [load] is its
          only caller (index.rs:612-647, :775-782), so there is no path to the
          buckets that bypasses the filter; the filter is loaded from disk on
          open and never rebuilt from the buckets (:363-366), so a reopen does
          not restore it; and caller-side compensation runs the wrong way -
          [save_consensus_output] de-duplicates on the POSITION index, not on
          digests (consensus_pack.rs:1034-1037), so a false-negative batch is
          never re-added, while [certificate_pack::Inner::save] skips on
          [load(digest).is_ok()] (certificate_pack.rs:279-282), so a false
          negative there causes a duplicate append rather than a repair. No
          sibling path repairs the deletion. *)
  | No_contains_bounds_check
      (** delete the [pos < self.data.file_len()] comparison from
          [ConsensusPack::Inner::contains_batch] (consensus_pack.rs:1241),
          returning [true] on any [Ok(pos)]. This ADDS the [Adv_yes]
          advertisement at states where the repair stranded d's index entry
          past the end of the truncated file.

          Sibling-repair hunt: the repair path explicitly does not prune the
          digest indexes (:680-684); there is no index rebuild anywhere
          ([validate_pack_file] only reports, pack_validate.rs:183-238); and
          [HdxIndex] exposes no delete API at all (index.rs:761-797). The
          fetch path's own bounds test and recheck (:1249-1263) are kept under
          this mutation and are the reason the advertisement and the fetch
          come apart: they repair the ANSWER, never the ADVERTISEMENT. *)

(** Append d's preimage at the end of the pack: a record at p0, the index
    entry, and (unless the accrue is deleted) d's bloom bits {x, y}
    ([save_consensus_batches] consensus_pack.rs:999-1013, [Index::save]
    index.rs:762-772). *)
let save_d mut s =
  let accrue = match mut with
    | Pristine | No_digest_recheck | No_contains_bounds_check -> true
    | No_bloom_accrue -> false
  in
  {
    s with
    cell0 = Rec_d;
    live = L1;
    idx_d = At_p0;
    bit_x = Bool.( || ) s.bit_x accrue;
    bit_y = Bool.( || ) s.bit_y accrue;
  }

(** Append e's preimage at the end of the pack. After the repair the end of
    the pack is p0 again, so this is the offset-recycling append the recheck
    comment names (consensus_pack.rs:1258-1260); e accrues bit {y}. *)
let save_e mut s =
  let accrue = match mut with
    | Pristine | No_digest_recheck | No_contains_bounds_check -> true
    | No_bloom_accrue -> false
  in
  { s with cell0 = Rec_e; live = L1; idx_e = At_p0;
    bit_y = Bool.( || ) s.bit_y accrue }

(** Append g's preimage at p1. A re-add after a repair overwrites the same
    digest with the same position in place, which is exactly what the repair
    comment says will happen (:681-682, duplicate overwrite index.rs:695-700);
    g accrues bit {y}. *)
let save_g mut s =
  let accrue = match mut with
    | Pristine | No_digest_recheck | No_contains_bounds_check -> true
    | No_bloom_accrue -> false
  in
  { s with cell1 = Rec_g; live = L2; idx_g = At_p1;
    bit_y = Bool.( || ) s.bit_y accrue }

(** The damaged-and-repaired episode: the data file is truncated back and the
    digest indexes are deliberately left holding entries for records that are
    no longer there (consensus_pack.rs:665-685, and the tracked length is
    reconciled to the healed length at :721-726). The bloom is untouched -
    nothing ever clears a bit. *)
let heal s = { s with cell0 = Vacant; cell1 = Vacant; live = L0; healed = true }

(** The archive's enabled writes and repairs. Appends land at the end of the
    pack, so which one is enabled is a function of the tracked length; e is
    only ever appended after the repair, which is the recycling case the
    family is about. The repair runs at most once: the model covers a single
    damage-and-repair episode. *)
let archive_steps mut s =
  let appends =
    match s.live with
    | L0 -> save_d mut s :: (if s.healed then [ save_e mut s ] else [])
    | L1 -> [ save_g mut s ]
    | L2 -> []
  in
  let repairs =
    match (s.live, s.healed) with
    | L2, false -> [ heal s ]
    | (L0 | L1 | L2), true | (L0 | L1), false -> []
  in
  appends @ repairs

(** [ConsensusPack::Inner::contains_batch] (consensus_pack.rs:1236-1245): the
    index answer, then the bounds test - which is what
    {!No_contains_bounds_check} deletes. *)
let advertise mut s =
  let ok =
    match mut with
    | Pristine | No_digest_recheck | No_bloom_accrue ->
        Bool.( && ) (lookup_ok_d s) (entry_in_bounds s.idx_d s.live)
    | No_contains_bounds_check -> lookup_ok_d s
  in
  if ok then Adv_yes else Adv_no

(** The d slot of [ConsensusPack::Inner::batch] (consensus_pack.rs:1248-1265):
    the index answer, the bounds early return (kept under every mutation, a
    different gate from the advertisement's), the fetch, and then the digest
    recheck - which is what {!No_digest_recheck} deletes. *)
let serve_d_slot mut s =
  if Bool.not (lookup_ok_d s) then D_nothing
  else if Bool.not (entry_in_bounds s.idx_d s.live) then D_nothing
  else
    let r = record_at s.idx_d s in
    match mut with
    | Pristine | No_bloom_accrue | No_contains_bounds_check ->
        if cell_is_d r then D_preimage else D_nothing
    | No_digest_recheck ->
        if cell_is_d r then D_preimage
        else if cell_is_record r then D_substitute
        else D_nothing

(** The g slot of the same fetch. Offset p1 is only ever written by
    {!save_g}, so g's recheck has no substitution case to catch in this model
    and the mutation is observationally inert on this slot; the arm is spelled
    out anyway so the deletion is modelled where the code makes it - once, for
    every digest [Inner::batch] serves. *)
let serve_g_slot mut s =
  if Bool.not (lookup_ok_g s) then false
  else if Bool.not (entry_in_bounds s.idx_g s.live) then false
  else
    let r = record_at s.idx_g s in
    match mut with
    | Pristine | No_bloom_accrue | No_contains_bounds_check -> cell_is_g r
    | No_digest_recheck -> cell_is_record r

(** The archive's answer to the two-digest request {d, g}. *)
let serve mut s =
  let g = serve_g_slot mut s in
  match serve_d_slot mut s with
  | D_nothing -> if g then Serve_g else Serve_nothing
  | D_preimage -> if g then Serve_d_g else Serve_d
  | D_substitute -> if g then Serve_sub_g else Serve_sub

(** The transition relation. While no request is in flight the archive may
    append, repair, or accept a request; once a request is in flight the pack
    service runs it to completion - [run_pack_loop] drains [PackMessage] on ONE
    thread (consensus_pack.rs:132-192), so no append or repair interleaves the
    advertisement and the fetch of a single exchange. A served state has no
    successor and is stutter-closed by the kernel. *)
let next_with mut s =
  match s.exch with
  | X_idle -> archive_steps mut s @ [ { s with exch = X_asked } ]
  | X_asked -> [ { s with exch = X_advertised (advertise mut s) } ]
  | X_advertised a -> [ { s with exch = X_served (a, serve mut s) } ]
  | X_served (_, _) -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The first initial state: a freshly created epoch pack - no records, no
    index entries, no bloom bits, no repair yet. *)
let initial =
  {
    cell0 = Vacant;
    cell1 = Vacant;
    live = L0;
    idx_d = No_entry;
    idx_e = No_entry;
    idx_g = No_entry;
    bit_x = false;
    bit_y = false;
    healed = false;
    exch = X_idle;
  }

(** The second initial state: an already-repaired pack that never held d at
    all - e at p0 and g at p1, both readable, index entries and bloom bits for
    e and g only. This is the hidden branch that makes the requester's
    knowledge contingent: an answer carrying g alone is equally consistent
    with this pack and with the repaired-and-recycled one, so the two live in
    one V1-view class. Its [healed] flag is already set, so the single
    modelled repair episode is spent and the archive is terminal here. *)
let initial_no_d_entry =
  {
    cell0 = Rec_e;
    cell1 = Rec_g;
    live = L2;
    idx_d = No_entry;
    idx_e = At_p0;
    idx_g = At_p1;
    bit_x = false;
    bit_y = true;
    healed = true;
    exch = X_idle;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Holds_d
      (** the pack really holds d's preimage at a readable offset - a fact
          about bytes, in no agent's view *)
  | Holds_g  (** the pack really holds g's preimage at a readable offset *)
  | Index_has_d  (** the digest index has a bucket entry for d *)
  | Index_has_q
      (** the digest index has a bucket entry for the probe digest q: never,
          in any reachable state - q is the digest that is only ever looked
          up, never saved *)
  | Filter_admits_d  (** [bloom.contains(d)] - both of d's bits are set *)
  | Filter_admits_q  (** [bloom.contains(q)] - q's single bit is set *)
  | Lookup_ok_d  (** [load(d)] returned a position *)
  | In_bounds_d  (** d's index entry points inside the data file *)
  | Dangling_d
      (** d's index entry points at p0 while p0 does not hold d's preimage -
          the state the repair leaves behind *)
  | Healed  (** the damage-and-repair episode has run *)
  | Asked  (** the requester has sent the request {d, g} *)
  | Advertised_yes  (** the archive answered [contains_batch(d)] with true *)
  | Answered_d  (** the archive's fetch filled the d slot of its answer *)
  | Kept_g  (** the requester validated and kept g's preimage *)
  | Poisoned
      (** the requester rejected the whole exchange because a batch it never
          asked for arrived *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Holds_d -> holds_d s
  | Holds_g -> holds_g s
  | Index_has_d -> entry_present s.idx_d
  | Index_has_q -> false
  | Filter_admits_d -> filter_admits_d s
  | Filter_admits_q -> filter_admits_q s
  | Lookup_ok_d -> lookup_ok_d s
  | In_bounds_d -> entry_in_bounds s.idx_d s.live
  | Dangling_d ->
      Bool.( && ) (entry_present s.idx_d) (Bool.not (holds_d s))
  | Healed -> s.healed
  | Asked -> ( match s.exch with
      | X_asked -> true
      | X_idle | X_advertised _ | X_served (_, _) -> false)
  | Advertised_yes -> ( match s.exch with
      | X_advertised Adv_yes -> true
      | X_advertised Adv_no | X_idle | X_asked | X_served (_, _) -> false)
  | Answered_d -> ( match s.exch with
      | X_served (_, sv) -> (
          match served_by_v0_of sv with
          | Sv_d | Sv_dg -> true
          | Sv_none | Sv_g -> false)
      | X_idle | X_asked | X_advertised _ -> false)
  | Kept_g -> ( match s.exch with
      | X_served (_, sv) -> (
          match keep_of sv with
          | Keep_g | Keep_d_g -> true
          | Keep_nothing | Keep_d | Keep_poisoned -> false)
      | X_idle | X_asked | X_advertised _ -> false)
  | Poisoned -> ( match s.exch with
      | X_served (_, sv) -> (
          match keep_of sv with
          | Keep_poisoned -> true
          | Keep_nothing | Keep_d | Keep_g | Keep_d_g -> false)
      | X_idle | X_asked | X_advertised _ -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Holds_d -> "holds(v,preimage(d))"
  | Holds_g -> "holds(v,preimage(g))"
  | Index_has_d -> "index_entry(d)"
  | Index_has_q -> "index_entry(q)"
  | Filter_admits_d -> "bloom_contains(d)"
  | Filter_admits_q -> "bloom_contains(q)"
  | Lookup_ok_d -> "load(d)=Ok"
  | In_bounds_d -> "pos(d)<file_len"
  | Dangling_d -> "dangling(d)"
  | Healed -> "healed"
  | Asked -> "asked(w,{d,g})"
  | Advertised_yes -> "contains_batch(d)=true"
  | Answered_d -> "answered(v,d)"
  | Kept_g -> "kept(w,preimage(g))"
  | Poisoned -> "exchange_poisoned"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every
    reachable world by test/t_archive_digest_lookup_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the two initial states, the
    mutation-parameterized transitions, the two-agent view, the atom
    valuation. *)
let spec_of mut =
  {
    Checker.init = [ initial; initial_no_d_entry ];
    next = next_with mut;
    view;
    label;
  }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
