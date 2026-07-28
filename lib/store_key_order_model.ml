(** Finite interpreted system for the STORE_KEY_ORDER family: the ordered
    [CertificateDigestByOrigin] index of the certificate store, the backwards
    probe [last_round_number] that reads it, and the one consumer of that probe
    - the certificate fetcher's [should_fetch_certificate] gate. File citations
    refer to Telcoin-Association/telcoin-network at 0c59c15b (working tree);
    every one of them was opened in this checkout.

    THE MECHANISM, layer by layer.

    - THE TABLE. [CertificateDigestByOrigin] is keyed [(AuthorityIdentifier,
      Round)] and valued [HeaderDigest] (storage/src/lib.rs:93). The only
      writer is [save_cert], which derives the key from the certificate itself:
      [let key = (certificate.origin().clone(), certificate.round()); txn
      .insert::<CertificateDigestByOrigin>(&key, &digest)?]
      (stores/certificate_store.rs:140-142). A row for (a, r) therefore exists
      in a node's index only because that node accepted a certificate that a
      authored at round r - that is the model's [row -> signed] invariant.

    - THE ORDER. Both persistent backends sort rows by the RAW BYTES of the
      encoded key and never by the Rust [Ord] of the decoded key. redb says so
      outright: [impl<K: KeyT> Key for KeyWrap<K> { fn compare(data1: &[u8],
      data2: &[u8]) -> std::cmp::Ordering { data1.cmp(data2) } }]
      (storage/src/redb/wraps.rs:10-16). mdbx says so by omission: every table
      is opened with [txn.create_db(Some(T::NAME), DatabaseFlags::default())?]
      (storage/src/mdbx/database.rs:154-159), i.e. no custom comparator, so
      MDBX's default lexicographic byte compare applies. The in-memory layer is
      a third copy of the same order - [DashMap<&'static str,
      Arc<RwLock<BTreeMap<Vec<u8>, Vec<u8>>>>>] (storage/src/mem_db.rs:10) -
      and the two composed databases only dispatch between the copies without
      re-sorting anything ([LayeredDatabase::record_prior_to],
      storage/src/layered_db.rs:447-453;
      [CompositeDatabase::record_prior_to], storage/src/composite_db.rs:121-123,
      which routes by [T::HINT] and so sends this [TableHint::Epoch] table
      straight to one of them).

    - THE AGREEMENT. Byte order is made to agree with [Ord] by ONE line:
      [bincode::DefaultOptions::new().with_big_endian().with_fixint_encoding()
      .serialize(obj)] in [encode_key] (types/src/codec.rs:43-49), whose
      sibling doc states the contract - "The binary format for a DB key should
      sort correctly (the with_fixint_encoding()). This proper sorting MUST be
      maintained else stuff will break." (types/src/codec.rs:18-19, repeated at
      :30-31 and :41-42). [AuthorityIdentifier] is [Arc<[u8; 32]>] with derived
      [Ord] and a binary [Serialize] that emits the raw bytes
      (types/src/committee.rs:301-319), so the authority prefix is fixed-width
      and byte order equals [Ord] on it no matter what the integer endianness
      is; only the [Round] (a [u32]) suffix moves.

    - THE PROBE. [last_round_number(origin)] builds the sentinel key
      [(origin.clone(), Round::MAX)] and takes the record strictly before it:
      [if let Some(((name, round), _)) =
      self.record_prior_to::<CertificateDigestByOrigin>(&key) { if &name ==
      origin { return Ok(Some(round)); } } Ok(None)]
      (stores/certificate_store.rs:411-419). [record_prior_to] is not a seek:
      it walks the whole table in BYTE order and stops at the first row whose
      DECODED key is at or after the probe key - [for (k, v) in self.iter::<T>()
      { if &k >= key { break; } last = Some((k, v)); } last]
      (storage/src/mdbx/database.rs:231-240; identical in
      storage/src/redb/database.rs:239-251, and byte-compared in
      storage/src/mem_db.rs:259-278). Iterating in one order and stopping on
      another is exactly where the encoding contract is spent.

    - THE CONSUMER. [should_fetch_certificate] reads the probe and nothing
      else: [let header_is_newer = self.certificate_store
      .last_round_number(header.author())?.map(|last_round| header.round() >
      last_round).unwrap_or(true)]
      (consensus/primary/src/certificate_fetcher.rs:232-238). Note
      [unwrap_or(true)]: a [None] answer means FETCH. The gate sits in
      [handle_command] at :207, and BOTH fetch entry points reach it - the
      header path and the missing-parent path, which sends
      [CertificateFetcherCommand::Ancestors(...)]
      (consensus/primary/src/state_sync/cert_manager.rs:157-177) into the very
      same [handle_command] (certificate_fetcher.rs:178-191, falling through to
      :207). The model therefore represents both triggers with ONE [Probed]
      stage: the sibling route is present, not omitted, and any deletion that
      corrupts the probe disables it too.

    WHY THE MODELLED KEY DOMAIN IS THE WHOLE STORY.

    - Authority [j] is fixed ABOVE authority [k] in the 32-byte identifier
      order, so [k]'s block of rows immediately precedes [j]'s. That is the
      adversarial half: when [j] has no rows at all, the record before
      [(j, Round::MAX)] is [k]'s, and the [&name == origin] test at :414-416 is
      the only thing standing between that and a false answer.
    - Rows of any authority [m] ABOVE [j] are omitted WITHOUT LOSS. Their
      decoded key [(m, r)] is [>= (j, Round::MAX)], so the [break] at
      mdbx/database.rs:234 (redb/database.rs:245) fires on the first of them
      and [last] is already fixed. The authority prefix is raw bytes, so this
      holds under both modelled encodings.
    - Two rounds suffice, and they must be rounds whose big-endian and
      little-endian byte orders DISAGREE: [R_lo = 1] encodes [00 00 00 01]
      big-endian and [01 00 00 00] little-endian, [R_hi = 256] encodes
      [00 00 01 00] big-endian and [00 01 00 00] little-endian. Big-endian:
      [R_lo] sorts before [R_hi], agreeing with [Ord]. Little-endian: [R_hi]
      sorts before [R_lo]. [Round::MAX = 0xFFFFFFFF] is byte-palindromic, so
      the sentinel stays the byte-maximum under both and the [break] never
      fires inside [j]'s block either way.

    SCOPE, stated rather than hidden.

    - The model covers the FIRST fetch decision for [j]. The earlier skip [if
      let Some(target_round) = self.targets.get(header.author()) { if
      header.round() <= *target_round { return Ok(false); } }]
      (certificate_fetcher.rs:225-229) is therefore not enabled: [self.targets]
      gains an entry for [j] only at :212, after the gate has already passed.
      That skip could not be a counterexample to the liveness statement anyway
      - it fires precisely when a fetch for [j] at that round or later is
      already scheduled.
    - GC ([gc_rounds], stores/certificate_store.rs:150-172), the single-record
      [delete] (:281-293) and the epoch [clear] (:438-447) remove rows. They
      are not modelled, and they cannot repair anything: removing a row only
      produces states of the shape "row absent while the authority did sign",
      which the model already contains because the signing ghosts are free
      whenever the row is absent. For the origin-guard deletion in particular
      GC is an amplifier, not a repair: it empties an authority's block, which
      is the precondition of the false answer, and it prunes by ROUND across
      all authorities at once, so it cannot selectively remove the neighbour
      row the false answer comes from without also making the trigger itself
      too old to be handled. Every mutator of [CertificateDigestByOrigin]
      derives its key from the certificate ([save_cert] :141-142, [delete]
      :289-290, [gc_rounds] :168), which is what makes the model's
      "row implies the authority signed" invariant exact.
    - Authorship is tracked only at [R_hi], the round the statements quantify
      over. No atom mentions authorship at [R_lo].

    COMPONENTS. Three index rows ([j_lo], [j_hi], [k_hi]); two signing ghosts
    ([j_signed_hi], [k_signed_hi]) constrained so a row implies its authority's
    signature; and one [stage] running [Filling] (the index is being written)
    -> [Probed answer] (a fetch trigger for [(j, R_hi)] reached
    [should_fetch_certificate], which called [last_round_number(j)] and got
    [answer]) -> [Decided verdict] (the [header.round() > last_round]
    comparison resolved). Splitting the read from the comparison is what makes
    the suppressed outcome a state of its own rather than a label.

    ROLE MAPPING (knowledge agents must have a real, non-constant view; idle
    validators carry the blank view and never appear under K):
    - V0 is the STORING AND PROBING node. Its view is exactly what it can read:
      its own three [CertificateDigestByOrigin] rows and the stage its fetch
      decision has reached (including the value the probe returned to it). V0
      does NOT see whether [j] or [k] actually signed a certificate at [R_hi] -
      that is another node's act, and the only evidence V0 ever gets for it is
      a row it wrote itself.
    - V1 is [j], the authority the probe names; V2 is [k], the authority whose
      block of rows immediately precedes [j]'s. V1, V2 and V3..V9 are idle: the
      constant blank view, never under K. Only V0 runs a store in this family,
      so the committee's other members contribute nothing to the view lattice. *)

(** Presence of one row in V0's [CertificateDigestByOrigin] index. The sole
    writer is [save_cert] (stores/certificate_store.rs:140-142). *)
type row =
  | Absent  (** no row for this (authority, round) pair *)
  | Present  (** a row, hence a certificate this node accepted and stored *)

(** Total order index for {!row}. *)
let row_index = function Absent -> 0 | Present -> 1

(** Total order on {!row}. *)
let row_compare a b = Int.compare (row_index a) (row_index b)

(** [true] iff the row is in the index. *)
let row_is_present = function Absent -> false | Present -> true

(** What [last_round_number(j)] returned (stores/certificate_store.rs:411-419).
    [Ans_none] is its [Ok(None)]. *)
type answer =
  | Ans_none  (** [Ok(None)]: no record before the sentinel named [j] *)
  | Ans_lo  (** [Ok(Some(R_lo))] *)
  | Ans_hi  (** [Ok(Some(R_hi))] *)

(** Total order index for {!answer}. *)
let answer_index = function Ans_none -> 0 | Ans_lo -> 1 | Ans_hi -> 2

(** Total order on {!answer}. *)
let answer_compare a b = Int.compare (answer_index a) (answer_index b)

(** The outcome of [should_fetch_certificate] for a trigger naming
    [(j, R_hi)] (consensus/primary/src/certificate_fetcher.rs:223-238). *)
type verdict =
  | Fetch
      (** the gate returned true, so [self.targets] gained [j] and a fetch task
          was started (certificate_fetcher.rs:211-217) *)
  | Skip  (** the gate returned false, so no ancestor fetch happens for [j] *)

(** Total order index for {!verdict}. *)
let verdict_index = function Fetch -> 0 | Skip -> 1

(** Total order on {!verdict}. *)
let verdict_compare a b = Int.compare (verdict_index a) (verdict_index b)

(** How far the one modelled fetch decision has got. *)
type stage =
  | Filling  (** rows are still being written; no trigger has been handled *)
  | Probed of answer
      (** a fetch trigger for [(j, R_hi)] - from the header path
          (certificate_fetcher.rs:207) or from the missing-parent path
          (cert_manager.rs:169-177 into certificate_fetcher.rs:180) - reached
          [should_fetch_certificate], which called [last_round_number(j)] and
          received this answer *)
  | Decided of verdict
      (** the [header.round() > last_round] comparison at
          certificate_fetcher.rs:235 resolved; terminal *)

(** Total order on {!stage}: every cross-constructor arm spelled out. *)
let stage_compare a b =
  match (a, b) with
  | Filling, Filling -> 0
  | Filling, (Probed _ | Decided _) -> -1
  | (Probed _ | Decided _), Filling -> 1
  | Probed x, Probed y -> answer_compare x y
  | Probed _, Decided _ -> -1
  | Decided _, Probed _ -> 1
  | Decided x, Decided y -> verdict_compare x y

(** The joint global state: V0's three index rows, the two signing ghosts, and
    the stage of the one modelled fetch decision. *)
type state = {
  j_lo : row;  (** the row [(j, R_lo)] *)
  j_hi : row;  (** the row [(j, R_hi)] *)
  k_hi : row;  (** the row [(k, R_hi)]; [k] sorts immediately below [j] *)
  j_signed_hi : bool;  (** GHOST: [j] really signed a certificate at [R_hi] *)
  k_signed_hi : bool;  (** GHOST: [k] really signed a certificate at [R_hi] *)
  stage : stage;  (** how far the fetch decision has got *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = row_compare s1.j_lo s2.j_lo in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = row_compare s1.j_hi s2.j_hi in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = row_compare s1.k_hi s2.k_hi in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare s1.j_signed_hi s2.j_signed_hi in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.k_signed_hi s2.k_signed_hi in
          if Bool.not (Int.equal c4 0) then c4 else stage_compare s1.stage s2.stage

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. V0 sees its own index rows and the stage its
    fetch decision has reached; it never sees a signing ghost, because
    "authority a signed a certificate at round r" is a's act and V0's only
    evidence for it is a row V0 wrote itself. *)
type view =
  | View_store of row * row * row * stage
      (** V0: [(j_lo, j_hi, k_hi, stage)] *)
  | View_idle  (** the constant blank view of the non-agents V1, V2, V3 *)

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_store (_, _, _, _) -> -1
  | View_store (_, _, _, _), View_idle -> 1
  | View_store (a1, a2, a3, a4), View_store (b1, b2, b3, b4) ->
      let c = row_compare a1 b1 in
      if Bool.not (Int.equal c 0) then c
      else
        let c1 = row_compare a2 b2 in
        if Bool.not (Int.equal c1 0) then c1
        else
          let c2 = row_compare a3 b3 in
          if Bool.not (Int.equal c2 0) then c2 else stage_compare a4 b4

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 is the only knowledge agent; V1 ([j]) and V2 ([k]) are
    the subjects of the K operands, and they - like V3..V9 - are idle
    non-agents with the constant blank view that never appear under K. *)
let view v s =
  match v with
  | Validator.V0 -> View_store (s.j_lo, s.j_hi, s.k_hi, s.stage)
  | Validator.V1 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine  (** the code as written at 0c59c15b *)
  | No_big_endian
      (** delete [.with_big_endian()] - the single line types/src/codec.rs:45,
          inside [encode_key] at :43-49 - so bincode's [DefaultOptions] encodes the
          [Round] suffix little-endian. The stored bytes still decode to the
          right [Round] (the [decode_key] pair at :20-26 and :32-37 moves with
          it), but the BYTE order inside an authority's block reverses for the
          modelled pair - [R_hi = 256] encodes [00 01 00 00] and [R_lo = 1]
          encodes [01 00 00 00] - so the cursor emits [(j, R_hi)] BEFORE
          [(j, R_lo)]. Transition changed: [Filling -> Probed a] now computes
          [a] from a permuted stream, so [record_prior_to] hands back [j]'s
          LOWEST stored round instead of its highest. No sibling path repairs
          it. Both backends sort by raw bytes and nothing re-sorts: redb's
          comparator IS [data1.cmp(data2)] (redb/wraps.rs:10-16), mdbx uses
          MDBX's default byte compare (mdbx/database.rs:154-159), [skip_to] is
          a [skip_while] over the same raw stream and not a seek
          (mdbx/database.rs:211-220, redb/database.rs:176-206), [last_record]
          is the cursor's byte-maximum (mdbx/database.rs:242-250,
          redb/database.rs:253-257), [reverse_iter] walks the same byte order
          backwards (mdbx/database.rs:222-229, redb/database.rs:208-237), and
          the memory layer keys a [BTreeMap<Vec<u8>, _>] by the very same bytes
          (mem_db.rs:10, :259-278) so it is a third copy of the order rather
          than a repair. *)
  | No_origin_guard
      (** delete the [if &name == origin] test from [last_round_number]
          (stores/certificate_store.rs:414-416), returning [Ok(Some(round))]
          unconditionally. Transition changed: [Filling -> Probed a] now
          answers [Ans_hi] from [k]'s row when [j] has no rows at all, so the
          probe reports a neighbour's round as [j]'s and
          [should_fetch_certificate] evaluates [R_hi > R_hi] to false -
          [Decided Skip] replaces [Decided Fetch]. No sibling path repairs it.
          [last_round] (:389-399) and [next_round_number] (:428-434) carry
          their own copies of the same test, but they answer different
          questions and no caller cross-checks them: the sole consumer,
          [should_fetch_certificate] (certificate_fetcher.rs:232-238), reads
          [last_round_number] alone and compares rounds only. The stored value
          is a [HeaderDigest] and [last_round_number] returns the KEY's round
          without loading the certificate (:415), so nothing downstream
          re-derives the author. The second fetch entry point is not a repair
          either: [cert_manager.rs:169-177] sends
          [CertificateFetcherCommand::Ancestors] into the SAME [handle_command]
          (certificate_fetcher.rs:178-191), which falls through to the same
          gate at :207 - which is why the model gives both triggers one
          [Probed] stage. [CertificateFetcherCommand::Kick] (:181-190) starts a
          task only when [!self.targets.is_empty()], and targets are inserted
          only at :212 after the gate has passed, so a kick cannot create a
          target the gate refused. [get_written_rounds] / [origins_after_round]
          (:352-374, stores/certificate_store.rs:332-351) read the by-ROUND
          index and only PRUNE targets (:347), never add one. *)

(** The three modelled rows, named by the (authority, round) pair each keys.
    Rows of any authority above [j] are omitted without loss: the [break] at
    mdbx/database.rs:234 fires on the first of them. *)
type slot =
  | Slot_k_hi  (** [(k, R_hi)] - [k] is the authority immediately below [j] *)
  | Slot_j_lo  (** [(j, R_lo)] *)
  | Slot_j_hi  (** [(j, R_hi)] *)

(** Is this row present in V0's index? *)
let slot_present s = function
  | Slot_k_hi -> row_is_present s.k_hi
  | Slot_j_lo -> row_is_present s.j_lo
  | Slot_j_hi -> row_is_present s.j_hi

(** The order in which the backend cursor emits the modelled rows, i.e. the
    raw-byte order of their encoded keys. The authority prefix is raw
    fixed-width bytes (types/src/committee.rs:315-318) so [k] always precedes
    [j]; only the [Round] suffix moves with the encoding. *)
let scan_order = function
  | Pristine | No_origin_guard -> [ Slot_k_hi; Slot_j_lo; Slot_j_hi ]
  | No_big_endian -> [ Slot_k_hi; Slot_j_hi; Slot_j_lo ]

(** [record_prior_to((j, Round::MAX))] (mdbx/database.rs:231-240): walk the
    table in byte order keeping the last row seen, stopping at the first row
    whose DECODED key is at or after the probe key. No modelled row is at or
    after [(j, Round::MAX)], so the [break] never fires and the answer is the
    byte-order-last present row. *)
let last_row_before_sentinel mut s =
  List.fold_left
    (fun acc sl -> if slot_present s sl then Some sl else acc)
    None (scan_order mut)

(** [last_round_number(j)] (stores/certificate_store.rs:411-419): the record
    before the sentinel, admitted only when its authority really is [j]. *)
let probe_answer mut s =
  Option.fold ~none:Ans_none
    ~some:(fun sl ->
      match sl with
      | Slot_j_lo -> Ans_lo
      | Slot_j_hi -> Ans_hi
      | Slot_k_hi -> (
          match mut with
          | Pristine | No_big_endian -> Ans_none
          | No_origin_guard -> Ans_hi))
    (last_row_before_sentinel mut s)

(** [.map(|last_round| header.round() > last_round).unwrap_or(true)] for a
    header of [j] at round [R_hi] (certificate_fetcher.rs:232-238). A missing
    answer means FETCH; an answer of [R_hi] means the strict comparison fails. *)
let fetch_verdict = function
  | Ans_none -> Fetch
  | Ans_lo -> Fetch
  | Ans_hi -> Skip

(** The transition relation: while [Filling] an authority may sign at [R_hi] or
    a row may be written (a row for [(a, R_hi)] requires [a]'s signature, since
    [save_cert] derives the key from the certificate itself,
    stores/certificate_store.rs:140-142), and at any moment a fetch trigger may
    reach [should_fetch_certificate] and read the index. The store cannot
    change under the read: [should_fetch_certificate] is a synchronous call
    inside [handle_command] (certificate_fetcher.rs:207). *)
let next_with mut s =
  match s.stage with
  | Filling ->
      List.concat
        [
          (if s.j_signed_hi then [] else [ { s with j_signed_hi = true } ]);
          (if s.k_signed_hi then [] else [ { s with k_signed_hi = true } ]);
          (match s.j_lo with
          | Present -> []
          | Absent -> [ { s with j_lo = Present } ]);
          (match s.j_hi with
          | Present -> []
          | Absent ->
              if s.j_signed_hi then [ { s with j_hi = Present } ] else []);
          (match s.k_hi with
          | Present -> []
          | Absent ->
              if s.k_signed_hi then [ { s with k_hi = Present } ] else []);
          [ { s with stage = Probed (probe_answer mut s) } ];
        ]
  | Probed a -> [ { s with stage = Decided (fetch_verdict a) } ]
  | Decided (Fetch | Skip) -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: an empty index, nothing signed, no trigger handled. *)
let initial =
  {
    j_lo = Absent;
    j_hi = Absent;
    k_hi = Absent;
    j_signed_hi = false;
    k_signed_hi = false;
    stage = Filling;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Row_j_high  (** [(j, R_hi)] is in V0's [CertificateDigestByOrigin] *)
  | Row_j_low  (** [(j, R_lo)] is in it *)
  | Row_k_high  (** [(k, R_hi)] is in it *)
  | J_signed_high
      (** [j] signed a certificate at [R_hi]: an act of another node, hidden
          from V0 except through a row V0 wrote itself *)
  | K_signed_high  (** [k] signed a certificate at [R_hi]; equally hidden *)
  | Probe_returned  (** [last_round_number(j)] has returned to the fetcher *)
  | Answer_high  (** it returned [Ok(Some(R_hi))] *)
  | Answer_low  (** it returned [Ok(Some(R_lo))] *)
  | Answer_absent  (** it returned [Ok(None)] *)
  | Fetch_started  (** the gate passed: an ancestor fetch for [j] was started *)
  | Fetch_suppressed  (** the gate returned false: no ancestor fetch for [j] *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Row_j_high -> row_is_present s.j_hi
  | Row_j_low -> row_is_present s.j_lo
  | Row_k_high -> row_is_present s.k_hi
  | J_signed_high -> s.j_signed_hi
  | K_signed_high -> s.k_signed_hi
  | Probe_returned -> (
      match s.stage with
      | Probed (Ans_none | Ans_lo | Ans_hi) -> true
      | Filling | Decided (Fetch | Skip) -> false)
  | Answer_high -> (
      match s.stage with
      | Probed Ans_hi -> true
      | Probed (Ans_none | Ans_lo) | Filling | Decided (Fetch | Skip) -> false)
  | Answer_low -> (
      match s.stage with
      | Probed Ans_lo -> true
      | Probed (Ans_none | Ans_hi) | Filling | Decided (Fetch | Skip) -> false)
  | Answer_absent -> (
      match s.stage with
      | Probed Ans_none -> true
      | Probed (Ans_lo | Ans_hi) | Filling | Decided (Fetch | Skip) -> false)
  | Fetch_started -> (
      match s.stage with
      | Decided Fetch -> true
      | Decided Skip | Filling | Probed (Ans_none | Ans_lo | Ans_hi) -> false)
  | Fetch_suppressed -> (
      match s.stage with
      | Decided Skip -> true
      | Decided Fetch | Filling | Probed (Ans_none | Ans_lo | Ans_hi) -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Row_j_high -> "row(j,R_hi)"
  | Row_j_low -> "row(j,R_lo)"
  | Row_k_high -> "row(k,R_hi)"
  | J_signed_high -> "signed(j,R_hi)"
  | K_signed_high -> "signed(k,R_hi)"
  | Probe_returned -> "last_round_number(j)=returned"
  | Answer_high -> "last_round_number(j)=Some(R_hi)"
  | Answer_low -> "last_round_number(j)=Some(R_lo)"
  | Answer_absent -> "last_round_number(j)=None"
  | Fetch_started -> "fetch_ancestors(j)"
  | Fetch_suppressed -> "no_fetch(j)"

(** The CTLK checker over this family's ordered state and view: the presheaf-
    topos denotation, pinned to agree with {!System} at every reachable world
    by test/t_store_key_order_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state, the
    mutation-parameterized transitions, the one-agent view, the atom
    valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
