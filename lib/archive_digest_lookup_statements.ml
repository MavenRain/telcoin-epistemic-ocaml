(** The ARCHIVE_DIGEST_LOOKUP statements: three stages of one by-digest read
    pipeline over the interpreted system of {!Archive_digest_lookup_model} -
    the bloom filter at the front (S2), the bounds test in the middle that the
    possession advertisement answers from (S3), and the content recheck at the
    end whose deletion voids an entire batch exchange (S1).

    READING GUIDE for the K operands - why neither is a projection of its own
    knower's view, and why neither is rigid:

    - [K_V1(holds(v, preimage(g)))] in S1. V1's view is its request phase and
      the batches its OWN digest validation kept (handle.rs:754-761); V0's
      pack, index, offsets and repair history are not in it. "V0's pack holds
      g's preimage at a readable offset" is a fact about V0's disk, false at
      plenty of reachable states (a fresh pack, a pack mid-repair, a pack
      holding only d), and the model contains two archives that are
      V1-indistinguishable at the moment g arrives: the repaired-and-recycled
      one, where d's index entry dangles over a record that is not d's, and
      the second initial state, an already-repaired pack that never held d at
      all. The knowledge is therefore contingent AND the view class is not a
      singleton. Deleting the recheck collapses it: the substituted record
      turns a two-digest answer into a [ProtocolError] that keeps NOTHING, and
      a poisoned exchange is equally consistent with an archive that holds g
      and one that does not.

    - [K_V0(holds(v, preimage(d)))] in S3. V0's view is the two values
      [contains_batch] reads - the index answer for d and the pack's file
      length (consensus_pack.rs:1236-1245) - plus its own trace of the
      exchange. The bytes at an offset it has not fetched are NOT in it, and a
      served substitute is indistinguishable from a served preimage precisely
      because telling them apart is the comparison at :1261-1263. So at the
      advertisement the operand is unknown (conjunct B: the same index answer
      and the same file length are produced by a pack that holds d and by one
      whose recycled offset holds e), and only after the fetch's recheck does
      it become known (conjunct C). Conjunct C's view class is not a singleton
      either: a pre-repair pack and a post-repair pack that re-saved d produce
      the same index answer, length and answer trace.

    Buckets reuse the frozen {!Statements} vocabulary. *)

open Archive_digest_lookup_model

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

(** S1 - recheck-keeps-a-recycled-offset-from-voiding-the-whole-batch-exchange
    [liveness].

    Once a worker has asked its peer's archive for the digests {d, g} and that
    archive really holds g's preimage at a readable offset, the exchange
    inevitably reaches a state where the worker KNOWS the archive held g.

    Conjunct by conjunct, this is a single [leads_to]:
    [AG( asked(w,{d,g}) /\ holds(v,preimage(g)) -> AF K_w holds(v,preimage(g)) )].
    - the antecedent is observable to w only in its first half; the second
      half is a fact about v's disk (consensus_pack.rs:1236-1245 reads the
      index and the file length, never the bytes, so not even v knows it
      before it fetches);
    - the consequent is reached in two steps: v answers [contains_batch]
      (:1236-1245), then [Inner::batch] fetches, bounds-checks (:1249-1256)
      and RECHECKS the digest (:1261-1263) before the record leaves; the
      worker then re-hashes every batch it reads and keeps only what it asked
      for (handle.rs:754-761, local path batch_fetcher.rs:229-232).

    MUTATION PIN. {!No_digest_recheck} deletes :1261-1263 and thereby ADDS the
    [Serve_sub_g] answer at the state where the repair stranded d's index
    entry (:680-684) and a later append recycled offset p0 (:1258-1260). The
    worker's own validation then rejects the whole exchange - one unrequested
    digest is a [ProtocolError] for the entire stream, so the honestly served
    batch for g is discarded with it - and a poisoned exchange is
    V1-indistinguishable from one where the archive never held g at all
    (the [L1] recycled state). The knowledge is never reached, so the [AF]
    fails at a terminal state and the statement is refuted.

    SIBLING-REPAIR HUNT. The two repairs that exist for a substituted record
    are the requester's re-hash (handle.rs:754-761) and the local path's
    re-keying by [b.digest()] (batch_fetcher.rs:229-232); BOTH are modelled,
    in [keep_of], and both are exactly what converts the substitution into the
    loss of the whole exchange. The fetch's own [pos >= file_len] early return
    (:1249-1256) is kept under the mutation and cannot help - a recycled
    offset is in range by construction. The storage boundary compares no
    digests (consensus.rs:1031-1045) and the per-record CRC validates the
    wrong record just as happily (archive/pack.rs:346-365). The epoch stream
    importer's own recheck (:1486-1492) is a different route and is not on the
    [PackMessage::Batch] path (:175-177). *)
let s1 =
  {
    name = "recheck-keeps-a-recycled-offset-from-voiding-the-whole-batch-exchange";
    bucket = Statements.Liveness;
    formula =
      Formula.leads_to
        (Formula.And (atom Asked, atom Holds_g))
        (Formula.K (Validator.V1, atom Holds_g));
    antecedent = Formula.And (atom Asked, atom Holds_g);
  }

(** S2 - bloom-accrue-is-the-sole-writer-of-the-only-fast-path-negative
    [safety].

    [HdxIndex::load] is the single door to every possession predicate in the
    archive, and it answers NEGATIVELY from an in-memory bloom filter without
    ever touching a bucket (index.rs:775-782). The filter is therefore
    one-sided in the only direction that matters, and it is not authoritative
    in the other.

    - conjunct A, [AG( index_entry(d) -> bloom_contains(d) )]: a key with a
      bucket entry is never short-circuited away, because the ONLY writer of a
      bloom bit is [Index::save] itself, on the line above the bucket write
      ([self.bloom.accrue(key)], index.rs:770, in the sequence :762-772), and
      [Bloom::contains] is a monotone conjunction over the positions
      [Bloom::accrue] sets - there is no clear and no delete
      (bloom.rs:65-95);
    - conjunct B, [AG( holds(v,preimage(d)) -> load(d)=Ok )]: consequently a
      payload the pack really holds is never lost by the front of the
      pipeline;
    - conjunct C, [EF( bloom_contains(q) /\ ~index_entry(q) )]: the filter is
      NOT authoritative - the probe digest q, whose bit set is a subset of
      d's, is admitted by the filter as soon as d is saved although no bucket
      ever held it, and the authoritative scan [fetch_position]
      (index.rs:612-647) is what eliminates it.

    SCOPE, stated rather than hidden: the model has no index rollback, so
    conjunct A is a claim about the filter's monotonicity and the sole-writer
    property, not about durability. A crash strictly inside [sync] - after
    [save_bucket_cache] wrote a bucket page and before [write_header] wrote
    the bloom page (index.rs:507-526, :449-454, :785-796) - could in principle
    leave a bucket entry durable with its bit lost; that window is outside
    this model and the statement does not claim anything about it.

    MUTATION PIN. {!No_bloom_accrue} deletes index.rs:770, so no save ever
    sets a bit: conjunct A fails at the very first save (a bucket entry with
    no bit) and conjunct B with it. SIBLING-REPAIR HUNT: [fetch_position] is
    private with [load] as its only caller, so nothing reaches the buckets
    around the filter; the filter is read back from disk on open and never
    rebuilt from the buckets (:363-366); and caller-side compensation runs the
    wrong way - [save_consensus_output] de-duplicates on the position index
    rather than on digests (consensus_pack.rs:1034-1037) and
    [certificate_pack::Inner::save] skips on [load(digest).is_ok()]
    (certificate_pack.rs:279-282), so a false negative causes a duplicate
    append, never a repair. *)
let s2 =
  let sole_writer =
    Formula.Ag (Formula.Implies (atom Index_has_d, atom Filter_admits_d))
  in
  let no_live_payload_lost =
    Formula.Ag (Formula.Implies (atom Holds_d, atom Lookup_ok_d))
  in
  let filter_not_authoritative =
    Formula.Ef
      (Formula.And (atom Filter_admits_q, Formula.Not (atom Index_has_q)))
  in
  {
    name = "bloom-accrue-is-the-sole-writer-of-the-only-fast-path-negative";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [ sole_writer; no_live_payload_lost; filter_not_authoritative ];
    antecedent = atom Index_has_d;
  }

(** S3 - contains-is-an-index-and-bounds-fact-while-only-the-fetch-binds-the-payload
    [safety].

    A positive [contains_batch] answer certifies an INDEX fact and a BOUNDS
    fact, and nothing about the bytes; only the fetch, which re-hashes what it
    read, certifies the payload.

    - conjunct A, [AG( contains_batch(d)=true -> pos(d)<file_len )]: the sole
      gate on the advertisement is the bounds comparison
      [pos < self.data.file_len()] (consensus_pack.rs:1241), whose own comment
      names the state it exists for - "in a very rare case of repairing a
      damaged pack we might have something in the index not in the pack file
      (yet)" (:1237-1239);
    - conjunct B, [AG( contains_batch(d)=true -> ~K_v holds(v,preimage(d)) )]:
      the advertisement never reads the data file, so at the moment it is
      given the archive does not know whether the offset holds d's preimage.
      The witness pair is concrete and reachable: a pack that saved d and one
      that was repaired (:680-684) and then recycled p0 with a different
      record (:1258-1260) return the SAME index answer and the SAME file
      length, and disagree on the payload;
    - conjunct C, [AG( answered(v,d) -> K_v holds(v,preimage(d)) )]: once the
      fetch has run its bounds early return (:1249-1256) and its digest
      recheck (:1261-1263), the archive does know. This is the asymmetry
      between the advertisement and the answer, and it is duplicated verbatim
      for consensus headers (:1076-1085 vs :1088-1108) and for certificates
      (certificate_pack.rs:291-297 vs :299-312).

    MUTATION PINS. {!No_contains_bounds_check} deletes :1241, so the
    advertisement fires on any [Ok(pos)] and conjunct A is refuted at the
    repaired state where d's entry points past the truncated file.
    {!No_digest_recheck} deletes :1261-1263, so the archive answers with the
    record occupying the recycled offset while believing it answered for d,
    and conjunct C is refuted.

    SIBLING-REPAIR HUNT for the bounds deletion: nothing prunes the digest
    index on repair (:680-684 says so explicitly), nothing rebuilds an index
    from the data file ([validate_pack_file] opens the data file read-only and
    only reports, pack_validate.rs:183-238), and [HdxIndex] exposes no delete
    API at all (index.rs:761-797). The fetch path's own bounds test and
    recheck are kept under this mutation and repair the ANSWER, never the
    ADVERTISEMENT - which is precisely why conjunct C still holds there and
    conjunct A does not. Reported honestly: the consensus-chain wrapper of
    this advertisement ([contains_current_batch], consensus.rs:1026-1028 and
    the trait declaration types/src/consensus_chain_traits.rs:115) has no
    in-tree caller at 0c59c15b, so conjunct A is a property of the storage
    API surface rather than of a live decision path; conjuncts B and C are on
    the live [PackMessage::Batch] path (:175-177). *)
let s3 =
  let bounds_gate =
    Formula.Ag (Formula.Implies (atom Advertised_yes, atom In_bounds_d))
  in
  let advertisement_is_not_payload_knowledge =
    Formula.Ag
      (Formula.Implies
         ( atom Advertised_yes,
           Formula.Not (Formula.K (Validator.V0, atom Holds_d)) ))
  in
  let answer_is_payload_knowledge =
    Formula.Ag
      (Formula.Implies
         (atom Answered_d, Formula.K (Validator.V0, atom Holds_d)))
  in
  {
    name =
      "contains-is-an-index-and-bounds-fact-while-only-the-fetch-binds-the-payload";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [
          bounds_gate;
          advertisement_is_not_payload_knowledge;
          answer_is_payload_knowledge;
        ];
    antecedent = atom Advertised_yes;
  }

(** The family's statements. *)
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
