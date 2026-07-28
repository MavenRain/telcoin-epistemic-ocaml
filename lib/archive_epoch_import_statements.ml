(** Statements of the ARCHIVE-EPOCH-IMPORT family: what
    [ConsensusChain::stream_import] (crates/storage/src/consensus.rs:441-541)
    certifies when it publishes a peer's epoch pack, what it refuses to
    certify, what it protects while it does so, and what it lets a hostile
    stream buffer on the way.

    {b Reading guide for the [K] operands.} The only knowledge agent that
    appears under [K] is [V0], the importing node [v]. Its view
    ({!Archive_epoch_import_model.View_node}) is its own pipeline position, the
    stream version it dispatched on, the digest count the header declared, its
    own buffer occupancy and the outcome of its own
    [consensus_header_by_number] lookup.

    - [K_v(holds(w, start..final))] is NOT a projection of [v]'s view: the
      operand is what the serving peer's archive actually contains, and the
      model never puts {!Archive_epoch_import_model.hold} in [V0]'s view. It is
      not rigid either - it is FALSE at every state of the
      {!Archive_epoch_import_model.initial_peer_prefix} run, where the peer
      held only start..final-1. The knowledge is created by the publish-time
      equality at consensus.rs:492-497 on top of the streamed linkage checks at
      consensus_pack.rs:975-986: gapless-from-the-previous-epoch plus
      last-header-equals-the-certified-final is what upgrades "some prefix
      arrived" to "the peer had the whole interval".
    - [~K_v(holds(w, final+1))] is the matching ignorance. The responder streams
      only up to the requested final number, so a peer that is exactly at the
      boundary and a peer that is a whole output past it put identical bytes on
      the wire and produce an identical import outcome; [V0]'s view coincides
      and the two states disagree on the operand. Concretely
      {!Archive_epoch_import_model.initial_peer_exact}'s published state and
      {!Archive_epoch_import_model.initial_peer_ahead}'s published state are
      that pair, and they are also the two members that make the positive [K]'s
      view class non-singleton.

    S2 and S3 carry no [K]: S2 is an availability property of the install and
    S3 is a resource bound on adversary-controlled input. *)

open Archive_epoch_import_model

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

(** S1 - an-epoch-pack-is-published-only-after-its-final-header-matches-the-
    certified-record [security].

    Conjunct A: [AG( published(v,e) -> K_v( holds(w, start..final) ) )]. An
    imported epoch is streamed into a throwaway [import-{e}] directory
    ([ImportPath], consensus.rs:1289-1335), verified link by link as it arrives
    ([output.parent_hash() != parent_digest -> InvalidConsensusChain],
    [consensus_number > final_consensus_number -> InvalidConsensusNumber],
    [parent_digest = output.digest()], consensus_pack.rs:975-986) from an
    anchor that is the PREVIOUS epoch's final hash (:952-956) behind
    [verify_epoch_meta] (:932, definition :1318), and only then compared
    against the certified epoch record:
    [if epoch_record.final_consensus.number != last_header.number ||
    epoch_final_hash != last_header.digest() { return
    Err(ConsensusChainError::InvalidImport) }] (consensus.rs:492-497). Only
    after that does the rename at :520 publish it. So whenever [v] has
    published, [v] knows - in the indistinguishability sense - that the peer it
    streamed from really held the whole gapless interval, because every
    reachable state sharing [v]'s view at a published state has a peer that
    did.

    Conjunct B: [AG( published(v,e) -> ~K_v( holds(w, final+1) ) )]. It implies
    nothing about the far side of the epoch boundary. The stream simply stops
    at the requested final number, and a stopped stream is indistinguishable
    from a peer that has more and was asked for less.

    {b Mutation pin.} {!No_final_header_link} deletes consensus.rs:492-497,
    which removes the {!St_batches} -> {!St_link_rejected} transition of the
    {!Peer_prefix} run and adds {!St_batches} -> {!St_published} in its place.
    A published state then shares [v]'s view with a state whose peer held only
    start..final-1, so conjunct A fails. No sibling path repairs it at publish
    time: the streamed linkage certifies gaplessness, never arrival at the
    requested final; [files_consistent] (consensus_pack.rs:894-902) passes on a
    truncated-but-cleanly-closed pack; and [is_epoch_complete]
    (consensus.rs:922-930) is a LATER re-check that can prompt a re-stream but
    never un-publishes what was already renamed in. The one caller-side filter
    that does re-run the equality is [get_epoch_stream] (consensus.rs:549-566),
    which refuses to serve an incomplete pack ONWARD to a peer; it bounds
    propagation, not local trust, since [get_partial_epoch_stream] (:587-602)
    explicitly does not require completeness and the ordinary read path takes
    whatever is published ([get_static] then [get_consensus_output_bytes],
    :906-918). The statement is about what publishing certifies, and that is
    what the deletion breaks. *)
let s1 =
  let publish_certifies_possession =
    Formula.Ag
      (Formula.Implies
         ( atom Published,
           Formula.K (Validator.V0, atom Peer_holds_full_epoch) ))
  in
  let publish_says_nothing_beyond =
    Formula.Ag
      (Formula.Implies
         ( atom Published,
           Formula.Not (Formula.K (Validator.V0, atom Peer_holds_beyond_epoch))
         ))
  in
  {
    name =
      "an-epoch-pack-is-published-only-after-its-final-header-matches-the-certified-record";
    bucket = Statements.Security;
    formula =
      Formula.And (publish_certifies_possession, publish_says_nothing_beyond);
    antecedent = atom Published;
  }

(** S2 - an-already-held-epoch-is-never-unlinked-for-a-redundant-import
    [liveness].

    Conjunct A: [AG( already_held(v,e) -> AG( reader_waiting -> AF(
    reader_answered ) ) )]. Installing an imported epoch is a remove-then-rename
    of the live directory - [if std::fs::exists(&base_dir) {
    remove_dir_all(&base_dir) }] at consensus.rs:513-519 then [rename] at :520 -
    and the source says in-line that this "will leave a tiny window before the
    rename where it is not available". Readers do not synchronise with it:
    [ConsensusChain::get_static] (:1067-1088) consults [current_pack], scans
    the [recent_packs] FIFO and otherwise calls
    [ConsensusPack::open_static(&self.base_path, epoch)], taking no
    [pack_install] lock at any point. The guard at :450-464 - [get_static],
    then [consensus_header_by_number(final.number)], then
    [have.digest() == epoch_final_hash] then [return Ok(())] - is what keeps a
    redundant import from entering that window at all, so every reader of an
    already-held epoch is answered.

    Conjunct B: [AG( already_held(v,e) -> ~epoch_dir_absent )], the safety twin:
    in the already-held branch the canonical directory is never unlinked in the
    first place.

    {b Mutation pin.} {!No_already_held_shortcircuit} deletes
    consensus.rs:458-464, which removes {!St_idle} -> {!St_shorted} for
    [have = Have_final] and adds the full remove+rename pipeline, so the
    already-held run passes through {!St_unlinked} (conjunct B) and a reader
    that reaches [open_static] there is answered with an error (conjunct A).

    {b Sibling-repair hunt.} The [recent_packs] cache genuinely answers inside
    the window - a cached [ConsensusPack] keeps its descriptors and the
    installer's purge at :526 runs AFTER the rename at :520, not inside the
    window - so the model gives it to the reader
    ({!Archive_epoch_import_model.reader_answer}). It is defeated the way the
    real cache is defeated: the FIFO holds [PACK_CACHE_SIZE = 10] entries
    (:323) and [get_static] evicts with [pop_front] before every push
    (:1080-1083). [ImportPath::new] refuses only a second concurrent import of
    the same epoch in this process (:1305-1308); the [pack_install] mutex
    (:509, declared :305-311) serialises installers, not readers; and
    [import_partial_to_staging] (:312-318) diverts only PARTIAL sync prefixes -
    the full-pack branch at
    crates/consensus/primary/src/network/mod.rs:1264-1265 still calls
    [stream_import]. No caller retries either: every [get_static] site is an
    [if let Ok(pack) = .. else <give up>] (consensus.rs:549, 593, 762, 800,
    839, 869, 906-918, 968, 984, 1000, 1037), whose give-up arm is [Ok(None)],
    [StreamUnavailable] or the staging fallback for the in-progress epoch -
    which is why a failed reader is terminal in the model rather than
    eventually served.

    {b Not true by omission.} The pristine model does contain the unlink
    window: {!initial_incomplete_pack} and {!initial_incomplete_pack_ahead}
    hold an [epoch-{N}] directory that does not resolve the requested final
    number, so the short circuit does not fire, [std::fs::exists] at :513 is
    true and the run passes through {!St_unlinked} with no mutation applied.
    S2 is about the already-held branch, not about the window not existing. *)
let s2 =
  let readers_always_answered =
    Formula.Ag
      (Formula.Implies
         ( atom Redundant_import,
           Formula.Ag
             (Formula.Implies (atom Reader_waiting, Formula.Af (atom Reader_served)))
         ))
  in
  let directory_never_unlinked =
    Formula.Ag
      (Formula.Implies (atom Redundant_import, Formula.Not (atom Epoch_dir_absent)))
  in
  {
    name = "an-already-held-epoch-is-never-unlinked-for-a-redundant-import";
    bucket = Statements.Liveness;
    formula = Formula.And (readers_always_answered, directory_never_unlinked);
    antecedent = atom Redundant_import;
  }

(** S3 - a-streamed-output-declares-its-batch-count-before-any-batch-is-buffered
    [security].

    Conjunct A: [AG( importing(v,w) -> buffered <= MAX_BATCHES_PER_OUTPUT )].
    Whichever stream version the sender chose, the importer never holds more
    than the cap in [available_batches]. The v1 decoder rejects up front
    (consensus_pack.rs:1466-1468) and the legacy v0 decoder trips a running
    counter after at most the cap (:1575, :1587-1590);
    [stream_import] dispatches between them on [stream_iter.version() == 0]
    (:960-974), i.e. the SENDER picks, so both branches must hold.

    Conjunct B: [AG( stream_v1 /\ declared > MAX -> buffered = 0 )]. In the v1
    format the header arrives first - a leading [Batch] record is rejected
    outright (:1428-1440) - so the number of batch digests the output references
    is known from [expected_batch_digests.len()] (:1451-1459) before the batch
    loop at :1477 inserts anything, and an over-cap declaration is refused
    with [TooManyBatches] having buffered nothing at all. The cap is one
    constant applied to every peer (:1371-1376, 50 under [cfg(test)]): there is
    no per-peer exemption and nothing a stream can do to raise its own limit.
    The conjunct is deliberately restricted to v1, because it is FALSE of the
    legacy path, which buffers up to the cap before its counter trips - that
    asymmetry is the content of the "reject early - before reading/buffering
    any batches - like the legacy path does" comment at :1463-1465.

    {b Mutation pin.} {!No_batch_count_cap} deletes
    consensus_pack.rs:1466-1468, which removes {!St_header} -> {!St_capped}
    for a v1 flood and adds {!St_header} -> {!St_batches} with {!Buf_flood}:
    both conjuncts fail at that state.

    {b Sibling-repair hunt.} [MAX_RECORD_SIZE] bounds each record but not how
    many are named (archive/pack_iter.rs:25, :100-102, :120-123); the loop's
    terminating condition [if digest_count == expected_digest_count] (:1496-1499)
    is derived from the same unbounded count; the per-record
    [tokio::time::timeout] (:1409-1419) bounds latency, not memory; and the v0
    counter is in a different function that the sender can simply decline to
    use. The v0 branch is kept live in the model so that this can be checked
    rather than asserted: under the mutation the v0 flood is still capped and
    only the v1 flood overruns, which
    test/t_archive_epoch_import_mutation.ml asserts. *)
let s3 =
  let import_buffer_is_bounded =
    Formula.Ag
      (Formula.Implies
         (atom Stream_in_progress, Formula.Not (atom Buffer_over_cap)))
  in
  let over_cap_declaration_buffers_nothing =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Stream_is_v1, atom Declares_over_cap),
           Formula.Not (atom Batches_buffered) ))
  in
  {
    name = "a-streamed-output-declares-its-batch-count-before-any-batch-is-buffered";
    bucket = Statements.Security;
    formula =
      Formula.And
        (import_buffer_is_bounded, over_cap_declaration_buffers_nothing);
    antecedent =
      Formula.And (atom Stream_is_v1, atom Declares_over_cap);
  }

(** The family's statements. *)
let all = [ s1; s2; s3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st = Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

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
