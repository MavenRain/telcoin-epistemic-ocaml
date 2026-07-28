(** The ARCHIVE-PACK-HEAL family statements, encoded over the
    {!Archive_pack_heal_model} interpreted system. Every mechanism claim was
    re-verified against Telcoin-Association/telcoin-network at git 0c59c15b
    (working tree) while writing this module; file citations are to that
    checkout.

    What was mined: the three gates one epoch pack's files pass through
    between a failed append and the next open - the write-failure latch
    (archive/pack.rs:269), the append-open repair (consensus_pack.rs:664-728)
    and the read-only-open agreement gate (consensus_pack.rs:894-902) - and,
    for each, what the node running the pack can and cannot conclude from what
    it is actually shown.

    {b Reading guide for the K operands.}

    - S3's positive [K_V0 (data-ahead-of-index)] is knowledge of a fact about
      the background thread's private files. It is not a projection of [V0]'s
      own view: [V0] sees the collected error signal and the number of outputs
      the position index has committed to
      ([ConsensusPack::get_error], consensus_pack.rs:356-363;
      [contains_consensus_header_number], :1070-1072), and NEITHER of those is
      the data-file length - no method on [ConsensusPack] exposes
      [Pack::file_len] at all. The operand is contingent (false at every
      state before a save fails) and, crucially, the view does NOT determine
      it in the other direction: at a state where an error has been published
      but not yet collected, the data is already ahead of the index and [V0]'s
      view is the clean one, so the operative class is a genuine
      indistinguishability class rather than a relabelling of the signal.
    - S3's [not K_V0 (pack-latched)] and [not K_V0 (not pack-latched)] are the
      reason the positive conjunct stops where it does. Two different failure
      routes publish on the same watch and are erased into the same
      [PackError] by [send_replace] (:142): a torn data write, which DOES
      latch (archive/pack.rs:269), and an index-save failure at :1056-1058 or
      :1060-1062, which does NOT (the non-latching arm, archive/pack.rs:
      270-274). Both leave the files in the same shape, so the witness pair
      shares [V0]'s view exactly and disagrees on the latch.
    - S1's [not K_V0 (holds(w, n))] and [not K_V0 (not holds(w, n))] are about
      another node's disk. After the repair discards output [n], nothing the
      reopened node can read tells it whether it had already streamed those
      bytes to [w]: [get_partial_epoch_stream] (consensus.rs:587-602) is
      one-directional and leaves no receipt, and [trunc_and_heal] reports
      neither what it trimmed nor that it trimmed anything
      (consensus_pack.rs:665-670). The witness pair is two reachable healed
      states with an identical [V0] view - same four lengths - and opposite
      possession by [w].

    S2 carries NO K on purpose: it is the pure three-file agreement invariant,
    and the interesting thing about it is that it is the only place the
    agreement is ENFORCED rather than repaired. Any [K_V0] of it at a
    successfully-opened state would be rigid inside the operative view class
    (the four lengths [V0] sees ARE the agreement) and epistemically empty. *)

open Archive_pack_heal_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so a statement is never certified on
          the strength of an unreachable antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - append-open-repair-never-zero-extends-a-pack-whose-batch-index-survived
    [safety].

    Conjunct A - [AG (heal-ran /\ batch-final-above-header -> not
    heal-extended)]: whenever a pack is reopened for append with its batch
    digest index still tracking a real length, the repair can only ever
    shorten the data file. [Pack::truncate] is [DataFile::set_len]
    (archive/pack.rs:424-427), whose own doc says "Set the file length by
    truncating or extending" (archive/data_file.rs:134-136), so a repair that
    computed a length above the surviving data would zero-fill the gap. Two
    places compute such a length. Phase A (consensus_pack.rs:671-685) picks a
    surviving tracked length, and under this conjunct's guard both of its
    branches are bounded by the data: the [consensus_final > batch_final &&
    batch_final > DATA_HEADER_BYTES] branch (:675-676) truncates to
    [batch_final], and the [else if consensus_final > DATA_HEADER_BYTES]
    branch (:677-678) is only entered when [pack_len] already exceeds
    [consensus_final]. Phase B walks the position index back to the newest
    entry that fits (:687-712) and is clamped shrink-only at :713-716.

    The guard is load-bearing and is NOT decoration: drop it and the conjunct
    is FALSE on the pristine model. When the batch index is back at the bare
    header, :675's second test fails, control falls to :677, and
    [data.truncate(consensus_final)] runs with nothing bounding
    [consensus_final] by the bytes that survived - so a pack whose data tail
    was lost while its consensus digest index was already synced ahead grows
    on reopen. That state is reachable here (crash pattern
    [Dm_data_and_batch]) and test/t_archive_pack_heal.ml asserts it reachable,
    precisely so this statement cannot be read as claiming more than the clamp
    actually buys.

    Conjunct B - [AG (heal-ran /\ heal-dropped -> not K_V0 (holds(w, n)) /\
    not K_V0 (not holds(w, n)))]: when the repair drops an output the index
    had committed to, the node cannot conclude anything about that output's
    fate elsewhere. It may already have streamed those bytes to [w]
    ([get_partial_epoch_stream], consensus.rs:587-602, which serves the
    in-progress epoch straight off the live pack via
    [ConsensusChain::get_static]'s current-epoch short circuit,
    consensus.rs:1069-1072), or never have been asked. Both directions of the
    ignorance hold, so it can neither treat the output as lost nor as safe
    elsewhere.

    Mutation pin: [No_shrink_clamp] deletes consensus_pack.rs:716. On the
    at-rest configuration where the data file was lost back to the header
    while a single position-index entry survived, phase B's walk-back falls
    through to [idx = 0], calls [truncate_all], and carries that entry's
    [output_end] out of the loop; the clamp is the only thing that stops it
    being written into [data.truncate], so its deletion adds a healed state
    with [heal-extended] set AND the batch index above the header, refuting
    conjunct A. No sibling path repairs it - see the constructor's own doc:
    [files_consistent] never runs on an append open, [set_len] has no
    shrink-only assertion, and the repair's epilogue (:721-726) writes the
    extended length into both digest indexes, so a later [open_static] finds
    three agreeing files over a zero-filled region. *)
let s1 =
  let repair_only_shrinks =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Heal_ran, atom Batch_index_survived),
           Formula.Not (atom Heal_extended) ))
  in
  let dropped_output_fate_unknown =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Heal_ran, atom Heal_dropped_output),
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom Peer_holds_epoch_bytes)),
               Formula.Not
                 (Formula.K
                    ( Validator.V0,
                      Formula.Not (atom Peer_holds_epoch_bytes) )) ) ))
  in
  {
    name = "append-open-repair-never-zero-extends-a-pack-whose-batch-index-survived";
    bucket = Statements.Safety;
    formula = Formula.And (repair_only_shrinks, dropped_output_fate_unknown);
    antecedent = Formula.And (atom Heal_ran, atom Heal_dropped_output);
  }

(** S2 - read-only-open-enforces-the-three-file-agreement-that-append-open-only-repairs
    [safety].

    Conjunct A - [AG (open-static-ok -> files-consistent)]: the mode every
    peer-facing read of a past epoch goes through refuses outright unless the
    data-file length equals BOTH digest indexes' tracked lengths and the last
    position-index entry's [output_end]
    ([Inner::open_static] consensus_pack.rs:862-904, gate at :894-902 over
    [files_consistent] :640-662). This is the only place in the pack layer
    where that three-way agreement is enforced instead of quietly repaired,
    and it is what stands between a damaged archive and the dozen read paths
    that go through [ConsensusChain::get_static] (consensus.rs:450, 549, 593,
    762, 800, 839, 869, 906, 968, 984, 1000, 1037; the opened pack is then
    cached with no further validation, :1080-1087).

    Conjunct B - [AG (heal-ran -> digest-lengths-match)]: the append mode
    never refuses - it repairs - and its repair always terminates with the
    data file and BOTH digest indexes on the same length, because the
    epilogue writes the healed length into both unconditionally
    (consensus_pack.rs:721-726). That epilogue is exactly the sibling that
    would silently rescue a naive version of conjunct A, so it is modelled
    rather than omitted. The restart test at consensus.rs:1554-1560 documents
    the asymmetry from the other side: a torn-write pack that
    [open_append_exists] heals is a pack the old [open_static] path answered
    with [CorruptPack].

    Conjunct B stops at the digest halves of [files_consistent] (:647-652) on
    purpose, and this was checked rather than assumed: the append repair does
    NOT restore the position-index half (:653-658) in every case. Both index
    truncations in the walk-back are guarded by [idx != start_idx] (:695 and
    :706), so a position index holding exactly ONE entry - where [start_idx]
    is already 0 - is left completely untouched when that entry does not fit
    the surviving data, and the clamp at :716 then leaves the file where it
    was. The reopened pack therefore carries an entry claiming an [output_end]
    past the end of its own data file, which is precisely what conjunct A's
    gate rejects, so an append-open "repair" can produce a pack a later
    read-only open refuses. That state is reachable on the pristine model and
    test/t_archive_pack_heal.ml asserts it reachable, so the statement cannot
    be read as claiming the repair restores full three-file agreement.

    Mutation pin: [No_static_consistency_gate] deletes the :894-902 block, so
    the read-only open succeeds on every at-rest configuration and conjunct A
    is refuted by any damaged one. Conjunct B is untouched, which the
    targeting group in test/t_archive_pack_heal_mutation.ml asserts. The
    sibling hunt found exactly one partial repair, [get_epoch_stream]'s
    additional final-header check (consensus.rs:543-576); it covers the
    full-epoch-stream consumer only, and neither
    [get_partial_epoch_stream] (:587-602) nor any by-digest or by-number read
    re-checks anything the gate checked. *)
let s2 =
  let static_open_is_strict =
    Formula.Ag (Formula.Implies (atom Static_open_served, atom Files_agree))
  in
  let append_open_reconciles_the_digest_indexes =
    Formula.Ag (Formula.Implies (atom Heal_ran, atom Digest_lengths_match))
  in
  {
    name = "read-only-open-enforces-the-three-file-agreement-append-open-only-repairs";
    bucket = Statements.Safety;
    formula =
      Formula.And
        (static_open_is_strict, append_open_reconciles_the_digest_indexes);
    antecedent = atom Static_open_served;
  }

(** S3 - a-published-pack-error-reveals-the-index-fell-behind-but-not-whether-the-pack-fail-stopped
    [security].

    Conjunct A - [AG (error-seen -> K_V0 (data-ahead-of-index))]: when the
    node collects an error off the pack's watch, it KNOWS the background
    thread's data file now holds bytes past the last record the position index
    accounts for. Every route that reaches [tx_error.send_replace]
    (consensus_pack.rs:141-143) is an [Err] out of
    [Inner::save_consensus_output] (:1018-1067), and each of them appends
    before it indexes: the data append is at :1048-1051, the digest save at
    :1056-1058 and the position save at :1060-1062, all [?]-propagating, so no
    failing save ever leaves the index caught up with the data. That is a fact
    about files the node has no API to read - [Pack::file_len] is private to
    [Inner] - and it is precisely the condition the four defensive
    [pos < self.data.file_len()] guards were written for (:1080-1084,
    :1097-1099, :1240-1244, :1254-1256, each with the comment "in a very rare
    case of repairing a damaged pack we might have something in the index not
    in the pack file").

    Conjunct B - [AG (error-seen -> not K_V0 (pack-latched) /\ not K_V0 (not
    pack-latched))]: and that is ALL it learns. It does not learn whether the
    pack fail-stopped. [send_replace] keeps one erased [PackError] with no
    route identity, and two routes reach it with identical file effects: a
    torn data write, which sets [PackInner.failed] and makes every later
    append and commit fail (archive/pack.rs:269, :262-263, :299-301), and an
    index-save failure, which is an [IndexAppend] error and explicitly does
    NOT latch (the non-latching arm, archive/pack.rs:270-274). Both directions
    of the ignorance hold at the same view.

    What this statement deliberately does NOT claim is that the latch stops a
    well-formed record following a torn one. It does not, in this pack: two
    siblings get there first and are modelled rather than omitted. The caller
    short-circuits on the watch before it ever sends the next output
    ([save_consensus_output], consensus_pack.rs:367-368), and even if it did
    send, the consensus-number check (:1034-1043) refuses any output whose
    index is not exactly [consensus_pos_idx.len()] - which a torn save left
    behind. A digest-keyed writer over the same [Pack] has no such sibling
    ([CertificatePack]'s [Inner::save], certificate_pack.rs:277-289, checks
    only the incoming digest), which is where the latch is load-bearing for
    interleaving; that pack is out of this family's scope.

    Mutation pin: [No_write_failure_latch] deletes archive/pack.rs:269, so no
    reachable state is latched at all, [K_V0 (not pack-latched)] becomes true
    and conjunct B is refuted. The antecedent stays reachable under the
    mutation (the non-latching index-error route still publishes), so the pin
    is a genuine refutation and not a vacuity report. No sibling
    re-establishes the flag: [run_pack_loop] never rebuilds [inner]
    (consensus_pack.rs:132-193, certificate_pack.rs:53-86) and
    [DataFile::write] has no latch of its own (archive/data_file.rs:334-358).
    The one real repair - a fresh [PackInner] after a restart has
    [failed: false] (archive/pack.rs:202) - is in the model, as the crash
    erasing the latch, which is why the conjuncts are scoped to a state where
    the error is still being observed by a live process. *)
let s3 =
  let error_reveals_the_gap =
    Formula.Ag
      (Formula.Implies
         (atom Error_seen, Formula.K (Validator.V0, atom Data_ahead_of_index)))
  in
  let error_hides_the_latch =
    Formula.Ag
      (Formula.Implies
         ( atom Error_seen,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom Pack_latched)),
               Formula.Not
                 (Formula.K (Validator.V0, Formula.Not (atom Pack_latched))) )
         ))
  in
  {
    name = "published-pack-error-reveals-the-index-gap-not-whether-the-pack-fail-stopped";
    bucket = Statements.Security;
    formula = Formula.And (error_reveals_the_gap, error_hides_the_latch);
    antecedent = atom Error_seen;
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
