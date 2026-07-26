(** The EPOCH_RECORD statement family, encoded over the
    {!Epoch_record_model} interpreted system. All three statements were mined
    from telcoin-network, re-grounded line by line against this checkout (HEAD
    0c59c15b) and stated in the form that survived. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide. The hidden facts of this family are [Quorum_endorsed] - "at
    least 3 of the 4 epoch-1 committee members really did produce a BLS
    signature over [digest(R1)]", V1's OWN record - and the weaker
    [Some_record_certified] - "at least 3 of them signed SOME epoch-1 record,
    V1's R1 or a divergent R1'". Both are facts about OTHER validators'
    signing acts, and V1's view - (stage, store, byz) - contains no component
    of [endorse] at all. Outside its own vote-tally window V1 knows only its
    own signature (it signs and gossips its own vote at epoch_votes.rs:59-73),
    so every [K (V1, ...)] here is a claim that V1 has come to know a REMOTE
    collective act; and the operands are contingent, being false at the
    reachable [E_pending], [E_solo] and [E_byz] worlds.

    Two model features exist because the code has them and the statements must
    survive them, not because they make anything easier:

    - THE TALLY WINDOW. [manage_epoch_votes] sets [reached_quorum = true] the
      instant [signed_authorities.len() >= quorum] (epoch_votes.rs:103-104),
      strictly before the aggregate/verify/save at :152-166. Inside that
      window V1 holds quorum-many individually verified signatures and its
      database is still certless, so a blanket "certless implies ignorant"
      would be FALSE of the real system. Both ignorance conjuncts - S2(A) and
      S3(A) - therefore carry the [~tally_quorum_held(R1)] guard, and
      t_epoch_record.ml proves that the excluded window is exactly where V1
      does know ([tally-quorum-window-knows]).
    - THE DIVERGENT BRANCH. If the committee certifies R1' <> R1, the
      collector's cursor still advances past epoch 1 (epoch.rs:100-115) while
      [get_epoch_by_number(1)] stays [(R1, None)] for ever, because [save]
      files the certificate under the FETCHED record's digest
      (epoch_records.rs:601, :611-614) and reads resolve it under the STORED
      record's digest (:374-375). So "cursor past epoch 1" does NOT imply
      "my record is certified"; what it does imply is that SOME epoch-1
      record cleared [verify_with_cert]. S2(B)/(C) state that, and S2(D)
      states the contrapositive fact the divergence leaves behind.

    The three statements split the epoch-record lifecycle into: what a stored
    certificate BUYS (S1, security), what its absence leaves open and what the
    collector's cursor therefore does and does not certify (S2, safety), and
    that a genuine certified-record gap is inevitably closed (S3, liveness).

    A deliberate asymmetry, stated so it is not mistaken for an omission: S1
    asserts that a certificate buys knowledge of the quorum but NOT knowledge
    of the roster. V1 ends up knowing "three of us signed" while still unable
    to rule out that the Byzantine member was one of them - because the
    aggregator stops collecting at quorum and only lingers 1s for stragglers
    (epoch_votes.rs:103-110), so the frozen [RoaringBitmap] can under-report
    the true signer set. That third conjunct is also the family's R2
    non-degeneracy discharge, written into the statement rather than left to
    the test suite. *)

open Epoch_record_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a false antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - epoch-cert-implies-known-super-quorum-endorsement [security].
    Whenever V1's epoch DB holds a certificate for its own epoch-1 record, a
    super-quorum really did sign that record's digest, and V1 KNOWS a
    super-quorum signed - yet V1 still cannot tell WHICH members signed.

    (A) gate: AG( store_has_cert(1) -> quorum_endorsed(R1) ).
    [EpochRecord::verify_with_cert] refuses a certificate whose [epoch_hash]
    is not the record's own digest (crates/types/src/primary/epoch.rs:59-63),
    then counts matched [RoaringBitmap] indices into [auth_iter] (:65-79) and
    returns false BEFORE the pairing check when
    [auth_iter < self.super_quorum()] (:84-88); [super_quorum] is
    [((committee.len() * 2) / 3) + 1] = 3 for n = 4 (:94-96). Distinctness is
    structural: the bitmap yields sorted distinct indices and the closure
    advances [auth_iter] at most once per committee slot. Every production
    certificate write is downstream of that predicate - epoch.rs:107 via
    state-sync/src/epoch.rs:102, epoch_votes.rs:159 via :156,
    epoch_votes.rs:207/:213 via :200 - and the digest keying of the write
    (epoch_records.rs:601, :611-614) is what makes [store_has_cert(1)] mean
    "certified R1", not merely "certified something": on the divergent branch
    [E_alt] the certificate lands under [digest(R1')] and this atom stays
    false.

    (B) known: AG( store_has_cert(1) -> K_V1( quorum_endorsed(R1) ) ).
    [BlsAggregateSignature::verify_secure] aggregate-verifies one copy of the
    intent message per listed public key and returns false ONLY for an empty
    key list (crates/types/src/crypto/bls_signature.rs:270-286), so clearing
    epoch.rs:84-88 is exactly "three distinct committee members each produced a
    BLS signature over this epoch digest". Those signatures are REMOTE acts,
    gossiped as [EpochVote] and admitted only after a committee-membership
    check plus a full BLS verify (handler.rs:452-461). K is not knower-local:
    [endorse] appears in no view, and outside its own tally window V1 locally
    knows only its own signature (epoch_votes.rs:59-73). It is not rigid
    either - [quorum_endorsed] is false at the reachable [E_pending],
    [E_solo], [E_byz] and [E_alt] worlds, and V1's view does not determine it
    in general: at (Sg_scan1, St_rec, B_avail) the worlds [E_solo] and
    [E_quorum3] share V1's view. Knowledge arrives exactly on the
    [Store_cert] classes, which is precisely what the certificate buys.

    (C) which_members_opaque:
    AG( (store_has_cert(1) /\\ ~byz_endorsed(R1)) ->
        ~K_V1( ~byz_endorsed(R1) ) ).
    The aggregator stops collecting once [signed_authorities] reaches
    [quorum] and then only lingers 1s for stragglers, breaking outright only at
    full committee (epoch_votes.rs:103-110), so a 4th member's vote can arrive
    after the bitmap is frozen; the stored certificate therefore does NOT
    determine the true signer set. Concretely: at
    (E_quorum3, St_cert, Sg_scan2, B_avail) - where V3 did not sign - V1 cannot
    rule out (E_quorum4, St_cert, Sg_scan2, B_avail), which shares its view.
    This conjunct IS the R2 non-singleton discharge for conjunct (B): the class
    that makes (B)'s K true provably holds two reachable worlds.

    DELIBERATELY NOT ASSERTED: an [Ef] "a sub-quorum certificate can be offered
    and refused" conjunct. It would make S1 spuriously refuted by BOTH other
    mutations (each makes the Byzantine offer unreachable for reasons unrelated
    to the quorum gate). It is discharged in t_epoch_record.ml as a contingency
    witness instead, keeping S1's refutation attributable to epoch.rs:84 alone.

    Mutation pin: {!Epoch_record_model.No_quorum_count} deletes the
    [auth_iter < super_quorum] branch (epoch.rs:84), rewriting the Byzantine
    answer at (Sg_scan1, St_rec, B_avail) from "refused, cursor lowered, retry"
    to "accepted and saved". (E_solo, St_cert, Sg_scan1, B_spent) becomes
    reachable: conjunct (A) is refuted directly, and conjunct (B) is refuted
    because the (Sg_scan1, St_cert, B_spent) class now contains an [E_solo]
    world. The one genuine sibling - the producer-side count at
    epoch_votes.rs:103 - is KEPT LIVE in the model (the [Sg_tally] and
    [Sg_tally_quorum] steps are mutation-independent), so the refutation cannot
    be an artefact of over-wide mutation. *)
let s1 =
  let gate =
    Formula.Ag (Formula.Implies (atom Store_cert, atom Quorum_endorsed))
  in
  let known =
    Formula.Ag
      (Formula.Implies
         (atom Store_cert, Formula.K (Validator.V1, atom Quorum_endorsed)))
  in
  let which_members_opaque =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Store_cert, Formula.Not (atom Byz_endorsed)),
           Formula.Not
             (Formula.K (Validator.V1, Formula.Not (atom Byz_endorsed))) ))
  in
  {
    name = "epoch-cert-implies-known-super-quorum-endorsement";
    bucket = Statements.Security;
    formula = Formula.And (gate, Formula.And (known, which_members_opaque));
    antecedent =
      Formula.And (atom Store_cert, Formula.Not (atom Byz_endorsed));
  }

(** S2 - uncertified-epoch-record-implies-ignorance-until-cert [safety].
    Outside its own vote-tally window, a certless epoch-1 record leaves V1
    ignorant of whether a super-quorum endorsed THAT record; and the
    collector's cursor passes epoch 1 only once some epoch-1 record has been
    super-quorum certified - which V1 then knows - even though the record so
    certified need not be V1's own.

    (A) ignorance:
    AG( (~store_has_cert(1) /\\ ~tally_quorum_held(R1)) ->
        ~K_V1( quorum_endorsed(R1) ) ).
    At epoch close a member persists its self-built [EpochRecord] with
    [save_record], i.e. with NO certificate
    (crates/node/src/manager/node/close_epoch.rs:238-247); "record without
    cert" is first-class and persistent in storage - [get_epoch_by_number]
    returns [(EpochRecord, Option<EpochCertificate>)]
    (crates/storage/src/epoch_records.rs:369-377). The code's own witness that
    the committee may certify a DIFFERENT record is the [alt_recs] tally and
    its "Reached quorum on epoch record X instead of Y" error
    (epoch_votes.rs:112-127). So the certless window is exactly where V1's view
    is compatible with "the committee will certify my record", with "the
    committee reached quorum on something else" and with "nobody reached
    quorum".

    The [~tally_quorum_held(R1)] guard is NOT a convenience: [manage_epoch_votes]
    flips [reached_quorum = true] at epoch_votes.rs:103-104, holding
    quorum-many votes that each cleared the handler's BLS verify
    (handler.rs:452-461), strictly BEFORE it aggregates (:152), re-verifies
    (:156) and saves (:159). In that window the database is certless and V1
    demonstrably DOES know, so the unguarded claim would be false of the real
    system. The window is bounded and non-persistent: every exit arm returns
    from [manage_epoch_votes] and drops [sigs]/[signed_authorities]
    (epoch_votes.rs:158-186, :232), and the model's next stage is a process
    restart, so the ignorance resumes at [Sg_boot] and after.

    (B) completion_needs_some_quorum:
    AG( cursor>1 -> quorum_certified(some epoch-1 record) ).
    [collect_epoch_records] sets [result_epoch = epoch] only inside the
    [if let Some((rec, Some(_)))] complete arm
    (crates/state-sync/src/epoch.rs:61-64) - whose certificate was itself
    written downstream of a [verify_with_cert] - or after a fetched pair passes
    the parent, committee and [verify_with_cert] conjuncts (epoch.rs:100-115);
    it breaks at the first epoch it could not confirm
    ([if result_epoch != epoch { break; }], epoch.rs:147-149) and every failure
    path lowers the cursor with [return epoch.saturating_sub(1)] (epoch.rs:96,
    :113, :136). So passing epoch 1 certifies the EXISTENCE of a super-quorum
    signed epoch-1 record, and nothing about whose it is.

    (C) completion_implies_knowledge:
    AG( cursor>1 -> K_V1( quorum_certified(some epoch-1 record) ) ).
    V1 runs the verification itself (epoch.rs:102) or already held the
    certificate that let it skip (epoch.rs:61), so the existential is settled
    for V1 at the moment the cursor moves - which is also the moment it
    publishes [rec.final_consensus] as a trusted sync checkpoint
    (epoch.rs:66-73). R2 for this positive K is the two-world class
    (Sg_scan2, St_cert, B_avail), holding both (E_quorum3, ...) and
    (E_quorum4, ...): V1 knows the existential without knowing the roster.
    Stated honestly, on the divergent branch the class
    (Sg_scan2, St_rec, B_avail) is a singleton - there V1's own verification
    IS its evidence - so the non-degenerate content of this conjunct lives at
    the [St_cert] classes, which is where the test suite discharges it.

    (D) certless_completion_means_divergence:
    AG( (cursor>1 /\\ ~store_has_cert(1)) -> ~quorum_endorsed(R1) ).
    The newly modelled fact. If the cursor passed epoch 1, some pair cleared
    [verify_with_cert], which requires [cert.epoch_hash] to equal the FETCHED
    record's digest (types/src/primary/epoch.rs:59-63). Had that record been R1
    itself, [Inner::save] would have filed the certificate under [digest(R1)]
    (epoch_records.rs:601, :611-614), which is exactly the key
    [get_epoch_by_number] reads it back under (:374-375), so
    [store_has_cert(1)] would be true. Hence a certless completion means the
    certified record was R1' <> R1 - and with n = 4, f = 1 two distinct
    super-quorum certified records are impossible (any two 3-subsets of a
    4-set share 2 members, who would each have had to vote twice; the vote
    bookkeeping at epoch_votes.rs:98 and :115 is annotated "so a validator can
    only vote once (correct or alt), no equivocation"), so R1 was not
    super-quorum endorsed. Note that this is permanent: the record is not
    overwritten ([save_record] no-ops on a filled epoch slot,
    epoch_records.rs:570-576) and a rescan hits the cert-already-stored early
    return (:607-609).

    Mutation pin: {!Epoch_record_model.Cert_conjunct_dropped} relaxes
    epoch.rs:61 to [Some((rec, _))], replacing the whole (Sg_scan1, St_rec)
    fetch fan-out with a single [{ stage = Sg_scan2 }] step.
    (E_solo, St_rec, Sg_scan2, B_avail) becomes reachable - a cursor past an
    epoch NOBODY certified - refuting (B) directly, refuting (C) because the
    (Sg_scan2, St_rec, B_avail) class then contains an [E_solo] world, and
    refuting (D) because (E_quorum3, St_rec, Sg_scan2, B_avail) becomes
    reachable too. The serve-side certificate demand at handler.rs:1010-1025
    limits contagion to peers but is not a repair of V1's own belief.
    {!Epoch_record_model.Cursor_starts_at_latest} refutes (C) as a side effect
    (documented, not the chosen pin). *)
let s2 =
  let ignorance =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             (Formula.Not (atom Store_cert), Formula.Not (atom Tally_quorum_held)),
           Formula.Not (Formula.K (Validator.V1, atom Quorum_endorsed)) ))
  in
  let completion_needs_some_quorum =
    Formula.Ag
      (Formula.Implies (atom Collector_past_epoch, atom Some_record_certified))
  in
  let completion_implies_knowledge =
    Formula.Ag
      (Formula.Implies
         ( atom Collector_past_epoch,
           Formula.K (Validator.V1, atom Some_record_certified) ))
  in
  let certless_completion_means_divergence =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Collector_past_epoch, Formula.Not (atom Store_cert)),
           Formula.Not (atom Quorum_endorsed) ))
  in
  {
    name = "uncertified-epoch-record-implies-ignorance-until-cert";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [
          ignorance;
          completion_needs_some_quorum;
          completion_implies_knowledge;
          certless_completion_means_divergence;
        ];
    antecedent = Formula.And (atom Collector_past_epoch, atom Store_cert);
  }

(** S3 - restart-rescan-from-zero-recovers-certified-record-gap [liveness].
    On a branch where a super-quorum really did endorse V1's own epoch-1
    record but V1 holds the record without the certificate, V1 does not yet
    know a super-quorum endorsed - unless it is still inside its own tally
    window - and, because the collector task initialises its scan cursor to
    epoch 0 on every process start, it inevitably comes to know it.

    (A) gap_is_ignorant:
    AG( (~store_has_cert(1) /\\ quorum_endorsed(R1) /\\
         ~tally_quorum_held(R1)) ->
        ~K_V1( quorum_endorsed(R1) ) ).
    The same certless window as S2(A) (close_epoch.rs:238-247; storage keeps
    [(record, None)] indefinitely, epoch_records.rs:369-377), with the same
    tally-window guard for the same reason: [reached_quorum] is set at
    epoch_votes.rs:103-104 while the DB is still certless, so an unguarded
    claim would be false of the real system. This conjunct is load-bearing for
    the liveness: it guarantees the [Af] target is NOT already true at the
    settled gap states, so the "eventually" is not degenerate there.
    Ignorance witness (R3): (E_solo, St_rec, Sg_boot, B_avail) and
    (E_quorum3, St_rec, Sg_boot, B_avail) share V1's view
    View_v1 (Sg_boot, St_rec, B_avail) and disagree on [quorum_endorsed]; the
    divergent world (E_alt, St_rec, Sg_boot, B_avail) sits in the same class.

    (B) backfill:
    AG( (~store_has_cert(1) /\\ quorum_endorsed(R1)) ->
        AF K_V1( quorum_endorsed(R1) ) ), i.e. [Formula.leads_to].
    Unguarded on purpose: inside the tally window the target already holds, so
    the [Af] is satisfied immediately there and the claim is strictly stronger
    than the guarded one. Elsewhere it is the collector that delivers:
    [spawn_epoch_record_collector] deliberately sets
    [let mut last_epoch: Epoch = 0;] (crates/state-sync/src/epoch.rs:190) under
    the comment "Always start from epoch 0 so any gaps (epochs whose certs were
    never saved, e.g. because the node was killed during a failed-quorum
    recovery) are back-filled on restart" (epoch.rs:185-189). Already-complete
    epochs are skipped immediately (epoch.rs:61-75), the gap falls through to
    [request_epoch_cert] (epoch.rs:78) and the three-conjunct verification
    (epoch.rs:100-107); every failure lowers the cursor (epoch.rs:136) and the
    outer select re-arms on the 5s [EPOCH_COLLECT_RETRY_SECS] timer as well as
    on the watch (epoch.rs:15-16, :206-212). Because a super-quorum really
    signed R1 on these branches, the certificate a correct peer serves is one
    for R1 itself, so [save] files it under the stored record's own digest and
    [get_epoch_by_number] resolves it (epoch_records.rs:601, :611-614,
    :374-375) - the divergent branch of S2(D) is exactly the case this
    antecedent excludes.

    The environment assumption is NOT manufactured (R8): [request_epoch_cert]
    retries up to three times from three DIFFERENT peers
    (crates/consensus/primary/src/network/mod.rs:809-829), which with f = 1 of
    4 reaches a correct peer, so the model encodes exactly one adversarial or
    failed answer per gap as the one-slot [byz] budget. Note also that the
    reset to 0 is a PROCESS-START behaviour, not a per-tick one - the binding
    sits outside the loop (epoch.rs:190-191) - so the model encodes it as the
    one-shot [Sg_boot] step and needs no "restarts infinitely often" fairness
    assumption.

    Mutation pin: {!Epoch_record_model.Cursor_starts_at_latest} makes the
    [Sg_boot] step land on [Sg_scan2] instead of [Sg_scan0], so [Sg_scan0] and
    [Sg_scan1] become unreachable and (E_quorum3, St_rec, Sg_scan2, B_avail)
    livelocks on its self-loop forever: the [Af] target is never reached and
    (B) fails. The kernel stutter-closes terminals, so the livelock is honest.
    {!Epoch_record_model.Cert_conjunct_dropped} and
    {!Epoch_record_model.No_quorum_count} also refute it (documented, not the
    chosen pin: the first skips the fetch so the gap is never filled, the
    second poisons the K by admitting an [E_solo] world into the [St_cert]
    view classes). *)
let s3 =
  let gap = Formula.And (Formula.Not (atom Store_cert), atom Quorum_endorsed) in
  let settled_gap =
    Formula.And (gap, Formula.Not (atom Tally_quorum_held))
  in
  let gap_is_ignorant =
    Formula.Ag
      (Formula.Implies
         ( settled_gap,
           Formula.Not (Formula.K (Validator.V1, atom Quorum_endorsed)) ))
  in
  let backfill =
    Formula.leads_to gap (Formula.K (Validator.V1, atom Quorum_endorsed))
  in
  {
    name = "restart-rescan-from-zero-recovers-certified-record-gap";
    bucket = Statements.Liveness;
    formula = Formula.And (gap_is_ignorant, backfill);
    antecedent = gap;
  }

(** The family's statements: what a certificate buys (S1), what its absence
    leaves open and what the cursor does and does not certify (S2), and that a
    genuine gap is inevitably closed (S3). *)
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
