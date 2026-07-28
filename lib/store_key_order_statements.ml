(** The STORE_KEY_ORDER statements: three readings of one ordered index over
    the interpreted system of {!Store_key_order_model} - the encoding contract
    that makes a byte-ordered scan mean what its consumers think it means (S1),
    what the guarded probe entitles the probing node to KNOW about another
    node's act (S2), and what the same guard is holding up on the liveness side
    - the ancestor fetch for an authority the node has never heard from (S3).

    S1 is the premise of S2 and S3 rather than a restatement of them: it is
    about which ROW the scan lands on, and it is refuted by deleting an encoder
    option in types/src/codec.rs; S2 and S3 are about which AUTHORITY the
    landed-on row is allowed to speak for, and they are refuted by deleting a
    name test in stores/certificate_store.rs. Neither mutation refutes the
    other's statements - test/t_store_key_order_mutation.ml asserts that
    separation explicitly.

    READING GUIDE for the K operands - why neither is a projection of its own
    knower's view, and why neither is rigid:

    - [K_V0(signed(j, R_hi))] in S2 conjunct A. V0's view is its own three
      [CertificateDigestByOrigin] rows plus the stage its fetch decision has
      reached ({!Store_key_order_model.view}). "Authority [j] signed a
      certificate at round [R_hi]" is [j]'s act, not a function of that view:
      the model's signing ghost is free at every state where V0 has no row for
      [(j, R_hi)], so V0's view is compatible with both truth values there -
      which is precisely the real situation of a node whose fetch has not
      completed. Nor is the operand rigid: it is false at plenty of reachable
      states (any state where [j] has been silent). What makes it KNOWN at an
      [Answer_high] state is not V0's belief but the write path: a row exists
      only because [save_cert] derived its key from a certificate [j] authored
      (stores/certificate_store.rs:140-142), and the [&name == origin] test at
      :414-416 is what forces the answered round to come from [j]'s own row.
      Delete that test and V0's view is unchanged while the operand is false -
      that is the refutation.
      NON-DEGENERACY (R2): at an operative [Answer_high] state, V0's view class
      is not a singleton - it contains at least the two states that differ in
      whether [k] signed at [R_hi], which V0 cannot see when it holds no row
      for [k]. test/t_store_key_order.ml discharges that as
      [Answer_high /\ ~K_V0(~signed(k, R_hi))].

    - [~K_V0(~signed(j, R_hi))] in S2 conjunct B. The negative answer is NOT
      knowledge. [Ok(None)] at stores/certificate_store.rs:418 means only "no
      record before the sentinel named [j]"; it says nothing about whether [j]
      authored, because V0's index is the set of certificates V0 has RECEIVED
      and verified, not the set that exists. The ignorance witness is a pair of
      reachable states with identical V0 views - both with an empty [j] block,
      so both answering [None] - that disagree on the ghost. This is exactly
      the state the [unwrap_or(true)] at certificate_fetcher.rs:236 is written
      for: a missing answer is treated as "go and find out", not as "there is
      nothing to find".

    Buckets reuse the frozen {!Statements} vocabulary. *)

open Store_key_order_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;  (** unique across every family *)
  bucket : Statements.bucket;  (** Safety | Liveness | Fairness | Security *)
  formula : atom Formula.t;  (** the claim, proved with [prove_nonvacuous] *)
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - ordered-scan-lands-on-the-origins-greatest-stored-round [safety].

    Both persistent backends order rows by the RAW BYTES of the encoded key
    (redb: [fn compare(data1, data2) { data1.cmp(data2) }],
    storage/src/redb/wraps.rs:10-16; mdbx: tables opened with
    [DatabaseFlags::default()], i.e. MDBX's default lexicographic byte compare,
    storage/src/mdbx/database.rs:154-159), while [record_prior_to] iterates
    that byte stream and stops on the DECODED [Ord] of the key
    (mdbx/database.rs:231-240, redb/database.rs:239-251). The statement is that
    the two orders agree, so the record before the sentinel [(j, Round::MAX)]
    really is [j]'s greatest stored round. That agreement is manufactured by
    one line - [.with_big_endian()] at types/src/codec.rs:45, inside
    [encode_key] at :43-49 - under the contract stated at :18-19 ("This proper
    sorting MUST be maintained else stuff will break").

    - Conjunct A: whenever the probe has run and [(j, R_hi)] is stored, the
      answer is [R_hi]. This is the top of the scan: the highest-sorting row of
      [j]'s block must be the one the walk ends on.
    - Conjunct B: an answer of [R_lo] happens only when [R_lo] really is [j]'s
      greatest stored round - the scan never reports a round that a larger
      stored round shadows.
    - Conjunct C: when [j]'s only row is at [R_lo], the probe does report it.
      The [break] at mdbx/database.rs:234 fires on the first decoded key at or
      after the sentinel, and [Round::MAX = 0xFFFFFFFF] is byte-palindromic, so
      the sentinel stays the byte-maximum under either encoding and no present
      row of [j] is ever cut off. Nothing in the family refutes this conjunct;
      it is stated because it is what confines the endianness damage to the
      choice BETWEEN rows rather than to their visibility.

    MUTATION PIN. {!Store_key_order_model.No_big_endian} deletes
    [.with_big_endian()] from [encode_key] (types/src/codec.rs:45). The
    [Round] suffix then encodes little-endian, so for the modelled pair
    [R_lo = 1] ([01 00 00 00]) and [R_hi = 256] ([00 01 00 00]) the cursor
    emits [(j, R_hi)] BEFORE [(j, R_lo)] and the walk ends on the LOWER round:
    conjuncts A and B both fail at the state where both of [j]'s rows are
    stored. No sibling path repairs it - [skip_to] is a [skip_while] over the
    same raw stream and not a seek (mdbx/database.rs:211-220,
    redb/database.rs:176-206), [last_record] is the cursor's byte-maximum
    (mdbx/database.rs:242-250, redb/database.rs:253-257), [reverse_iter] walks
    the same bytes backwards (mdbx/database.rs:222-229,
    redb/database.rs:208-237), and the in-memory layer keys a
    [BTreeMap<Vec<u8>, _>] by the identical bytes (mem_db.rs:10, :259-278), so
    it is a third copy of the order rather than a correction of it. *)
let s1 =
  let highest_row_wins =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Probe_returned, atom Row_j_high),
           atom Answer_high ))
  in
  let low_answer_is_really_the_maximum =
    Formula.Ag
      (Formula.Implies
         ( atom Answer_low,
           Formula.And (atom Row_j_low, Formula.Not (atom Row_j_high)) ))
  in
  let a_lone_low_row_is_not_skipped =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             ( atom Probe_returned,
               Formula.And (atom Row_j_low, Formula.Not (atom Row_j_high)) ),
           atom Answer_low ))
  in
  {
    name = "ordered-scan-lands-on-the-origins-greatest-stored-round";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [
          highest_row_wins;
          low_answer_is_really_the_maximum;
          a_lone_low_row_is_not_skipped;
        ];
    antecedent = Formula.And (atom Row_j_low, atom Row_j_high);
  }

(** S2 - origin-guard-makes-the-round-answer-knowledge-of-the-named-authoritys-act
    [security].

    [last_round_number] takes the record strictly before [(origin, Round::MAX)]
    and admits it only if its authority is the one asked about:
    [if let Some(((name, round), _)) = self.record_prior_to::<
    CertificateDigestByOrigin>(&key) { if &name == origin { return
    Ok(Some(round)); } } Ok(None)] (stores/certificate_store.rs:411-419). The
    key is [(AuthorityIdentifier, Round)] (storage/src/lib.rs:93) and the
    identifier is a raw fixed-width 32 bytes (types/src/committee.rs:301-319),
    so the index is authority-major: with [j]'s block empty, the record before
    the sentinel belongs to whichever authority precedes [j]. The [&name ==
    origin] test is the whole of the difference between a fact about [j] and a
    fact about [j]'s neighbour.

    - Conjunct A (positive knowledge): an answer of [R_hi] entitles V0 to KNOW
      that [j] signed a certificate at [R_hi]. Under the guard, the answer can
      only have come from a row of [j]'s own block, and a row exists only
      because [save_cert] keyed it from a certificate [j] authored
      (stores/certificate_store.rs:140-142). The operand is another node's act,
      is false at reachable states, and V0's view class at the operative state
      is not a singleton - see the reading guide and the [contingency] group of
      test/t_store_key_order.ml.
    - Conjunct B (ignorance): an answer of [None] is NOT knowledge that [j]
      never signed at [R_hi]. V0's index is what V0 has received, not what
      exists; two reachable states with an empty [j] block and identical V0
      views disagree on the ghost. That is why the consumer reads a missing
      answer as "fetch" ([unwrap_or(true)],
      consensus/primary/src/certificate_fetcher.rs:236) rather than as
      "nothing to fetch".

    MUTATION PIN. {!Store_key_order_model.No_origin_guard} deletes the [if
    &name == origin] test (stores/certificate_store.rs:414-416). Conjunct A
    then fails at the state where [j] has no rows at all, [k] - the authority
    immediately below [j] - has a row at [R_hi], and [j] never signed: the
    probe answers [Some(R_hi)] while the operand is false, with V0's view
    unchanged. No sibling path repairs it. [last_round] (:389-399) and
    [next_round_number] (:428-434) carry their own copies of the same test but
    answer different questions, and the sole consumer of THIS answer,
    [should_fetch_certificate] (certificate_fetcher.rs:232-238), reads
    [last_round_number] alone and compares rounds only; the stored value is a
    [HeaderDigest] and :415 returns the KEY's round without loading the
    certificate, so nothing downstream re-derives the author. *)
let s2 =
  let answered_round_is_the_named_authoritys_act =
    Formula.Ag
      (Formula.Implies
         (atom Answer_high, Formula.K (Validator.V0, atom J_signed_high)))
  in
  let absent_answer_is_not_knowledge_of_silence =
    Formula.Ag
      (Formula.Implies
         ( atom Answer_absent,
           Formula.Not
             (Formula.K (Validator.V0, Formula.Not (atom J_signed_high))) ))
  in
  {
    name =
      "origin-guard-makes-the-round-answer-knowledge-of-the-named-authoritys-act";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( answered_round_is_the_named_authoritys_act,
          absent_answer_is_not_knowledge_of_silence );
    antecedent = atom Answer_high;
  }

(** S3 - origin-guard-keeps-the-ancestor-fetch-alive-for-a-silent-authority
    [liveness].

    [should_fetch_certificate] is the sole consumer of [last_round_number]:
    [let header_is_newer = self.certificate_store
    .last_round_number(header.author())?.map(|last_round| header.round() >
    last_round).unwrap_or(true)]
    (consensus/primary/src/certificate_fetcher.rs:232-238). A [None] answer
    means fetch; an answer equal to the trigger's own round means the strict
    comparison fails and the fetch is skipped at :207-209.

    - Conjunct A (liveness): once a fetch trigger for [(j, R_hi)] has read the
      index, if V0 does not hold [j]'s certificate at [R_hi] then the ancestor
      fetch for [j] is inevitably started. Under the guard the probe answers
      [None] (empty [j] block) or [Some(R_lo)] (a lower round of [j]), and both
      admit the fetch.
    - Conjunct B (the safety companion): a fetch is suppressed only when V0
      really does hold [j]'s certificate at [R_hi]. Suppression is the only
      irreversible half of the decision - the fetcher's own comment at :342-346
      leans on a later certificate re-triggering the fetch, which is precisely
      what a header path that never reaches the certificate path does not
      supply.

    MUTATION PIN. {!Store_key_order_model.No_origin_guard} deletes the [if
    &name == origin] test (stores/certificate_store.rs:414-416). At a state
    where [j] has no rows and [k] holds a row at [R_hi] - the post-GC or
    new-committee-member shape - the probe answers [Some(R_hi)], the comparison
    [R_hi > R_hi] is false, and the decision terminates in [Decided Skip]: the
    [AF] of conjunct A fails and conjunct B is violated by a suppression with
    no row of [j] behind it.

    R8, no manufactured liveness. The deleted test is a real gate, not a
    sibling path the code would have skipped anyway, and the OTHER fetch entry
    point is modelled rather than omitted: the missing-parent path
    (state_sync/cert_manager.rs:157-177) sends
    [CertificateFetcherCommand::Ancestors] into the SAME [handle_command]
    (certificate_fetcher.rs:178-191), which falls through to the SAME gate at
    :207 - so the model gives both triggers one [Probed] stage and the mutation
    disables both. [CertificateFetcherCommand::Kick] (:181-190) starts a task
    only when [!self.targets.is_empty()] and targets are inserted only at :212
    after the gate has passed, so a kick cannot create a target the gate
    refused. [get_written_rounds] / [origins_after_round] (:352-374,
    stores/certificate_store.rs:332-351) read the by-ROUND index and only PRUNE
    targets (:347). The earlier [self.targets] skip (:225-229) is out of scope
    because the model covers the first decision for [j], and it could not be a
    counterexample anyway: it fires exactly when a fetch for [j] at that round
    or later is already scheduled. That the model does not simply always fetch
    is asserted in the [sanity] group of test/t_store_key_order.ml. *)
let s3 =
  let unheld_round_is_inevitably_fetched =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Probe_returned, Formula.Not (atom Row_j_high)),
           Formula.Af (atom Fetch_started) ))
  in
  let suppression_is_grounded_in_a_stored_row =
    Formula.Ag (Formula.Implies (atom Fetch_suppressed, atom Row_j_high))
  in
  {
    name = "origin-guard-keeps-the-ancestor-fetch-alive-for-a-silent-authority";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        (unheld_round_is_inevitably_fetched, suppression_is_grounded_in_a_stored_row);
    antecedent =
      Formula.And (atom Probe_returned, Formula.Not (atom Row_j_high));
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
