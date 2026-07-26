(** The VERIF_PROV statement family, encoded over the {!Verif_prov_model}
    interpreted system: the provenance of a certificate's verification MARK on
    telcoin-network's catch-up certificate-FETCH ingress, versus the provenance
    of the cryptographic EVIDENCE the mark stands for. All three statements were
    mined from the Rust, re-grounded line by line against this checkout
    (HEAD 0c59c15b) and stated in the form that survived. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide for the K operands. The single knowledge agent is V1, the
    catching-up fetcher. Both K operands are facts about OTHER validators' remote
    acts, never about V1's own state:

    - [C_endorsed] = "2f+1 distinct committee members produced BLS signatures
      over C's header digest". V1 never runs a single pairing operation on C -
      [classify_certificates_for_verification] routes C past
      [validate_and_verify] entirely (cert_validator.rs:288-294) - so all V1
      holds locally is a header, an attacker-rewritable RoaringBitmap
      (certificate.rs:27-38) and an enum tag. The model's [c_endorse] field
      appears in NO view constructor. The operand is not rigid: it is FALSE at
      the eight reachable [No_quorum] states. It is not knower-local: V1 is a
      member of ALL THREE endorsement values ([No_quorum] = {V0,V1},
      [Q_v2] = {V0,V1,V2}, [Q_v3] = {V0,V1,V3}), so V1's own vote on C's header
      is constant across the class and discriminates nothing.
    - [C_signed_by_v3] = "the hidden third signer was V3 rather than V2". It is
      the anonymity operand: knowing that SOME quorum signed does not reveal
      WHICH, because C's [signed_authorities] bitmap is peer-rewritable without
      disturbing digest(C) (certificate.rs:473-479) and is never checked against
      an aggregate on this route.

    The knowledge in statement 2 arrives solely through the directly-verified
    dependent D: Certificate::digest() IS the header digest
    (certificate.rs:473-479), so a batch member naming digest(C) as a parent
    commits its own 2f+1 signers to the exact header C carries, and every one of
    those signers ran the vote path, which blocks on reading all parent
    certificates out of its own store and then enforces distinct authorities plus
    quorum stake before signing (handler.rs:693-738). That inheritance is the
    modelled premise declared in {!Verif_prov_model}. *)

open Verif_prov_model

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

(** S1 - fetched-parent-never-stored-before-dependent-signature-check [safety].
    On the certificate-FETCH (catch-up) ingress, for a two-certificate response
    in which the round-2 certificate D's header names digest(C) as a parent and
    neither round is a multiple of the 50-round verification interval:

    (A) STORAGE WEAK-UNTIL. C is never written to V1's certificate store before
    the aggregate BLS signature of D has actually been checked against the
    committee keys and passed - A[ ~stored(C) W dep_aggregate_verified(D) ].
    Encoded with the kernel identity A[p W q] = ~E[ ~q U (~p /\\ ~q) ] taking
    p = ~stored(C) (so ~p = [Stored_c]) and q = [Dep_crypto_verified]: no path
    keeps the evidence absent all the way to a state where C is stored and the
    evidence is still absent. Grounding: cert_validator.rs:246-268 -
    [classify_certificates_for_verification] at :256-257, then
    [self.verify_certificate_chunk(...).await?] at :260, whose `?` is the only
    thing standing between the batch and [forward_verified_certs] (:133-226);
    :327-345 ([verify_certificate_chunk], `??` at :336-341); :347-363
    ([spawn_verification_task], inner [validate_and_verify(cert)?] at :356-361);
    cert_manager.rs:121-124 and :189-196, the only write to the certificate store
    on this route.

    (B) THE MARK-BEFORE-EVIDENCE WINDOW REALLY EXISTS -
    EF( marked_indirectly(C) /\\ ~dep_aggregate_verified(D) ). This conjunct is
    asserted, not assumed, precisely so that (A) cannot be true by absence of the
    window. It also records the CORRECTION to the mined card: the card claimed
    "never accepted_as_verified before direct verification", which is FALSE of
    the code. [mark_verified_indirectly] stamps C [VerifiedIndirectly] at
    cert_validator.rs:293 via :314-324 - a pure tag rewrite from the
    certificate's own aggregate bytes, no cryptography - and :256-257 strictly
    precede :260. The mark genuinely does precede the evidence; only STORAGE does
    not.

    (C) THE INGRESS RESET NEUTRALISES, IT DOES NOT REJECT -
    EF( peer_claims_verified /\\ stored(C) ). [validate_fetched_certificate]
    overwrites the peer's tag with [Unverified(self.aggregated_signature()?)]
    (certificate.rs:462-471), and [aggregated_signature] (:329-337) keeps the
    signature BYTES for [VerifiedDirectly] / [VerifiedIndirectly] / [Unverified] /
    [Unsigned], returning [None] only for [Genesis] - the one tag that gets the
    response rejected outright. So honest traffic that happens to arrive tagged
    is still stored, and (A) is not achieved by throwing tagged traffic away.

    Mutation pins. {!Verif_prov_model.No_wire_tag_reset} adds
    Classified(dep_genuine=false, peer_claim=true) -> Checked([Ck_pass_tag]) ->
    Settled([St_cd]), so C is stored with [Dep_crypto_verified] never true;
    {!Verif_prov_model.No_leaf_direct_verification} replaces every Classified ->
    Checked edge with [Ck_none] and then stores the batch;
    {!Verif_prov_model.No_chunk_abort} adds Checked([Ck_fail]) ->
    Settled([St_c]). Each refutes (A). Conjuncts (B) and (C) survive all three,
    so every refutation is cleanly attributable to (A). The antecedent - the
    mark-before-evidence window itself - is reachable in every configuration's
    cone under every mutation, so no flip is a masked [Vacuous_antecedent]. *)
let s1 =
  let storage_weak_until =
    (* A[ ~stored(C) W dep_verified ] = ~E[ ~dep_verified U (stored(C) /\
       ~dep_verified) ]. *)
    Formula.Not
      (Formula.Eu
         ( Formula.Not (atom Dep_crypto_verified),
           Formula.And (atom Stored_c, Formula.Not (atom Dep_crypto_verified)) ))
  in
  let window_exists =
    Formula.Ef
      (Formula.And
         (atom Marked_indirect_c, Formula.Not (atom Dep_crypto_verified)))
  in
  let reset_neutralises =
    Formula.Ef (Formula.And (atom Peer_claims_verified, atom Stored_c))
  in
  {
    name = "fetched-parent-never-stored-before-dependent-signature-check";
    bucket = Statements.Safety;
    formula =
      Formula.And
        (storage_weak_until, Formula.And (window_exists, reset_neutralises));
    antecedent =
      Formula.And
        (atom Marked_indirect_c, Formula.Not (atom Dep_crypto_verified));
  }

(** S2 - indirectly-verified-parent-carries-known-but-anonymous-quorum
    [security]. Whenever the catching-up node V1 has admitted into its
    certificate store a certificate C whose own aggregate signature it never
    checked (C carries [VerifiedIndirectly]), V1 nonetheless KNOWS that a quorum
    of 2f+1 distinct committee members signed C's header - yet it does NOT know
    WHICH quorum.

    (A) KNOWN QUORUM -
    AG( (stored(C) /\\ marked_indirectly(C)) -> K_V1(endorsed_by_quorum(C)) ).
    The knowledge arrives solely through the directly-verified dependent D:
    [requires_direct_verification] (cert_validator.rs:303-312) forces the batch's
    leaf through the real check (certificate.rs:225-251 and the aggregate
    verification at :269-292), while the parent gets no cryptography at all
    (cert_validator.rs:314-324). Because Certificate::digest() IS the header
    digest (certificate.rs:473-479), D naming digest(C) commits D's 2f+1 signers
    to the exact header C carries, and each of those signers blocked on reading
    the parent certificates out of its own store and then enforced distinct
    authorities plus quorum stake before signing (handler.rs:693-738). That is
    the modelled premise; the store write it is claimed about is
    cert_manager.rs:85-93 / :189-196.

    (B) ANONYMITY - AG( (stored(C) /\\ marked_indirectly(C)) ->
    (~K_V1(signed_by(V3,C)) /\\ ~K_V1(~signed_by(V3,C))) ). Nothing on this route
    ever tells V1 which third member signed: [signed_authorities] travels on the
    wire as an unauthenticated RoaringBitmap (certificate.rs:27-38), the only
    code that ever reads it is [signed_by]/threshold inside [validate_and_verify]
    (:243-248), and that is skipped entirely for an indirectly-marked certificate
    (cert_validator.rs:288-294).

    R2 non-degeneracy. At the operative state (Settled, [Ck_pass_real],
    [St_cd], peer_claim = p) the V1-view class contains EXACTLY TWO reachable
    worlds: w_a = (dep_genuine = true, c_endorse = [Q_v2] = {V0,V1,V2}) and
    w_b = (dep_genuine = true, c_endorse = [Q_v3] = {V0,V1,V3}), both with
    peer_claim = p. [C_endorsed] holds in both, so (A) is true and is NOT true by
    a singleton class; they DISAGREE on [C_signed_by_v3], so (B) is true and the
    class is provably not a singleton. [C_endorsed] is genuinely false elsewhere
    in the reachable set - at the eight [No_quorum] states, whose cone pristine
    ends at [Ck_fail] with [St_empty] and so never enters the class.

    Mutation pins. All three mutations refute (A) by letting a [No_quorum] world
    into the operative view class: {!Verif_prov_model.No_wire_tag_reset} adds
    Classified(dep_genuine=false, peer_claim=true) -> Checked([Ck_pass_tag]) ->
    Settled([St_cd]), and [Ck_pass_tag] is observationally identical to
    [Ck_pass_real]; {!Verif_prov_model.No_leaf_direct_verification} sends every
    configuration to Checked([Ck_none]) -> Settled([St_cd]);
    {!Verif_prov_model.No_chunk_abort} adds Checked([Ck_fail]) ->
    Settled([St_c]), whose class is the three [dep_genuine] = false worlds.
    Conjunct (B) survives all three - each mutant class still contains a [Q_v2]
    and a [Q_v3] world - so attribution is clean. *)
let s2 =
  let operative = Formula.And (atom Stored_c, atom Marked_indirect_c) in
  let known_quorum =
    Formula.Ag
      (Formula.Implies
         (operative, Formula.K (Validator.V1, atom C_endorsed)))
  in
  let anonymity =
    Formula.Ag
      (Formula.Implies
         ( operative,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom C_signed_by_v3)),
               Formula.Not
                 (Formula.K
                    (Validator.V1, Formula.Not (atom C_signed_by_v3))) ) ))
  in
  {
    name = "indirectly-verified-parent-carries-known-but-anonymous-quorum";
    bucket = Statements.Security;
    formula = Formula.And (known_quorum, anonymity);
    antecedent = operative;
  }

(** S3 - failed-dependent-quarantines-the-pre-marked-batch [safety]. If the
    aggregate signature check of the batch's directly-verified member D fails,
    then NOTHING from that fetched response ever reaches the certificate store -
    not D, and in particular not the parent C that classify already stamped
    [VerifiedIndirectly] before any cryptography ran.

    (A) QUARANTINE - AG( dep_aggregate_failed(D) -> AG( ~stored(C) /\\
    ~stored(D) ) ). The sole thing standing between the pre-stamped C and storage
    is the error propagation of the chunk verification: classify then
    [self.verify_certificate_chunk(certs).await?] at cert_validator.rs:255-261,
    [task.await.map_err(...)??] at :336-341, and
    [validator.validate_and_verify(cert)?] at :356-361;
    [process_fetched_certificates_in_parallel] (:235-243) forwards only on [Ok].
    The obvious candidate sibling, cert_manager's [if !cert.is_verified()] at
    cert_manager.rs:85-93 (comment "NOTE: this is the only time this is
    checked"), does NOT cover C, because [VerifiedIndirectly] satisfies
    [is_verified] (certificate.rs:356-364); it stops only the still-[Unverified]
    leaf D, and its storage write is at :189-196.

    (B) THE STAMP BY ITSELF CONVEYS NOTHING - AG( (marked_indirectly(C) /\\
    ~stored(C) /\\ ~dep_aggregate_verified(D)) -> ~K_V1(endorsed_by_quorum(C)) ).
    This is the honest converse of S2: as long as the batch is unstored and the
    dependent's check has not passed, V1 cannot tell an endorsed parent from a
    fabricated one, because the stamp is a pure tag rewrite performed BEFORE
    :260's verification (cert_validator.rs:288-294, :314-324) and
    [set_signature_verification_state] is an unguarded assignment
    (certificate.rs:344-347).

    R3 ignorance witness for (B): at (Classified, [Ck_none], [St_empty],
    peer_claim = false) the V1-view class contains the FIVE reachable
    configurations with peer_claim = false, among them the colliding pair
    u_a = (dep_genuine = true, c_endorse = [Q_v2]) where [C_endorsed] is TRUE and
    u_b = (dep_genuine = false, c_endorse = [No_quorum]) where it is FALSE. The
    same disagreement recurs at (Checked, [Ck_fail]), whose class is the three
    [dep_genuine] = false worlds. Conjunct (A)'s non-vacuity is witnessed by
    [Dep_crypto_failed] being reachable at the six [dep_genuine] = false
    configurations.

    ANTECEDENT DISJUNCTION, deliberate. The antecedent is
    dep_aggregate_failed(D) \\/ (marked_indirectly(C) /\\ ~stored(C) /\\
    ~dep_aggregate_verified(D)). Under
    {!Verif_prov_model.No_leaf_direct_verification} nothing is ever checked, so
    nothing can fail and the FIRST disjunct becomes unreachable; without the
    second disjunct [prove_nonvacuous] would return [Vacuous_antecedent] and
    manufacture a FAKE refutation for a mutation that does not actually break
    this statement. With the disjunction, that mutation correctly leaves S3
    PROVED.

    Mutation pin: {!Verif_prov_model.No_chunk_abort}, and ONLY that mutation. It
    adds Checked([Ck_fail]) -> Settled([St_c]): C, already stamped
    [VerifiedIndirectly], flows through [forward_verified_certs] into the manager
    and is written to storage, so the inner AG of (A) fails at the [Ck_fail]
    state. {!Verif_prov_model.No_wire_tag_reset} leaves (A) true - the
    peer_claim = false, dep_genuine = false path still fails and still aborts -
    and {!Verif_prov_model.No_leaf_direct_verification} leaves (A) vacuously true
    with a still-reachable antecedent, so both correctly leave S3 proved.
    Conjunct (B) survives {!Verif_prov_model.No_chunk_abort} (the class at the
    Classified and [Ck_fail] states is unchanged), so the refutation is cleanly
    attributable to (A). *)
let s3 =
  let quarantine =
    Formula.Ag
      (Formula.Implies
         ( atom Dep_crypto_failed,
           Formula.Ag
             (Formula.And
                (Formula.Not (atom Stored_c), Formula.Not (atom Stored_d))) ))
  in
  let stamp_time_ignorance_premise =
    Formula.And
      ( atom Marked_indirect_c,
        Formula.And
          ( Formula.Not (atom Stored_c),
            Formula.Not (atom Dep_crypto_verified) ) )
  in
  let stamp_conveys_nothing =
    Formula.Ag
      (Formula.Implies
         ( stamp_time_ignorance_premise,
           Formula.Not (Formula.K (Validator.V1, atom C_endorsed)) ))
  in
  {
    name = "failed-dependent-quarantines-the-pre-marked-batch";
    bucket = Statements.Safety;
    formula = Formula.And (quarantine, stamp_conveys_nothing);
    antecedent =
      Formula.Or (atom Dep_crypto_failed, stamp_time_ignorance_premise);
  }

(** The family's statements: the storage weak-until, the known-but-anonymous
    quorum, and the failed-dependent quarantine - three distinct load-bearing
    gates on one catch-up ingress pipeline. *)
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
