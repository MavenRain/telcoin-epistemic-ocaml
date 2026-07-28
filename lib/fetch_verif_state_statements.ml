(** The FETCH_VERIF_STATE statement family, encoded over the
    {!Fetch_verif_state_model} interpreted system: what the ROUND-STRUCTURED
    verification plan of a bulk certificate fetch does and does not tell the
    fetching node, on a chain that straddles a multiple of the real default
    [certificate_verification_round_interval]. All three statements were mined
    from the Rust and re-grounded line by line against this checkout (HEAD
    0c59c15b). File citations refer to Telcoin-Association/telcoin-network.

    READING GUIDE FOR THE K OPERANDS. The single knowledge agent is V1, the
    catching-up fetcher; V0, V2, V3 are the other members of the modelled
    four-member committee (f = 1, quorum 2f+1 = 3) and V4..V9 are outside it,
    all with the constant blank view.

    - [Anchor_quorum_genuine] = "a real 2f+1 BLS aggregate over C50's header
      exists, i.e. three of the four committee members actually produced
      signatures over it". It is a fact about OTHER validators' remote signing
      acts and about the honesty partition (three of four signers with f = 1
      forces at least f+1 = 2 honest ones); it is in NO view constructor of the
      model. It is not rigid - it is FALSE at the [Fg_anchor] and
      [Fg_anchor_and_link] responses, sixteen reachable states - and it is not
      knower-local: V1 signs nothing here, it only fetches.
    - [Link_quorum_genuine] = the same fact about C51, the member one round
      above the anchor. C51 is stamped [VerifiedIndirectly] at
      cert_validator.rs:293 and its aggregate is never put to the committee
      keys, so this operand is the family's ignorance operand and doubles as the
      R2 non-singleton witness for the positive K.

    WHY THE LEAF'S CHECK DOES NOT LEAK C51's AUTHENTICITY. A genuine aggregate
    over C52's header does prove that C52's 2f+1 signers each blocked on
    [notify_read_parent_certificates] and then enforced distinct parent
    authorities plus quorum stake before signing (network/handler.rs:688-738).
    That establishes those signers HELD C51 in their own stores; it does not
    establish that C51's own aggregate is real, because a certificate is
    accepted on this very route by an indirect STAMP with no cryptography
    (cert_validator.rs:314-324 with cert_manager.rs:88-93) and is never
    re-examined afterwards - [verify_signature] returns [Ok] forever on
    [VerifiedIndirectly] (certificate.rs:271-274), the re-checking [verify_cert]
    (certificate.rs:253-266) has only the gossip caller
    (network/handler.rs:252), and [Certificate::signed_authorities]
    (certificate.rs:352-354) has no non-test caller in the tree. That residual
    is exactly what the periodic anchor exists to bound, which is what S1 and S2
    say. *)

open Fetch_verif_state_model

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

(** S1 - anchored-round-certificate-carries-known-quorum-its-neighbour-does-not
    [security]. For one bulk fetch of the chain C49 <- C50 <- C51 <- C52 at
    rounds 49..52 with the default 50-round verification interval, so that the
    plan of [requires_direct_verification] (cert_validator.rs:303-312) is
    {C50 by the periodic disjunct at :309-311, C52 by the leaf disjunct at :308}
    and {C49, C51} are stamped [VerifiedIndirectly] at :293:

    (A) KNOWN QUORUM AT THE ANCHOR - AG( batch_accepted ->
    K_V1( genuine_quorum(C50) ) ). Whenever the whole response has been written
    to V1's store, V1 KNOWS that three of the four committee members really
    signed C50's header, hence - with f = 1 - that at least two HONEST members
    did. The warrant is first-hand and cryptographic: C50 is in the chunk
    (cert_validator.rs:331-334), [validate_and_verify] runs its aggregate
    against the committee keys (certificate.rs:225-251, :269-292), and the
    response reaches storage only if that chunk returned [Ok]
    (the [?] at cert_validator.rs:260, the [??] at :338-341).

    (B) NO SUCH KNOWLEDGE ONE ROUND UP - AG( batch_accepted ->
    ( ~K_V1( genuine_quorum(C51) ) /\\ ~K_V1( ~genuine_quorum(C51) ) ) ). C51 is
    a parent and 51 is not a multiple of 50, so it takes
    [mark_verified_indirectly] (cert_validator.rs:314-324): its aggregate is
    never put to the committee keys, and the stamp is a pure tag rewrite off the
    certificate's own bytes. V1 therefore cannot tell an authentic C51 from a
    fabricated one, in EITHER direction.

    (C) THE GAP IS REAL - EF( batch_accepted /\\ ~genuine_quorum(C51) ). Asserted
    rather than assumed, so that (B) cannot be true by the fabricated case being
    unreachable.

    (D) THE INGRESS RESET NEUTRALISES, IT DOES NOT REJECT -
    EF( peer_claims_verified /\\ batch_accepted ). [validate_fetched_certificate]
    overwrites the peer's tag with [Unverified(self.aggregated_signature()?)]
    (certificate.rs:462-471), and [aggregated_signature] (:329-337) keeps the
    signature BYTES for [VerifiedDirectly], so a response that happens to arrive
    pre-tagged is still accepted. (A) is therefore NOT obtained by throwing
    tagged traffic away. This conjunct survives every mutation, so it can never
    be the cause of a flip.

    R2 NON-DEGENERACY. At an operative state (Settled, [Cl_anchor_direct],
    [Obs_pass], [St_all], peer_tag = t) the V1-view class contains EXACTLY TWO
    reachable worlds, [Fg_none] and [Fg_link], both at that same [peer_tag]:
    those are the only forgeries whose chunk passes under the pristine plan.
    [Anchor_quorum_genuine] holds in both, so (A) is true and NOT by a singleton
    class; they DISAGREE on [Link_quorum_genuine], which is what makes (B) true
    and what the non-singleton contingency test asserts.

    MUTATION PINS, and what each one breaks.
    {!Fetch_verif_state_model.No_periodic_anchor} refutes (A): with the
    [is_multiple_of] disjunct gone the plan collapses to [Cl_leaf_only], C50 is
    stamped [VerifiedIndirectly] instead of checked, and the [Fg_anchor] and
    [Fg_anchor_and_link] responses now reach [St_all], so the operative class
    grows to four worlds and contains one where C50's aggregate is garbage.
    {!Fetch_verif_state_model.No_wire_state_reset} also refutes (A): a surviving
    [VerifiedDirectly] tag short-circuits [verify_signature]
    (certificate.rs:271-274) for BOTH chunk members, so on the pre-tagged branch
    every forgery reaches [St_all] and the class contains a forged anchor.
    {!Fetch_verif_state_model.No_chunk_abort} correctly leaves S1 PROVED: it
    changes only what happens after a FAILED chunk, and [Batch_accepted] still
    requires [Chk_real_pass]. Conjuncts (B), (C) and (D) hold under all three
    mutations, so both refutations are cleanly attributable to (A). *)
let s1 =
  let known_anchor_quorum =
    Formula.Ag
      (Formula.Implies
         ( atom Batch_accepted,
           Formula.K (Validator.V1, atom Anchor_quorum_genuine) ))
  in
  let ignorant_of_link_quorum =
    Formula.Ag
      (Formula.Implies
         ( atom Batch_accepted,
           Formula.And
             ( Formula.Not
                 (Formula.K (Validator.V1, atom Link_quorum_genuine)),
               Formula.Not
                 (Formula.K
                    (Validator.V1, Formula.Not (atom Link_quorum_genuine))) )
         ))
  in
  let gap_is_real =
    Formula.Ef
      (Formula.And
         (atom Batch_accepted, Formula.Not (atom Link_quorum_genuine)))
  in
  let reset_neutralises =
    Formula.Ef (Formula.And (atom Peer_tagged, atom Batch_accepted))
  in
  {
    name = "anchored-round-certificate-carries-known-quorum-its-neighbour-does-not";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( known_anchor_quorum,
          Formula.And
            (ignorant_of_link_quorum, Formula.And (gap_is_real, reset_neutralises))
        );
    antecedent = atom Batch_accepted;
  }

(** S2 - fetched-chain-never-runs-two-unchecked-rounds-in-a-row [safety]. The
    periodic disjunct of [requires_direct_verification]
    (cert_validator.rs:309-311) bounds how long a fetched chain can be admitted
    on digest linkage alone: on the modelled chain, which straddles the
    multiple-of-50 round, the run of consecutive indirectly-stamped rounds is
    never longer than one.

    (A) NO ADJACENT PAIR - AG( marked_indirectly(C51) ->
    ~marked_indirectly(C50) ). Whenever C51 is admitted on linkage alone, its
    immediate predecessor C50 is not: 50 is a multiple of the interval, so
    [requires_direct_verification] selects it for the chunk at :331-334 even
    though [all_parents] contains digest(C50). This is the interval bound stated
    on the one adjacency the modelled chain contains.

    (B) INDIRECT ADMISSION IS REAL - EF( marked_indirectly(C51) /\\
    batch_accepted ). Asserted so that (A) cannot be true by nothing ever being
    stamped indirectly: [classify_certificates_for_verification] really does
    stamp C51 at :293 and the response really does reach storage.

    MUTATION PIN. {!Fetch_verif_state_model.No_periodic_anchor} refutes (A) and
    ONLY that mutation does: deleting [|| cert.header().round()
    .is_multiple_of(...)] at :309-311 leaves only the leaf test at :308, so C50
    joins C49 and C51 under [mark_verified_indirectly] and the chain runs three
    consecutive rounds - 49, 50 and 51 - with no aggregate check of their own.
    NO SIBLING REPAIRS IT: the leaf disjunct still anchors C52, but nothing in
    the tree ever re-examines a stored certificate ([verify_signature] short-
    circuits forever on [VerifiedIndirectly], certificate.rs:271-274;
    [verify_cert] has only the gossip caller, network/handler.rs:252;
    [signed_authorities] has no non-test caller), and cert_manager's
    [is_verified] gate (cert_manager.rs:88-93) is exactly what
    [VerifiedIndirectly] satisfies (certificate.rs:356-364).
    {!Fetch_verif_state_model.No_wire_state_reset} and
    {!Fetch_verif_state_model.No_chunk_abort} touch neither
    [requires_direct_verification] nor [mark_verified_indirectly] and correctly
    leave S2 PROVED. *)
let s2 =
  let no_adjacent_unchecked_pair =
    Formula.Ag
      (Formula.Implies
         ( atom Link_marked_indirect,
           Formula.Not (atom Anchor_marked_indirect) ))
  in
  let indirect_admission_is_real =
    Formula.Ef
      (Formula.And (atom Link_marked_indirect, atom Batch_accepted))
  in
  {
    name = "fetched-chain-never-runs-two-unchecked-rounds-in-a-row";
    bucket = Statements.Safety;
    formula =
      Formula.And (no_adjacent_unchecked_pair, indirect_admission_is_real);
    antecedent = atom Link_marked_indirect;
  }

(** S3 - failed-anchor-quarantines-the-pre-stamped-chain [safety]. The two
    members selected for direct verification, the round-50 anchor and the leaf,
    travel in ONE chunk (the default [certificate_verification_chunk_size] is
    50, crates/config/src/network.rs:251-254, :268) and are examined in
    ascending index order. If the anchor's aggregate check fails, the whole
    fetched response is discarded - including C49 and C51, which
    [classify_certificates_for_verification] had already stamped
    [VerifiedIndirectly] before any cryptography ran at all.

    (A) QUARANTINE - AG( aggregate_check_failed(C50) -> AG( ~stored(C49) ) ).
    The only thing standing between the pre-stamped C49 and storage is the error
    propagation of the chunk: [validator.validate_and_verify(cert)?] at
    cert_validator.rs:356-361, the [??] at :338-341, and the [?] on
    [self.verify_certificate_chunk(...).await?] at :260;
    [process_fetched_certificates_in_parallel] (:235-243) forwards only on [Ok].
    The obvious candidate sibling, cert_manager's [if !cert.is_verified()] at
    cert_manager.rs:88-93 ("NOTE: this is the only time this is checked"), does
    NOT cover C49, because [VerifiedIndirectly] satisfies [is_verified]
    (certificate.rs:356-364); it stops only the still-[Unverified] members, and
    C49 precedes them in the manager's loop.

    (B) THE ANCHOR SHIELDS THE LEAF FROM EXAMINATION -
    AG( aggregate_check_failed(C50) -> ~aggregate_examined(C52) ). Inside a
    chunk, [spawn_verification_task] runs
    [for (_idx, cert) in certs.iter_mut() { validator.validate_and_verify(cert)? }]
    (cert_validator.rs:348-363): the [?] ends the chunk at the anchor, so the
    leaf's own aggregate is never put to the committee keys even though the leaf
    is the member the leaf disjunct at :308 was supposed to anchor. This is why
    (A) has to be all-or-nothing: on a failed anchor there is no second,
    independent cryptographic warrant left anywhere in the response.

    (C) THE STAMPS REALLY PRECEDE THE CRYPTOGRAPHY -
    EF( marked_indirectly(C51) /\\ aggregate_check_failed(C50) /\\
    ~batch_accepted ). Asserted so that (A) cannot be true because nothing was
    ever stamped: the classify call at cert_validator.rs:256-257 strictly
    PRECEDES [self.verify_certificate_chunk(...).await?] at :260, so the
    indirect stamps exist at the moment the anchor's check fails.

    ANTECEDENT DISJUNCTION, deliberate. The antecedent is
    aggregate_check_failed(C50) \\/ ( marked_indirectly(C51) /\\ ~batch_accepted ).
    Under {!Fetch_verif_state_model.No_periodic_anchor} the anchor is never
    checked, so the FIRST disjunct becomes unreachable; without the second
    disjunct [prove_nonvacuous] would return [Vacuous_antecedent] and dress a
    vacuity up as a refutation. With the disjunction the antecedent stays
    reachable under every mutation and every verdict below is a real one.

    MUTATION PINS. {!Fetch_verif_state_model.No_chunk_abort} refutes (A): with
    the [??] at :337-343 gone the failing chunk is merely dropped,
    [verify_collection] writes back nothing for its slots (:262-265) but returns
    the WHOLE vector (:267), and the manager writes C49 - which carries
    [VerifiedIndirectly] - before hitting the still-[Unverified] C50 at
    cert_manager.rs:90-93. {!Fetch_verif_state_model.No_periodic_anchor} refutes
    (C), for the honest reason that deleting the periodic disjunct removes the
    anchor's aggregate check altogether, so the window (C) asserts no longer
    exists. {!Fetch_verif_state_model.No_wire_state_reset} correctly leaves S3
    PROVED: on the branch where the response arrives untagged the anchor's check
    still runs, still fails and still aborts the whole response. *)
let s3 =
  let quarantine =
    Formula.Ag
      (Formula.Implies
         ( atom Anchor_check_failed,
           Formula.Ag (Formula.Not (atom Low_stored)) ))
  in
  let leaf_never_examined =
    Formula.Ag
      (Formula.Implies
         ( atom Anchor_check_failed,
           Formula.Not (atom Leaf_aggregate_examined) ))
  in
  let stamped_before_crypto =
    Formula.And
      ( atom Link_marked_indirect,
        Formula.And
          (atom Anchor_check_failed, Formula.Not (atom Batch_accepted)) )
  in
  let window_exists = Formula.Ef stamped_before_crypto in
  {
    name = "failed-anchor-quarantines-the-pre-stamped-chain";
    bucket = Statements.Safety;
    formula =
      Formula.And (quarantine, Formula.And (leaf_never_examined, window_exists));
    antecedent =
      Formula.Or
        ( atom Anchor_check_failed,
          Formula.And
            (atom Link_marked_indirect, Formula.Not (atom Batch_accepted)) );
  }

(** The family's statements: the anchor's first-hand quorum knowledge against
    its neighbour's absence of it, the interval bound on consecutive unchecked
    rounds, and the all-or-nothing quarantine a failed anchor imposes on the
    pre-stamped chain. *)
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
