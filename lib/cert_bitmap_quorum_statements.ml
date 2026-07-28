(** The CERT_BITMAP_QUORUM statement family, encoded over the
    {!Cert_bitmap_quorum_model} interpreted system. Three properties of the
    roaring signer bitmap of a [Certificate], the single aggregate signature it
    indexes and the three ingress routes that dispose of a peer-supplied
    certificate (crates/types/src/primary/certificate.rs:177-292 and
    crates/consensus/primary/src/state_sync/cert_validator.rs:288-363). File
    citations refer to Telcoin-Association/telcoin-network at git HEAD 0c59c15b.

    {1 Reading guide for the K operands}

    One knowledge agent: V0, the receiving validator. V1..V9 are idle and never
    appear under K. V0's view is (route, wire projection, verdict) - see the
    {!Cert_bitmap_quorum_model} header for why that is the whole wire surface.

    - [K (V0, exists 3 distinct signers of digest(c))] (S1). The operand is a
      fact about OTHER nodes' signing acts. It is not a projection of V0's view:
      the aggregate is one group element naming nobody, and on the fetch path V0
      never receives the individual [Vote]s at all. Concretely, the view class
      [(Fetch_direct, Wire_quorum_bitmap, offered)] contains {!Quorum_faithful}
      (three signers), {!Quorum_dropped_vote} (four) and {!Padded_bitmap} (two),
      so the proposition genuinely varies inside a class. Nor is it rigid: it is
      FALSE at every {!Inquorate_single}, {!Padded_bitmap}, {!Genesis_empty} and
      {!Genesis_padded_garbage} state. What makes it KNOWN after direct
      verification is the pair of gates - the bitmap is resolved to a set of
      pairwise distinct [BTreeSet] keys (certificate.rs:177-199), that set must
      reach the threshold (certificate.rs:246 / :261), and the aggregate must
      verify against exactly those keys (certificate.rs:284-286). Delete either
      and the knowledge goes with it.
    - [K (V0, signed_authorities(c) subset_of signers(c))] (S2). Also hidden: V0
      holds the bitmap but not the signer set, and cannot tell a padded bitmap
      from a faithful one by inspection - only the aggregate check can, and only
      because the key list it is handed is DERIVED from the bitmap. R2 evidence:
      at the operative state the class is
      [(route, Wire_quorum_bitmap, verified_directly)] = {{!Quorum_faithful},
      {!Quorum_dropped_vote}}, two reachable states, and the operand is false at
      the reachable {!Padded_bitmap} states.
    - [~K (V0, signers(c) subset_of signed_authorities(c))] and its dual (S2).
      The assembler returns the certificate at the FIRST vote that crosses quorum
      (aggregators/votes.rs:65-89) and discards later votes, so a member that
      voted may simply not appear in the bitmap. {!Quorum_faithful} and
      {!Quorum_dropped_vote} are byte-identical on the wire and differ exactly on
      this proposition: that pair is the ignorance witness, in both directions.
      The witness is robust to the one thing V0's view leaves out - its own
      signing act - because V0 is credited and signing in BOTH members of the
      pair; the vote that separates them is V3's.
    - [~K (V0, signed_authorities(c) subset_of signers(c))] and its dual (S3).
      At a round-0 acceptance nothing about the signature material has been
      looked at: certificate.rs:236-238 returns [Ok] before :243-248. The witness
      pair is {!Genesis_padded_garbage} and {!Genesis_padded_signed} - the same
      canonical genesis header, the same bitmap crediting three members, and a
      genuine three-key aggregate in one case and arbitrary bytes in the other.

    {1 Scope, stated rather than assumed}

    S1 and S2 are scoped to DIRECT verification, not to [Certificate::is_verified()].
    That is not a convenience: [mark_verified_indirectly]
    (cert_validator.rs:317-323) stamps [VerifiedIndirectly] on any fetched
    certificate that is a parent of another certificate in the batch
    ([requires_direct_verification], cert_validator.rs:303-312) and runs NO
    threshold and NO signature check on it. The model carries that route, and
    [test/t_cert_bitmap_quorum.ml] asserts that an inquorate certificate really
    can reach [Verified_indirectly] pristine, so the scoping is visible as a
    reachable counterexample rather than an omission (contract R5).

    S2 additionally carries the [|signed_authorities(c)|=quorum] and
    [~round(c)=0] guards. Both are implied pristine - the threshold gate at
    certificate.rs:246 admits nothing else at a positive round, and the round-0
    shortcut produces a different verdict - so they weaken nothing on the real
    code. They are written out because they name the certificate shape the
    omission claim is ABOUT (a bitmap that stopped at quorum), and because they
    keep S2's refutation attributable to the signature-binding deletion rather
    than to the threshold deletion. *)

open Cert_bitmap_quorum_model

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

(** The operative state of S1 and S2: the ingress ran the real gate set and
    passed, i.e. the certificate reached [VerifiedDirectly]
    (certificate.rs:288-289) rather than being waved through by the round-0
    shortcut or the indirect-verification stamp. *)
let verified_directly = atom Verified_directly

(** The operative state of S1: a directly verified certificate at a positive
    round, i.e. a real DAG certificate rather than a genesis root. The
    [~round(c)=0] guard is a NON-DEGENERACY guard, not a convenience: a round-0
    certificate carrying a genuine three-key aggregate is directly verifiable on
    the gossip route (which has no shortcut, certificate.rs:255-266), and V0's
    view class there is a singleton, which would make the K instance at that one
    state trivially true. Round 0 is S3's subject; excluding it here keeps every
    in-scope instance of S1's K sitting on a two-member class. *)
let positive_round_cert_verified =
  Formula.And (verified_directly, Formula.Not (atom Round_zero))

(** The operative state of S2: a directly verified, positive-round certificate
    whose bitmap credits a quorum. *)
let quorum_cert_verified =
  Formula.And
    ( verified_directly,
      Formula.And (atom Credits_quorum, Formula.Not (atom Round_zero)) )

(** The operative state of S3's liveness conjunct: a round-0 certificate whose
    header the receiver recomputes as a canonical genesis header, offered on the
    direct-fetch route, with no [Genesis] claim in its wire verification state.
    Every conjunct is wire-observable or locally recomputable, so this names a
    real ingress situation and not the property being proved. *)
let genesis_offer_on_direct_fetch =
  Formula.And
    ( atom Offer_pending,
      Formula.And
        ( atom Round_zero,
          Formula.And
            ( atom Canonical_genesis_header,
              Formula.And
                ( atom On_direct_fetch,
                  Formula.Not (atom Wire_claims_genesis_state) ) ) ) )

(** S1 - direct-verification-implies-known-distinct-triple-signing [security].

    AG( verified_directly(v,c) /\\ ~round(c)=0 -> K_v( exists three
    pairwise-distinct committee members that each produced a BLS signature over
    [to_intent_message(header_digest(c))] ) ).

    The novel content is DISTINCTNESS, not "a quorum". The aggregate signature is
    one group element and carries no signer identities
    (crates/types/src/crypto/bls_signature.rs:269-287 aggregates one copy of the
    message per supplied key), so nothing in the signature turns "it verified"
    into "three different validators signed". Three mechanisms together do:

    (a) [Certificate::signed_by] (certificate.rs:177-199) resolves the roaring
    bitmap position-by-position against the committee's
    [BTreeSet<BlsPublicKey>] with a MONOTONE cursor -
    [Some(index) if *index == i as u32 => { weight += 1; auth_iter += 1;
    Some( *key ) }] (:190-194) - so [weight] and the key list advance in lockstep
    and the credited keys are pairwise distinct by construction; a repeated index
    cannot be counted twice.

    (b) [ensure!(weight >= threshold, CertificateError::Inquorate { .. })]
    (certificate.rs:246, with [let threshold = committee.quorum_threshold();] at
    :245) forces that distinct set to reach 3 for the four-member committee
    ([calculate_quorum_threshold], committee.rs:247-252, over
    [total_voting_power()] = [authorities.len()], committee.rs:261-263). The
    gossip ingress carries its own copy at certificate.rs:261 over the free
    [quorum_threshold(committee.len() as u64)] (committee.rs:686-688).

    (c) [verify_signature] (certificate.rs:269-292) checks the aggregate against
    EXACTLY those derived keys over a locally recomputed digest
    ([let certificate_digest = self.digest();] :282, [impl Hash for Certificate]
    :473-479): [if !aggregate_signature.verify_secure(&to_intent_message(
    certificate_digest), &pks[..]) { return Err(CertificateError::InvalidSignature); }]
    (:284-286).

    What v does NOT learn is which of the three is honest, or whether any member
    outside the three signed - that is S2.

    Scope, in two parts. The antecedent is direct verification, not
    [is_verified()], because [mark_verified_indirectly]
    (cert_validator.rs:317-323) stamps [VerifiedIndirectly] with no checks at all
    on a fetched non-leaf certificate; the model carries that route and
    t_cert_bitmap_quorum.ml exhibits an inquorate certificate reaching it, so the
    scope is a stated limit rather than an omission. And it excludes round 0,
    which is S3's subject: a round-0 certificate carrying a genuine three-key
    aggregate IS directly verifiable on the gossip route (certificate.rs:255-266
    has no shortcut), but V0's view class at that one state is a singleton, so
    keeping it in would add a K instance that is true for want of an
    alternative - exactly the degeneracy contract R2 forbids.

    Mutation pin: {!Cert_bitmap_quorum_model.No_weight_threshold} deletes
    certificate.rs:246 - the [validate_and_verify] copy of the threshold
    [ensure!] and only that copy - adding
    [Pending (Fetch_direct, Inquorate_single) -> Settled (.., Verified_direct)].
    One member signed, one index is credited, the aggregate verifies honestly
    against that one key, and the certificate is forwarded: the K operand is
    false at a state in V0's class, so the K fails. The two candidate repairs are
    modeled and neither closes it - [verify_secure]'s
    [if pks.is_empty() { return false; }] (bls_signature.rs:274-276) excludes
    only the ZERO-key case, and [verify_cert]'s independent threshold at
    certificate.rs:261 is reachable only from the gossip ingress
    (handler.rs:252), which the mutation leaves intact and which still rejects
    the same certificate. *)
let s1 =
  {
    name = "direct-verification-implies-known-distinct-triple-signing";
    bucket = Statements.Security;
    formula =
      Formula.Ag
        (Formula.Implies
           ( positive_round_cert_verified,
             Formula.K (Validator.V0, atom Three_distinct_signers) ));
    antecedent = positive_round_cert_verified;
  }

(** S2 - verified-bitmap-is-signature-bound-yet-omission-stays-hidden
    [security].

    AG( verified_directly(v,c) /\\ |signed_authorities(c)|=quorum /\\
    ~round(c)=0 -> K_v( every index in [signed_authorities(c)] names a committee
    member that really signed ) /\\ ~K_v( no member outside the bitmap signed )
    /\\ ~K_v( some member outside the bitmap signed ) ).

    (A) The CREDITED set is authentic. An index cannot be added to or removed
    from the bitmap without breaking verification, because the key list handed to
    the aggregate check is DERIVED from that same bitmap:
    [let (weight, pks) = self.signed_by(&committee.bls_keys());]
    (certificate.rs:243, and :257 on the gossip path) feeds
    [self.verify_signature(pks)?] (:248, :263) which is
    [verify_secure(&to_intent_message(certificate_digest), &pks[..])]
    (:284-286). Both the message and the key list are recomputed locally and
    neither is trusted from the wire, so a relayer that edits the bitmap
    invalidates the certificate.

    (B) The UNCREDITED members are unaccounted for, in both directions.
    [VotesAggregator::append] returns the certificate at the first vote that
    crosses quorum - [if self.weight >= committee.quorum_threshold() {]
    (aggregators/votes.rs:65) followed by [return Ok(Some(cert));] at :89 - and
    every later vote is discarded. So the bitmap is a LOWER bound on who signed,
    never an upper one, and no artifact downstream can settle the difference:
    [impl PartialEq for Certificate] (certificate.rs:495-502) compares only
    header digest, round, epoch and origin, so two certificates for the same
    header crediting different subsets are [==] and collapse in any equality- or
    digest-keyed store.

    R2 evidence for (A): at the operative state V0's class is
    [(route, Wire_quorum_bitmap, verified_directly)], which holds both
    {!Quorum_faithful} and {!Quorum_dropped_vote} - two reachable states - and
    the operand is false at the reachable {!Padded_bitmap} states, so the K is
    neither singleton-trivial nor rigid. R3 evidence for (B): that same pair
    disagrees on [signers(c) subset_of signed_authorities(c)].

    Mutation pin: {!Cert_bitmap_quorum_model.Trust_supplied_signer_set} replaces
    the bitmap-derived [pks] threaded from certificate.rs:243/:257 into
    certificate.rs:248/:263 with a caller-supplied signer list, so the aggregate
    check no longer binds the bitmap. That adds
    [Pending (_, Padded_bitmap) -> Settled (.., Verified_direct)] on both gated
    routes: an index for a member that never signed survives verification, and
    conjunct (A) fails. No sibling repairs it - [verify_cert]
    (certificate.rs:255-266) routes to the SAME [verify_signature] body, so the
    model applies the deletion to the gossip route too; and nothing outside
    crates/types re-derives or cross-checks the signer set, since
    [Certificate::signed_authorities()] (certificate.rs:352-354) has no consumer
    elsewhere in the workspace (the other [signed_authorities] occurrences are
    the unrelated [EpochCertificate] field, crates/types/src/primary/epoch.rs:144)
    and [signed_authorities_with_committee] (certificate.rs:169-173) merely
    re-runs [signed_by].

    S2 survives {!Cert_bitmap_quorum_model.No_weight_threshold} (whose new
    acceptance credits ONE member, excluded by the quorum guard) and
    {!Cert_bitmap_quorum_model.No_genesis_header_equality} (whose new acceptance
    is at round 0, excluded by the round guard), so the pin is attributable. *)
let s2 =
  let credited_set_authentic =
    Formula.K (Validator.V0, atom Bitmap_signature_backed)
  in
  let omission_unknown =
    Formula.And
      ( Formula.Not (Formula.K (Validator.V0, atom No_uncredited_signer)),
        Formula.Not
          (Formula.K (Validator.V0, Formula.Not (atom No_uncredited_signer))) )
  in
  {
    name = "verified-bitmap-is-signature-bound-yet-omission-stays-hidden";
    bucket = Statements.Security;
    formula =
      Formula.Ag
        (Formula.Implies
           ( quorum_cert_verified,
             Formula.And (credited_set_authentic, omission_unknown) ));
    antecedent = quorum_cert_verified;
  }

(** S3 - round-zero-certificate-is-admitted-on-header-equality-alone [safety].

    (A) Admission is inevitable: leads_to( a round-0 certificate offered on the
    direct-fetch route whose header the receiver recomputes as a canonical
    genesis header and whose wire state does not claim [Genesis], admitted by the
    genesis shortcut ). The shortcut is
    [if self.round() == 0 && Self::genesis(committee).contains(self) { return
    Ok(()); }] (certificate.rs:236-238), and [Certificate::genesis]
    (certificate.rs:46-59) rebuilds the comparison set locally from the
    committee, so the test needs nothing from the peer beyond the header.

    The liveness conjunct is scoped to certificates that REACH
    [Certificate::validate_and_verify], which is what the direct-fetch route
    means in this model. One upstream filter sits between the wire and that
    entry point and is named here rather than assumed away: [if
    certificate.round() < gc_round { return Err(CertificateError::TooOld(..)) }]
    (cert_validator.rs:115-125). A round-0 certificate clears it only while the
    receiver's [gc_round] is still 0 - which is exactly the bootstrapping window
    in which the fetcher asks a peer for genesis parents at all, so the scoping
    matches the situation the mechanism exists for rather than dodging a gate.

    (B) Admission certifies exactly the header: AG( admitted_by_genesis_shortcut
    -> round(c)=0 /\\ header(c) in genesis(committee) ). Nothing else is checked,
    because the shortcut returns before [header.validate] (:241,
    header.rs:97-132), before the threshold [ensure!] (:246) and before
    [verify_signature] (:248).

    (C) And it certifies NOTHING about the signature material: AG(
    admitted_by_genesis_shortcut /\\ |signed_authorities(c)|=quorum ->
    ~K_v( signed_authorities(c) subset_of signers(c) ) /\\ ~K_v( not that ) ).
    [impl PartialEq for Certificate] (certificate.rs:495-502) compares only
    header digest, round, epoch and origin - never [signed_authorities] and never
    [signature_verification_state] - so a peer may attach any bitmap and any 48
    bytes and still match the locally rebuilt genesis certificate. The ignorance
    witness is {!Genesis_padded_garbage} versus {!Genesis_padded_signed}: same
    canonical header, same bitmap crediting three members, arbitrary bytes in one
    and a genuine three-key aggregate in the other, wire-indistinguishable and
    both admitted. The [|signed_authorities(c)|=quorum] guard names the case the
    ignorance is about; at the empty-bitmap {!Genesis_empty} the subset claim is
    vacuously true and there is nothing to be ignorant of.

    Mutation pin: {!Cert_bitmap_quorum_model.No_genesis_header_equality} deletes
    certificate.rs:236-238. Execution falls through to :241 and :246, where the
    empty genesis bitmap resolves to weight 0 and is rejected as [Inquorate], so
    conjunct (A) is refuted at a still-reachable antecedent - a genuine
    refutation, not a vacuous one. Three candidate repairs were hunted and the
    model carries all three: (i) [Certificate::genesis] at proposer.rs:145 and
    crates/config/src/consensus.rs:144 seeds a node's OWN roots and filters
    nothing on ingress; (ii) the [SignatureVerificationState::Genesis] free pass
    at certificate.rs:272-274 is unreachable from the wire because both
    [validate_fetched_certificate] (:462-471) and [validate_received] (:295-301)
    overwrite the state and [aggregated_signature()] returns [None] for that
    variant (:329-337) - modeled as {!Genesis_state_claim}, rejected on every
    route; (iii) [mark_verified_indirectly] (cert_validator.rs:317-323) would be
    a real repair, but [requires_direct_verification] (cert_validator.rs:303-312)
    forces direct verification whenever the round is a multiple of
    [certificate_verification_round_interval] = 50 (network.rs:250, :267), and 0
    is a multiple of 50, so a round-0 certificate can never take the indirect
    route. *)
let s3 =
  let admitted = atom Admitted_by_genesis_shortcut in
  let inevitably_admitted =
    Formula.leads_to genesis_offer_on_direct_fetch admitted
  in
  let certifies_the_header =
    Formula.Ag
      (Formula.Implies
         ( admitted,
           Formula.And (atom Round_zero, atom Canonical_genesis_header) ))
  in
  let certifies_nothing_else =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (admitted, atom Credits_quorum),
           Formula.And
             ( Formula.Not
                 (Formula.K (Validator.V0, atom Bitmap_signature_backed)),
               Formula.Not
                 (Formula.K
                    ( Validator.V0,
                      Formula.Not (atom Bitmap_signature_backed) )) ) ))
  in
  {
    name = "round-zero-certificate-is-admitted-on-header-equality-alone";
    bucket = Statements.Safety;
    formula =
      Formula.And
        ( inevitably_admitted,
          Formula.And (certifies_the_header, certifies_nothing_else) );
    antecedent = genesis_offer_on_direct_fetch;
  }

(** The family's statements: two security properties of the bitmap/aggregate
    binding and one safety property of the round-0 shortcut. *)
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
