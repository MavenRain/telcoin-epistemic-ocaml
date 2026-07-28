(** Finite interpreted system for the CERT_BITMAP_QUORUM family: the roaring
    signer bitmap of a [Certificate], the single aggregate signature it indexes,
    and the three ingress routes that dispose of a peer-supplied certificate.
    File citations refer to Telcoin-Association/telcoin-network at git HEAD
    0c59c15b (working tree).

    {1 The modeled mechanism}

    A [Certificate] carries three fields (crates/types/src/primary/certificate.rs:29-38):
    the [header], one [signature_verification_state] holding a single aggregate
    [BlsSignature], and a [roaring::RoaringBitmap] naming which committee members
    are credited with having signed. The aggregate is one group element and
    carries no signer identities, so everything the receiver believes about WHO
    signed comes from resolving that bitmap against the committee.

    - {b bitmap resolution.} [Certificate::signed_by] (certificate.rs:177-199)
      walks the committee's [BTreeSet<BlsPublicKey>] with [enumerate()] and a
      monotone cursor: [Some(index) if *index == i as u32 => { weight += 1; //
      All validators have a voting weight of 1.  auth_iter += 1; Some( *key ) }].
      [weight] and [pks] therefore advance in lockstep, so [weight] equals
      [pks.len()] and the keys are pairwise DISTINCT because they come from a
      [BTreeSet] visited in order. That is the only reason a verified aggregate
      means "three different validators", and it is why the model's credit
      component is a set size and never a repeatable count.
    - {b the threshold gate.} [Certificate::validate_and_verify]
      (certificate.rs:225-251) gates on
      [ensure!(weight >= threshold, CertificateError::Inquorate { stake: weight,
      threshold })] at certificate.rs:246 with
      [let threshold = committee.quorum_threshold();] (:245).
      [CommitteeInner::calculate_quorum_threshold] (committee.rs:247-252) is
      [NonZeroU64::new(2 * total_votes / 3 + 1)] over [total_voting_power()] =
      [self.authorities.len()] (committee.rs:261-263), so for the four-member
      committee this family models the threshold is 3.
    - {b the binding gate.} [Certificate::verify_signature]
      (certificate.rs:269-292) checks the aggregate against exactly the key list
      the bitmap produced, over a LOCALLY recomputed digest
      ([let certificate_digest = self.digest();] at :282, and
      [impl Hash for Certificate] at :473-479 returns [self.header.digest()]):
      [if !aggregate_signature.verify_secure(&to_intent_message(certificate_digest),
      &pks[..]) { return Err(CertificateError::InvalidSignature); }]
      (:284-286). [verify_secure] (crates/types/src/crypto/bls_signature.rs:269-287)
      builds one copy of the message per key and calls
      [aggregate_verify], with one extra guard that this model carries verbatim:
      [if pks.is_empty() { return false; }] (:274-276) - it excludes the ZERO-key
      case only, not one or two keys.
    - {b the round-0 shortcut.} Before either gate,
      [if self.round() == 0 && Self::genesis(committee).contains(self) { return
      Ok(()); }] (certificate.rs:236-238). [Certificate::genesis]
      (certificate.rs:46-59) rebuilds, for every authority, the canonical
      [HeaderBuilder::default().author(authority.id()).epoch(committee.epoch())
      .build()] with [..Self::default()], i.e. an EMPTY bitmap and
      [SignatureVerificationState::Unsigned(BlsSignature::default())]
      (certificate.rs:451-455). [contains] uses [impl PartialEq for Certificate]
      (certificate.rs:495-502), which compares ONLY header digest, round, epoch
      and origin - never the bitmap and never the signature state. So the
      shortcut certifies the header exactly and the attached signature material
      not at all.

    {1 The three ingress routes, and why they are distinct transitions}

    The threshold [ensure!] exists in three places and they are NOT one gate:

    - {b [Fetch_direct]} - the certificate-fetcher / state-sync path.
      [certificate_fetcher.rs:494-505] normalises every fetched certificate
      through [validate_fetched_certificate] (certificate.rs:462-471), which
      overwrites the wire-supplied verification state with
      [Unverified(self.aggregated_signature()?)] and therefore FAILS with
      [RecoverBlsAggregateSignatureBytes] on a wire-supplied
      [SignatureVerificationState::Genesis], because [aggregated_signature()]
      returns [None] exactly for that variant (certificate.rs:329-337). The
      batch then reaches [CertificateValidator::verify_collection]
      (cert_validator.rs:246-268); a certificate classified as needing direct
      work goes to [validate_and_verify] (cert_validator.rs:358 -> :114-130 ->
      certificate.rs:225), where certificate.rs:246 is the ONLY threshold gate.
      This route means "reached the types-layer entry point", i.e. it is
      DOWNSTREAM of two upstream filters that the model does not carry as state
      because they are not part of the modeled mechanism. One is the fetcher's
      state normalisation just described; the other is the garbage-collection
      test at cert_validator.rs:115-125, [if certificate.round() < gc_round {
      return Err(CertificateError::TooOld(..)) }]. The gc test matters for the
      round-0 statement and is named there rather than assumed away: a genesis
      certificate clears it only while the receiver's [gc_round] is still 0,
      which is exactly the bootstrapping window in which the fetcher asks a peer
      for genesis parents in the first place.
    - {b [Fetch_indirect]} - the SAME fetched batch, for a certificate that is a
      parent of another certificate in the batch and whose round is not a
      multiple of the verification interval
      ([requires_direct_verification], cert_validator.rs:303-312). Such a
      certificate is stamped [VerifiedIndirectly] by [mark_verified_indirectly]
      (cert_validator.rs:317-323) and NO threshold and NO signature check runs on
      it at all. This route is modeled because leaving it out would make the
      family's security statement true only by omission (contract R5): the model
      must show that an inquorate or bitmap-padded certificate really can end up
      [is_verified()] without any gate, which is why S1 is scoped to DIRECT
      verification and not to [is_verified()].
    - {b [Gossip]} - the primary gossip path. [handler.rs:238-279] calls
      [cert.validate_received()] (certificate.rs:295-301, same
      [aggregated_signature()] normalisation) and then
      [cert.verify_cert(&committee)] (handler.rs:252). [verify_cert]
      (certificate.rs:255-266) carries its OWN threshold [ensure!] at
      certificate.rs:261 over the FREE function [quorum_threshold(committee.len()
      as u64)] (committee.rs:686-688), and it has NO round-0 shortcut and no
      [header.validate] call. This route is the sibling repair for the
      {!No_weight_threshold} deletion, and the model carries it so that the
      deletion is honestly scoped to the fetcher path.

    Round 0 never takes [Fetch_indirect]. [requires_direct_verification]
    (cert_validator.rs:303-312) is
    [!all_parents.contains(&cert.digest()) || cert.header().round()
    .is_multiple_of(self.config.network_config().sync_config()
    .certificate_verification_round_interval)] and the interval defaults to 50
    (crates/config/src/network.rs:250, :267), so round 0 is a multiple of it and
    a genesis certificate ALWAYS requires direct verification even when it is a
    parent. That fact is what stops [mark_verified_indirectly] from repairing the
    {!No_genesis_header_equality} deletion, so the model encodes it as a
    route/offer admissibility restriction rather than assuming it.

    {1 Components}

    - [route]: which of the three ingress paths above disposed of the offer.
    - [offer]: the peer-supplied certificate, as a curated class. Each class
      fixes both the wire-observable bytes and the HIDDEN global truth about who
      really produced a BLS signature over [to_intent_message(header_digest)].
    - the offer's life: [No_offer] -> [Pending (route, offer)] -> [Settled
      (route, offer, verdict)], the verdict being DERIVED by {!settle} from the
      route, the offer and the active mutation.

    Reachable pristine: 1 + 22 + 22 = 45 states (9 offers on each of the two
    round-0-capable routes plus 4 higher-round offers on [Fetch_indirect], each
    with exactly one settle step).

    {1 Role mapping}

    - {b V0 is the receiving validator} - the sole knowledge agent. Its view is
      the route the certificate arrived on, everything it can read off the wire
      or recompute locally (the round class, whether the header equals a
      canonical genesis header it rebuilds itself from the committee, the size of
      the credited bitmap, and whether the wire claimed the [Genesis]
      verification state), and the verdict it reached. It does NOT see who really
      signed: no vote traffic reaches it on the fetch path, the aggregate carries
      no identities, and the assembler's local vote buffer is not on the wire.

      One thing the view deliberately leaves out is V0's own signing act, on the
      grounds that a validator fetching a header's certificate as a missing DAG
      parent generally did not vote on it. That omission is checked, not assumed:
      the only place it could matter is the omission-ignorance conjunct, and the
      witness pair there is {!Quorum_faithful} versus {!Quorum_dropped_vote},
      whose difference is V3's discarded vote. V0 is credited and signing in BOTH
      members of that pair, so adding V0's own vote to the view would not
      separate them and the ignorance survives.
    - {b V1..V9 are idle non-agents} with the constant blank view {!View_idle};
      they never appear under K in any statement. *)

(** Which ingress path disposed of the offered certificate. The three are
    distinct transitions because they run different gate sets - see the module
    header. *)
type route =
  | Fetch_direct
      (** certificate-fetcher ingress, classified as needing direct work:
          certificate_fetcher.rs:494-505 -> cert_validator.rs:288-295, :358 ->
          certificate.rs:225-251. The round-0 shortcut (certificate.rs:236-238),
          [header.validate] (certificate.rs:241, header.rs:97-132), the threshold
          [ensure!] (certificate.rs:246) and the aggregate check
          (certificate.rs:284-286) all live on this path. *)
  | Fetch_indirect
      (** the same fetched batch, for a certificate that is a parent of another
          certificate in the batch: cert_validator.rs:293 ->
          [mark_verified_indirectly] (:317-323) stamps [VerifiedIndirectly] and
          runs NO threshold and NO signature check. Round 0 can never take this
          route (cert_validator.rs:303-312 with the interval 50 of
          network.rs:267: 0 is a multiple of 50). *)
  | Gossip
      (** primary gossip ingress: handler.rs:246 [validate_received]
          (certificate.rs:295-301) then handler.rs:252 [verify_cert]
          (certificate.rs:255-266), which carries its OWN threshold [ensure!] at
          certificate.rs:261 and has no round-0 shortcut. *)

(** Total order index for {!route}. *)
let route_index = function Fetch_direct -> 0 | Fetch_indirect -> 1 | Gossip -> 2

(** Total order on {!route}. *)
let route_compare a b = Int.compare (route_index a) (route_index b)

(** Every ingress route, in canonical order. *)
let all_routes = [ Fetch_direct; Fetch_indirect; Gossip ]

(** [true] iff the route runs the real gate set of certificate.rs:243-248 (or
    its [verify_cert] twin at certificate.rs:257-263) rather than stamping a
    verification state without checking anything. *)
let route_runs_gates = function
  | Fetch_direct | Gossip -> true
  | Fetch_indirect -> false

(** The credited weight of a certificate's roaring bitmap, i.e. the value
    [signed_by] (certificate.rs:177-199) returns as [weight] and equivalently the
    length of the key list it hands to the aggregate check. It is a SET size: the
    monotone cursor at certificate.rs:189-194 advances [auth_iter] once per
    credited position over a [BTreeSet], so the credited members are pairwise
    distinct and no index can be counted twice. *)
type credit =
  | Credit_none
      (** the empty bitmap [Certificate::genesis] builds via [..Self::default()]
          (certificate.rs:51-57): [signed_by] returns weight 0 and an EMPTY key
          list *)
  | Credit_one
      (** one credited index: weight 1, below the quorum threshold of 3 *)
  | Credit_quorum
      (** three distinct credited indices: weight 3, exactly
          [committee.quorum_threshold()] for the four-member committee
          (committee.rs:247-252, :261-263) *)

(** Total order index for {!credit}. *)
let credit_index = function
  | Credit_none -> 0
  | Credit_one -> 1
  | Credit_quorum -> 2

(** Total order on {!credit}. *)
let credit_compare a b = Int.compare (credit_index a) (credit_index b)

(** [true] iff the credited weight clears [committee.quorum_threshold()] = 3,
    i.e. iff [ensure!(weight >= threshold, ...)] (certificate.rs:246, and its
    twin certificate.rs:261) passes. *)
let credit_meets_quorum = function
  | Credit_none | Credit_one -> false
  | Credit_quorum -> true

(** [true] iff the bitmap credits nobody, so [signed_by] hands an EMPTY key list
    to [verify_secure] and [if pks.is_empty() { return false; }]
    (bls_signature.rs:274-276) rejects regardless of the signature bytes. *)
let credit_is_empty = function
  | Credit_none -> true
  | Credit_one | Credit_quorum -> false

(** How many committee members really produced a BLS signature over
    [to_intent_message(header_digest)] for the offered certificate. HIDDEN: no
    view projects it. The receiving validator never sees the individual [Vote]
    messages on the fetch path, and the aggregate is a single group element that
    names nobody. *)
type signers =
  | Signed_none  (** no committee member signed this header digest *)
  | Signed_one  (** exactly one member signed *)
  | Signed_two  (** exactly two distinct members signed *)
  | Signed_quorum  (** exactly three distinct members signed *)
  | Signed_all  (** all four members signed *)

(** Total order index for {!signers}. *)
let signers_index = function
  | Signed_none -> 0
  | Signed_one -> 1
  | Signed_two -> 2
  | Signed_quorum -> 3
  | Signed_all -> 4

(** Total order on {!signers}. *)
let signers_compare a b = Int.compare (signers_index a) (signers_index b)

(** [true] iff at least three PAIRWISE DISTINCT committee members signed. *)
let signers_at_least_three = function
  | Signed_none | Signed_one | Signed_two -> false
  | Signed_quorum | Signed_all -> true

(** [true] iff every committee member signed. Used only as the R2 non-singleton
    probe: it is the fact that separates {!Quorum_faithful} from
    {!Quorum_dropped_vote} inside one view class. *)
let signers_all_four = function
  | Signed_all -> true
  | Signed_none | Signed_one | Signed_two | Signed_quorum -> false

(** The class of peer-supplied certificate the environment offers. Each class
    fixes the wire-observable bytes AND the hidden truth behind them; the
    functions below are the two projections. *)
type offer =
  | Quorum_faithful
      (** round r > 0, bitmap credits {0,1,2}, and exactly those three signed:
          the assembler emitted at the first vote that crossed quorum
          (aggregators/votes.rs:64-90, [if self.weight >=
          committee.quorum_threshold()] at :65) and no further vote existed. *)
  | Quorum_dropped_vote
      (** round r > 0, the BYTE-IDENTICAL certificate crediting {0,1,2}, but all
          four members signed: V3's vote arrived after the assembler had already
          returned at votes.rs:89 and was discarded. This is the omission witness
          - nothing on the wire distinguishes it from {!Quorum_faithful}, and
          [impl PartialEq for Certificate] (certificate.rs:495-502) compares only
          header digest, round, epoch and origin, so the two collapse in any
          digest-keyed store. *)
  | Padded_bitmap
      (** round r > 0, bitmap credits {0,1,2} but only two of them signed: a
          relayer inserted an index for a member that produced no signature. The
          aggregate then does not verify against the three keys [signed_by]
          derives, so certificate.rs:284-286 rejects it. *)
  | Inquorate_single
      (** round r > 0, bitmap credits {0} and exactly that member signed: an
          honest but inquorate certificate. Rejected pristine by
          certificate.rs:246 / :261. *)
  | Genesis_empty
      (** round 0, header EQUAL to the canonical genesis header of a committee
          member, empty bitmap, and the default infinity-point aggregate that
          [Certificate::genesis] leaves behind (certificate.rs:46-59,
          :451-455). Nobody signed it. *)
  | Genesis_padded_garbage
      (** round 0, the SAME canonical genesis header, but the peer attached a
          bitmap crediting {0,1,2} and arbitrary aggregate bytes. Nobody signed.
          [PartialEq] ignores both fields (certificate.rs:495-502), so
          [Self::genesis(committee).contains(self)] still matches. *)
  | Genesis_padded_signed
      (** round 0, the SAME canonical genesis header and the SAME bitmap
          crediting {0,1,2}, but this time three distinct members really did
          produce signatures over [to_intent_message(genesis_header_digest)] and
          the attached bytes are their genuine aggregate. Wire-indistinguishable
          from {!Genesis_padded_garbage}: this pair is the ignorance witness for
          S3, and it exists precisely because the shortcut at
          certificate.rs:236-238 returns before certificate.rs:243-248 ever looks
          at the signature material. *)
  | Genesis_forged
      (** round 0, a header that is NOT in the locally rebuilt genesis set - its
          author is not a committee member - with an empty bitmap. The equality
          test at certificate.rs:236 fails and [header.validate]
          (certificate.rs:241, header.rs:118-122
          [HeaderError::UnknownAuthority]) fails too. *)
  | Genesis_state_claim
      (** round 0, canonical genesis header, but the peer set the wire
          [signature_verification_state] to
          [SignatureVerificationState::Genesis] (certificate.rs:446-448) hoping
          for the free pass at certificate.rs:272-274. Both ingress
          normalisations reject it first, because [aggregated_signature()]
          returns [None] exactly for that variant (certificate.rs:329-337):
          [validate_fetched_certificate] (certificate.rs:462-471) and
          [validate_received] (certificate.rs:295-301) both fail with
          [RecoverBlsAggregateSignatureBytes], and so does
          [mark_verified_indirectly] (cert_validator.rs:317-323). Modeling this
          class is what refutes the one sibling repair a skeptic would name for
          {!No_genesis_header_equality}. *)

(** Total order index for {!offer}. *)
let offer_index = function
  | Quorum_faithful -> 0
  | Quorum_dropped_vote -> 1
  | Padded_bitmap -> 2
  | Inquorate_single -> 3
  | Genesis_empty -> 4
  | Genesis_padded_garbage -> 5
  | Genesis_padded_signed -> 6
  | Genesis_forged -> 7
  | Genesis_state_claim -> 8

(** Total order on {!offer}. *)
let offer_compare a b = Int.compare (offer_index a) (offer_index b)

(** Every offer class, in canonical order. *)
let all_offers =
  [
    Quorum_faithful;
    Quorum_dropped_vote;
    Padded_bitmap;
    Inquorate_single;
    Genesis_empty;
    Genesis_padded_garbage;
    Genesis_padded_signed;
    Genesis_forged;
    Genesis_state_claim;
  ]

(** [true] iff the offered certificate has [round() == 0], the guard of the
    shortcut at certificate.rs:236. *)
let offer_is_round_zero = function
  | Quorum_faithful | Quorum_dropped_vote | Padded_bitmap | Inquorate_single ->
      false
  | Genesis_empty | Genesis_padded_garbage | Genesis_padded_signed
  | Genesis_forged | Genesis_state_claim ->
      true

(** [true] iff the offered header equals the canonical genesis header of some
    committee member, i.e. iff [Self::genesis(committee).contains(self)]
    (certificate.rs:236) holds. Locally computable by the receiver: it rebuilds
    the whole genesis set from the committee (certificate.rs:46-59). *)
let offer_has_canonical_genesis_header = function
  | Genesis_empty | Genesis_padded_garbage | Genesis_padded_signed
  | Genesis_state_claim ->
      true
  | Genesis_forged | Quorum_faithful | Quorum_dropped_vote | Padded_bitmap
  | Inquorate_single ->
      false

(** [true] iff the wire-supplied [signature_verification_state] is the [Genesis]
    variant (certificate.rs:446-448), the one [aggregated_signature()] maps to
    [None] (certificate.rs:329-337). *)
let offer_claims_genesis_state = function
  | Genesis_state_claim -> true
  | Quorum_faithful | Quorum_dropped_vote | Padded_bitmap | Inquorate_single
  | Genesis_empty | Genesis_padded_garbage | Genesis_padded_signed
  | Genesis_forged ->
      false

(** [true] iff the header clears [Header::validate] (header.rs:97-132): correct
    epoch, no more parents than the committee size, and an author that is a
    committee member. Called from certificate.rs:241, on the [Fetch_direct]
    route only - [verify_cert] (certificate.rs:255-266) does not call it. *)
let offer_header_validates = function
  | Genesis_forged -> false
  | Quorum_faithful | Quorum_dropped_vote | Padded_bitmap | Inquorate_single
  | Genesis_empty | Genesis_padded_garbage | Genesis_padded_signed
  | Genesis_state_claim ->
      true

(** The credited weight the offered bitmap resolves to under
    [signed_by]. WIRE-OBSERVABLE: the receiver holds the bitmap. *)
let offer_credit = function
  | Quorum_faithful | Quorum_dropped_vote | Padded_bitmap
  | Genesis_padded_garbage | Genesis_padded_signed ->
      Credit_quorum
  | Inquorate_single -> Credit_one
  | Genesis_empty | Genesis_forged | Genesis_state_claim -> Credit_none

(** How many committee members really signed the offered header digest. HIDDEN:
    projected into no view. *)
let offer_signers = function
  | Quorum_faithful -> Signed_quorum
  | Quorum_dropped_vote -> Signed_all
  | Padded_bitmap -> Signed_two
  | Inquorate_single -> Signed_one
  | Genesis_padded_signed -> Signed_quorum
  | Genesis_empty | Genesis_padded_garbage | Genesis_forged
  | Genesis_state_claim ->
      Signed_none

(** [true] iff every index the bitmap credits names a committee member that
    really signed - the credited set is a SUBSET of the true signer set. HIDDEN.
    This is what the aggregate check at certificate.rs:284-286 enforces: the key
    list is derived from the bitmap, so a credited non-signer makes the
    aggregate fail. *)
let offer_bitmap_is_signature_backed = function
  | Quorum_faithful | Quorum_dropped_vote | Inquorate_single
  | Genesis_padded_signed ->
      true
  | Padded_bitmap | Genesis_padded_garbage -> false
  | Genesis_empty | Genesis_forged | Genesis_state_claim ->
      (* empty bitmap: the subset claim is vacuously true *)
      true

(** [true] iff no committee member OUTSIDE the bitmap signed - the true signer
    set is a subset of the credited set. HIDDEN, and unknowable from the
    certificate: the assembler returns at the first vote that crosses quorum
    (aggregators/votes.rs:65-89), so a member that voted may simply not
    appear. *)
let offer_has_no_uncredited_signer = function
  | Quorum_faithful | Padded_bitmap | Inquorate_single | Genesis_empty
  | Genesis_padded_garbage | Genesis_padded_signed | Genesis_forged
  | Genesis_state_claim ->
      true
  | Quorum_dropped_vote -> false

(** [true] iff the (route, offer) pair is one the real ingress can produce.
    Round 0 never takes [Fetch_indirect]: [requires_direct_verification]
    (cert_validator.rs:303-312) short-circuits on
    [round().is_multiple_of(certificate_verification_round_interval)] and the
    interval defaults to 50 (network.rs:250, :267), and 0 is a multiple of 50, so
    every round-0 certificate in a fetched batch requires DIRECT verification
    even when it is a parent of another certificate in that batch. *)
let route_admits_offer r o =
  match r with
  | Fetch_direct | Gossip -> true
  | Fetch_indirect -> Bool.not (offer_is_round_zero o)

(** How the ingress disposed of the offered certificate. *)
type verdict =
  | Verified_direct
      (** the real gate set ran and passed: the threshold [ensure!]
          (certificate.rs:246 on the fetch path, :261 on the gossip path) and the
          aggregate check (certificate.rs:284-286) both cleared, and
          [verify_signature] stamped [VerifiedDirectly] (certificate.rs:288-289).
      *)
  | Genesis_shortcut
      (** [validate_and_verify] returned [Ok(())] at certificate.rs:237 on the
          strength of [self.round() == 0 && Self::genesis(committee)
          .contains(self)] ALONE, before [header.validate] (:241), before the
          threshold [ensure!] (:246) and before [verify_signature] (:248). Note
          the certificate is NOT [is_verified()] afterwards - the ingress
          normalisation had already set [Unverified] and the shortcut returns
          before :288-289 - but the caller (cert_validator.rs:103, :128, :358)
          sees [Ok] and forwards it. *)
  | Verified_indirect
      (** [mark_verified_indirectly] (cert_validator.rs:317-323) stamped
          [VerifiedIndirectly] on the strength of the certificate being a parent
          of another certificate in the fetched batch. No threshold check and no
          signature check ran on THIS certificate. *)
  | Rejected  (** the ingress returned an error and dropped the certificate *)

(** Total order index for {!verdict}. *)
let verdict_index = function
  | Verified_direct -> 0
  | Genesis_shortcut -> 1
  | Verified_indirect -> 2
  | Rejected -> 3

(** Total order on {!verdict}. *)
let verdict_compare a b = Int.compare (verdict_index a) (verdict_index b)

(** The life of the one modeled certificate offer. *)
type life =
  | No_offer  (** nothing has arrived at the receiving validator yet *)
  | Pending of route * offer
      (** the certificate has arrived on this route; the ingress has not yet
          dispositioned it, so the receiver has only the wire bytes *)
  | Settled of route * offer * verdict
      (** the ingress ran and reached a verdict *)

(** Total deterministic order on {!life}: [No_offer] < [Pending] < [Settled],
    field-wise within each constructor. Every constructor pair is spelled. *)
let life_compare a b =
  match (a, b) with
  | No_offer, No_offer -> 0
  | No_offer, (Pending (_, _) | Settled (_, _, _)) -> -1
  | (Pending (_, _) | Settled (_, _, _)), No_offer -> 1
  | Pending (ra, oa), Pending (rb, ob) ->
      let c = route_compare ra rb in
      if Bool.not (Int.equal c 0) then c else offer_compare oa ob
  | Pending (_, _), Settled (_, _, _) -> -1
  | Settled (_, _, _), Pending (_, _) -> 1
  | Settled (ra, oa, va), Settled (rb, ob, vb) ->
      let c = route_compare ra rb in
      if Bool.not (Int.equal c 0) then c
      else
        let c1 = offer_compare oa ob in
        if Bool.not (Int.equal c1 0) then c1 else verdict_compare va vb

(** The joint global state: the one certificate offer and its life stage. *)
type state = { ingress : life }

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 = life_compare s1.ingress s2.ingress

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** What the receiving validator can read off the certificate bytes or recompute
    locally from the committee. This is the whole wire projection: the aggregate
    names no signer, the bitmap is public, and the genesis set is locally
    rebuildable (certificate.rs:46-59). *)
type wire =
  | Wire_quorum_bitmap
      (** round r > 0, bitmap credits three distinct members *)
  | Wire_single_bitmap  (** round r > 0, bitmap credits one member *)
  | Wire_genesis_empty
      (** round 0, header equals a canonical genesis header, empty bitmap *)
  | Wire_genesis_padded
      (** round 0, header equals a canonical genesis header, bitmap credits three
          members *)
  | Wire_genesis_forged
      (** round 0, header is NOT in the locally rebuilt genesis set *)
  | Wire_genesis_state_claim
      (** round 0, canonical header, wire verification state claims [Genesis] *)

(** Total order index for {!wire}. *)
let wire_index = function
  | Wire_quorum_bitmap -> 0
  | Wire_single_bitmap -> 1
  | Wire_genesis_empty -> 2
  | Wire_genesis_padded -> 3
  | Wire_genesis_forged -> 4
  | Wire_genesis_state_claim -> 5

(** Total order on {!wire}. *)
let wire_compare a b = Int.compare (wire_index a) (wire_index b)

(** The wire projection of an offer class. Note that {!Quorum_faithful},
    {!Quorum_dropped_vote} and {!Padded_bitmap} collapse to ONE wire class, and
    so do {!Genesis_padded_garbage} and {!Genesis_padded_signed}: those
    collapses are exactly the partial information this family is about. *)
let offer_wire = function
  | Quorum_faithful | Quorum_dropped_vote | Padded_bitmap -> Wire_quorum_bitmap
  | Inquorate_single -> Wire_single_bitmap
  | Genesis_empty -> Wire_genesis_empty
  | Genesis_padded_garbage | Genesis_padded_signed -> Wire_genesis_padded
  | Genesis_forged -> Wire_genesis_forged
  | Genesis_state_claim -> Wire_genesis_state_claim

(** A validator's local view.

    [View_pre] / [View_offered] / [View_settled]: V0, the RECEIVING validator and
    the family's only knowledge agent. Before anything arrives it has observed
    nothing; once a certificate arrives it holds the route and the wire
    projection; once the ingress runs it also holds the verdict. It never sees
    {!offer_signers}, {!offer_bitmap_is_signature_backed} or
    {!offer_has_no_uncredited_signer}: those are facts about other nodes' signing
    acts, and neither the aggregate (one group element) nor the bitmap (an
    assembler-chosen set) carries them.

    [View_idle]: the constant blank view of the non-agents V1..V9. *)
type view =
  | View_pre
  | View_offered of route * wire
  | View_settled of route * wire * verdict
  | View_idle

(** Total deterministic order over ALL fields of V0's settled view. *)
let settled_view_compare (r, w, v) (r', w', v') =
  let c = route_compare r r' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = wire_compare w w' in
    if Bool.not (Int.equal c1 0) then c1 else verdict_compare v v'

(** Total order on views: [View_idle] < [View_pre] < [View_offered] <
    [View_settled], field-wise inside each constructor. Every constructor pair is
    spelled: no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_pre | View_offered (_, _) | View_settled (_, _, _)) -> -1
  | (View_pre | View_offered (_, _) | View_settled (_, _, _)), View_idle -> 1
  | View_pre, View_pre -> 0
  | View_pre, (View_offered (_, _) | View_settled (_, _, _)) -> -1
  | (View_offered (_, _) | View_settled (_, _, _)), View_pre -> 1
  | View_offered (ra, wa), View_offered (rb, wb) ->
      let c = route_compare ra rb in
      if Bool.not (Int.equal c 0) then c else wire_compare wa wb
  | View_offered (_, _), View_settled (_, _, _) -> -1
  | View_settled (_, _, _), View_offered (_, _) -> 1
  | View_settled (ra, wa, va), View_settled (rb, wb, vb) ->
      settled_view_compare (ra, wa, va) (rb, wb, vb)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 (the receiving validator) is the only knowledge agent;
    V1..V9 are idle non-agents with the constant blank view and never appear
    under K.

    The projection deliberately drops every hidden field: V0 gets the route, the
    wire class and the verdict, and nothing about who actually signed. *)
let view v s =
  match v with
  | Validator.V0 -> (
      match s.ingress with
      | No_offer -> View_pre
      | Pending (r, o) -> View_offered (r, offer_wire o)
      | Settled (r, o, vd) -> View_settled (r, offer_wire o, vd))
  | Validator.V1 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | No_weight_threshold
      (** Delete
          [ensure!(weight >= threshold, CertificateError::Inquorate { stake:
          weight, threshold });] at crates/types/src/primary/certificate.rs:246 -
          the copy inside [validate_and_verify], and only that copy. This ADDS
          the transition [Pending (Fetch_direct, Inquorate_single) -> Settled (..,
          Verified_direct)]: a certificate crediting ONE member, whose aggregate
          verifies honestly against that member's single key, is verified and
          forwarded.

          Two candidate repairs exist and the model carries BOTH so the deletion
          cannot look unrepaired by omission. (1) [verify_secure]'s
          [if pks.is_empty() { return false; }] (bls_signature.rs:274-276) is
          modeled in {!aggregate_verifies} and does still reject the ZERO-credit
          offers ({!Genesis_empty}, {!Genesis_forged}), but it says nothing about
          one or two keys, so it does not repair the single-signer case. (2)
          [Certificate::verify_cert] (certificate.rs:255-266) carries an
          INDEPENDENT threshold [ensure!] at certificate.rs:261 over the free
          [quorum_threshold(committee.len() as u64)] (committee.rs:686-688); it
          is reached only from the gossip ingress (handler.rs:252), which the
          model carries as the {!Gossip} route and which this mutation leaves
          untouched - so an inquorate GOSSIPED certificate is still rejected.
          That is why the statement is scoped to direct verification reached over
          any route: the mutation still refutes it, because the fetcher path has
          no second threshold gate. [Certificate::new_internal]'s
          [ensure!(!check_stake || weight >= committee.quorum_threshold(), ...)]
          (certificate.rs:142-145) guards LOCAL construction from votes
          (aggregators/votes.rs:66-70) and never sees a peer-supplied
          certificate. *)
  | Trust_supplied_signer_set
      (** Verify the aggregate against a caller-supplied signer list instead of
          the key list the bitmap names: replace the [pks] argument threaded from
          [self.signed_by(&committee.bls_keys())] (certificate.rs:243, :257) into
          [self.verify_signature(pks)] (certificate.rs:248, :263) with a list the
          caller supplies, so [certificate.rs:284-286]
          [aggregate_signature.verify_secure(&to_intent_message(certificate_digest),
          &pks[..])] no longer binds the bitmap to the signature. This ADDS
          [Pending (Fetch_direct, Padded_bitmap) -> Settled (.., Verified_direct)]
          and its {!Gossip} twin: a relayer can insert an index for a member that
          never signed and the certificate still verifies.

          No sibling path repairs it. [verify_cert] (certificate.rs:255-266)
          routes to the SAME [verify_signature] body, so the gossip replica of
          the threshold gate is irrelevant here and the model applies the
          deletion on both gated routes. Nothing outside crates/types re-derives
          or cross-checks the signer set: [Certificate::signed_authorities()]
          (certificate.rs:352-354) has no consumer anywhere else in the workspace
          (every other [signed_authorities] hit is the unrelated
          [EpochCertificate] field of crates/types/src/primary/epoch.rs:144 and
          its producers in crates/node and crates/storage), and
          [signed_authorities_with_committee] (certificate.rs:169-173) merely
          re-runs [signed_by]. Individual [Vote]s are re-verified only during
          LOCAL aggregation (aggregators/votes.rs:49-57), never for a received
          certificate. *)
  | No_genesis_header_equality
      (** Delete the round-0 shortcut
          [if self.round() == 0 && Self::genesis(committee).contains(self) {
          return Ok(()); }] at crates/types/src/primary/certificate.rs:236-238.
          This REMOVES the transition
          [Pending (Fetch_direct, Genesis_empty) -> Settled (.., Genesis_shortcut)]
          and its two padded siblings: execution falls through to
          [header.validate] (:241) and the threshold [ensure!] (:246), where the
          empty genesis bitmap resolves to weight 0 and is rejected as
          [Inquorate].

          No sibling path repairs it for a PEER-SUPPLIED round-0 certificate.
          (a) [Certificate::genesis] is called at
          crates/consensus/primary/src/proposer.rs:145 and
          crates/config/src/consensus.rs:144 to seed a node's OWN DAG roots -
          local construction, not an ingress filter. (b) The
          [SignatureVerificationState::Genesis] free pass at
          certificate.rs:272-274 is unreachable from the wire: both
          [validate_fetched_certificate] (certificate.rs:462-471) and
          [validate_received] (certificate.rs:295-301) overwrite the state with
          [Unverified(self.aggregated_signature()?)] and
          [aggregated_signature()] returns [None] precisely for [Genesis]
          (certificate.rs:329-337), so such an offer fails with
          [RecoverBlsAggregateSignatureBytes]. The model carries that attempt as
          {!Genesis_state_claim} and it is rejected on every route, pristine and
          mutated alike. (c) [mark_verified_indirectly] (cert_validator.rs:317-323)
          would be a real repair - it stamps [VerifiedIndirectly] with no checks
          - but it is unreachable at round 0, because
          [requires_direct_verification] (cert_validator.rs:303-312) forces
          direct verification whenever
          [round().is_multiple_of(certificate_verification_round_interval)] and
          the interval is 50 (network.rs:250, :267), of which 0 is a multiple.
          The model encodes that as {!route_admits_offer}. *)

(** Does the aggregate check at certificate.rs:284-286 pass?

    Pristine and under the two unrelated deletions, [verify_secure] is handed
    exactly the keys the bitmap named, so it passes iff every credited member
    really signed AND the key list is non-empty - the latter being
    [if pks.is_empty() { return false; }] (bls_signature.rs:274-276), which is
    why a genesis certificate's empty bitmap can never clear this gate.

    Under {!Trust_supplied_signer_set} the key list is no longer derived from the
    bitmap, so a credited non-signer no longer breaks the check; the [is_empty]
    guard is the only thing left. *)
let aggregate_verifies mut o =
  match mut with
  | Trust_supplied_signer_set -> Bool.not (credit_is_empty (offer_credit o))
  | Pristine | No_weight_threshold | No_genesis_header_equality ->
      offer_bitmap_is_signature_backed o
      && Bool.not (credit_is_empty (offer_credit o))

(** Does the threshold [ensure!] on the [validate_and_verify] path
    (certificate.rs:246) pass? {!No_weight_threshold} deletes it; the other
    mutations leave it standing. *)
let fetch_threshold_passes mut o =
  match mut with
  | No_weight_threshold -> true
  | Pristine | Trust_supplied_signer_set | No_genesis_header_equality ->
      credit_meets_quorum (offer_credit o)

(** Does the round-0 shortcut at certificate.rs:236-238 fire?
    {!No_genesis_header_equality} deletes it. *)
let genesis_shortcut_fires mut o =
  match mut with
  | No_genesis_header_equality -> false
  | Pristine | No_weight_threshold | Trust_supplied_signer_set ->
      offer_is_round_zero o && offer_has_canonical_genesis_header o

(** The ingress verdict for one offer on one route under one mutation: the Rust
    control flow of certificate.rs:225-251 ([Fetch_direct]),
    certificate.rs:255-266 ([Gossip]) and cert_validator.rs:288-323
    ([Fetch_indirect]) as a total function.

    Both fetch routes and the gossip route first normalise the wire verification
    state, which is where a claimed [Genesis] state dies
    (certificate.rs:462-471, :295-301, cert_validator.rs:319-320). *)
let settle mut r o =
  match r with
  | Fetch_indirect ->
      if offer_claims_genesis_state o then Rejected else Verified_indirect
  | Gossip ->
      if offer_claims_genesis_state o then Rejected
      else if
        credit_meets_quorum (offer_credit o) && aggregate_verifies mut o
      then Verified_direct
      else Rejected
  | Fetch_direct ->
      if offer_claims_genesis_state o then Rejected
      else if genesis_shortcut_fires mut o then Genesis_shortcut
      else if
        offer_header_validates o
        && fetch_threshold_passes mut o
        && aggregate_verifies mut o
      then Verified_direct
      else Rejected

(** The transition relation: the environment offers one certificate class on one
    admissible ingress route, then the ingress runs exactly once and settles.
    [Settled] is terminal and the kernel stutter-closes it. *)
let next_with mut s =
  match s.ingress with
  | No_offer ->
      List.concat_map
        (fun r ->
          List.map
            (fun o -> { ingress = Pending (r, o) })
            (List.filter (route_admits_offer r) all_offers))
        all_routes
  | Pending (r, o) -> [ { ingress = Settled (r, o, settle mut r o) } ]
  | Settled (_, _, _) -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: nothing has arrived at the receiving validator yet. *)
let initial = { ingress = No_offer }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Offer_pending
      (** a certificate has arrived and the ingress has not yet dispositioned
          it *)
  | On_direct_fetch
      (** the certificate came in over the certificate-fetcher route and was
          classified as needing direct verification (cert_validator.rs:288-295,
          :358) *)
  | Verified_directly
      (** the real gate set ran and passed: the threshold [ensure!]
          (certificate.rs:246 or :261) and the aggregate check
          (certificate.rs:284-286) both cleared *)
  | Admitted_by_genesis_shortcut
      (** [validate_and_verify] returned [Ok] at certificate.rs:237 on the header
          equality test alone, before any gate ran *)
  | Verified_indirectly
      (** [mark_verified_indirectly] (cert_validator.rs:317-323) stamped
          [VerifiedIndirectly] without running any check on this certificate *)
  | Round_zero  (** the certificate's [round()] is 0 (certificate.rs:236) *)
  | Canonical_genesis_header
      (** the header equals the canonical genesis header of a committee member,
          i.e. [Self::genesis(committee).contains(self)] (certificate.rs:236,
          :46-59, :495-502) *)
  | Wire_claims_genesis_state
      (** the wire-supplied [signature_verification_state] is the [Genesis]
          variant (certificate.rs:446-448) *)
  | Credits_quorum
      (** the bitmap credits three distinct members, i.e. [signed_by] returns
          [weight] equal to [committee.quorum_threshold()] *)
  | Three_distinct_signers
      (** HIDDEN: at least three PAIRWISE DISTINCT committee members really
          produced a BLS signature over [to_intent_message(header_digest)] *)
  | All_four_signed  (** HIDDEN: every committee member signed *)
  | Bitmap_signature_backed
      (** HIDDEN: every index the bitmap credits names a committee member that
          really signed - the credited set is a subset of the true signer set *)
  | No_uncredited_signer
      (** HIDDEN: no committee member outside the bitmap signed - the true signer
          set is a subset of the credited set *)

(** [true] iff a certificate has arrived in this state and it satisfies [p].
    Nothing holds of the offer before one arrives. *)
let about_offer p s =
  match s.ingress with
  | No_offer -> false
  | Pending (_, o) -> p o
  | Settled (_, o, _) -> p o

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Offer_pending -> (
      match s.ingress with
      | No_offer -> false
      | Pending (_, _) -> true
      | Settled (_, _, _) -> false)
  | On_direct_fetch -> (
      match s.ingress with
      | No_offer -> false
      | Pending (r, _) -> (
          match r with
          | Fetch_direct -> true
          | Fetch_indirect | Gossip -> false)
      | Settled (r, _, _) -> (
          match r with
          | Fetch_direct -> true
          | Fetch_indirect | Gossip -> false))
  | Verified_directly -> (
      match s.ingress with
      | No_offer -> false
      | Pending (_, _) -> false
      | Settled (_, _, vd) -> (
          match vd with
          | Verified_direct -> true
          | Genesis_shortcut | Verified_indirect | Rejected -> false))
  | Admitted_by_genesis_shortcut -> (
      match s.ingress with
      | No_offer -> false
      | Pending (_, _) -> false
      | Settled (_, _, vd) -> (
          match vd with
          | Genesis_shortcut -> true
          | Verified_direct | Verified_indirect | Rejected -> false))
  | Verified_indirectly -> (
      match s.ingress with
      | No_offer -> false
      | Pending (_, _) -> false
      | Settled (_, _, vd) -> (
          match vd with
          | Verified_indirect -> true
          | Verified_direct | Genesis_shortcut | Rejected -> false))
  | Round_zero -> about_offer offer_is_round_zero s
  | Canonical_genesis_header -> about_offer offer_has_canonical_genesis_header s
  | Wire_claims_genesis_state -> about_offer offer_claims_genesis_state s
  | Credits_quorum ->
      about_offer (fun o -> credit_meets_quorum (offer_credit o)) s
  | Three_distinct_signers ->
      about_offer (fun o -> signers_at_least_three (offer_signers o)) s
  | All_four_signed -> about_offer (fun o -> signers_all_four (offer_signers o)) s
  | Bitmap_signature_backed ->
      about_offer offer_bitmap_is_signature_backed s
  | No_uncredited_signer -> about_offer offer_has_no_uncredited_signer s

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Offer_pending -> "offered(c)"
  | On_direct_fetch -> "route(c)=fetch_direct"
  | Verified_directly -> "verified_directly(v,c)"
  | Admitted_by_genesis_shortcut -> "admitted_by_genesis_shortcut(v,c)"
  | Verified_indirectly -> "verified_indirectly(v,c)"
  | Round_zero -> "round(c)=0"
  | Canonical_genesis_header -> "header(c) in genesis(committee)"
  | Wire_claims_genesis_state -> "wire_state(c)=Genesis"
  | Credits_quorum -> "|signed_authorities(c)|=quorum"
  | Three_distinct_signers -> "exists 3 distinct signers of digest(c)"
  | All_four_signed -> "all 4 signed digest(c)"
  | Bitmap_signature_backed -> "signed_authorities(c) subset_of signers(c)"
  | No_uncredited_signer -> "signers(c) subset_of signed_authorities(c)"

(** The CTLK checker over this family's ordered state and view: the presheaf-
    topos denotation, pinned to agree with {!System} at every reachable world by
    test/t_cert_bitmap_quorum_topos.ml.

    This family's reachability relation is a POSET: the offer life
    [No_offer -> Pending -> Settled] is a three-layer DAG and nothing undoes
    itself, so {!Frame.certify_functorial} certifies antisymmetry. That
    classification is pinned by the [poset] group of the topos gate. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state, mutation-
    parameterized transitions, the one-agent view, the atom valuation. *)
let spec_of mut = { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
