(** Finite interpreted system for the VERIF_PROV family: the provenance of a
    certificate's verification MARK on telcoin-network's catch-up
    certificate-FETCH ingress, versus the provenance of the cryptographic
    EVIDENCE that mark is supposed to stand for. File citations refer to
    Telcoin-Association/telcoin-network at HEAD 0c59c15b.

    The modeled mechanism. A catching-up validator V1 fetches a two-certificate
    response {C at round 1, D at round 2} in which D's header names digest(C)
    as a parent. The response walks a four-edge pipeline:

    - INGRESS -> FETCHED: the peer's vector is handed to
      [validate_fetched_certificate], which OVERWRITES whatever verification tag
      the peer put on the wire with [Unverified(aggregated_signature)]
      (crates/types/src/primary/certificate.rs:462-471, sole call site
      crates/consensus/primary/src/certificate_fetcher.rs:494-505).
      [aggregated_signature] keeps the signature BYTES for every tag except
      [Genesis] (certificate.rs:329-337), so the reset NEUTRALISES a peer-asserted
      tag rather than rejecting the response - honest tagged traffic still flows.
    - FETCHED -> CLASSIFIED: [classify_certificates_for_verification]
      (cert_validator.rs:272-296) partitions the batch. D is a leaf (nothing
      names digest(D)), so [requires_direct_verification] (:303-312) sends it to
      the real check; C IS named as a parent and round 1 is not a multiple of the
      default 50-round verification interval (crates/config/src/network.rs:250-268),
      so C is stamped [VerifiedIndirectly] at :293 via [mark_verified_indirectly]
      (:314-324) - a pure tag rewrite from the certificate's OWN aggregate bytes,
      with no cryptography whatsoever.
    - CLASSIFIED -> CHECKED: [verify_certificate_chunk] (:327-345) runs D's
      aggregate BLS check inside [spawn_verification_task] (:347-363). Note the
      ORDER at cert_validator.rs:255-261: the classify call at :256-257 strictly
      PRECEDES the [self.verify_certificate_chunk(...).await?] at :260. The mark
      genuinely precedes the evidence; what never precedes the evidence is
      STORAGE, and that is what this family states.
    - CHECKED -> SETTLED: on [Ok], [process_fetched_certificates_in_parallel]
      (:235-243) forwards the collection through [forward_verified_certs]
      (:133-226) to the certificate manager, whose [is_verified] gate
      (cert_manager.rs:85-93, comment "NOTE: this is the only time this is
      checked") admits every member and writes to storage at :121-124 /
      [accept_verified_certificates] :189-220. On [Err] the `?` at :260 discards
      the ENTIRE collection.

    Components of the state: (1) the pipeline [step]; (2) the disposition
    [check] of D's direct chunk; (3) V1's certificate [store]; (4) HIDDEN
    [dep_genuine] - whether a real 2f+1 aggregate signature exists over D's
    header; (5) OBSERVABLE [peer_claim] - whether the response arrived carrying a
    self-asserted verified tag ([VerifiedDirectly] or [Genesis],
    certificate.rs:431-449); (6) HIDDEN [c_endorse] - which committee members
    actually signed C's header.

    SCOPE, stated in every statement's English and load-bearing nowhere else:
    the batch is pinned at rounds 1 and 2 and to the shape "D names C". At those
    rounds the surviving periodic disjunct of [requires_direct_verification]
    (:309-311) is inert - exactly its status in the real code at low rounds - so
    the modelled runs are faithful and the leaf-verification mutation is not
    silently repaired within them. The complementary batch shape merely routes C
    through direct verification and cannot make any statement true.

    MODELLED PREMISE, enforced only on the Ingress fan-out: [dep_genuine]
    implies [c_endorse] <> [No_quorum]. This is the vote-path induction the real
    protocol rests on - each of D's 2f+1 signers blocked on
    [notify_read_parent_certificates] and then enforced distinct parent
    authorities plus quorum stake before signing its vote
    (crates/consensus/primary/src/network/handler.rs:693-738), and with f = 1 at
    least two of them were honest. Certificate::digest() IS the header digest
    (certificate.rs:473-479), so "D's header names digest(C)" content-addresses
    the exact header C carries and the inheritance is sound. The premise is a
    fact about the world, not a code gate: it is identical in all four models and
    is only ever consulted on the [dep_genuine] = true branch, while every
    mutation works by admitting [dep_genuine] = false batches, so it rigs nothing.

    CONSERVATIVE OMISSION, declared: the [signed_by] weight >= quorum_threshold
    test (certificate.rs:243-246) counts bits of the peer-supplied,
    unauthenticated [signed_authorities] RoaringBitmap (certificate.rs:27-38,
    :349-354), so it is modelled as always satisfied by the adversary. The
    omission strictly favours the attacker and therefore cannot make a safety
    statement true.

    Role mapping (knowledge agents must be validators with a real, non-constant
    view; a blank-view party may never appear under K):
    - V1 is the SOLE knowledge agent: the catching-up node running
      certificate_fetcher.rs:386-441 and cert_validator.rs:235-268. Its view is
      its own pipeline position, the chunk outcome AS IT APPEARS TO IT, its own
      certificate store, and the peer-supplied tag it received.
    - V0, V2 and V3 are the other committee members whose BLS signatures
      constitute the quorums over C's header. They are idle non-agents with the
      constant [View_idle] and NEVER appear under K.
    - The serving peer is a phantom, not a {!Validator.t}.

    What V1 does NOT see. (a) [dep_genuine]: it is inferable ONLY through the
    observable chunk outcome, which is the whole point - [Ck_pass_real] implies
    it, [Ck_fail] refutes it, and [Ck_pass_tag] / [Ck_none] say nothing, which is
    why the mutations destroy the knowledge. (b) [c_endorse]: this NEVER enters
    any view under any mutation, because V1 runs no cryptography on C at all
    (cert_validator.rs:288-294 routes C straight past [validate_and_verify]) and
    C's [signed_authorities] bitmap is peer-rewritable without disturbing
    digest(C). Crucially [Ck_pass_real] and [Ck_pass_tag] collapse to the SAME
    observable [Obs_pass]: a node cannot tell a genuine aggregate verification
    from a short-circuit on a peer-supplied tag, because [verify_signature]
    returns [Ok(())] in both cases (certificate.rs:269-292, short-circuit arm
    :271-274). Declining to hand V1 that distinction is what keeps the knowledge
    statement honest. *)

(** Where the fetched response sits in V1's ingress pipeline. *)
type step =
  | Ingress
      (** the fetch request is outstanding and no response has arrived
          (certificate_fetcher.rs:412-421) *)
  | Fetched
      (** [validate_fetched_certificate] has been applied to every member, so
          the peer's tag is gone (certificate.rs:462-471 via
          certificate_fetcher.rs:494-505) *)
  | Classified
      (** [classify_certificates_for_verification] has stamped C
          [VerifiedIndirectly] and queued D for direct verification
          (cert_validator.rs:272-296) *)
  | Checked
      (** [verify_certificate_chunk] has run to completion or to its first error
          (cert_validator.rs:327-345) *)
  | Settled
      (** the certificate manager has run: [is_verified] gate and the storage
          write (cert_manager.rs:85-124, :189-220) *)

(** Total order index for {!step}. *)
let step_index = function
  | Ingress -> 0
  | Fetched -> 1
  | Classified -> 2
  | Checked -> 3
  | Settled -> 4

(** Total order on {!step}. *)
let step_compare a b = Int.compare (step_index a) (step_index b)

(** [true] iff C already carries the [VerifiedIndirectly] tag, i.e. classify has
    run (cert_validator.rs:293, :314-324). *)
let step_marked_indirect = function
  | Ingress -> false
  | Fetched -> false
  | Classified -> true
  | Checked -> true
  | Settled -> true

(** The disposition of the batch's direct-verification chunk. *)
type check =
  | Ck_none
      (** the chunk has not run yet, or ran empty because nothing was routed to
          direct verification (cert_validator.rs:327-334 over an empty vector) *)
  | Ck_pass_real
      (** the aggregate BLS signature was checked against the committee keys and
          PASSED (certificate.rs:281-291) *)
  | Ck_pass_tag
      (** [verify_signature] short-circuited on a surviving peer-supplied tag and
          returned [Ok(())] without touching a pairing (certificate.rs:271-274);
          reachable only under {!No_wire_tag_reset} *)
  | Ck_fail
      (** the aggregate verification ran and FAILED
          (certificate.rs:284-286, [CertificateError::InvalidSignature]) *)

(** Total order index for {!check}. *)
let check_index = function
  | Ck_none -> 0
  | Ck_pass_real -> 1
  | Ck_pass_tag -> 2
  | Ck_fail -> 3

(** Total order on {!check}. *)
let check_compare a b = Int.compare (check_index a) (check_index b)

(** [true] iff D's aggregate signature was actually verified against committee
    keys and passed - real cryptographic evidence, not a tag. *)
let check_is_real_pass = function
  | Ck_none -> false
  | Ck_pass_real -> true
  | Ck_pass_tag -> false
  | Ck_fail -> false

(** [true] iff D's aggregate verification ran and failed. *)
let check_is_fail = function
  | Ck_none -> false
  | Ck_pass_real -> false
  | Ck_pass_tag -> false
  | Ck_fail -> true

(** What V1's certificate store holds once the certificate manager has run. *)
type store =
  | St_empty  (** nothing from this response was written *)
  | St_c
      (** only the pre-stamped parent C was written: [is_verified] admits
          [VerifiedIndirectly] (certificate.rs:356-364) while the still
          [Unverified] leaf D is rejected at cert_manager.rs:90-93 *)
  | St_cd  (** the whole response was written (cert_manager.rs:189-196) *)

(** Total order index for {!store}. *)
let store_index = function St_empty -> 0 | St_c -> 1 | St_cd -> 2

(** Total order on {!store}. *)
let store_compare a b = Int.compare (store_index a) (store_index b)

(** [true] iff the parent C is in V1's certificate store. *)
let store_has_c = function St_empty -> false | St_c -> true | St_cd -> true

(** [true] iff the dependent D is in V1's certificate store. *)
let store_has_d = function St_empty -> false | St_c -> false | St_cd -> true

(** Which committee members actually signed C's header. V1 is a member of ALL
    THREE values, so "did I myself vote on C's header" is constant across the
    class and leaks nothing about the hidden third signer - without that repair
    the knowledge operand would be knower-local and R1 would be violated. *)
type endorse =
  | No_quorum  (** {V0,V1} only - two of four, below the 2f+1 threshold *)
  | Q_v2  (** {V0,V1,V2} - a genuine quorum whose third signer is V2 *)
  | Q_v3  (** {V0,V1,V3} - a genuine quorum whose third signer is V3 *)

(** Total order index for {!endorse}. *)
let endorse_index = function No_quorum -> 0 | Q_v2 -> 1 | Q_v3 -> 2

(** Total order on {!endorse}. *)
let endorse_compare a b = Int.compare (endorse_index a) (endorse_index b)

(** [true] iff 2f+1 distinct committee members signed C's header. *)
let endorse_is_quorum = function
  | No_quorum -> false
  | Q_v2 -> true
  | Q_v3 -> true

(** [true] iff the hidden third signer of C's header was V3 rather than V2. *)
let endorse_third_is_v3 = function
  | No_quorum -> false
  | Q_v2 -> false
  | Q_v3 -> true

(** The joint global state of one catch-up fetch. *)
type state = {
  step : step;  (** where the response sits in V1's ingress pipeline *)
  check : check;  (** the disposition of D's direct-verification chunk *)
  store : store;  (** what V1's certificate store holds *)
  dep_genuine : bool;
      (** HIDDEN: a real 2f+1 aggregate signature exists over D's header *)
  peer_claim : bool;
      (** OBSERVABLE: the response arrived carrying a self-asserted verified tag *)
  c_endorse : endorse;  (** HIDDEN: who really signed C's header *)
}

(** Total deterministic comparison over ALL state fields, in declaration order. *)
let state_compare s1 s2 =
  let c = step_compare s1.step s2.step in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = check_compare s1.check s2.check in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = store_compare s1.store s2.store in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare s1.dep_genuine s2.dep_genuine in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.peer_claim s2.peer_claim in
          if Bool.not (Int.equal c4 0) then c4
          else endorse_compare s1.c_endorse s2.c_endorse

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** The chunk outcome AS V1 OBSERVES IT. A node cannot tell a genuine aggregate
    verification from a short-circuit on a peer-supplied tag: [verify_signature]
    returns [Ok(())] in both cases (certificate.rs:269-292), so [Ck_pass_real]
    and [Ck_pass_tag] must collapse to one observable. *)
type obs_check =
  | Obs_no_verification
      (** no direct check has run yet, or the chunk was empty *)
  | Obs_pass  (** the chunk returned [Ok] - real pass and tag pass are one *)
  | Obs_fail  (** the chunk returned [Err] *)

(** Total order index for {!obs_check}. *)
let obs_check_index = function
  | Obs_no_verification -> 0
  | Obs_pass -> 1
  | Obs_fail -> 2

(** Total order on {!obs_check}. *)
let obs_check_compare a b = Int.compare (obs_check_index a) (obs_check_index b)

(** The observable projection of a chunk disposition: the two [Ok] dispositions
    are indistinguishable to V1. *)
let obs_of_check = function
  | Ck_none -> Obs_no_verification
  | Ck_pass_real -> Obs_pass
  | Ck_pass_tag -> Obs_pass
  | Ck_fail -> Obs_fail

(** A validator's local view. *)
type view =
  | View_fetcher of step * obs_check * store * bool
      (** V1: its own pipeline step, the chunk outcome as it appears to it, its
          own certificate store, and the peer-supplied verification tag it
          received. It does NOT contain [dep_genuine] and does NOT contain
          [c_endorse]. Including the peer tag is the conservative choice - V1
          did read those bytes, and it makes V1's knowledge stronger and every
          statement harder. *)
  | View_idle  (** the constant blank view of the non-agents V0, V2, V3 *)

(** Total deterministic order over ALL fields of V1's view. *)
let view_fetcher_compare (sa, oa, ra, ta) (sb, ob, rb, tb) =
  let c = step_compare sa sb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = obs_check_compare oa ob in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = store_compare ra rb in
      if Bool.not (Int.equal c2 0) then c2 else Bool.compare ta tb

(** Total order on views: [View_idle] < [View_fetcher], with the field-wise
    order within the fetcher constructor. Every constructor is spelled: no
    wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_fetcher _ -> -1
  | View_fetcher _, View_idle -> 1
  | View_fetcher (sa, oa, ra, ta), View_fetcher (sb, ob, rb, tb) ->
      view_fetcher_compare (sa, oa, ra, ta) (sb, ob, rb, tb)

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 is the sole knowledge agent (the catching-up fetcher);
    V0, V2 and V3 are the idle non-agents whose signatures constitute the
    quorums, and they never appear under K. *)
let view v s =
  match v with
  | Validator.V1 ->
      View_fetcher (s.step, obs_of_check s.check, s.store, s.peer_claim)
  | Validator.V0 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 -> View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | No_wire_tag_reset
      (** delete the ingress tag reset - the
          [set_signature_verification_state(Unverified(aggregated_signature()?))]
          assignment inside [validate_fetched_certificate]
          (certificate.rs:465-469), whose sole call site is
          certificate_fetcher.rs:494-505 - AND its twin inside
          [Certificate::validate_received] (certificate.rs:295-301), so the
          gossip ingress cannot be claimed as a repair. A peer-asserted
          [VerifiedDirectly] tag then survives into [verify_signature], which
          returns [Ok(())] at certificate.rs:271-274 before touching a pairing.
          ADDS Classified([dep_genuine] = false, [peer_claim] = true) ->
          Checked([Ck_pass_tag]) -> Settled([St_cd]) and REMOVES the
          corresponding [Ck_fail] -> [St_empty] rejection: a forged batch with a
          garbage aggregate is stored in full. NO SIBLING REPAIRS IT: the
          [signed_by] weight test (certificate.rs:243-246) counts bits of the
          peer-supplied bitmap (:27-38) so a forger sets it quorate;
          [Header::validate] (header.rs:100-132) checks epoch, parent count,
          author membership and worker ids but no signature; cert_manager's
          [is_verified] (cert_manager.rs:90-93) is exactly what
          [VerifiedDirectly] satisfies (certificate.rs:356-364); the genesis
          short-circuit (certificate.rs:235-238) needs round 0 and the modelled
          rounds are 1 and 2; [append_certificate]
          (aggregators/certificates.rs:24-90) weighs and de-equivocates but
          never verifies; and nothing downstream of the certificate store ever
          re-verifies a stored certificate. *)
  | No_leaf_direct_verification
      (** delete the [!all_parents.contains(&cert.digest())] disjunct at
          cert_validator.rs:308 inside [requires_direct_verification]
          (:303-312) - the clause that forces the batch's source certificate,
          the one no other member names as a parent, through the real aggregate
          check. [classify_certificates_for_verification] (:287-295) then stamps
          BOTH C and D [VerifiedIndirectly] and returns an empty
          direct_verification vector, so [verify_certificate_chunk] (:327-345)
          returns [Ok(vec![])] without spawning a task. Every Classified ->
          Checked edge carries [Ck_none], the [Ck_pass_real] and [Ck_fail] edges
          vanish, and Checked([Ck_none]) -> Settled([St_cd]) is added: a wholly
          fabricated batch is stored with zero cryptography. NO SIBLING REPAIRS
          IT: the surviving periodic disjunct
          [round.is_multiple_of(certificate_verification_round_interval)]
          (:309-311) is a genuine sibling and IS modelled - its default is 50
          (crates/config/src/network.rs:250-268) and the batch is scoped to
          rounds 1 and 2, exactly where the real code leaves it inert;
          cert_manager's [is_verified] (:90-93) accepts [VerifiedIndirectly] by
          design (certificate.rs:443-445); [get_missing_parents]
          (cert_manager.rs:139-180) only asks whether parent DIGESTS are present
          (:156-166) or are genesis (:144-153), never a signature, and is
          skipped entirely when round <= gc_round + 1 (:108); and
          [accept_verified_certificates] (:189-220) writes straight to storage. *)
  | No_chunk_abort
      (** delete the whole-collection error propagation: the `?` on
          [self.verify_certificate_chunk(certs_for_verification).await?] at
          cert_validator.rs:260, together with the `??` at :336-341 and the
          [validator.validate_and_verify(cert)?] at :356-361 - i.e. the
          discipline that a single failed direct verification discards the
          ENTIRE fetched collection instead of only the offending certificate.
          ADDS Checked([Ck_fail]) -> Settled([St_c]) in place of
          Checked([Ck_fail]) -> Settled([St_empty]): C, already stamped
          [VerifiedIndirectly] at :293 before any cryptography ran, survives
          [verify_collection], flows through [forward_verified_certs] (:133-226)
          into the manager and is written at cert_manager.rs:121-124 / :189-196,
          even though the only certificate ever cryptographically examined
          failed. THE SIBLING IS REAL, PARTIAL, AND MODELLED: cert_manager's
          [if !cert.is_verified()] (:85-93, "NOTE: this is the only time this is
          checked") stops the LEAF D - still [Unverified], since
          [verify_signature] returns at certificate.rs:284-286 before the :288
          assignment - but it does NOT stop C, because [VerifiedIndirectly]
          satisfies [is_verified] (certificate.rs:356-364). That is exactly why
          the mutated store is [St_c] and not [St_cd]. The ordering premise the
          sibling turns on also holds: certificate_fetcher.rs:413-426 hands the
          peer's vector straight to [process_fetched_certificates_in_parallel]
          with no client-side sort, and cert_manager.rs:85-93 iterates that order
          and [return Err]s on the first unverified member, so with the natural
          round-ascending order C is written at :121-124 before D's rejection and
          that write cannot be undone. Remaining candidates rejected:
          [accept_verified_certificates] (:189-220) never re-verifies,
          [get_missing_parents] (:139-180) checks digest presence and genesis
          membership only, and nothing downstream of the store re-verifies. *)

(** Every peer-chosen batch configuration, before the vote-path premise filters
    it: the hidden [dep_genuine], the observable [peer_claim], and the hidden
    [c_endorse]. *)
let all_endorse = [ No_quorum; Q_v2; Q_v3 ]

(** The two truth values, as a list, for the configuration fan-out. *)
let all_bool = [ false; true ]

(** The MODELLED VOTE-PATH PREMISE (handler.rs:693-738): if a real 2f+1
    aggregate signature exists over D's header, then each of those signers had
    already read C out of its own store and enforced distinct-authority quorum
    stake over C's header digest, so C really was endorsed by a quorum. Consulted
    ONLY on the [dep_genuine] = true branch and identical in all four models. *)
let config_admissible dep_genuine c_endorse =
  Bool.not dep_genuine || endorse_is_quorum c_endorse

(** The ten batch configurations the serving peer may produce: four with
    [dep_genuine] = true (the premise forces a genuine quorum on C) and six with
    [dep_genuine] = false (C's endorsement is then unconstrained). *)
let peer_configs =
  List.filter
    (fun (dep_genuine, _peer_claim, c_endorse) ->
      config_admissible dep_genuine c_endorse)
    (List.concat_map
       (fun dep_genuine ->
         List.concat_map
           (fun peer_claim ->
             List.map
               (fun c_endorse -> (dep_genuine, peer_claim, c_endorse))
               all_endorse)
           all_bool)
       all_bool)

(** The chunk disposition produced by the Classified -> Checked edge under a
    mutation. Pristine, the real aggregate check decides:
    [dep_genuine] gives [Ck_pass_real], otherwise [Ck_fail]. *)
let outcome_of mut s =
  match mut with
  | Pristine -> if s.dep_genuine then Ck_pass_real else Ck_fail
  | No_chunk_abort -> if s.dep_genuine then Ck_pass_real else Ck_fail
  | No_wire_tag_reset ->
      if s.peer_claim then Ck_pass_tag
      else if s.dep_genuine then Ck_pass_real
      else Ck_fail
  | No_leaf_direct_verification -> Ck_none

(** The store contents produced by the Checked -> Settled edge under a mutation.
    Every [Ok] disposition passes cert_manager's [is_verified] gate for BOTH
    members and stores the whole response; a failure stores nothing, unless
    {!No_chunk_abort} has deleted the collection-wide abort, in which case the
    pre-stamped parent C alone slips through. *)
let settle_of mut c =
  match c with
  | Ck_pass_real -> St_cd
  | Ck_pass_tag -> St_cd
  | Ck_none -> St_cd
  | Ck_fail -> (
      match mut with
      | Pristine -> St_empty
      | No_wire_tag_reset -> St_empty
      | No_leaf_direct_verification -> St_empty
      | No_chunk_abort -> St_c)

(** The transition relation under a mutation. The batch configuration is chosen
    once, on the Ingress -> Fetched edge, and never changes afterwards; the
    [check] field is CARRIED FORWARD unchanged into Settled, which is what makes
    the storage weak-until meaningful (at every stored state the evidence label
    is still readable). [Settled] is terminal and stutter-closed by the kernel. *)
let next_with mut s =
  match s.step with
  | Ingress ->
      List.map
        (fun (dep_genuine, peer_claim, c_endorse) ->
          { s with step = Fetched; dep_genuine; peer_claim; c_endorse })
        peer_configs
  | Fetched -> [ { s with step = Classified } ]
  | Classified -> [ { s with step = Checked; check = outcome_of mut s } ]
  | Checked -> [ { s with step = Settled; store = settle_of mut s.check } ]
  | Settled -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: the fetch request is outstanding and no response has
    arrived, so the batch fields hold the canonical "nothing claimed, nothing
    endorsed" placeholders. No statement's antecedent is satisfied here and no K
    is ever evaluated here, so the placeholders are never load-bearing; [Ingress]
    also has a view class of its own, which cannot pollute any other class
    because [step] is in the view. *)
let initial =
  {
    step = Ingress;
    check = Ck_none;
    store = St_empty;
    dep_genuine = false;
    peer_claim = false;
    c_endorse = No_quorum;
  }

(** The atom vocabulary the three VERIF_PROV statements quantify over. *)
type atom =
  | Stored_c
      (** C is in V1's certificate store; the write is cert_manager.rs:189-196 *)
  | Stored_d  (** D is in V1's certificate store *)
  | Marked_indirect_c
      (** C's local verification-state tag is [VerifiedIndirectly]
          (cert_validator.rs:293, :314-324) *)
  | Dep_crypto_verified
      (** the aggregate BLS signature of D - the certificate naming digest(C) as
          a parent - was verified against the committee keys and PASSED
          (certificate.rs:281-291) *)
  | Dep_crypto_failed
      (** that same aggregate verification ran and FAILED
          (certificate.rs:284-286) *)
  | C_endorsed
      (** HIDDEN: 2f+1 distinct committee members signed C's header; the K
          operand *)
  | C_signed_by_v3
      (** HIDDEN: the third signer of C's header was V3 rather than V2; the
          anonymity operand that witnesses the non-singleton view class *)
  | Peer_claims_verified
      (** OBSERVABLE: the fetch response carried a self-asserted verified tag,
          [VerifiedDirectly] or [Genesis] (certificate.rs:431-449) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Stored_c -> store_has_c s.store
  | Stored_d -> store_has_d s.store
  | Marked_indirect_c -> step_marked_indirect s.step
  | Dep_crypto_verified -> check_is_real_pass s.check
  | Dep_crypto_failed -> check_is_fail s.check
  | C_endorsed -> endorse_is_quorum s.c_endorse
  | C_signed_by_v3 -> endorse_third_is_v3 s.c_endorse
  | Peer_claims_verified -> s.peer_claim

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Stored_c -> "stored(C)"
  | Stored_d -> "stored(D)"
  | Marked_indirect_c -> "marked_indirectly(C)"
  | Dep_crypto_verified -> "dep_aggregate_verified(D)"
  | Dep_crypto_failed -> "dep_aggregate_failed(D)"
  | C_endorsed -> "endorsed_by_quorum(C)"
  | C_signed_by_v3 -> "signed_by(V3,C)"
  | Peer_claims_verified -> "peer_claims_verified"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: single initial state, mutation-
    parameterized transitions, the single-agent view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
