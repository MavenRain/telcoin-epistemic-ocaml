(** Finite interpreted system for the FETCH_VERIF_STATE family: the
    ROUND-STRUCTURED verification plan that telcoin-network's bulk certificate
    fetch computes for one fetched chain, and the wire-carried
    [SignatureVerificationState] that plan is written into. File citations refer
    to Telcoin-Association/telcoin-network at HEAD 0c59c15b, working tree as
    read.

    THE MODELLED MECHANISM. A catching-up validator V1 fetches one response and
    hands it to [StateSynchronizer::process_fetched_certificates_in_parallel]
    (crates/consensus/primary/src/state_sync/cert_validator.rs:235-243). The
    response walks five positions:

    - INGRESS -> FETCHED. Every member is mapped through
      [validate_fetched_certificate]
      (crates/types/src/primary/certificate.rs:462-471) at
      crates/consensus/primary/src/certificate_fetcher.rs:494-505 - the sole
      call site in the tree - which OVERWRITES the peer's wire-claimed
      verification tag with [Unverified(aggregated_signature()?)].
      [aggregated_signature] keeps the signature BYTES for every tag except
      [Genesis] (certificate.rs:329-337), so the reset NEUTRALISES a
      peer-asserted tag; it does not reject the response.
    - FETCHED -> CLASSIFIED. [classify_certificates_for_verification]
      (cert_validator.rs:272-296) collects [all_parents] over the batch and
      splits it with [requires_direct_verification] (:303-312):
      [!all_parents.contains(&cert.digest()) || cert.header().round()
      .is_multiple_of(certificate_verification_round_interval)]. Everything not
      selected is stamped [VerifiedIndirectly] at :293 by
      [mark_verified_indirectly] (:314-324) - a pure tag rewrite off the
      certificate's own aggregate bytes, with no cryptography at all.
    - CLASSIFIED -> CHECKED. [verify_certificate_chunk] (:327-345) chunks the
      selected certificates ([certificate_verification_chunk_size], default 50,
      crates/config/src/network.rs:251-254, :268) and awaits each task; the
      double [??] at :338-341 propagates both the join error and the inner
      verification error. Inside a chunk, [spawn_verification_task] (:348-363)
      runs [for (_idx, cert) in certs.iter_mut() { validator
      .validate_and_verify(cert)? }], so the FIRST failure ends the chunk and
      the later members of that chunk are never examined at all.
      [validate_and_verify] (:114-130) delegates to
      [Certificate::validate_and_verify] (certificate.rs:225-251), whose
      cryptography is [verify_signature] (:269-292).
    - CHECKED -> SETTLED. On [Ok], [verify_collection] (:246-268) writes the
      verified clones back into their original vector slots (:262-265) and
      returns the WHOLE vector; [forward_verified_certs] (:133-226) hands it to
      the certificate manager, which loops member by member and gates each on
      [if !cert.is_verified()] (cert_manager.rs:88-93, "NOTE: this is the only
      time this is checked"), writing accepted members at :121-124 /
      [accept_verified_certificates] :189-196. On [Err] the [?] at :260 discards
      the entire response before any write.

    THE BATCH SHAPE, and why it is the interesting one. The modelled response is
    a four-certificate chain at rounds 49, 50, 51, 52 - C50 names digest(C49),
    C51 names digest(C50), C52 names digest(C51) - fetched with the DEFAULT
    interval [certificate_verification_round_interval = 50]
    (crates/config/src/network.rs:250, :267). No constant is rescaled: the
    chain simply straddles one multiple of the real default. Then
    [all_parents] = {d49, d50, d51} and [requires_direct_verification] selects

    - C52 (round 52): a leaf, nothing in the batch names it   -> DIRECT
    - C51 (round 51): a parent, 51 is not a multiple of 50    -> INDIRECT
    - C50 (round 50): a parent, but 50 IS a multiple of 50    -> DIRECT
    - C49 (round 49): a parent, 49 is not a multiple of 50    -> INDIRECT

    so the chunk handed to [spawn_verification_task] is exactly [C50; C52] in
    ascending index order. This family is about that second, PERIODIC anchor and
    about the intra-chunk order it creates; the covered {!Verif_prov_model}
    family deliberately scopes its batch to rounds 1 and 2, where the periodic
    disjunct at :309-311 is inert, and states so in its own header.

    COMPONENTS OF THE STATE. (1) the pipeline [stage]; (2) HIDDEN [forgery] -
    which member's aggregate is not a real 2f+1 BLS aggregate over its header;
    (3) OBSERVABLE [peer_tag] - whether the response arrived carrying a
    self-asserted [VerifiedDirectly] tag (certificate.rs:431-449); (4) [cls] -
    the verification plan classify computed; (5) [chk] - the chunk disposition;
    (6) [store] - what the certificate manager actually wrote.

    ROLE MAPPING. The modelled committee is the four-member roster {V0, V1, V2,
    V3} with f = 1 and quorum 2f+1 = 3, the module-local convention the isolated
    family models use (lib/validator.mli).
    - V1 is the SOLE knowledge agent: the catching-up node running
      certificate_fetcher.rs:386-441 and cert_validator.rs:235-268. Its view is
      its own pipeline position, the verification plan it computed, the chunk
      outcome AS IT APPEARS TO IT, its own store, and the tag bytes it received.
    - V0, V2, V3 are the other committee members whose BLS signatures do or do
      not constitute the aggregates over the chain's headers. V4..V9 are outside
      the modelled committee. All of them are idle non-agents with the constant
      blank [View_idle] and NEVER appear under K.
    - The serving peer is a phantom, not a {!Validator.t}.

    WHAT V1 DOES NOT SEE. (a) [forgery]: whether a given member's aggregate is
    real is learned ONLY by running the aggregate check on that member, which
    happens for C50 and C52 and never for C49 and C51 - that asymmetry is the
    whole epistemic content of this family. (b) The difference between a real
    aggregate pass and a short-circuit on a surviving wire tag: [verify_signature]
    returns [Ok(())] in both cases (certificate.rs:271-274 vs :281-291), so
    [Chk_real_pass] and [Chk_tag_pass] collapse to one observable [Obs_pass].
    V1 DOES see which member failed, which is the conservative choice: it
    strengthens V1 and makes every ignorance conjunct harder.

    DECLARED SCOPE AND CONSERVATIVE OMISSIONS - each one either favours the
    attacker or cannot make a stated conjunct true.
    - Vector order. The responder streams certificates in ascending round order
      (a [BinaryHeap<Reverse<(Round, AuthorityIdentifier)>>],
      cert_collector.rs:33-36 and :136-150), and the requester collects them in
      stream order (certificate_fetcher.rs:488-512), so the certificate manager
      loops C49, C50, C51, C52. A reordering peer can only change WHICH prefix
      of a partially-accepted response is written, never restore atomicity, and
      the pristine abort path writes nothing under any order.
    - Missing parents. The modelled fetch fills a gap immediately above V1's
      tip, so C49's own parents are already in storage and
      [get_missing_parents] (cert_manager.rs:139-180) returns empty. The
      alternative - C49 parked by [insert_pending] (:110-117) - only DEFERS the
      write: the unlock path at :121-124 accepts the parked certificate with no
      re-verification, so it is not a repair.
    - The [Inquorate] test. [signed_by] (certificate.rs:177-199) counts bits of
      the peer-supplied, unauthenticated [signed_authorities] RoaringBitmap
      (:27-38, :349-354) and [validate_and_verify] ensures [weight >= threshold]
      at :243-246. A forger sets the bitmap quorate for free, so the test is
      modelled as always satisfied. The omission strictly favours the attacker.
    - [forward_verified_certs]'s [TooNew] rejection (cert_validator.rs:193-214)
      and the [self.header.validate(committee)?] call inside
      [Certificate::validate_and_verify] (certificate.rs:241) can only reject
      MORE; omitting them cannot make a safety conjunct true.
    - The vote-path induction. A genuine aggregate over C52's header proves its
      2f+1 signers each blocked on [notify_read_parent_certificates] and
      enforced distinct parent authorities plus quorum stake before signing
      (network/handler.rs:688-738). That establishes those signers HELD C51 - it
      does NOT establish that C51's own aggregate is real, because on this very
      route a certificate is accepted on an indirect stamp
      (cert_validator.rs:314-324 with cert_manager.rs:88-93) and is never
      re-examined afterwards. The model therefore does not let the leaf's check
      leak anything about C51, and that is the faithful reading, not an
      omission: it is precisely the residual the periodic anchor exists to
      bound. *)

(** Where the fetched response sits in V1's ingress pipeline. *)
type stage =
  | Ingress
      (** the fetch request is outstanding and no response has arrived
          (certificate_fetcher.rs:412-421) *)
  | Fetched
      (** the response arrived and every member went through
          [validate_fetched_certificate] (certificate.rs:462-471 via
          certificate_fetcher.rs:494-505) *)
  | Classified
      (** [classify_certificates_for_verification] (cert_validator.rs:272-296)
          has stamped the unselected members [VerifiedIndirectly] and built the
          direct-verification vector *)
  | Checked
      (** [verify_certificate_chunk] (cert_validator.rs:327-345) has run to
          completion or to its first error *)
  | Settled
      (** the certificate manager has looped the response: the [is_verified]
          gate at cert_manager.rs:88-93 and the writes at :121-124 / :189-196 *)

(** Total order index for {!stage}. *)
let stage_index = function
  | Ingress -> 0
  | Fetched -> 1
  | Classified -> 2
  | Checked -> 3
  | Settled -> 4

(** Total order on {!stage}. *)
let stage_compare a b = Int.compare (stage_index a) (stage_index b)

(** Which member of the fetched chain carries an aggregate that is NOT a real
    2f+1 BLS aggregate over its own header. This is the adversary's choice, made
    once when the response is served, and it is HIDDEN from every view: an
    aggregate's authenticity is learned only by running the check on it. C49 is
    never given a forgery of its own - it is the member whose fate is decided
    entirely by the others, which is exactly what the partial-acceptance
    statement is about. *)
type forgery =
  | Fg_none  (** all four aggregates are genuine *)
  | Fg_anchor
      (** the round-50 anchor C50 carries garbage aggregate bytes; the other
          three are genuine *)
  | Fg_link
      (** the round-51 member C51 carries garbage aggregate bytes; C50 and C52
          are genuine. C51 is stamped [VerifiedIndirectly] and never checked, so
          this choice is invisible to V1 on the pristine route *)
  | Fg_leaf
      (** the round-52 leaf C52 carries garbage aggregate bytes; C50 and C51 are
          genuine *)
  | Fg_anchor_and_link
      (** both C50 and C51 carry garbage; the maximal forgery the modelled
          adversary can hide behind a genuine leaf *)

(** Total order index for {!forgery}. *)
let forgery_index = function
  | Fg_none -> 0
  | Fg_anchor -> 1
  | Fg_link -> 2
  | Fg_leaf -> 3
  | Fg_anchor_and_link -> 4

(** Total order on {!forgery}. *)
let forgery_compare a b = Int.compare (forgery_index a) (forgery_index b)

(** The adversary's whole choice set, fanned out at the [Ingress] edge. *)
let all_forgeries = [ Fg_none; Fg_anchor; Fg_link; Fg_leaf; Fg_anchor_and_link ]

(** [true] iff a real 2f+1 aggregate over C50's header exists, i.e. three of the
    four committee members actually signed it. With f = 1 that forces at least
    f+1 = 2 HONEST signers, which is the operand of the family's positive K. *)
let forgery_anchor_genuine = function
  | Fg_none -> true
  | Fg_anchor -> false
  | Fg_link -> true
  | Fg_leaf -> true
  | Fg_anchor_and_link -> false

(** [true] iff a real 2f+1 aggregate over C51's header exists. *)
let forgery_link_genuine = function
  | Fg_none -> true
  | Fg_anchor -> true
  | Fg_link -> false
  | Fg_leaf -> true
  | Fg_anchor_and_link -> false

(** [true] iff a real 2f+1 aggregate over C52's header exists. *)
let forgery_leaf_genuine = function
  | Fg_none -> true
  | Fg_anchor -> true
  | Fg_link -> true
  | Fg_leaf -> false
  | Fg_anchor_and_link -> true

(** The verification plan [classify_certificates_for_verification] computed for
    this chain (cert_validator.rs:272-296). *)
type cls =
  | Cl_unclassified  (** classify has not run yet *)
  | Cl_anchor_direct
      (** [requires_direct_verification] (:303-312) selected BOTH the leaf C52
          (the [!all_parents.contains] disjunct at :308) and the round-50 anchor
          C50 (the [is_multiple_of] disjunct at :309-311); C49 and C51 were
          stamped [VerifiedIndirectly] at :293 *)
  | Cl_leaf_only
      (** only the leaf C52 was selected; C49, C50 and C51 were all stamped
          [VerifiedIndirectly]. Reachable only under {!No_periodic_anchor} *)

(** Total order index for {!cls}. *)
let cls_index = function
  | Cl_unclassified -> 0
  | Cl_anchor_direct -> 1
  | Cl_leaf_only -> 2

(** Total order on {!cls}. *)
let cls_compare a b = Int.compare (cls_index a) (cls_index b)

(** [true] iff the round-50 anchor C50 carries the [VerifiedIndirectly] stamp,
    i.e. it was admitted on digest linkage alone with no aggregate check of its
    own. *)
let cls_anchor_is_indirect = function
  | Cl_unclassified -> false
  | Cl_anchor_direct -> false
  | Cl_leaf_only -> true

(** [true] iff the round-51 member C51 carries the [VerifiedIndirectly] stamp.
    Both realised plans stamp it, because 51 is a multiple of nothing and C52
    names digest(C51). *)
let cls_link_is_indirect = function
  | Cl_unclassified -> false
  | Cl_anchor_direct -> true
  | Cl_leaf_only -> true

(** The disposition of the batch's single direct-verification chunk. The chunk
    is [C50; C52] under {!Cl_anchor_direct} and [C52] under {!Cl_leaf_only};
    both fit in one chunk because the default
    [certificate_verification_chunk_size] is 50
    (crates/config/src/network.rs:251-254, :268). *)
type chk =
  | Chk_pending  (** the chunk has not run *)
  | Chk_real_pass
      (** every selected member's aggregate was verified against the committee
          keys and passed (certificate.rs:281-291) *)
  | Chk_tag_pass
      (** the chunk returned [Ok] because a surviving peer-supplied tag made
          [verify_signature] return before touching a pairing
          (certificate.rs:271-274); reachable only under
          {!No_wire_state_reset} *)
  | Chk_anchor_fail
      (** the round-50 anchor's aggregate check ran and FAILED
          (certificate.rs:284-286). It is index 1 of the chunk and the leaf is
          index 3, so the [?] in [for (_idx, cert) in certs.iter_mut() {
          validator.validate_and_verify(cert)? }] (cert_validator.rs:356-361)
          ends the chunk here and the leaf's own aggregate is never examined *)
  | Chk_leaf_fail
      (** every earlier member of the chunk passed and the leaf's own aggregate
          check FAILED *)

(** Total order index for {!chk}. *)
let chk_index = function
  | Chk_pending -> 0
  | Chk_real_pass -> 1
  | Chk_tag_pass -> 2
  | Chk_anchor_fail -> 3
  | Chk_leaf_fail -> 4

(** Total order on {!chk}. *)
let chk_compare a b = Int.compare (chk_index a) (chk_index b)

(** [true] iff the round-50 anchor's own aggregate check ran and failed. *)
let chk_is_anchor_fail = function
  | Chk_pending -> false
  | Chk_real_pass -> false
  | Chk_tag_pass -> false
  | Chk_anchor_fail -> true
  | Chk_leaf_fail -> false

(** [true] iff the leaf C52's own aggregate was actually examined against the
    committee keys - true when the chunk ran to the leaf and either passed or
    failed there, false when an earlier member ended the chunk first and false
    when a wire tag short-circuited every member. *)
let chk_leaf_examined = function
  | Chk_pending -> false
  | Chk_real_pass -> true
  | Chk_tag_pass -> false
  | Chk_anchor_fail -> false
  | Chk_leaf_fail -> true

(** What the certificate manager wrote to V1's store for this response. *)
type store =
  | St_none  (** nothing from the response was written *)
  | St_low_only
      (** only C49 was written. The manager loops in ascending round order and
          C49 carries [VerifiedIndirectly], which satisfies [is_verified]
          (certificate.rs:356-364), so it is accepted at cert_manager.rs:121-124;
          the next member C50 is still [Unverified] and the loop returns
          [UnverifiedSignature] at :90-93 *)
  | St_all  (** the whole response was written (cert_manager.rs:189-196) *)

(** Total order index for {!store}. *)
let store_index = function St_none -> 0 | St_low_only -> 1 | St_all -> 2

(** Total order on {!store}. *)
let store_compare a b = Int.compare (store_index a) (store_index b)

(** [true] iff C49, the lowest member of the chain, is in V1's store. *)
let store_has_low = function
  | St_none -> false
  | St_low_only -> true
  | St_all -> true

(** [true] iff the WHOLE fetched response is in V1's store. *)
let store_is_all = function
  | St_none -> false
  | St_low_only -> false
  | St_all -> true

(** The joint global state of one bulk certificate fetch. *)
type state = {
  stage : stage;  (** where the response sits in V1's ingress pipeline *)
  forgery : forgery;  (** HIDDEN: which member's aggregate is not real *)
  peer_tag : bool;
      (** OBSERVABLE: the response arrived carrying a self-asserted
          [VerifiedDirectly] tag (certificate.rs:442) *)
  cls : cls;  (** the verification plan classify computed *)
  chk : chk;  (** the disposition of the direct-verification chunk *)
  store : store;  (** what the certificate manager wrote *)
}

(** Total deterministic comparison over ALL state fields, in declaration order. *)
let state_compare s1 s2 =
  let c = stage_compare s1.stage s2.stage in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = forgery_compare s1.forgery s2.forgery in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Bool.compare s1.peer_tag s2.peer_tag in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = cls_compare s1.cls s2.cls in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = chk_compare s1.chk s2.chk in
          if Bool.not (Int.equal c4 0) then c4
          else store_compare s1.store s2.store

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** The chunk outcome AS V1 OBSERVES IT. A node cannot tell a genuine aggregate
    verification from a short-circuit on a peer-supplied tag, because
    [verify_signature] returns [Ok(())] in both cases (certificate.rs:271-274
    and :281-291), so the two passes collapse to one observable. The two
    failures are kept apart: that is the conservative choice, it hands V1 more
    information than the [CertificateError::InvalidSignature] value actually
    carries, and it makes every ignorance conjunct harder rather than easier. *)
type obs =
  | Obs_pending  (** no direct-verification chunk has run yet *)
  | Obs_pass  (** the chunk returned [Ok] - real pass and tag pass are one *)
  | Obs_anchor_fail  (** the chunk returned [Err] on the round-50 anchor *)
  | Obs_leaf_fail  (** the chunk returned [Err] on the leaf *)

(** Total order index for {!obs}. *)
let obs_index = function
  | Obs_pending -> 0
  | Obs_pass -> 1
  | Obs_anchor_fail -> 2
  | Obs_leaf_fail -> 3

(** Total order on {!obs}. *)
let obs_compare a b = Int.compare (obs_index a) (obs_index b)

(** The observable projection of a chunk disposition. *)
let obs_of_chk = function
  | Chk_pending -> Obs_pending
  | Chk_real_pass -> Obs_pass
  | Chk_tag_pass -> Obs_pass
  | Chk_anchor_fail -> Obs_anchor_fail
  | Chk_leaf_fail -> Obs_leaf_fail

(** A validator's local view. *)
type view =
  | View_fetcher of stage * cls * obs * store * bool
      (** V1: its own pipeline stage, the verification plan it computed from the
          batch shape and the round interval, the chunk outcome as it appears to
          it, its own store, and the wire tag it received. It does NOT contain
          [forgery], and it does NOT distinguish a real aggregate pass from a
          tag short-circuit. *)
  | View_idle  (** the constant blank view of the non-agents V0, V2..V9 *)

(** Total deterministic order over ALL fields of V1's view. *)
let view_fetcher_compare (sa, la, oa, ra, ta) (sb, lb, ob, rb, tb) =
  let c = stage_compare sa sb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = cls_compare la lb in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = obs_compare oa ob in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = store_compare ra rb in
        if Bool.not (Int.equal c3 0) then c3 else Bool.compare ta tb

(** Total order on views: [View_idle] < [View_fetcher], with the field-wise
    order within the fetcher constructor. Every constructor pair is spelled: no
    wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_fetcher _ -> -1
  | View_fetcher _, View_idle -> 1
  | View_fetcher (sa, la, oa, ra, ta), View_fetcher (sb, lb, ob, rb, tb) ->
      view_fetcher_compare (sa, la, oa, ra, ta) (sb, lb, ob, rb, tb)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 is the SOLE knowledge agent - the catching-up node
    running the fetch pipeline. V0, V2 and V3 are the other members of the
    modelled four-member committee and V4..V9 are outside it; all of them are
    idle non-agents with the constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V1 ->
      View_fetcher (s.stage, s.cls, obs_of_chk s.chk, s.store, s.peer_tag)
  | Validator.V0 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_periodic_anchor
      (** delete the periodic disjunct [|| cert.header().round()
          .is_multiple_of(self.config.network_config().sync_config()
          .certificate_verification_round_interval)] at
          cert_validator.rs:309-311, leaving [requires_direct_verification]
          (:303-312) with only its leaf test at :308. The verification plan
          collapses from [Cl_anchor_direct] to [Cl_leaf_only]: C50 is no longer
          in the chunk, [classify_certificates_for_verification] stamps it
          [VerifiedIndirectly] at :293 instead, and the [Fg_anchor] and
          [Fg_anchor_and_link] responses - which pristine ends at
          [Chk_anchor_fail] / [St_none] - now reach [Chk_real_pass] / [St_all].
          NO SIBLING REPAIRS IT. The surviving leaf disjunct at :308 is a
          genuine partial sibling and IS modelled: it still routes C52 through
          the real check, which is why the family states the ANCHOR SPACING and
          the anchor's OWN aggregate rather than "something was verified".
          Nothing ever re-examines a stored certificate: [verify_signature]
          returns [Ok] forever on [VerifiedIndirectly]
          (certificate.rs:271-274); the one function that does force a re-check,
          [verify_cert] via [validate_received] (certificate.rs:253-266,
          :294-301), has exactly one production caller and it is the GOSSIP
          route (network/handler.rs:246, :252), unreachable from
          [fetch_and_process_certificates] (certificate_fetcher.rs:386-441); the
          vote-supplied-parent reset (network/handler.rs:670-682) is likewise a
          different route; [Certificate::signed_authorities] (certificate.rs:352-354)
          has no non-test caller in the tree, so the stored bitmap is never
          re-read; cert_manager's [is_verified] gate (cert_manager.rs:88-93) is
          exactly what [VerifiedIndirectly] satisfies (certificate.rs:356-364);
          and consensus [check_parents] (consensus/state.rs:187-214) compares
          digests only. *)
  | No_wire_state_reset
      (** delete the [validate_fetched_certificate] map at
          certificate_fetcher.rs:494-505 - i.e. the
          [set_signature_verification_state(Unverified(aggregated_signature()?))]
          assignment of certificate.rs:465-469 - and pass the peer's
          certificates through unchanged. A peer-asserted [VerifiedDirectly] tag
          then survives into [verify_signature], which returns [Ok(())] at
          certificate.rs:271-274 before touching a pairing, so BOTH members of
          the direct chunk are "verified" with no cryptography: ADDS
          Classified(peer_tag = true) -> Checked([Chk_tag_pass]) ->
          Settled([St_all]) for every forgery, and REMOVES the corresponding
          [Chk_anchor_fail] / [Chk_leaf_fail] rejections on that branch.
          NO SIBLING REPAIRS IT. The two other wire-state resets in the tree are
          on different routes and are unreachable from the fetch pipeline: the
          gossip reset [cert.validate_received()] at network/handler.rs:246 (and
          again inside [verify_cert] at certificate.rs:256), and the
          vote-supplied-parent reset at network/handler.rs:670-682. Downstream,
          cert_manager's [is_verified] (cert_manager.rs:88-93) is satisfied by
          [VerifiedDirectly] by construction (certificate.rs:356-364). The only
          residual is the [Inquorate] test (certificate.rs:243-246), which counts
          bits of the peer-supplied bitmap and is modelled as always satisfied. *)
  | No_chunk_abort
      (** delete the error propagation on the chunk result at
          cert_validator.rs:337-343 - the [??] on [task.await.map_err(...)] -
          collecting only the chunks that returned [Ok]. The inner
          [validator.validate_and_verify(cert)?] at :356-361 is NOT deleted, so
          a failing chunk still loses ALL of its members' results, including the
          leaf's. [verify_collection] then writes back nothing for those slots
          (:262-265) and returns the WHOLE vector (:267), so the certificate
          manager receives C49 carrying [VerifiedIndirectly] followed by a still
          [Unverified] C50. REPLACES Checked([Chk_anchor_fail]) ->
          Settled([St_none]) with Checked([Chk_anchor_fail]) ->
          Settled([St_low_only]), and likewise for [Chk_leaf_fail]: the response
          is PARTIALLY accepted and C49 is written on zero cryptography.
          NO SIBLING FULLY REPAIRS IT, AND THE PARTIAL ONE IS MODELLED.
          cert_manager's [if !cert.is_verified()] (cert_manager.rs:88-93) does
          stop the still-[Unverified] C50 and everything after it - that is
          exactly why the mutated store is [St_low_only] and not [St_all] - but
          it cannot stop C49, because [VerifiedIndirectly] satisfies
          [is_verified] (certificate.rs:356-364). The missing-parent check
          (cert_manager.rs:103-118) compares digests only and, when it fires, it
          parks rather than rejects (:110-117), and the unlock path at :121-124
          accepts the parked certificate with no re-verification. Consensus
          [check_parents] (consensus/state.rs:187-214) again compares digests
          only, and nothing re-verifies a stored certificate. *)

(** The verification plan classify computes under a mutation. Only
    {!No_periodic_anchor} touches [requires_direct_verification]. *)
let cls_of = function
  | Pristine -> Cl_anchor_direct
  | No_periodic_anchor -> Cl_leaf_only
  | No_wire_state_reset -> Cl_anchor_direct
  | No_chunk_abort -> Cl_anchor_direct

(** The chunk disposition when the chunk really runs cryptography, as a function
    of the plan and of the adversary's forgery. Members are examined in
    ascending index order (cert_validator.rs:356-361), and the chain's vector
    order is ascending by round, so the anchor is examined before the leaf. *)
let real_chunk_outcome cls forgery =
  match cls with
  | Cl_unclassified -> Chk_pending
  | Cl_anchor_direct ->
      if Bool.not (forgery_anchor_genuine forgery) then Chk_anchor_fail
      else if Bool.not (forgery_leaf_genuine forgery) then Chk_leaf_fail
      else Chk_real_pass
  | Cl_leaf_only ->
      if Bool.not (forgery_leaf_genuine forgery) then Chk_leaf_fail
      else Chk_real_pass

(** The chunk disposition under a mutation. Only {!No_wire_state_reset} can
    replace real cryptography with a tag short-circuit, and it does so exactly
    on the responses that arrived pre-tagged. *)
let chk_of mut s =
  match mut with
  | Pristine -> real_chunk_outcome s.cls s.forgery
  | No_periodic_anchor -> real_chunk_outcome s.cls s.forgery
  | No_chunk_abort -> real_chunk_outcome s.cls s.forgery
  | No_wire_state_reset ->
      if s.peer_tag then Chk_tag_pass else real_chunk_outcome s.cls s.forgery

(** What the certificate manager writes, given the chunk disposition. Only
    {!No_chunk_abort} lets a failed chunk reach the manager at all. *)
let settle_of mut chk =
  match mut with
  | Pristine | No_periodic_anchor | No_wire_state_reset -> (
      match chk with
      | Chk_real_pass -> St_all
      | Chk_tag_pass -> St_all
      | Chk_anchor_fail -> St_none
      | Chk_leaf_fail -> St_none
      | Chk_pending -> St_none)
  | No_chunk_abort -> (
      match chk with
      | Chk_real_pass -> St_all
      | Chk_tag_pass -> St_all
      | Chk_anchor_fail -> St_low_only
      | Chk_leaf_fail -> St_low_only
      | Chk_pending -> St_none)

(** The transition relation: the response walks the five pipeline positions,
    with the adversary's whole choice - which member is forged and whether the
    response arrives pre-tagged - fanned out on the single [Ingress] edge, where
    the peer serves the batch. [Settled] is terminal and stutter-closed by the
    kernel. *)
let next_with mut s =
  match s.stage with
  | Ingress ->
      List.concat_map
        (fun forgery ->
          List.map
            (fun peer_tag ->
              {
                stage = Fetched;
                forgery;
                peer_tag;
                cls = Cl_unclassified;
                chk = Chk_pending;
                store = St_none;
              })
            [ false; true ])
        all_forgeries
  | Fetched -> [ { s with stage = Classified; cls = cls_of mut } ]
  | Classified -> [ { s with stage = Checked; chk = chk_of mut s } ]
  | Checked -> [ { s with stage = Settled; store = settle_of mut s.chk } ]
  | Settled -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: the fetch request is outstanding and no response has
    arrived, so the response fields hold the canonical "nothing served, nothing
    claimed" placeholders. No statement's antecedent holds here and no K is ever
    evaluated here; [Ingress] also has a view class of its own, because [stage]
    is in the view, so the placeholders cannot pollute any other class. *)
let initial =
  {
    stage = Ingress;
    forgery = Fg_none;
    peer_tag = false;
    cls = Cl_unclassified;
    chk = Chk_pending;
    store = St_none;
  }

(** The atom vocabulary the three FETCH_VERIF_STATE statements quantify over. *)
type atom =
  | Batch_accepted
      (** the WHOLE fetched response is in V1's certificate store
          (cert_manager.rs:189-196) *)
  | Low_stored
      (** C49, the lowest member of the chain, is in V1's certificate store -
          true both for a whole response and for a partially accepted one *)
  | Anchor_quorum_genuine
      (** HIDDEN: a real 2f+1 BLS aggregate over C50's header exists, i.e. three
          of the four committee members actually signed it, which with f = 1
          forces at least two HONEST signers. The positive K operand *)
  | Link_quorum_genuine
      (** HIDDEN: the same fact about C51, the member one round above the
          anchor. The ignorance operand *)
  | Anchor_marked_indirect
      (** C50 carries [VerifiedIndirectly] (cert_validator.rs:293, :314-324),
          i.e. it was admitted on digest linkage alone *)
  | Link_marked_indirect  (** C51 carries [VerifiedIndirectly] *)
  | Anchor_check_failed
      (** the round-50 anchor's own aggregate check ran and FAILED
          (certificate.rs:284-286, [CertificateError::InvalidSignature]) *)
  | Leaf_aggregate_examined
      (** the leaf C52's own aggregate was actually put to the committee keys,
          rather than skipped by an earlier failure in its chunk
          (cert_validator.rs:356-361) or by a tag short-circuit
          (certificate.rs:271-274) *)
  | Peer_tagged
      (** OBSERVABLE: the response arrived carrying a self-asserted
          [VerifiedDirectly] tag (certificate.rs:442) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Batch_accepted -> store_is_all s.store
  | Low_stored -> store_has_low s.store
  | Anchor_quorum_genuine -> forgery_anchor_genuine s.forgery
  | Link_quorum_genuine -> forgery_link_genuine s.forgery
  | Anchor_marked_indirect -> cls_anchor_is_indirect s.cls
  | Link_marked_indirect -> cls_link_is_indirect s.cls
  | Anchor_check_failed -> chk_is_anchor_fail s.chk
  | Leaf_aggregate_examined -> chk_leaf_examined s.chk
  | Peer_tagged -> s.peer_tag

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Batch_accepted -> "batch_accepted"
  | Low_stored -> "stored(C49)"
  | Anchor_quorum_genuine -> "genuine_quorum(C50)"
  | Link_quorum_genuine -> "genuine_quorum(C51)"
  | Anchor_marked_indirect -> "marked_indirectly(C50)"
  | Link_marked_indirect -> "marked_indirectly(C51)"
  | Anchor_check_failed -> "aggregate_check_failed(C50)"
  | Leaf_aggregate_examined -> "aggregate_examined(C52)"
  | Peer_tagged -> "peer_claims_verified"

(** The CTLK checker over this family's ordered state and view: the presheaf-
    topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md), pinned
    to agree with {!System} at every reachable world by
    test/t_fetch_verif_state_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: a single initial state, mutation-
    parameterized transitions, the single-agent view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
