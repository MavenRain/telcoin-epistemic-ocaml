(** The PARENT_CLAIM_BINDING statement family, encoded over the
    {!Parent_claim_binding_model} interpreted system: the two-sided binding of
    one missing parent certificate to exactly one proposer on
    telcoin-network's vote path. Every file citation was opened in the
    [0c59c15b] checkout.

    Three statements, four gate deletions:

    - S1 [security] the voter admits a certificate riding along with a vote
      request only from the author its own outstanding-request table names,
      and pays for it in ignorance - pinned by
      {!Parent_claim_binding_model.No_requester_binding};
    - S2 [liveness] the missing digest is claimed first-come by exactly one
      proposer, and the second proposer's evaluation then blocks until storage
      or a deadline - pinned by
      {!Parent_claim_binding_model.No_vacant_claim} (conjunct A) and
      {!Parent_claim_binding_model.No_evaluation_deadline} (conjunct B);
    - S3 [security] the author's dual: it serves only parents its own header
      declares, and tears the request down otherwise - pinned by
      {!Parent_claim_binding_model.No_author_parent_filter}.

    {1 Reading guide for the K operands}

    [V1] is the voter [j] and is the only agent under [K]. Its view
    ([Vj of vphase]) is its own local evaluation state; it contains NO
    component of {!Parent_claim_binding_model.world}.

    - [~K_j(exists(d))] and [~K_j(~exists(d))] (S1 conjunct B, S2 conjunct C).
      The operand "a genuine certificate for [d] exists somewhere in the
      network" is a global possession fact. It is not a projection of [j]'s
      view - [j]'s [requested_parents] table records only WHOM it asked, never
      who HOLDS - and it is not rigid: it is false in [W_none]/[W_bogus] and
      true in [W_b_holds]/[W_c_holds], all four of which reach
      [Ph_b_filtered] with the identical [j]-view. The sharper half is S1
      conjunct B, which is asserted at the moment [j] has PHYSICALLY RECEIVED
      bytes claiming digest [d] and dropped them: that conjunct would be FALSE
      if the model omitted the Byzantine-[b] world [W_bogus], and the code
      justification for keeping it is that the [retain] of handler.rs:936-946
      runs strictly before the [process_peer_certificate] of
      handler.rs:948-951, so the dropped bytes were still
      [SignatureVerificationState::Unverified] (handler.rs:672-682) and prove
      nothing.
    - [K_j(exists(d))] (S1 conjunct C) is the family's only POSITIVE [K]. It
      is not rigid (false at every [W_none] state) and its view class at the
      operative state is not a singleton: [Vj Ph_stored] is shared by
      [(W_b_holds, Ph_stored)] and [(W_c_holds, Ph_stored)], which disagree on
      [holds(b,d)]. test/t_parent_claim_binding.ml discharges both halves.

    No [K (V2, _)] is asserted: nothing in the author scenario is hidden from
    the author. *)

open Parent_claim_binding_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a false antecedent. Each antecedent below is chosen to
          stay REACHABLE under the mutation that pins its statement, so the
          pin is a refutation and never a vacuity artefact. *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** The voter [j]: the family's only knowledge agent. *)
let j = Validator.V1

(** S1 - vote-path-certificate-admission-is-bound-to-the-requested-author
    [security].

    (A) The binding gate. A certificate that rides along with a vote request
    is admitted onto [j]'s vote path only if [j]'s own outstanding-request
    table names THIS header's author for that [(round, digest)] -
    AG( offered(b,d) /\\ bound(j,(r-1,d))=a -> ~admitted(j,d,from=b) ). Gate:
    handler.rs:936-946, whose [retain] keeps a parent only when
    [requested_parents.get(&req)] yields [Some(authority)] with
    [authority == header.author()]; only survivors reach
    [self.state_sync.process_peer_certificate(parent)] at handler.rs:948-951.
    The table is populated ONLY at handler.rs:910-921 and the only route into
    [try_accept_unknown_certs] is the non-empty-parents branch at
    handler.rs:670-686. So a committee member cannot use a vote request as a
    channel for pushing arbitrary certificates into [j]'s pending and
    certificate-fetcher machinery.

    (B) The price, in ignorance. When [j] drops a genuine certificate on this
    rule it learns nothing about whether that certificate exists at all -
    AG( offered(b,d) /\\ ~admitted(j,d,from=b) ->
    ~K_j(exists(d)) /\\ ~K_j(~exists(d)) ). Grounding: the [retain] runs
    BEFORE any verification, and the certificates were set to
    [SignatureVerificationState::Unverified] at handler.rs:672-682, so the
    dropped bytes are equally consistent with a Byzantine [b] forging them
    ([W_bogus]) and an honest [b] holding the real thing ([W_b_holds]). Those
    two states share [Vj Ph_b_offer_dropped] exactly.

    (C) The other side of the same coin: admission through the BOUND route is
    what does teach [j] - AG( stored(j,d) -> K_j(exists(d)) ). Non-degenerate:
    the [Vj Ph_stored] class holds two reachable states ([W_b_holds] and
    [W_c_holds]) and [exists(d)] is false at every [W_none] state.

    Mutation pin: {!Parent_claim_binding_model.No_requester_binding} deletes
    the [authority == header.author()] comparison at handler.rs:940-944,
    adding [Ph_b_filtered -> Ph_b_offer_taken], a state at which
    [offered(b,d)], [bound(j,(r-1,d))=a] and [admitted(j,d,from=b)] all hold -
    conjunct A is refuted. The antecedent [offered /\\ bound=a] is reachable
    under the mutation too (at [Ph_b_offer_taken]), so the flip is a
    refutation and not a vacuity. Sibling hunt: the BLS/quorum check of
    [Certificate::validate_and_verify]
    (types/src/primary/certificate.rs:225-251) does repair forgery and IS
    modeled - [W_bogus] never reaches [Ph_stored] even under the mutation - so
    conjunct C survives; what has no second enforcer, and what the mutation
    genuinely removes, is the BINDING. *)
let s1 =
  let binding_gate =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Offer_seen, atom Bound_a),
           Formula.Not (atom Offer_admitted) ))
  in
  let drop_teaches_nothing =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Offer_seen, Formula.Not (atom Offer_admitted)),
           Formula.And
             ( Formula.Not (Formula.K (j, atom D_exists)),
               Formula.Not (Formula.K (j, Formula.Not (atom D_exists))) ) ))
  in
  let admission_teaches =
    Formula.Ag
      (Formula.Implies (atom Stored, Formula.K (j, atom D_exists)))
  in
  {
    name = "vote-path-certificate-admission-is-bound-to-the-requested-author";
    bucket = Statements.Security;
    formula =
      Formula.And
        (binding_gate, Formula.And (drop_teaches_nothing, admission_teaches));
    antecedent = Formula.And (atom Offer_seen, atom Bound_a);
  }

(** S2 - a-missing-parent-is-claimed-by-exactly-one-proposer [liveness].

    (A) First-come exclusivity. While the [(r-1,d)] slot belongs to author
    [a], no reply [j] emits on the very next step names [d] to anybody else -
    AG( bound(j,(r-1,d))=a -> AX( ~(reply(j,h_b) = MissingParents([d])) ) ).
    Gate: the [Entry::Vacant] claim at handler.rs:910-921, whose
    [else { false }] silently removes the digest from the LATER author's
    missing list; with the list empty, handler.rs:659-669 does not return
    [MissingParents] at all.

    (B) The consequence, as a bounded block. [j]'s evaluation of [h_b] falls
    through to the blocking [notify_read_parent_certificates]
    (handler.rs:688-693, "NOTE: this check is necessary for correctness") and
    stays there until storage or a wall-clock teardown -
    AG( blocked(j,h_b) -> A[ blocked(j,h_b) U (stored(j,d) \\/
    timeout(j,h_b)) ] ). [notify_read] itself
    (storage/src/stores/certificate_store.rs:250-269) is a bare
    [receiver.await] with NO internal timeout, so this conjunct is carried
    entirely by the two wall-clock sites: the [max_header_delay] timeout at
    handler.rs:582-586 and the network layer's [cancel] arm at
    network/mod.rs:1531-1551.

    (C) And throughout that window, [j] cannot tell whether [d] is out there
    at all - AG( blocked(j,h_b) -> ~K_j(exists(d)) /\\ ~K_j(~exists(d)) ). All
    four worlds reach [Ph_b_filtered] with the identical [j]-view.

    Mutation pins. {!Parent_claim_binding_model.No_vacant_claim} replaces the
    [Vacant] guard with an unconditional insert-and-keep, so [b] IS told [d]
    is missing: [Ph_a_hinted]'s successor becomes [Ph_b_hinted] and conjunct A
    is refuted. Its antecedent [bound=a] is still reachable under that
    mutation (at [Ph_a_hinted]), so the flip is a refutation.
    {!Parent_claim_binding_model.No_evaluation_deadline} deletes BOTH
    wall-clock sites at once, leaving [Ph_b_filtered] terminal in [W_none];
    the kernel stutters terminals, so the until of conjunct B is refuted.
    That second pin is what keeps conjunct B from being manufactured
    liveness: it removes real gates, and it removes both of them because
    either alone is repaired by the other (network/mod.rs:1531-1551 drops the
    whole [vote] future on [cancel]).

    Sibling hunt for conjunct A: no second route re-establishes exclusivity -
    [try_accept_unknown_certs] reads the SAME table (so the rebound slot
    hands [b] the admission and starts dropping [a]'s own supply, modeled),
    the pending suppression at pending_cert_manager.rs:171-173 covers only
    locally pending digests, and the certificate fetcher is fired only by a
    processed CERTIFICATE (cert_manager.rs:169-177) or a TooNew one
    (cert_validator.rs:201-204), never by a header. *)
let s2 =
  let first_come_exclusivity =
    Formula.Ag
      (Formula.Implies
         (atom Bound_a, Formula.Ax (Formula.Not (atom Hb_told_missing))))
  in
  let bounded_block =
    Formula.Ag
      (Formula.Implies
         ( atom Hb_blocked,
           Formula.Au
             (atom Hb_blocked, Formula.Or (atom Stored, atom Hb_timedout)) ))
  in
  let blind_while_blocked =
    Formula.Ag
      (Formula.Implies
         ( atom Hb_blocked,
           Formula.And
             ( Formula.Not (Formula.K (j, atom D_exists)),
               Formula.Not (Formula.K (j, Formula.Not (atom D_exists))) ) ))
  in
  {
    name = "a-missing-parent-is-claimed-by-exactly-one-proposer";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        ( first_come_exclusivity,
          Formula.And (bounded_block, blind_while_blocked) );
    antecedent = atom Bound_a;
  }

(** S3 - the-author-serves-only-its-own-declared-parents [security]. The
    author-side mirror of S1's voter-side binding.

    (A) AG( ~served_undeclared(a) ): answering a [MissingParents(M)] reply,
    [a] reads [M] from its own certificate store but first intersects it with
    its own declared parent set, certifier.rs:146-155 -
    [certificate_store.read_all(missing_parents.into_iter().filter(|parent|
    header.parents().contains(parent)))] - so a digest [h_a] does not declare
    is never served, whatever [a] happens to hold.

    (B) AG( named_undeclared(v,a) -> AX( aborted(a,v) ) ): and [a] does not
    merely decline, it tears that peer's whole vote request down. [read_all]
    (storage/src/stores/certificate_store.rs:243-248) returns
    [Vec<Option<Certificate>>] and the [.flatten()] at certifier.rs:154 drops
    the [None]s, so the [parents.len() != expected_count] check at
    certifier.rs:157-165 is load-bearing; it returns
    [DagError::ProposedHeaderMissingCertificates], which propagates out of
    [request_vote] and ends that peer's vote task (the collector logs it at
    certifier.rs:350-357 and keeps waiting on the other peers).

    Mutation pin: {!Parent_claim_binding_model.No_author_parent_filter}
    deletes the [.filter] at certifier.rs:150-151, adding
    [Ph_auth_asked_undeclared -> Ph_auth_served_undeclared] - refuting (A) at
    that new state and (B) at its predecessor. Its antecedent
    [named_undeclared] is reachable under the mutation, so the flip is a
    refutation.

    Sibling hunt: the count check at certifier.rs:157-165 IS a sibling and it
    IS in the model - with the filter gone but [a]'s store holding only the
    declared parent, [read_all] returns [[None]], the count is 0 against an
    expected 1, and [a] still aborts. That is why the mutation bites only from
    the [As_p1_and_p2] initial state, and why (A) is a claim about
    DISCLOSURE rather than about aborting. On the voter's side there is no
    repair at all: the voter DID name the digest in its own [missing] list, so
    handler.rs:537-548's [parents.len() == missing.len()] and
    [missing.contains(&parent)] checks pass as well. Honest scoping:
    certificates are gossiped anyway (certifier.rs:454
    [self.network.publish_certificate(certificate)]), so the residual is not
    confidentiality but abort semantics plus the DB cost of repeated
    [read_all]s across the unbounded retry backoff at certifier.rs:206-218,
    whose tail arm is [_ => 10_000] ms forever. *)
let s3 =
  let serves_only_declared = Formula.Ag (Formula.Not (atom A_served_undeclared)) in
  let aborts_on_undeclared =
    Formula.Ag
      (Formula.Implies (atom A_asked_undeclared, Formula.Ax (atom A_aborted)))
  in
  {
    name = "the-author-serves-only-its-own-declared-parents";
    bucket = Statements.Security;
    formula = Formula.And (serves_only_declared, aborts_on_undeclared);
    antecedent = atom A_asked_undeclared;
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
