(** The PENDING_GC statement family, encoded over the {!Pending_gc_model}
    interpreted system. The three statements were mined from telcoin-network,
    re-grounded line by line against the working tree at git HEAD 0c59c15b, and
    are stated here in the form that survived that re-grounding. They share the
    single joint model and are pinned by four distinct gate deletions. File
    citations refer to Telcoin-Association/telcoin-network.

    Reading guide for the [K] operands. There are exactly three, and none is a
    projection of its own knower's view:

    - [K (Validator.V1, Peer_holds_parent)] and its negation in S1 target the
      NAMED peer [w]'s POSSESSION of the parent [d], where [w] is one of [c]'s
      signers. Both are asserted NEGATIVELY, and the reason is a Byzantine
      branch, not an absent channel. [c] carries the bitmap of its signers and
      [v] must clear [weight >= quorum_threshold] on it before accepting
      (certificate.rs:225-251, :177-199; threshold 3 of 4,
      committee.rs:684-688), and an honest signer cannot have voted without
      first holding every parent of the header (handler.rs:688-693 blocking on
      header_validator.rs:39-67). So [v] DOES know a quorum-level fact: at
      least [3 - f = 2] of [c]'s signers held [d], and still hold it (a store
      trims only below [round - 64], storage/src/lib.rs:46, while the horizon
      is at most 50 rounds back, types/src/primary/mod.rs:45). What [v] cannot
      do is name one. At the operative state [v] is itself not a signer of [c]
      (it never held [d], and its own vote would have blocked on notify_read
      for [d]), so with a committee of four the signers are exactly the other
      three and [w] is one of them; with [f = 1] any single one of the three
      may be faulty, and a faulty signer's vote is a bare BLS signature over
      the header digest that attests nothing about its store. The two initial
      states are exactly those two worlds. An EARLIER revision of this guide
      justified the ignorance by "no primary message reports store contents";
      a review refuted that (the certificate itself reports it, quorum-wise)
      and this is the repaired grounding.

    - [K (Validator.V0, Cert_accepted)] in S3 targets the VOTER's certificate
      store - a different node's possession. V0's view is only its own vote
      round, and [Cert_accepted] is false at every reachable [R_open] state whose
      [local_c] is [C_unknown] (the initial state among them), so the operand is
      neither view-determined nor rigid. It holds at [R_voted] exactly because
      the protocol gate - the blocking notify_read at handler.rs:693 - makes the
      observation informative, which is what {!Pending_gc_model.No_parent_wait}
      destroys. The [R_voted] view class is not a singleton: it holds all eight
      reachable voted states, which disagree on both [Horizon_past] and
      [Parent_stored], so the author knows the voter holds [c] and STILL cannot
      tell whether the voter is past its horizon or holds [c]'s own parent.
      Both facts are discharged by satisfiability tests in [t_pending_gc.ml]. *)

open Pending_gc_model

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

(** S1 - gc-horizon-acceptance-forfeits-parent-knowledge [safety]. A certificate
    is accepted with a parent the node never held ONLY once the local GC horizon
    has passed that parent's round; and at exactly such a state the accepting
    node can neither confirm nor rule out that the NAMED peer [w] holds that
    parent. Past the horizon, the second-hand quorum attestation that [c]
    carries is all [v] will ever have about [d]: it can no longer replace it
    with first-hand possession.

    SCOPE - what conjunct B does NOT claim. [v] is not in the dark about [d].
    Accepting [c] forces it to clear the certificate's signer bitmap against
    [quorum_threshold] (certificate.rs:225-251), and honest signers block on
    notify_read for every parent before voting (handler.rs:688-693,
    header_validator.rs:39-67), so [v] knows at least [3 - f = 2] of [c]'s
    signers held [d]. The claim is only that it cannot put a NAME to one, since
    with [f = 1] any single signer may be the faulty one whose signature
    attests nothing about its store. An earlier revision claimed the broader
    ignorance and grounded it on "no message reports store contents"; a review
    refuted that grounding and this statement is the retargeted, surviving
    claim.

    (A) CAUSAL-ORDER GATE:
    AG( (accepted_v(c) /\\ ~stored_v(d)) -> gc_past_v(d) ). The entire
    missing-parent check sits under [if cert.round() > self.gc_round() + 1]
    (cert_manager.rs:103-118), so ABOVE the horizon get_missing_parents
    (cert_manager.rs:139-180) and insert_pending park the certificate, and it
    can then only be accepted via cert_manager.rs:120-124 - update_pending
    followed by accept_verified_certificates - i.e. after the parent is present.
    At or below the horizon the guard is skipped and
    accept_verified_certificates (cert_manager.rs:189-220) writes, appends and
    forwards with no parent precondition at all. So parentless acceptance is
    exactly the post-horizon case.

    (B) NAMED-PEER IGNORANCE:
    AG( (accepted_v(c) /\\ ~stored_v(d)) ->
        ~K_v(holds_w(d)) /\\ ~K_v(~holds_w(d)) ). What [v] verifies about [c] is
    a WEIGHT: signed_by walks the roaring bitmap and validate_and_verify
    enforces [weight >= committee.quorum_threshold()] and the aggregate
    signature (certificate.rs:177-199, :225-251, :349-354). Nothing in that
    check ties a signer's key to its store contents; possession is enforced
    only by the honest vote path (handler.rs:688-693 blocking on
    header_validator.rs:39-67), which a faulty validator simply does not run.
    With a committee of four the threshold is 3 (committee.rs:684-688) and, at
    a state where [v] never held [d], [v] cannot itself be one of [c]'s signers
    (its own vote would have blocked on notify_read for [d], and the retention
    margin - stores trim only below [round - 64], storage/src/lib.rs:46, while
    the horizon is at most [MAX_GC_DEPTH = 50] rounds back,
    types/src/primary/mod.rs:45 - rules out "held [d], then GC'd it") - so the
    signer set is the other three, [w] among them, and the [f = 1] fault budget
    may or may not be spent on [w]. Neither world is excluded by anything [v]
    can see. The ignorance witness is the colliding pair
    W1 = (C_accepted, D_absent, H_past, R_open, W_holds_parent) - the
    all-honest world - and
    W2 = (C_accepted, D_absent, H_past, R_open, W_without_parent) - the world
    in which [w] is the faulty signer: both reachable, identical under
    [View_local], disagreeing on [holds_w(d)].

    The horizon's contribution is that it makes this ignorance TERMINAL. Below
    it, [v] can still settle the question by acquiring [d] itself - the fetcher
    still targets [d] (certificate_fetcher.rs:258-286, :350-379) and direct
    verification still accepts it. At or past it, every fetch target is
    strictly above [gc_round] and [d] is rejected as [TooOld]
    (cert_validator.rs:114-125), so the [lose_d] branch is real and [v] may
    hold nothing but the quorum attestation forever.

    Mutation pin: {!Pending_gc_model.No_parent_check} refutes this OUTRIGHT.
    Deleting cert_manager.rs:109-117 makes [deliver_c] accept unconditionally,
    adding (C_unknown, D_absent, H_below) -> (C_accepted, D_absent, H_below) - a
    reachable state at which conjunct A's consequent [gc_past_v(d)] is false.
    {!Pending_gc_model.No_gc_release} additionally degrades it to a vacuous
    antecedent, since accepted-without-parent becomes unreachable once both the
    horizon skip and the GC release are gone; that is noted but not the pin. *)
let s1 =
  let accepted_without_parent =
    Formula.And (atom Cert_accepted, Formula.Not (atom Parent_stored))
  in
  let causal_order_gate =
    Formula.Ag (Formula.Implies (accepted_without_parent, atom Horizon_past))
  in
  let horizon_ignorance =
    Formula.Ag
      (Formula.Implies
         ( accepted_without_parent,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom Peer_holds_parent)),
               Formula.Not
                 (Formula.K
                    (Validator.V1, Formula.Not (atom Peer_holds_parent))) ) ))
  in
  {
    name = "gc-horizon-acceptance-forfeits-parent-knowledge";
    bucket = Statements.Safety;
    formula = Formula.And (causal_order_gate, horizon_ignorance);
    antecedent = accepted_without_parent;
  }

(** S2 - pending-certificate-always-released [liveness]. A verified certificate
    parked for a missing parent is always released - inevitably accepted - and
    both release routes are genuinely live: the parent-acceptance cascade, which
    leaves the parent stored, and the garbage-collection release, which accepts
    it with the parent still absent.

    (A) INEVITABILITY: AG( pending_v(c) -> AF accepted_v(c) ). Exactly two
    release routes exist. Route 1 is cert_manager.rs:120-124 driving
    pending_cert_manager.rs:85-131: a parent's acceptance cascades through
    update_pending, which removes it from [missing_parent_digests] and pushes
    the unlocked deque into accept_verified_certificates. Route 2 is the
    process_gc_round drain loop, cert_manager.rs:235-238: next_for_gc_round
    (pending_cert_manager.rs:137-156) SELECTS the lowest
    [(round, digest)] key of [missing_for_pending] with [round <= gc_round],
    and update_pending (pending_cert_manager.rs:97-131) then removes that key
    and returns every child whose [missing_parent_digests] emptied, which
    accept_verified_certificates writes. gc.rs:66-92 makes route 2 fire on every
    committed-round update. (The release is the loop plus update_pending;
    next_for_gc_round's [round > gc_round] bound is the loop's termination test
    and its [missing_parent_digests.clear()] is unreachable - see the ANCHOR
    NOTE on {!Pending_gc_model.No_gc_release}.)

    (B) BOTH ROUTES LIVE: AG( pending_v(c) ->
    E[ pending_v(c) U (accepted_v(c) /\\ stored_v(d)) ] /\\
    E[ pending_v(c) U (accepted_v(c) /\\ ~stored_v(d)) ] ). This is the
    anti-manufactured-liveness conjunct: the [Af] is witnessed by two distinct
    successor branches, not by one rigged edge. Route 1 is the [deliver_d]
    cascade (C_pending, D_absent, H_below) -> (C_accepted, D_stored, H_below);
    route 2 is the [gc_tick] release
    (C_pending, D_absent, H_below) -> (C_accepted, D_absent, H_past).

    Non-vacuity: [pending_v(c)] is reachable - [deliver_c] at
    (C_unknown, D_absent, H_below) parks it. The [Af] is honest because every
    component of the model is monotone, so the reachable graph is a finite DAG
    whose only stuttering states are fully advanced ones; under the pin a
    stuttering state that still has a parked certificate appears.

    Mutation pin: {!Pending_gc_model.No_gc_release}, which deletes both the
    process_gc_round drain loop (cert_manager.rs:235-238 together with the
    update_pending effect it consumes, pending_cert_manager.rs:97-131) and its
    sibling cert_manager.rs:108 (the horizon skip). [gc_tick] no longer accepts
    a parked certificate and
    [deliver_c] at [H_past] no longer accepts without the parent, so
    (C_pending, D_absent, H_past) becomes reachable and [lose_d] carries it to
    the terminal (C_pending, D_lost, H_past): a stutter loop with the
    certificate parked forever, refuting the [Af]; conjunct B's second [Eu] dies
    with it, since accepted-without-parent becomes unreachable. This statement
    carries no [K]: it is the reachability backbone that keeps the other two
    statements' operative states out of permanent deadlock, so R1 is not
    engaged. *)
let s2 =
  let inevitability =
    Formula.Ag
      (Formula.Implies (atom Cert_pending, Formula.Af (atom Cert_accepted)))
  in
  let cascade_route =
    Formula.Eu
      (atom Cert_pending, Formula.And (atom Cert_accepted, atom Parent_stored))
  in
  let gc_route =
    Formula.Eu
      ( atom Cert_pending,
        Formula.And (atom Cert_accepted, Formula.Not (atom Parent_stored)) )
  in
  let both_routes_live =
    Formula.Ag
      (Formula.Implies
         (atom Cert_pending, Formula.And (cascade_route, gc_route)))
  in
  {
    name = "pending-certificate-always-released";
    bucket = Statements.Liveness;
    formula = Formula.And (inevitability, both_routes_live);
    antecedent = atom Cert_pending;
  }

(** S3 - vote-round-respects-pending-parent-state [safety]. The voter never
    names a parent it already holds pending in the [MissingParents] response it
    COMPUTES, and a vote is a proof of possession: when the header author
    receives a vote it knows the voter has that parent in its certificate store
    - even though it learns nothing about the voter's horizon or the parent's
    own parent.

    (A) A COMPUTED MissingParents NEVER NAMES A PARKED PARENT:
    AG( (unanswered_v(h) /\\ (pending_v(c) \\/ accepted_v(c))) ->
        AX ~missing_computed(v->a,c) ). The [Ax] form, rather than a plain state
    implication, is REQUIRED: the report is an instant, and after it is emitted
    the parent may legitimately become pending, so
    AG( missing_computed -> ~pending_v(c) ) is FALSE on the pristine model.
    Grounding: identify_unkown_parents (header_validator.rs:195-229) does
    multi_contains and then round-trips the residue through
    [FilterUnkownDigests] (cert_manager.rs:298-301);
    filter_unknown_digests retains only digests NOT in the pending map
    (pending_cert_manager.rs:171-173); and handler.rs:653-669 builds
    [PrimaryResponse::MissingParents] solely from that filtered set. A pending
    certificate is never in storage either - write_all happens only in
    accept_verified_certificates (cert_manager.rs:196) - so a pending digest is
    dropped exclusively by the retain.

    SCOPE, and why the antecedent carries [unanswered_v(h)]. Those gates run
    when the voter COMPUTES a response. A response already computed is cached
    per author (handler.rs:510-516) and REPLAYED: a repeat request for the same
    header digest with an empty parents list returns the cached
    [MissingParents] set verbatim (handler.rs:519-534) - before any storage
    read, before identify_unkown_parents, before the [FilterUnkownDigests]
    round trip - and the empty-parents retry is ordinary rather than
    restart-only, since certifier.rs:185-196 clears the missing-parent hint on
    any non-RPC network error and certifier.rs:143-168 then re-sends with no
    parents. So a digest that was genuinely unknown when the set was computed
    CAN be named again after it has been parked. That replay copies an earlier
    answer instead of consulting the pending map, and conjunct A deliberately
    does not cover it: [unanswered_v(h)] holds exactly when no response for [h]
    has been computed yet, so the [Ax] successor is the computed response. An
    earlier revision stated this over an "outstanding request" and was refuted
    on the replay branch; this is the weakened, surviving claim.

    (B) A VOTE CERTIFIES POSSESSION:
    AG( vote_issued(v->a) -> K_a(accepted_v(c)) ). handler.rs:688-693 blocks on
    notify_read_parent_certificates for every parent; header_validator.rs:39-67
    maps [notify_read] over [header.parents()]; certificate_store.rs:250-269
    returns only once the certificate is actually written, which happens exactly
    in accept_verified_certificates (cert_manager.rs:196); and the vote is
    created and stored only after the quorum check (handler.rs:700-738,
    handler.rs:860-872). The knowledge is non-degenerate: V0's [R_voted] view
    class holds all eight reachable voted states, among them
    A = (C_accepted, D_stored, H_below, R_voted, W_without_parent) and
    B = (C_accepted, D_absent, H_past, R_voted, W_holds_parent), which disagree
    on both [gc_past_v(d)] and [stored_v(d)] - so the author cannot rule out that
    the voter is past its horizon, nor learn whether the voter holds the
    grandparent.

    Mutation pins: TWO, one per conjunct.
    {!Pending_gc_model.No_pending_filter} refutes conjunct A - deleting the
    retain at pending_cert_manager.rs:171-173 adds
    (C_pending, *, *, R_open) -> (C_pending, *, *, R_missing), so a successor of
    an antecedent state satisfies [missing_computed] and the [Ax] fails.
    {!Pending_gc_model.No_parent_wait} refutes conjunct B - deleting the
    blocking notify_read at handler.rs:693 adds
    (C_pending, *, *, R_open) -> (C_pending, *, *, R_voted), putting a state
    whose [local_c] is [C_pending] into V0's [R_voted] class, so
    [K_a(accepted_v(c))] fails. The antecedent stays reachable under both, so
    both produce a real refutation rather than a vacuity. *)
let s3 =
  let pending_never_named =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             ( atom Vote_unanswered,
               Formula.Or (atom Cert_pending, atom Cert_accepted) ),
           Formula.Ax (Formula.Not (atom Missing_reported)) ))
  in
  let vote_certifies_possession =
    Formula.Ag
      (Formula.Implies
         (atom Vote_issued, Formula.K (Validator.V0, atom Cert_accepted)))
  in
  {
    name = "vote-round-respects-pending-parent-state";
    bucket = Statements.Safety;
    formula = Formula.And (pending_never_named, vote_certifies_possession);
    antecedent = Formula.And (atom Vote_unanswered, atom Cert_pending);
  }

(** The family's statements: the causal-order gate paired with the named-peer
    ignorance, the two-route release liveness backbone, and the vote-round
    safety pair. *)
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
