(** CTLK statements for the SERVE_SLOT_QUOTA family: one serving primary's
    admission bookkeeping across its two service classes, and the knowledge a
    stream-class capacity denial hands the peer that receives it. All citations
    are [crates/consensus/primary/src/network/mod.rs] at git HEAD 0c59c15b
    unless another file is named, and every one was opened in this checkout.

    READING GUIDE FOR THE K OPERANDS. There is exactly one positive [K] in the
    family, S3 conjunct A, and one ignorance conjunct in each of S1 and S3.

    - S3(A) [K_V2( distinct_other_stream_holders >= 2 )] is not a projection of
      V2's own view. V2's view is the pair (answer to my stream open, answer to
      my record request) - {!Serve_slot_quota_model.View_honest} - and carries
      no component of the responder's semaphore, of [pending_epoch_requests], of
      [sync_stream_peers] or of any other peer's holdings. The operand is a fact
      about OTHER peers' admissions. It is not rigid either: it is false at the
      initial state and at every state in which only one peer has been admitted,
      and the mutation
      {!Serve_slot_quota_model.No_per_peer_stream_cap} makes it false at a
      denied state, which is exactly how the pin lands. The knowledge is
      DERIVED, not observed: V2 sees only a [Deny(DenyReason::AtCapacity)]
      frame, and it is the arithmetic of a per-peer cap strictly below the pool
      that converts that one bit into a fact about the rest of the committee.
    - S3(B) [~K_V2( stream_inflight(P) = 2 )] is the limit of that inference:
      the same view value covers both ways an exhausted pool can be split, so
      the denial reveals an aggregate and never a distribution. Its witness pair
      is the two reachable denied states with (P, T) holding (1, 2) and (2, 1);
      that pair is also this family's R2 non-singleton evidence for the positive
      K, since it shows the view class at a denied state contains at least two
      reachable states.
    - S1(B) [~K_V2( stream_permits_taken = 3 )] is about the OTHER class: a
      record answer, taken alone, is uninformative about the stream pool,
      because the epoch-record serve path never consults it (mod.rs:351-363,
      doc at :349-350). It is guarded by [no_stream_request(Q)] on purpose - a
      requester that ALSO holds a denial does know something about the pool,
      which is S3, and the two conjuncts must not contradict each other. *)

open Serve_slot_quota_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;  (** unique across every family *)
  bucket : Statements.bucket;  (** Safety | Liveness | Fairness | Security *)
  formula : atom Formula.t;  (** what is proved on the pristine model *)
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - record-admission-survives-a-saturated-stream-pool [fairness]. The
    primary serves two request classes out of two SEPARATE budgets, and the
    separation is what stops either from starving the other.

    The two budgets are two distinct [Arc<Semaphore>] values built at
    mod.rs:1402 and mod.rs:1413 and held in two distinct fields, mod.rs:1357
    [epoch_stream_semaphore] and mod.rs:1375 [epoch_record_semaphore], the
    latter documented verbatim at mod.rs:1373-1374 as "Separate from
    [epoch_stream_semaphore] so an epoch-record flood and the stream-serving
    paths never starve one another"; the constant repeats the rationale at
    mod.rs:72-81. Their per-peer counters are separate as well
    ([sync_stream_peers] mod.rs:1370 and [pending_epoch_requests] mod.rs:1411
    versus [epoch_record_peers] mod.rs:1378), and [try_admit_epoch_record]
    (mod.rs:351-363) reads only the record pair - its own doc says "Unlike
    [try_admit_sync] this path has its own semaphore and counter, so it neither
    consults nor contends the stream pending map" (mod.rs:349-350).

    Conjunct A (the isolation, stated at the admission test rather than as a
    liveness claim): AG( record_request_outstanding(Q) /\ stream_permits_taken =
    3 -> EX record_served(Q) ). At EVERY reachable state in which the stream
    pool is completely exhausted and Q's epoch-record request is outstanding,
    the responder can answer it on the very next step: [try_admit_epoch_record]
    is called synchronously at mod.rs:1602-1603 and, if it returns a permit, the
    serve task is spawned at mod.rs:1619-1639. [EX] is the honest operator here
    - the claim is that the stream class never makes the record admission FAIL,
    not that a scheduler will run it, so no fairness assumption is smuggled in
    (R8).

    Conjunct B (the epistemic price of the separation): AG( record_served(Q) /\
    no_stream_request(Q) -> ~K_V2( stream_permits_taken = 3 ) ). A requester
    whose only channel is the record arm learns nothing about the stream class
    from being served, because the record admission never touched it. The
    witness pair is (i) the state reached by serving Q's record request straight
    from {!Serve_slot_quota_model.initial}, where the pool is empty, and (ii) a
    state in which P and T have filled all three permits before Q's record
    request is served; V2's view is [View_honest (Qs_unsent, Qr_served)] in
    both.

    Mutation pin: {!Serve_slot_quota_model.Shared_permit_pool} deletes the
    dedicated record budget (field mod.rs:1375, construction mod.rs:1413) and
    routes the mod.rs:1602-1603 admission at [epoch_stream_semaphore]. At a
    stream-exhausted state the record admission then returns [None] and the
    request is shed at mod.rs:1612, so no successor answers Q and conjunct A
    fails. No sibling repairs it inside this responder: the shed is silent by
    design ("Dropping the channel sends no rejection over the wire",
    mod.rs:1605-1611), the serve holds its permit for its whole lifetime
    (mod.rs:1619-1622) so nothing is freed early, and the one recovery the code
    names - [request_epoch_cert] rotating to a DIFFERENT peer after its
    request-response timeout (mod.rs:1607-1609) - leaves the node whose fairness
    is at issue. The 30-second pending sweep (mod.rs:1451-1456) would eventually
    free a stream permit, but conjunct A is an [EX] claim evaluated at the
    exhausted state, so a later release cannot repair it. *)
let s1 =
  let isolation =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Q_record_pending, atom Stream_pool_full),
           Formula.Ex (atom Q_record_served) ))
  in
  let record_answer_is_uninformative =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Q_record_served, atom Q_stream_unsent),
           Formula.Not (Formula.K (Validator.V2, atom Stream_pool_full)) ))
  in
  {
    name = "record-admission-survives-a-saturated-stream-pool";
    bucket = Statements.Fairness;
    formula = Formula.And (isolation, record_answer_is_uninformative);
    antecedent = Formula.And (atom Q_record_pending, atom Stream_pool_full);
  }

(** S2 - stream-slots-are-capped-per-peer-across-both-admission-paths [safety].
    The epoch-stream class has ONE budget and TWO admission paths, and the
    per-peer cap is computed over the union of both in each of them - which is
    what stops a peer from doubling its footprint by switching protocol.

    The legacy path is [accept_stream_request] (mod.rs:1647-1705): it takes a
    permit from [epoch_stream_semaphore] at mod.rs:1654-1656 and then computes,
    verbatim at mod.rs:1664-1666, [let legacy_count = pending_map.keys()
    .filter(|(p, _)| *p == peer).count(); let sync_count =
    self.sync_stream_peers.lock().get(&peer).copied().unwrap_or(0); let
    peer_count = legacy_count + sync_count;], refusing at mod.rs:1667-1676 with
    the comment "permit drops here, freeing the slot". The sync path is
    [try_admit_sync] (mod.rs:326-341), called at mod.rs:1876-1881 with the SAME
    semaphore, and it adds the same two terms at mod.rs:334-337 before its
    [.then]. Its doc names the intent at mod.rs:319-321: "the peer's combined
    in-flight count (legacy pending requests plus sync streams) is below
    [MAX_PENDING_REQUESTS_PER_PEER], so the per-peer cap holds across both
    paths".

    Conjunct A (the cap itself, as a reachability invariant of the two gates
    rather than a restatement of the constant): AG( ~ some_peer_stream_inflight
    > 2 ). No peer's legacy entries plus sync streams ever exceed
    [MAX_PENDING_REQUESTS_PER_PEER = 2] (mod.rs:102-105).

    Conjunct B (what the cap buys): AG( stream_permits_taken = 3 /\
    ~holds_stream_slot(Q) -> distinct_other_stream_holders >= 2 ). An exhausted
    pool is necessarily spread over more than one peer, so no single requester
    can make the stream class unavailable on its own. With the model's three
    permits and the real cap of two this is "at least two distinct holders";
    under the deployed [MAX_CONCURRENT_EPOCH_STREAMS = 5] (mod.rs:66-70) the
    identical argument gives at least three.

    Mutation pin: {!Serve_slot_quota_model.No_cross_path_count} deletes only the
    CROSS terms - [+ sync_count] at mod.rs:1665-1666 and [legacy_count +] at
    mod.rs:334-337 - leaving both caps and the semaphore in place. P then takes
    two legacy slots under its legacy-only count and a sync stream under its
    sync-only count, so both conjuncts fail at the state (p_leg = 2, p_syn = 1,
    t_str = 0). Nothing repairs it: those two expressions are the only sites
    where the two counters are summed, the semaphore is a global bound that does
    not distinguish peers, [PeerSlotPermit]'s [Drop] (mod.rs:305-315) decrements
    the same counter its admission incremented and so cannot re-couple them, and
    the libp2p per-peer limiter ([inbound_rate_limited],
    crates/network-libp2p/src/stream/behavior.rs:281-290) is a RATE of 256
    inbound streams per one-second window (behavior.rs:42-45) that neither
    reserves nor releases a slot - it is the one genuine partial sibling in this
    area and it delays a monopolisation without preventing one. *)
let s2 =
  let cap_holds =
    Formula.Ag (Formula.Not (atom Peer_over_stream_cap))
  in
  let exhaustion_needs_two_peers =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             (atom Stream_pool_full, Formula.Not (atom Q_holds_stream_slot)),
           atom Two_stream_holders ))
  in
  {
    name = "stream-slots-are-capped-per-peer-across-both-admission-paths";
    bucket = Statements.Safety;
    formula = Formula.And (cap_holds, exhaustion_needs_two_peers);
    antecedent = atom Stream_pool_full;
  }

(** S3 - a-capacity-denial-tells-a-slotless-requester-two-peers-are-served
    [security]. The stream class differs from the record class in that it
    ANSWERS a refusal, and the answer is not epistemically neutral.

    That the refusal is delivered is explicit on both paths. Legacy:
    [let ack = self.accept_stream_request(peer, request_digest, kind);
    self.send_stream_ack(ack, ...)] (mod.rs:1746-1747) puts the bool on the wire
    as [PrimaryResponse::StreamRequestAck { ack }] (mod.rs:1715) and the client
    branches on it - [if !ack { continue; }] (mod.rs:976-984). Sync: the shed
    branch writes [SyncFrame::<PrimarySyncRequest>::Deny(DenyReason::
    AtCapacity)] without reading (mod.rs:1892-1906; the variant is declared at
    crates/network-libp2p/src/sync/frame.rs:51), as its doc records at
    mod.rs:1866-1869. Contrast the record class, which sheds by dropping the
    channel and sends nothing at all (mod.rs:1604-1612) - the two classes make
    opposite choices about telling the truth to a refused peer.

    Conjunct A: AG( denied_at_capacity(Q) -> K_V2( distinct_other_stream_holders
    >= 2 ) ). [try_admit_sync] returns [None] on either of two grounds - an
    empty semaphore (mod.rs:332) or an over-cap peer (mod.rs:337) - so a denial
    is ambiguous in general. Q, which holds no stream slot of its own, can rule
    the second out from its own view, so its denial pins the first: the pool was
    full. A full pool with a per-peer cap strictly below it cannot be one peer's
    doing, so Q learns a fact about the rest of the committee that no message it
    ever receives contains. The operand is phrased over admissions rather than
    instantaneous occupancy on purpose: it is monotone, so it stays true after
    any later release and the claim does not depend on this model's admission-
    window scope.

    Conjunct B: AG( denied_at_capacity(Q) -> ~K_V2( stream_inflight(P) = 2 ) ).
    The inference stops at the aggregate. The two reachable denied states in
    which (P, T) hold (1, 2) and (2, 1) are indistinguishable to V2 - both
    project to [View_honest (Qs_denied, _)] - so Q can never attribute the
    crowding to a particular peer, which is also why a denial is not usable as
    an accusation.

    Mutation pin: {!Serve_slot_quota_model.No_per_peer_stream_cap} deletes the
    per-peer refusal on both stream paths (the [if peer_count >=
    MAX_PENDING_REQUESTS_PER_PEER] block at mod.rs:1667-1676 and the [(... <
    MAX_PENDING_REQUESTS_PER_PEER)] guard at mod.rs:337), leaving the global
    semaphore. P alone then takes all three permits, so the state (p_leg = 3,
    t_str = 0, Q denied) is reachable, the operand of conjunct A is FALSE there,
    and since that state shares V2's view with every other denied state the
    knowledge collapses everywhere. The denial frame still goes out unchanged -
    the mutation removes the inference, not the message, which is precisely the
    point. No sibling re-establishes the bound: see the mutation constructor's
    own doc comment in {!Serve_slot_quota_model} for the enumeration (the
    semaphore is peer-blind, [Drop] only decrements, the primary's pending entry
    holds its permit from acceptance to service so there is no handoff site, and
    the libp2p limiter is a per-second rate rather than a concurrency
    reservation). *)
let s3 =
  let denial_is_informative =
    Formula.Ag
      (Formula.Implies
         ( atom Q_stream_denied,
           Formula.K (Validator.V2, atom Two_stream_holders) ))
  in
  let denial_hides_the_distribution =
    Formula.Ag
      (Formula.Implies
         ( atom Q_stream_denied,
           Formula.Not (Formula.K (Validator.V2, atom Flooder_at_cap)) ))
  in
  {
    name = "a-capacity-denial-tells-a-slotless-requester-two-peers-are-served";
    bucket = Statements.Security;
    formula = Formula.And (denial_is_informative, denial_hides_the_distribution);
    antecedent = atom Q_stream_denied;
  }

(** The family's statements: the class isolation plus its epistemic neutrality,
    the union per-peer cap and its anti-monopoly arithmetic, and the knowledge a
    delivered capacity denial creates. *)
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
