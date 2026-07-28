(** The RECORD_SERVE_POOL statement family, encoded over the
    {!Record_serve_pool_model} interpreted system: the primary's [EpochRecord]
    request-response arm from admission control (network/mod.rs:343-363,
    :1594-1613) through dispatch (handler.rs:990-1026) to the penalty split
    (error/network.rs:141-205). All three statements are properties of that one
    pipeline over that one slot table, and each is pinned by its own gate
    deletion. File citations refer to Telcoin-Association/telcoin-network
    (HEAD 0c59c15b), read in this checkout.

    READING GUIDE for the K operands - why none of them is a projection of its
    own knower's view, and none is rigid.

    - [K (V1, admitted(P))] in S2. V1 is the probing requester. [admitted(P)]
      is the RESPONDER's hidden branch decision at network/mod.rs:1602-1613 -
      whether [try_admit_epoch_record] handed back a [PeerSlotPermit] or
      [None]. V1 never sees the slot table and gets no rejection on the wire
      (:1607-1609), so while its request is outstanding [admitted(P)] is
      strictly outside its view: the model has reachable states with V1's
      view [Pv_inflight sel] on BOTH sides of the branch. The knowledge is
      acquired, not definitional: it arrives with the response, because in
      this arm only an admitted request can produce one. It is not rigid
      either - [admitted(P)] is false at every idle and every shed state, and
      shed states are reachable pristine.
    - [~K (V1, shed(P))] and [~K (V1, serving(P))] in S2 are the two halves of
      the same ignorance: the shed state and the running-serve states share
      V1's view exactly, so neither branch is knowable from inside. The
      witness pair is concrete: [(load = (1,2,2), Pb_shed sel)] and
      [(load = (0,2,2), Pb_serve sel)] both project to [Pv_inflight sel].
    - [~K (V0, deviant_request(P))] and [~K (V0, ~deviant_request(P))] in S3.
      V0 is the responder. It DOES see the request's bytes - [(epoch, hash)]
      is a parameter of [process_epoch_record_request] (network/mod.rs:1589-
      1590) - so the model gives V0 the wire shape. What it cannot see is who
      wrote those bytes: a client following the request type's own
      documentation (network/message.rs:73-74) and a peer farming a
      penalty-free flood emit the identical [(None, None)]. The witness pair is
      [(load, Pb_serve Sel_none_doc)] and [(load, Pb_serve Sel_none_grief)] at
      the SAME load, which share V0's view [(load, Rs_serving W_unaddressed)]
      and disagree on the operand. Not rigid: at an addressed serve the operand
      is false and V0 does know it. *)

open Record_serve_pool_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a false antecedent - and each antecedent below is chosen
          to stay REACHABLE under the mutation that pins its statement, so the
          pin flips on the property and never on vacuity *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - record-serve-pool-exhaustion-needs-three-distinct-requesters
    [fairness]. The two caps of the [EpochRecord] serve pool are arithmetically
    coupled, and the coupling is a genuine anti-monopoly guarantee:

    (A) AG( occupancy = 5 -> distinct_holders >= 3 ). The global budget is
    [MAX_CONCURRENT_EPOCH_RECORD_REQUESTS = 5] (network/mod.rs:72-81) and no
    requester may hold more than [MAX_PENDING_REQUESTS_PER_PEER = 2]
    (network/mod.rs:102-105, enforced at :359), so an exhausted pool is
    necessarily 2 + 2 + 1 across three distinct peers: ceil(5 / 2) = 3.
    Neither one Byzantine requester nor a colluding PAIR can make the arm
    unavailable to everyone else. The accounting that makes this exact is the
    [PeerSlotPermit] [Drop] impl (network/mod.rs:288-315), which decrements the
    peer's entry and releases the global permit together.

    (B) AG( no requester holds more than 2 ) - the per-peer cap itself,
    asserted as a reachability invariant of the admission gate rather than as a
    restatement of the constant. It is exact and not best-effort because the
    count and the increment happen under ONE [peers.lock()] guard
    (network/mod.rs:357-362), leaving no window in which two admissions both
    observe the same sub-cap count.

    Scope, stated so the claim is not read as more than it is: "distinct
    requesters" means distinct [BlsPublicKey] (the counter's key,
    network/mod.rs:1378) and the arm admits any peer whose identity resolves
    rather than committee members only (network/mod.rs:74-75), so three SYBIL
    identities exhaust the pool exactly as three honest peers do. The
    guarantee is that no ONE resolved identity, and no PAIR, can.

    This is not a manufactured invariant: it is the property the cap was added
    for. The arm is reachable "by any peer whose identity resolves (not
    committee membership)" (network/mod.rs:74-75) and the pre-fix code had no
    bound at all (GHSA-vc2r-9cp2-w74j, cited at :80 and in the regression tests
    at tests/network_tests.rs:1624-1627).

    Mutation pin: {!Record_serve_pool_model.No_per_peer_record_cap} deletes the
    [count < MAX_PENDING_REQUESTS_PER_PEER] conjunct at network/mod.rs:359. One
    requester then takes a third, fourth and fifth slot, so the table [(0,0,5)]
    is reachable: occupancy 5 with ONE holder refutes (A) and a requester over
    the cap refutes (B). The antecedent [occupancy = 5] stays reachable under
    that mutation, so the flip is on the property. No sibling repairs the
    deletion - see the constructor's own sibling hunt: the libp2p per-peer
    inbound limiter is a 256-per-second RATE on streams, not a concurrency cap
    on request-response; [try_admit_sync] guards a different semaphore and a
    different counter; and the request-response and QUIC defaults (100 per
    peer, 10_000 streams) are orders of magnitude above five. *)
let s1 =
  let exhaustion_needs_three =
    Formula.Ag
      (Formula.Implies (atom Pool_exhausted, atom Three_distinct_holders))
  in
  let per_peer_cap_holds = Formula.Ag (Formula.Not (atom Requester_over_cap)) in
  {
    name = "record-serve-pool-exhaustion-needs-three-distinct-requesters";
    bucket = Statements.Fairness;
    formula = Formula.And (exhaustion_needs_three, per_peer_cap_holds);
    antecedent = atom Pool_exhausted;
  }

(** S2 - epoch-record-serve-bounded-and-shed-invisible-to-the-shed-requester
    [security]. What the admission gate buys, and what it costs the requester
    epistemically:

    (A) AG( occupancy <= 5 ). Concurrent [EpochRecord] serves never exceed the
    global budget, because an over-budget request is shed before any task is
    spawned: [process_epoch_record_request] takes the permit at
    network/mod.rs:1602-1603 and returns at :1612 when it is refused, and an
    admitted serve holds its permit for its whole lifetime (:1619-1622), so the
    cap bounds the in-flight certificate-wait budget too (each serve can sit in
    the five-times-300ms wait of handler.rs:1014-1021).

    (B) AG( shed(P) -> ~K_P(shed(P)) ). The shed is a silent O(1) drop of the
    response channel. Its own comment states the consequence verbatim:
    "Dropping the channel sends no rejection over the wire, so the caller
    (`request_epoch_cert`) rotates to another peer only after its
    request-response timeout elapses" (network/mod.rs:1605-1611). So the shed
    requester's view - request sent, nothing back - is the SAME value it has
    while the responder is slowly serving it.

    (C) AG( serving(P) -> ~K_P(serving(P)) ). The dual, and the reason (B) is
    not an artefact: the ignorance runs both ways, an admitted requester cannot
    tell it was admitted either. Note that [request_epoch_cert] discards the
    failure kind entirely - [if let Ok(Ok(NetworkResponseMessage { .. })) =
    res.await] (network/mod.rs:820-826) - so even the transport-level
    distinctions the libp2p layer does draw (consensus.rs:1203-1274) never
    reach the logic that would act on them.

    (D) AG( replied(P) -> K_P(admitted(P)) ). The one positive: a response, of
    any kind, does tell the requester that its request was admitted to the
    pool, because in this arm only an admitted request produces one - a shed
    request produces nothing. This is knowledge about the RESPONDER's hidden
    admission branch, and it is contingent: at idle and at shed states
    [admitted(P)] is false, and V1's view class at a replied state contains
    eight reachable states (every slot table the serve could have been admitted
    from), so the K is not a singleton artefact.

    Mutation pin: {!Record_serve_pool_model.No_record_admission_gate} deletes
    the [try_admit_epoch_record] call and its [else { return; }] arm
    (network/mod.rs:1602-1613), spawning a serve for every request. Occupancy
    then exceeds five, refuting (A) - and, because the shed branch disappears
    with it, "sent and nothing back" can only mean a running serve, so
    [K_P(serving(P))] becomes TRUE and (C) is refuted as well. The antecedent
    [serving(P)] is still reachable under the mutation, so neither flip is
    vacuity. No sibling repairs it: [task_spawner.spawn_task] is an unbounded
    spawn, the deleted call is the crate's only epoch-record limiter, and the
    libp2p request-response and QUIC defaults are far above five. *)
let s2 =
  let global_bound = Formula.Ag (Formula.Not (atom Pool_over_cap)) in
  let shed_is_invisible =
    Formula.Ag
      (Formula.Implies
         ( atom Probe_shed,
           Formula.Not (Formula.K (Validator.V1, atom Probe_shed)) ))
  in
  let serve_is_invisible =
    Formula.Ag
      (Formula.Implies
         ( atom Probe_serving,
           Formula.Not (Formula.K (Validator.V1, atom Probe_serving)) ))
  in
  let reply_confirms_admission =
    Formula.Ag
      (Formula.Implies
         (atom Probe_replied, Formula.K (Validator.V1, atom Probe_admitted)))
  in
  {
    name = "epoch-record-serve-bounded-and-shed-invisible-to-the-shed-requester";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( global_bound,
          Formula.And
            ( shed_is_invisible,
              Formula.And (serve_is_invisible, reply_confirms_admission) ) );
    antecedent = atom Probe_serving;
  }

(** S3 - unaddressed-epoch-record-request-is-charged-only-when-the-pool-had-room
    [security]. The handler splits requester faults into two classes with
    opposite penalties, and the charged class is charged blind and by luck:

    (A) AG( serving_unaddressed(P) -> ~EF( replied(P) /\\ ~penalty_medium(P) ) ).
    An ADMITTED request naming neither an epoch number nor a hash is never
    answered without the Medium charge: [retrieve_epoch_record] returns
    [Err(PrimaryNetworkError::InvalidEpochRequest)] on the [(None, None)] arm
    (handler.rs:999), [From<&PrimaryNetworkError> for Option<Penalty>] maps it
    to [Some(Penalty::Medium)] (error/network.rs:192-193) and the spawned serve
    applies it (network/mod.rs:1627-1630). This is charged against the request
    type's OWN wire contract, which documents that exact case as legal: "If
    neither number or hash are set then will return the latest epoch record the
    node has available" (network/message.rs:73-74). Either that doc comment or
    handler.rs:999 is wrong; the statement forces the choice. The conjunct is
    deliberately stated as "no reachable answer without the charge" rather than
    as an [AF] inevitability, because the serve runs inside a [tokio::select!]
    whose [_ = cancel => ()] arm (network/mod.rs:1623, :1636) can abort it
    before the charge - a cancelled serve answers nothing, so it does not
    weaken this form, whereas it would falsify a bare [AF penalty_medium(P)].
    That is the one place where a more detailed model of the real code could
    have refuted a lazier encoding of this claim.

    (B) AG( serving_addressed(P) -> AG ~penalty_medium(P) ). The other class is
    deliberately free: an epoch this node does not have yields
    [UnavailableEpoch] / [UnavailableEpochDigest] (handler.rs:1022, :1024,
    :1045, :1047), which error/network.rs:196-197 maps to [None] with the
    comment "A node might not have this yet...", so honest catch-up is never
    scored down.

    (C) AG( shed(P) -> AG ~penalty_medium(P) ). The luck: the SAME unaddressed
    bytes cost nothing when the pool is full, because the admission shed at
    network/mod.rs:1602-1613 returns before [retrieve_epoch_record] is ever
    called and carries no penalty of its own. Whether a deviant request is
    punished is therefore a function of the responder's load at that instant,
    not of the request.

    (D) AG( serving_unaddressed(P) -> ~K_V0(deviant) /\\ ~K_V0(~deviant) ).
    And it is charged blind: the responder can see the bytes but not their
    author, so at the moment it applies the Medium it can neither confirm nor
    rule out that it is scoring down a client written to its own documented
    contract.

    Mutation pin: {!Record_serve_pool_model.No_unaddressed_request_reject}
    deletes the [(None, None) => return Err(...)] arm at handler.rs:999 and
    serves the latest record as message.rs:73-74 documents. The admitted
    unaddressed serve then answers instead of charging, [penalty_medium(P)]
    becomes unreachable and (A) is refuted, while the antecedent
    [serving_unaddressed(P)] stays reachable - the flip is on the property. No
    sibling charges it instead: [InvalidEpochRequest] is constructed at
    handler.rs:999 and nowhere else in the tree (every other occurrence is a
    classification arm at error/network.rs:56/:132/:192 and message.rs:354, or
    a unit test); [request_epoch_cert] forwards [epoch] and [hash] verbatim
    with no non-[None] requirement (network/mod.rs:809-829); the shed drops the
    channel without penalty and runs strictly before the match; and
    [PrimaryResponse::Error] (network/mod.rs:1632, message.rs:330-357) carries
    no penalty of its own. *)
let s3 =
  let unaddressed_is_charged =
    Formula.Ag
      (Formula.Implies
         ( atom Serve_unaddressed,
           Formula.Not
             (Formula.Ef
                (Formula.And
                   (atom Probe_replied, Formula.Not (atom Probe_charged)))) ))
  in
  let addressed_is_free =
    Formula.Ag
      (Formula.Implies
         (atom Serve_addressed, Formula.Ag (Formula.Not (atom Probe_charged))))
  in
  let shed_is_free =
    Formula.Ag
      (Formula.Implies
         (atom Probe_shed, Formula.Ag (Formula.Not (atom Probe_charged))))
  in
  let charged_blind =
    Formula.Ag
      (Formula.Implies
         ( atom Serve_unaddressed,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom Serving_deviant)),
               Formula.Not
                 (Formula.K
                    (Validator.V0, Formula.Not (atom Serving_deviant))) ) ))
  in
  {
    name =
      "unaddressed-epoch-record-request-is-charged-only-when-the-pool-had-room";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( unaddressed_is_charged,
          Formula.And (addressed_is_free, Formula.And (shed_is_free, charged_blind))
        );
    antecedent = atom Serve_unaddressed;
  }

(** The family's statements: the fairness arithmetic of the two caps, the
    security bound plus the requester's blindness, and the penalty split plus
    the responder's blindness. *)
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
