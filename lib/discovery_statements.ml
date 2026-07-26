(** The DISCOVERY statement family, encoded over the {!Discovery_model}
    interpreted system: three security statements about the kad GET, kad PUT and
    peer-exchange routes into telcoin-network's peer manager. All three were
    mined from the Rust, re-grounded line by line against the working tree at
    git HEAD [0c59c15b], and are stated here in the form that survived that
    re-grounding plus an adversarial faithfulness review - two were reworded and
    two retargeted (the PUT statement twice: its non-regression claim is now
    guarded by the local kad store, which is what [is_newer_record] actually
    reads, and it was renamed accordingly); see the per-statement docs for
    exactly what changed and why. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide for the K operands. V0 is the local node running the peer
    manager and the only knowledge agent; its view is [(known_peers entry for A,
    the running episode)] and contains NO component of [nature]. Two hidden
    facts are quantified over:

    - [newer_record_exists] - "authority A has published a record strictly newer
      than r0 somewhere in the system". That is a fact about ANOTHER node's
      publication act, held by DHT peers V0 may never reach. The one POSITIVE
      knowledge claim in the family, [knows_newer], asserts V0 comes to know it
      by validating such a record: [peer_record_valid] (consensus.rs:531-565)
      verifies the BLS signature over the advertised info and that
      publisher==advertised network key, so a validated newer-timestamped record
      is proof that A published beyond r0. It is not knower-local (V0's own view
      does not determine it: at four reachable [N_current] query states it is
      false) and not rigid, so R1/R2 hold; the operative view class has two
      members ([N_lagging] and [N_replayer] with an identical observable
      projection), which [t_discovery] proves with a non-singleton probe.
    - [source_deviated] - "the remote peer holds the newer record and deviates:
      it replays r0, forges invalid records, or the endpoints it exchanged are
      sybils it controls". That is S's own possession and intent. V0 sees only
      the record bytes plus the authenticated transport identity of S, so every
      claim about it in this family is an IGNORANCE claim.

    A positive K at the invalid-PUT state was CONSIDERED AND REJECTED: only the
    deviating world can produce a signature-invalid record, so that view class is
    a singleton and [K_V0(source_deviated)] there would be trivially true -
    exactly the collapsed-K defect this contract's R2 forbids. The
    attributability contrast is carried NON-epistemically instead, by
    [attribution_sound]. *)

open Discovery_model

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

(** SA - kad-query-adopts-max-timestamp-record-yet-currency-stays-unknown
    [security]. During one kad GET for authority A's record:

    (1) [fold_keeps_max] - AG( query_got_r1 -> query_result=r1 ). The strict-max
    arm [Some(tracked) if tracked.info.timestamp < new_record.info.timestamp =>
    *tracked = new_record] inside [process_kad_query_result]'s
    [match &mut query.result] (consensus.rs:1993-1999) makes [KadQuery.result]
    ORDER-INDEPENDENT: if ANY signature-valid response carrying the newer record
    arrived, the query tracks it. With only the [None =>] and [Some(_) => {}]
    arms the query would be first-response-wins, and a fast Byzantine responder
    answering first with an older-but-valid record would decide the outcome.

    (2) [commit_is_max] - AG( (query_closed /\\ query_got_r1) -> known_peers(A)=r1
    ). [close_kad_query] hands exactly [query.result] to [add_discovered_peer]
    (consensus.rs:2015-2024), which after the committee-membership gate
    (manager.rs:787-797) reaches [cache_known_peer] and [known_peers.insert]
    (manager.rs:851-875, the insert at :868). The fold's winner IS what V0
    adopts.

    (3) [knows_newer] - AG( query_got_r1 -> K_V0(newer_record_exists) ). Every
    [GetRecord] result is put through [peer_record_valid] first
    (consensus.rs:1744-1755 and :531-565: BLS signature over the advertised
    info, publisher==advertised network key, multiaddr cap), so a validated
    newer-timestamped record is PROOF that A published beyond r0; an invalid one
    is Fatal-penalized and never reaches the fold (consensus.rs:1756-1771). This
    is the family's one positive K; R2 is discharged in [t_discovery] by a
    contingency test and a non-singleton-class probe.

    (4) [currency_unknown] - AG( (query_closed /\\ query_result=r0 /\\
    ~query_got_r1) -> (~K_V0(~newer_record_exists) /\\ ~K_V0(newer_record_exists))
    ). The query commits on [step.last] (consensus.rs:2008-2012) over whatever
    responders happened to answer; a holder of the newer record that did not
    answer, or a [FinishedWithNoAdditionalRecord] close
    (consensus.rs:1773-1778), is indistinguishable from "no newer record
    exists". So having adopted r0, V0 can neither confirm nor rule out that what
    it adopted is A's current endpoint.

    Reworded from the mined card. The card pictured a Byzantine responder
    DOWNGRADING V0's cached endpoint on the GET route; that is wrong, because a
    kad GET is only ever opened for a BLS key ABSENT from [known_peers]
    ([trigger_missing_authorities], manager.rs:749-755;
    [find_authorities], manager.rs:878-892), so there is no prior entry to roll
    back. The real exposure is "V0 adopts the stale record instead of the fresh
    one it also received", which is what (1) and (2) now say; the one route that
    CAN overwrite an existing entry for a committee authority is the PUT route,
    which is statement SB.

    Mutation pin: {!Discovery_model.No_query_max_fold} deletes the strict-max
    arm, adding (got_r1=false,res=Q_r0) --recv_r1--> (got_r1=true,res=Q_r0) and
    making that state and its closed twin (cache=[C_r0]) reachable; (1) and (2)
    both go false there. (3) and (4) SURVIVE the mutation, so the refutation is
    cleanly attributable to the fold. *)
let s_query =
  let fold_keeps_max =
    Formula.Ag (Formula.Implies (atom Query_got_r1, atom Query_result_r1))
  in
  let commit_is_max =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Query_closed, atom Query_got_r1),
           atom Cache_r1 ))
  in
  let knows_newer =
    Formula.Ag
      (Formula.Implies
         ( atom Query_got_r1,
           Formula.K (Validator.V0, atom Newer_record_exists) ))
  in
  let currency_unknown =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [
               atom Query_closed;
               atom Query_result_r0;
               Formula.Not (atom Query_got_r1);
             ],
           Formula.And
             ( Formula.Not
                 (Formula.K
                    (Validator.V0, Formula.Not (atom Newer_record_exists))),
               Formula.Not
                 (Formula.K (Validator.V0, atom Newer_record_exists)) ) ))
  in
  {
    name = "kad-query-adopts-max-timestamp-record-yet-currency-stays-unknown";
    bucket = Statements.Security;
    formula =
      Formula.conj
        [ fold_keeps_max; commit_is_max; knows_newer; currency_unknown ];
    antecedent = Formula.And (atom Query_closed, atom Query_got_r1);
  }

(** SB - stale-replay-regression-is-gated-only-by-the-local-kad-store
    [security]. An inbound kad PUT carrying a byte-valid but OLDER record for
    committee authority A, relayed by a third party S:

    (1) [no_regression_while_store_fresh] - AG( (put_stale_processed /\\
    kad_store_fresh) -> known_peers(A)=r1 ). The [if
    self.is_newer_record(&record)] conditional (consensus.rs:1916) guards BOTH
    the store put and [add_self_advertised_peer]; the else branch
    (consensus.rs:1932-1937) only trace-logs. Without it the relayed record
    would reach [add_self_advertised_peer] -> committee branch ->
    [cache_known_peer] -> [known_peers.insert], an UNCONDITIONAL overwrite
    (manager.rs:820-821, :851-875). Note the relay is not stopped upstream: the
    [source == advertised] test at manager.rs:822 only guards the NON-committee
    else-branch.

    The [kad_store_fresh] guard is not decoration and is the whole content of
    the retarget below. [is_newer_record] (consensus.rs:1954-1972) compares
    against the LOCAL KAD RECORD STORE, not [known_peers], and its else arm is
    literally [true] - "Also returns true if the record is not found"
    (consensus.rs:1968-1971) - while [KadStore::get] returns [None] once a stored
    record's TTL passes (kad.rs:325-337). The store's only writers are
    [provide_our_data] for OUR OWN key (consensus.rs:569-573) and this accept
    branch (:1917-1922); the GET route never writes it (consensus.rs:1744-1755
    folds into [KadQuery.result], :2015-2024 calls [add_discovered_peer]) and
    neither does the startup restore ([add_known_peer], consensus.rs:438-439 ->
    manager.rs:771-774). So when [known_peers(A)=r1] was learned by a GET or
    restored at startup - exactly the configuration this family's own GET
    episode leaves behind - the store holds nothing for A's key, :1916 evaluates
    TRUE, the older record is stored and cached, and [known_peers(A)] REGRESSES
    to r0. That branch is modelled ([Discovery_model.St_absent]) and
    [t_discovery] asserts its reachability, so this conjunct is scoped rather
    than true by omission.

    (2) [attribution_sound] - AG( put_source_penalized -> source_deviated ). The
    only Fatals on this route are the invalid-record branch
    (consensus.rs:1938-1944) and the missing-publisher branch
    (consensus.rs:1903-1906); a signature-valid stale republish takes neither,
    so no honest restarted replicator is ever scored down. The restraint is
    deliberate and commented as such at consensus.rs:1933-1935.

    (3) [replay_unattributable] - AG( put_stale_processed ->
    (~K_V0(source_deviated) /\\ ~K_V0(~source_deviated)) ). It HAS to be
    restraint rather than detection: [peer_record_valid] (consensus.rs:531-565)
    passes a verbatim replay - it checks the signature, the multiaddr cap and
    publisher==advertised network key, NEVER the source and never the timestamp
    - so the bytes V0 sees are identical whoever relayed them. (The :552-553
    comment overstates: publisher-matching stops key substitution, not replay.)

    Reworded, then RETARGETED. The mined card's [AX (cached_info unchanged /\\
    score unchanged)] cannot be stated as a bare global monotonicity invariant,
    because [close_kad_query] -> [add_discovered_peer] -> [cache_known_peer] ->
    [known_peers.insert] (manager.rs:868) is itself an unconditional overwrite
    with no timestamp compare; the statement is therefore scoped to states
    labelled by the PUT event actually processed, and the "score unchanged" half
    is strengthened into the soundness form (2), which is refutable by its own
    gate. The retarget is the [kad_store_fresh] guard on (1) and the rename from
    [stale-record-replay-cannot-regress-cache-and-is-unattributable]: the
    unguarded form asserted that a stale relayed record can NEVER regress
    [known_peers(A)], which is false of the Rust whenever the local kad store
    has no unexpired entry for A's key, and it was true of the previous model
    only because that model had no store component at all. What survives - and
    is what the code actually buys - is that the regression is impossible while
    the store still holds the newer record, that the honest lagging republisher
    is never penalized for it, and that V0 can never tell the two apart.

    Mutation pins: {!Discovery_model.No_put_freshness_gate} deletes the :1916
    conditional, so the stale-PUT step sets cache := [C_r0] on the [St_fresh]
    half too and [put_stale_processed /\\ kad_store_fresh] holds at a state where
    [known_peers(A)=r1] is false - refuting (1). (The [St_absent] half is NOT
    what refutes it: there the pristine conditional already evaluates true, so
    deleting it changes nothing - which is precisely why the conjunct is guarded.)
    {!Discovery_model.Penalize_stale_record} INDEPENDENTLY refutes (2): it makes
    the stale branch call [process_penalty(source, Fatal)], so in the [N_lagging]
    world [put_source_penalized] holds while [source_deviated] is false. (3)
    survives both, so each refutation is attributable to its own gate. *)
let s_put =
  let no_regression_while_store_fresh =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Put_stale_processed, atom Kad_store_fresh),
           atom Cache_r1 ))
  in
  let attribution_sound =
    Formula.Ag
      (Formula.Implies (atom Put_source_penalized, atom Source_deviated))
  in
  let replay_unattributable =
    Formula.Ag
      (Formula.Implies
         ( atom Put_stale_processed,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom Source_deviated)),
               Formula.Not
                 (Formula.K (Validator.V0, Formula.Not (atom Source_deviated)))
             ) ))
  in
  {
    name = "stale-replay-regression-is-gated-only-by-the-local-kad-store";
    bucket = Statements.Security;
    formula =
      Formula.conj
        [
          no_regression_while_store_fresh;
          attribution_sound;
          replay_unattributable;
        ];
    antecedent = Formula.And (atom Put_stale_processed, atom Kad_store_fresh);
  }

(** SC - peer-exchange-confers-no-identity-and-no-sybil-knowledge [security]. A
    peer-exchange map received from S:

    (1) [identity_needs_signature] - AG( px_identity_bound ->
    signed_record_seen ). [PeerExchangeMap] is a bare UNSIGNED
    [HashMap<BlsPublicKey,(NetworkPublicKey,HashSet<Multiaddr>)>]
    (peers/types.rs:169) intercepted straight off the req-res path
    (consensus.rs:1129-1141), and [process_peer_exchange] binds
    [|(_, (net_key, addrs))|] at manager.rs:624 - DISCARDING the advertised BLS
    key - then only ever writes [self.discovery_peers] (:649). The sole writers
    of a bls<->peer_id binding are [AllPeers::upsert_peer] via
    [cache_known_peer] (manager.rs:867) and via [add_self_advertised_peer]
    (manager.rs:829), both downstream of [peer_record_valid]
    (consensus.rs:531-565, called at :1914 and :1747). So every confirmed
    identity V0 holds for a px-hinted endpoint traces back to a
    signature-validated kad record from that endpoint itself.

    (2) [sybil_unknown] - AG( px_hints_ingested -> (~K_V0(source_deviated) /\\
    ~K_V0(~source_deviated)) ). Nothing in the px message is signed or
    challenged; [eligible_for_discovery] (manager.rs:980-987) screens only
    self-identity, ip validity/bans and dialability, and the reciprocal
    disconnect (consensus.rs:1137-1139) drops the SENDER, not the listed
    endpoints.

    (3) [binding_is_not_distinctness] - AG( (px_hints_ingested /\\
    px_identity_bound) -> ~K_V0(~source_deviated) ). Confirming key ownership is
    not confirming distinctness: [add_self_advertised_peer]
    (manager.rs:813-838) confirms bls<->peer_id only because libp2p proved the
    SENDER owns that transport key, and a sybil the attacker runs owns its own
    keys too. The confirmation is orthogonal to whether the endpoint is a
    distinct real node.

    Retargeted from the mined card. The card's second half -
    "|kad_discovered_candidates| does not decrease as a result of px ingestion"
    - is DROPPED, not modelled, because it is FALSE as stated:
    [process_peers_for_discovery] (manager.rs:992-997) is uncapped, so the pool
    can exceed [max_discovery_peers] from the kad side alone and
    [discovery_heartbeat]'s random excess prune (manager.rs:1000-1058) can then
    evict kad-derived candidates with the px cap (manager.rs:620, :646) fully
    intact; the heartbeat also removes the candidates it selects for dialing.
    The honest px-scoped version would need the whole pool plus the random prune
    in the model, well past the R6 state budget. The surviving halves - px
    content can never confer identity, and can never confer distinctness
    knowledge - are unconditional, and are what (1)-(3) assert. The repair path
    is modelled rather than omitted (R5): a hinted endpoint IS dialed, connects
    and pushes its own signed record, and (1) is proved against that path.

    Mutation pin: {!Discovery_model.Px_binds_identity} deletes the BLS discard,
    so [recv_px] sets bound=true while signed_seen is still false and
    [px_identity_bound] holds at a state where [signed_record_seen] is false -
    refuting (1). (2) and (3) survive it (the px view class is still all three
    worlds), so the refutation is attributable to the discard alone. *)
let s_px =
  let identity_needs_signature =
    Formula.Ag
      (Formula.Implies (atom Px_identity_bound, atom Signed_record_seen))
  in
  let sybil_unknown =
    Formula.Ag
      (Formula.Implies
         ( atom Px_hints_ingested,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom Source_deviated)),
               Formula.Not
                 (Formula.K (Validator.V0, Formula.Not (atom Source_deviated)))
             ) ))
  in
  let binding_is_not_distinctness =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Px_hints_ingested, atom Px_identity_bound),
           Formula.Not
             (Formula.K (Validator.V0, Formula.Not (atom Source_deviated))) ))
  in
  {
    name = "peer-exchange-confers-no-identity-and-no-sybil-knowledge";
    bucket = Statements.Security;
    formula =
      Formula.conj
        [ identity_needs_signature; sybil_unknown; binding_is_not_distinctness ];
    antecedent = atom Px_hints_ingested;
  }

(** The family's statements: the kad GET fold, the inbound-PUT freshness gate,
    and the peer-exchange identity boundary. All three are security. *)
let all = [ s_query; s_put; s_px ]

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
