(** The WORKER_STREAM_QUOTA statements: what the worker's batch-stream
    admission accounting guarantees about equal treatment by identity, about
    the pending -> serving handoff, and about what a shed sync requester does
    and does not learn. Encoded over {!Worker_stream_quota_model}; every file
    citation was opened in the telcoin-network checkout at HEAD 0c59c15b.

    READING GUIDE FOR THE K OPERANDS. The only knowledge agent is V2, the
    victim requester on the sync path, and both of its positive [K] operands
    are facts about state V2 cannot see.

    - [K_V2 (~read_request(R,V2))] - "the responder never decoded the digest
      set of the stream it just refused". [Resp_read_v2_request] is a
      RESPONDER-side bit (network/mod.rs:728-739 is reached only on the
      admitted arm), and it is deliberately NOT a projection of V2's view: the
      model's [v2phase_of] maps {!Worker_stream_quota_model.At_shed} and
      {!Worker_stream_quota_model.At_shed_read} to the same [Ph_denied],
      because both are the identical [SyncFrame::Deny(DenyReason::AtCapacity)]
      frame on the wire. The operand is not rigid either: it is FALSE at every
      reachable served state, where R has read the frame. The card this was
      mined from wrote the operand as [~K_R(requested_digests(V2))]; it is
      flattened here because R either decoded the frame or did not, so the
      inner [K_R] would be a projection of R's own view and the contract
      forbids resting anything on such a [K]. The flattened atom says exactly
      what the nested form meant.
    - [K_V2 (pool_exhausted(R))] - "the responder's global permit pool is
      full", i.e. OTHER peers are holding its capacity. This is a fact about
      V1's possession and R's semaphore; V2 sees neither. It is not rigid: it
      is false at the initial state and at every lightly loaded state.

    The matching ignorance is that the SAME [Deny] does not tell V2 which cap
    tripped once V2 is itself at the per-peer cap: [try_admit_sync] returns
    [None] from the semaphore (network/mod.rs:235) and from the per-peer check
    (network/mod.rs:239-243) alike, and [DenyReason] does not distinguish them
    - its own doc comment reads "The responder is at its concurrency cap
    (global or per-peer) and is shedding load"
    (network-libp2p/src/sync/frame.rs:48-51). *)

open Worker_stream_quota_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - per-peer-stream-cap-reserves-capacity-for-every-peer [fairness].

    CONJUNCT A (the quota). No peer ever holds more of the responder's
    batch-stream slots than [MAX_PENDING_REQUESTS_PER_PEER]
    (network/mod.rs:60-65), where "holds" counts every global permit the peer
    is responsible for - pending legacy requests, legacy serves and sync
    exchanges alike, which is precisely the sum [peer_in_flight] computes
    (network/mod.rs:206-216). The flooder's half of this is enforced by
    [try_admit_legacy]'s refusal at network/mod.rs:280-289 and the victim's by
    [try_admit_sync]'s mirror at network/mod.rs:239-243. Stated for both peers
    because the guarantee the code's own doc comment makes is universal ("no
    single peer can fill all global slots ... and starve its peers"); only the
    flooder's half is deleted by the mutation that pins this statement, and the
    victim's half is enforced by the [try_admit_sync] check that this family
    deliberately never mutates - that intactness IS the sibling-path argument
    for the deletion.

    CONJUNCT B (draining the pool takes more than one identity). Whenever the
    responder's global pool is exhausted, at least two DISTINCT requesters are
    holding it. This is the constant's own documented purpose - "no single peer
    can fill all global slots ([MAX_CONCURRENT_BATCH_STREAMS]) and starve its
    peers" (network/mod.rs:60-64) - and the general form is that exhaustion
    needs at least [ceil(pool_cap / per_peer_cap)] resolved identities: three
    in the real code (5 and 2), two in this model (3 and 2), which is what two
    modelled requesters can witness.

    WHAT THIS STATEMENT DELIBERATELY DOES NOT CLAIM. It does NOT claim that a
    requester holding nothing is always admitted. {!Validator.t} is a ten-node
    committee, so a responder faces nine requesters against five permits, and
    three other identities at their caps deny an idle peer. The candidate card
    asserted that non-starvation step ("a fresh request from the third peer is
    always admitted on the next step"), which is arithmetic for a
    three-requester committee; it is false at this committee size and was
    dropped rather than encoded against a two-peer model that would have made
    it look true.

    MUTATION PIN. {!Worker_stream_quota_model.No_legacy_per_peer_cap} deletes
    network/mod.rs:280-289 and adds legacy admissions above the cap: the
    flooder reaches three concurrent permits, refuting conjunct A directly, and
    those three permits are the whole pool held by ONE identity, refuting
    conjunct B. No sibling repairs it: [try_admit_sync]'s identical check gates
    only the sync path and a legacy flood never traverses it, the global
    semaphore is peer-blind, and [cleanup_stale_pending_requests]
    (network/mod.rs:803-809, modelled) only expires entries and refuses no
    admission. *)
let s_1 =
  let quota =
    Formula.Ag
      (Formula.And
         ( Formula.Not (atom V1_over_peer_cap),
           Formula.Not (atom V2_over_peer_cap) ))
  in
  let two_distinct_holders =
    Formula.Ag
      (Formula.Implies
         ( atom Pool_exhausted,
           Formula.And (atom V1_holds_any, Formula.Not (atom V2_idle_at_r)) ))
  in
  {
    name = "per-peer-stream-cap-reserves-capacity-for-every-peer";
    bucket = Statements.Fairness;
    formula = Formula.And (quota, two_distinct_holders);
    antecedent = atom Pool_exhausted;
  }

(** S2 - serving-legacy-stream-stays-charged-to-its-peer [security].

    CONJUNCT A (no vanishing count). Every global permit the flooder holds for
    a legacy stream is charged to the flooder in the responder's own
    accounting. A legacy request leaves [pending_batch_requests] the instant
    the requester opens its stream, yet its [OwnedSemaphorePermit] lives on
    inside the removed [PendingBatchStream] (network/mod.rs:94-96), so the two
    maps must be updated as one: [begin_serving_legacy] (network/mod.rs:323-332)
    does the [remove] and the [LegacyStreamGuard::admit] under a single
    [pending.lock()], and the guard's [Drop] (network/mod.rs:190-200) releases
    the tally when the serve ends. This conjunct says the responder is never in
    the state that pairing exists to forbid.

    CONJUNCT B (the consequence). A peer already serving
    [MAX_PENDING_REQUESTS_PER_PEER] streams never simultaneously holds a
    pending admission slot. This is the concrete attack the CVE describes: keep
    re-arming pending slots while earlier streams are still being served, and
    end up holding every global permit. Note conjunct B is stated over the
    peer's TRUE serving load (charged or not), so a deletion that merely hides
    the load from R still refutes it.

    MUTATION PIN. {!Worker_stream_quota_model.No_serving_guard} deletes
    network/mod.rs:330 so the handoff drops the tally while the permit lives
    on. Conjunct A fails on the first stream open, and the flooder then walks
    to two uncharged serves plus a fresh pending request, refuting conjunct B.
    The in-tree regression tests name the defect: [// Regression guard for
    GHSA-h9fv-qwvh-jv37] (network/mod.rs:860-863, :907-910). No sibling keeps a
    serving stream chargeable: the surviving permit is peer-blind (and is kept
    in the model, so the mutation is no stronger than the real defect),
    [sync_stream_peers] counts sync streams only (network/mod.rs:353-359),
    [cleanup_stale_pending_requests] retains over a map the entry has already
    left (network/mod.rs:803-809), and [SEND_STREAM_TIMEOUT] (handler.rs:39,
    applied at handler.rs:299 and :363) bounds one serve's duration, not a
    peer's count. *)
let s_2 =
  let charge_never_vanishes = Formula.Ag (Formula.Not (atom V1_uncounted_serve)) in
  let no_rearm_while_serving =
    Formula.Ag
      (Formula.Not (Formula.And (atom V1_serving_at_cap, atom V1_pending_any)))
  in
  {
    name = "serving-legacy-stream-stays-charged-to-its-peer";
    bucket = Statements.Security;
    formula = Formula.And (charge_never_vanishes, no_rearm_while_serving);
    antecedent = atom V1_serving_at_cap;
  }

(** S3 - sync-shed-conceals-request-and-saturation [security].

    CONJUNCT A (the shed discloses nothing). Whenever the responder answers the
    victim's stream with [Deny(DenyReason::AtCapacity)], the victim KNOWS the
    responder never decoded that stream's request frame. The shed arm
    (network/mod.rs:704-722) writes the [Deny] and closes; the
    [read_frame::<_, WorkerSyncRequest>] that would disclose the digest set is
    at :728-739, strictly after, and is reached only with a permit in hand.
    That line order is the whole guarantee, and it is not undercut elsewhere:
    :712 is the ONLY [SyncFrame::Deny] write in the worker crate, because the
    serve path writes only [Ack], [Data], [End] and
    [Err(SyncFrameError::Internal)] (handler.rs:332-390). A [Deny] on a worker
    sync stream is therefore always a pre-read shed.
    The knowledge is genuine and not a re-reading of V2's own view: the model
    carries a distinct responder-side arm {!Worker_stream_quota_model.At_shed_read}
    that produces the byte-identical [Deny], and V2's view maps it to the same
    [Ph_denied]. It is contingent, not rigid: at every served state the
    responder HAS read the frame, so the operand is false there.

    CONJUNCT B (a denial teaches the victim about its peers). A victim denied
    while it is UNDER its own per-peer cap knows the responder's global pool is
    exhausted - a fact about V1's possession and R's semaphore that V2 can
    observe by no other means. [try_admit_sync] can only have failed at
    [semaphore.clone().try_acquire_owned().ok()?] (network/mod.rs:235) when the
    per-peer branch at :239-243 could not have fired.

    CONJUNCT C (and nothing more than that). Once the victim is AT its own
    per-peer cap the same [Deny] is ambiguous in both directions: it knows
    neither that the pool is exhausted nor that it is not. Both causes produce
    the identical frame - [DenyReason]'s own doc comment says so, "The
    responder is at its concurrency cap (global or per-peer) and is shedding
    load" (network-libp2p/src/sync/frame.rs:48-51) - and the requester-side
    classifier keeps no more than the reason string
    ([SyncFrame::Deny(reason) => Err(SyncAttempt::Failed(NetworkError::
    RPCRetryable(format!("peer denied sync batch request: {reason:?}"))))],
    handle.rs:450-453).

    SCOPE, STATED. The claim is about the SYNC protocol. On the legacy path R
    decodes the digest set before admitting - the destructure at
    network/mod.rs:438-446 and the [generate_batch_request_id] hash at :577
    (handle.rs:816-821) both precede the [try_admit_legacy] call at :578 - so a
    REFUSED LEGACY request has already disclosed its digests. That asymmetry is
    real and is why this statement is protocol-scoped rather than stated about
    everything a responder can learn.

    MUTATION PIN. {!Worker_stream_quota_model.No_pre_read_sync_shed} deletes
    the early shed block at network/mod.rs:704-722, so a refused stream falls
    through to the request-frame read at :728-739 and is denied afterwards. The
    wire answer is unchanged, so V2's view is unchanged and the denied states
    remain reachable - but R now holds the digest set of a request it refused,
    so conjunct A's [K] fails. No sibling gives R those digests on the pristine
    sync path: the [Deny] frame carries only a [DenyReason]
    (network-libp2p/src/sync/frame.rs:48-54), a denied sync requester does not
    retry the same peer over legacy ([Failed], not [Unsupported], is what
    [Deny] maps to - handle.rs:450-453 against handle.rs:327-340), and worker
    gossip carries an author's single digest, not a requester's set
    (network/message.rs:10-15). *)
let s_3 =
  let shed_discloses_nothing =
    Formula.Implies
      ( atom V2_denied,
        Formula.K (Validator.V2, Formula.Not (atom Resp_read_v2_request)) )
  in
  let denial_reveals_saturation =
    Formula.Implies
      ( Formula.And (atom V2_denied, Formula.Not (atom V2_at_own_cap)),
        Formula.K (Validator.V2, atom Pool_exhausted) )
  in
  let cause_stays_hidden =
    Formula.Implies
      ( Formula.And (atom V2_denied, atom V2_at_own_cap),
        Formula.And
          ( Formula.Not (Formula.K (Validator.V2, atom Pool_exhausted)),
            Formula.Not
              (Formula.K (Validator.V2, Formula.Not (atom Pool_exhausted))) ) )
  in
  {
    name = "sync-shed-conceals-request-and-saturation";
    bucket = Statements.Security;
    formula =
      Formula.Ag
        (Formula.conj
           [ shed_discloses_nothing; denial_reveals_saturation; cause_stays_hidden ]);
    antecedent = atom V2_denied;
  }

(** The family's statements. *)
let all = [ s_1; s_2; s_3 ]

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
