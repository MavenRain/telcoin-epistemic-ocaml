(** The BATCH_VERDICT statement family, encoded over the
    {!Batch_verdict_model} interpreted system: three statements about what the
    batch author V0 does and does not learn from the quorum wait for one sealed
    batch. All three were mined from telcoin-network, re-grounded against the
    code and then adversarially rewritten where the mined claim turned out to
    be false of the code (see each statement's doc comment). File citations
    refer to Telcoin-Association/telcoin-network.

    Reading guide for the [K] operands. V0 is the only knowledge agent; every
    [K] here is [K (Validator.V0, _)] and every operand is REMOTE state that no
    local read path can recover:
    - [holds(Vj)] is peer Vj's own [NodeBatchesCache] row (handler.rs:252-254).
      V0 has no remote-possession oracle - [get_batch_local_cache] reads the
      LOCAL table (batch_fetcher.rs:58-68) and the consensus-chain fallback at
      :52 needs a committed certificate, impossible for a batch that never
      reached quorum.
    - [permanent_reject(Vj)] is the PEER's own responder-side classification of
      its failure, computed at the remote node by
      [WorkerResponse::into_error_ref] (message.rs:125-155) or by its network
      layer (mod.rs:455-456).
    - [local_verdict(V1)] is whether the peer actually executed its own
      committee check / [validate_batch] (handler.rs:237-246).
    What V0 keeps of a peer answer is only the waiter-level outcome
    ([Ok] / [Rejected] / [Network] stake, quorum_waiter.rs:186-219), so none of
    these operands is a function of V0's view, and each is contingent: it is
    true at some reachable states and false at others. *)

open Batch_verdict_model

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

(** S1 - anti-quorum-leaves-peer-possession-unknown [safety]. At every
    reachable state where the author's quorum wait ended in [AntiQuorum] AND
    the author folded a retry-exhausted [WaiterError::Network] outcome for peer
    V1, V0 neither knows that V1 holds a [NodeBatchesCache] row for this batch
    nor knows that it does not:
    AG( (verdict=anti_quorum /\\ exhausted(V1)) ->
        ~K_V0(holds(V1)) /\\ ~K_V0(~holds(V1)) ).

    (1) ~K_V0(holds(V1)) - V0 cannot conclude V1 stored the batch. The peer
    writes its [NodeBatchesCache] row at handler.rs:252-254 BEFORE producing
    the ack at :262, so a peer that completed the write and then lost all three
    acks in transport is folded by the author as [WaiterError::Network] exactly
    like a peer that never stored anything (quorum_waiter.rs:91, 101-115).

    (2) ~K_V0(~holds(V1)) - V0 also cannot rule possession out.
    [WaiterError::Network(deliver)] carries only the stake
    (quorum_waiter.rs:115) and the fold at :216-218 decrements
    [available_stake] and discards the error entirely; there is no
    remote-possession oracle (batch_fetcher.rs:58-68).

    ANTECEDENT REPAIR (the mined card was FALSE as written). The card claimed
    G( anti_quorum -> ~K(holds(V1)) /\\ ~K(~holds(V1)) ) with NO restriction on
    V1's leg. That is false of the code and of any faithful model: an
    [AntiQuorum] can also be produced by a leg that PERMANENTLY rejected
    (quorum_waiter.rs:212-215 followed by the :241 check), and a permanent
    rejection provably PRECEDES any store (handler.rs:237-246 rejects before
    the insert at :252), so at those anti-quorum states V0 DOES know
    ~holds(V1) and the second conjunct is refuted. Conjoining [exhausted(V1)]
    into the antecedent is the exact repair.

    R3 ignorance witnesses (both conjuncts, one colliding pair, both worlds
    reachable and sharing V0's view): world A = (leg1 = Exh_possess,
    leg2 = Rej_verdict, Anti) - V1 ran handler.rs:244-262 to completion, row
    written, primary told, and all three acks were lost in transport, so the
    author retried at :108-111 and folded [Network] at :115; world B =
    (leg1 = Exh_transport, leg2 = Rej_verdict, Anti) - the report never got a
    response out of V1 at all: [send_request] or the response channel failed and
    handle.rs:175-176 propagated a non-[RPCError] [NetworkError] with [?], which
    the catch-all arm at quorum_waiter.rs:101-112 retried three times before
    :115. [holds(V1)] differs; V0's view (Saw_exhausted, Saw_reject, Anti) is
    identical. The same pair exists with leg2 exhausted.

    Mutation pin - ONE gate, and the fix that made that honest.
    {!Batch_verdict_model.No_peer_store_before_ack} deletes handler.rs:252-254,
    so [Exh_possess] disappears and every reachable exhausted leg is
    possession-free ([Exh_transport]); [holds(V1)] is then false throughout the
    view class, K_V0(~holds(V1)) becomes TRUE and conjunct 2 fails - the
    statement flips.

    {!Batch_verdict_model.No_recoverable_class} is a NEGATIVE CONTROL, not a
    pin, and an earlier revision of this family had that backwards. It claimed
    the gate refuted conjunct 1 because deleting handle.rs:186-188 left
    [Exh_possess] as the only exhaustion value. That was an artefact of a scope
    cut, not of the code: the deleted arm lives inside the [WorkerResponse]
    match at handle.rs:177-189, which is reached only when a response came back,
    because [send_request] and the response channel are unwrapped with [?] at
    :175-176. A dial failure, a dropped connection or an outbound timeout
    therefore never touches the arm, still exhausts through
    quorum_waiter.rs:101-115 ("Transient errors are retried ... This includes
    transport failures", :72-83), and still leaves the peer holding nothing. In
    the real system conjunct 1 SURVIVES that deletion, so the model now carries
    [Exh_transport] on [leg1] and S1 is asserted to keep proving under
    {!Batch_verdict_model.No_recoverable_class}
    ([t_batch_verdict_mutation.ml], attribution controls). *)
let s1 =
  let window = Formula.And (atom Verdict_anti, atom Exhausted_v1) in
  let unknown_possession =
    Formula.Not (Formula.K (Validator.V0, atom Holds_v1))
  in
  let unknown_absence =
    Formula.Not (Formula.K (Validator.V0, Formula.Not (atom Holds_v1)))
  in
  {
    name = "anti-quorum-leaves-peer-possession-unknown";
    bucket = Statements.Safety;
    formula =
      Formula.Ag
        (Formula.Implies
           (window, Formula.And (unknown_possession, unknown_absence)));
    antecedent = window;
  }

(** S2 - accepted-report-implies-known-peer-possession [safety].

    (A) AG( verdict=quorum -> holds(V1) /\\ holds(V2) ) - whenever the quorum
    wait returns [Ok(())], both peers whose acks the author folded hold the
    batch. Reaching the threshold needs [total_stake >= 3]
    (quorum_waiter.rs:166-170, 187-190) against the author's own seed of 1
    (:167) with [EQUAL_VOTING_POWER] = 1 over 4 authorities (committee.rs:25,
    247-252, 261-263, 508), i.e. two folded peer accepts; each accept is a
    [WorkerResponse::ReportBatch], produced at mod.rs:490-491 only on [Ok(())]
    from [process_report_batch], which returns [Ok] only after
    handler.rs:252-254 wrote the row.

    (B) AG( accepted(V1) -> K_V0(holds(V1)) ) - whenever the author has folded
    an [Ok(stake)] for peer V1 it KNOWS V1 holds a [NodeBatchesCache] row,
    because the peer's ordering gate is strict: [validate_batch]
    (handler.rs:244-246), then [store.insert::<NodeBatchesCache>] (:252-254),
    then [report_others_batch] (:257-260), then [Ok] (:262). handle.rs:177-178
    maps [WorkerResponse::ReportBatch] to [Ok(())] and quorum_waiter.rs:93
    folds it as [Ok(deliver)]. No branch acks before the write.

    RETARGET NOTE. This statement replaces the mined card
    "fatal-db-halt-under-unknown-peer-possession", which was DROPPED for model
    fit rather than falsity: honestly encoding it needs an own-write component
    and a builder-liveness component that this family's interpreted system does
    not represent, and its liveness conjunct would have been manufactured on a
    component added solely to carry it (R6/R8). S2 lives natively on the
    quorum-verdict model.

    R1/R2 non-degeneracy. [holds(V1)] is peer V1's own storage state, not a
    component of V0's view (which carries only the waiter-level outcome,
    quorum_waiter.rs:186-219) and not derivable from anything local. It is not
    rigid: it is FALSE at both reachable rejected states and at every
    [Exh_transport] state, so [~K_V0(holds(V1))] is satisfiable. The view class
    at the operative state (leg1 = Ack_possess, leg2 = Exh_nopossess, Waiting),
    V0-view (Saw_accept, Saw_exhausted, Waiting), is non-singleton: it also
    contains (leg1 = Ack_possess, leg2 = Exh_possess, Waiting), which is V2
    having stored the batch and lost its acks rather than V2's own insert
    failing - both reachable, disagreeing on [holds(V2)].

    Mutation pin: {!Batch_verdict_model.No_peer_store_before_ack} deletes
    handler.rs:252-254, replacing every [Pending -> Ack_possess] with
    [Pending -> Ack_nopossess] (the peer still validates and acks, it just
    holds nothing), so at the quorum state [holds(V1) /\\ holds(V2)] is false
    (conjunct A refuted) and at every accept state K_V0(holds(V1)) is false
    (conjunct B refuted). {!Batch_verdict_model.No_recoverable_class} leaves it
    untouched, so the refutation is cleanly attributable. *)
let s2 =
  let quorum_implies_both_hold =
    Formula.Ag
      (Formula.Implies
         (atom Verdict_quorum, Formula.And (atom Holds_v1, atom Holds_v2)))
  in
  let accept_implies_known_possession =
    Formula.Ag
      (Formula.Implies
         (atom Accepted_v1, Formula.K (Validator.V0, atom Holds_v1)))
  in
  {
    name = "accepted-report-implies-known-peer-possession";
    bucket = Statements.Safety;
    formula =
      Formula.And (quorum_implies_both_hold, accept_implies_known_possession);
    antecedent = atom Accepted_v1;
  }

(** S3 - quorum-rejected-implies-known-permanent-but-opaque-verdict [security].

    (A) AG( verdict=quorum_rejected ->
            K_V0(permanent_reject(V1) /\\ permanent_reject(V2)) ) - whenever the
    seal ends in [QuorumRejected] the author KNOWS that both peers whose
    rejections produced it answered with a PERMANENT application-level error,
    never with a transient responder-side condition. [rejected_stake] is
    incremented on exactly one event, [WaiterError::Rejected]
    (quorum_waiter.rs:212-215), produced only for [NetworkError::RPCError] and
    with NO retry (:94-100); [report_batch] maps a response to [RPCError] only
    for [WorkerResponse::Error] and sends [RecoverableError] to [RPCRetryable]
    instead (handle.rs:185-188); and [into_error_ref] puts every transient
    responder-side condition ([Internal], [Timeout], [Network], [StreamClosed],
    [DBInsert], [DBCommit], [DBRead], [StdIo]) into [RecoverableError]
    (message.rs:126-137). With 4 authorities of unit power the threshold is 3
    and [max_rejected_stake] = (3+1)-3 = 1 (committee.rs:247-252,
    quorum_waiter.rs:166-170), so the break at :236-239 needs two
    permanent-class rejections.

    (B) AG( verdict=quorum_rejected -> ~K_V0(local_verdict(V1)) ) - yet the
    author does NOT know that peer V1 actually ran its own committee check /
    [validate_batch]. [WaiterError::Rejected(deliver)] carries only the stake
    (quorum_waiter.rs:99) and the fold at :212-215 keeps only the stake, so the
    permanent-error string that would distinguish a
    [BatchValidation]/[NonCommitteeBatch] verdict (handler.rs:237-246) from the
    responder's unknown-requester race (consensus.rs:1149, 1174-1177 ->
    mod.rs:455-456) never enters the author's state.

    RETARGET NOTE (the mined card's central quantifier was FALSE). The card
    claimed the strictly stronger K_V0( at least two peers each locally
    executed [validate_batch] ), justified by "the permanent
    [WorkerResponse::Error] variants are produced only inside
    [process_report_batch]". They are not: network/mod.rs:455-456 turns
    [NetworkEvent::Error] into a permanent [WorkerResponse::Error], and that
    event is emitted by crates/network-libp2p/src/consensus.rs:1174-1177 when
    the responder cannot map the requesting [PeerId] to a BLS key - no batch
    verdict is computed at all - and handle.rs:179-184 adds two more
    verdict-free [RPCError] routes (wrong response type). The entailed half is
    kept as conjunct A (both rejections were permanent-CLASS) and the
    unentailed half becomes conjunct B, an ignorance claim.

    R1/R2/R3 non-degeneracy, one colliding pair discharging both. Operative
    state (leg1 = Rej_verdict, leg2 = Rej_verdict, Rejected); the second world
    in the same V0-view class (Saw_reject, Saw_reject, Rejected) is
    (leg1 = Rej_unknown, leg2 = Rej_verdict, Rejected), where V1's permanent
    error came from consensus.rs:1174-1177 so V1 never ran [validate_batch].
    Both reachable, identical V0-view; [permanent_reject(V1)] is true in both
    (conjunct A survives) while [local_verdict(V1)] differs (conjunct B's
    ignorance). Conjunct A's [K] is not rigid either: the conjunction is FALSE
    at the quorum state, at every anti-quorum state and at every timeout state,
    so [~K_V0(permanent_reject(V1) /\\ permanent_reject(V2))] is satisfiable.

    Mutation pin: {!Batch_verdict_model.No_recoverable_class} deletes the
    handle.rs:186-188 [RecoverableError] arm, so a peer's own
    [NodeBatchesCache] write failure (handler.rs:252-254 -> [Internal] ->
    [RecoverableError], message.rs:128-137) arrives as [RPCError]: V2's
    [Pending -> Exh_nopossess] resolution becomes [Pending -> Rej_transient],
    and ONE such leg beside a genuine permanent rejection on V1 already reaches
    [rejected_stake] = 2 > [max_rejected_stake] = 1 and breaks [QuorumRejected]
    (quorum_waiter.rs:170, 236-239) at a state where
    [permanent_reject(V1) /\\ permanent_reject(V2)] is FALSE - false at the very
    state, so conjunct A's [K] fails there. The gate is genuinely load-bearing
    for this conjunct: [rejected_stake] has exactly one source
    (quorum_waiter.rs:212-215), fed only by [NetworkError::RPCError] (:94-100),
    and with the arm deleted every responder-classified [RecoverableError]
    reaches it. {!Batch_verdict_model.No_peer_store_before_ack} leaves the two
    reachable rejected states unchanged, so the refutation is cleanly
    attributable. *)
let s3 =
  let known_permanent_class =
    Formula.Ag
      (Formula.Implies
         ( atom Verdict_rejected,
           Formula.K
             ( Validator.V0,
               Formula.And (atom Permanent_reject_v1, atom Permanent_reject_v2)
             ) ))
  in
  let unattributable_verdict =
    Formula.Ag
      (Formula.Implies
         ( atom Verdict_rejected,
           Formula.Not (Formula.K (Validator.V0, atom Local_verdict_v1)) ))
  in
  {
    name = "quorum-rejected-implies-known-permanent-but-opaque-verdict";
    bucket = Statements.Security;
    formula = Formula.And (known_permanent_class, unattributable_verdict);
    antecedent = atom Verdict_rejected;
  }

(** The family's statements: two safety, one security, all three on the single
    47-state quorum-verdict model and each pinned by at least one gate. *)
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
