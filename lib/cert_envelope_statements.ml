(** The CERT_ENVELOPE statement family, encoded over the
    {!Cert_envelope_model} interpreted system. All three statements were mined
    from telcoin-network, re-grounded against the code at HEAD 0c59c15b, and
    are stated here in the form that survived that pass. File citations refer
    to Telcoin-Association/telcoin-network.

    The common shape. V1 runs the ONLY gated batch ingress -
    [process_report_batch] calls [validate_batch] before storing
    (handler.rs:231-263, the call at :245). V2 is a remote node that reaches
    possession through routes that never validate at all: the gossip prefetch
    insert (handler.rs:201-208), the [is_certified] sync store
    (primary.rs:104-111) and [fetch_for_primary] (batch_fetcher.rs:186-200).
    [validate_batch] has exactly two production call sites in the whole tree
    (handler.rs:245, primary.rs:108), so V2's ignorance of provenance is real
    and not a modelling convenience.

    Reading guide for the K operands. Each positive [K (V1, _)] targets a fact
    about a REMOTE node - V2's executed block, V2's engine abort, V2's stored
    payload - and no [v2] component appears in ANY V1 view constructor
    ({!Cert_envelope_model.View_v1_unseen} / [View_v1_seen (verdict, content)]),
    so no operand is knower-local (R1). The licence for the transfer from V1's
    LOCAL verdict to a REMOTE node's copy is content addressing: [Batch::digest]
    hashes the entire serialization, including [transactions] and
    [base_fee_per_gas], skipping only [received_at]
    (types/src/worker/sealed_batch.rs:63-89, :116-124), and every fetch path
    re-derives the digest and matches it against what was requested
    (handle.rs:498-523, batch_fetcher.rs:222-232). No operand is rigid either -
    each is FALSE at a reachable state where the bad bytes entered V2 through
    an ungated route while V1 never saw them at all.

    The symmetric [~K (V2, _)] in S3 is the converse: V2's view carries no [v1]
    component because the ungated ingresses transmit no provenance and a
    rejection elsewhere is a purely local peer penalty (error.rs:76-104) with
    no negative cache anywhere. *)

open Cert_envelope_model

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

(** S1 - accepted-batch-implies-known-uniform-execution-base-fee [security].
    If V1's gated [ReportBatch] ingress accepted and stored the batch behind
    [D], then:

    (a) GATE: the bytes behind [D] carry the epoch base fee [f_epoch] -
    AG( accepted_1(D) -> ~content(D)=forged_fee ). [validate_basefee] rejects
    any batch whose [base_fee_per_gas] differs from the validator's per-epoch
    [u64] snapshot (validator.rs:188-195, called at :80). That snapshot is not
    local taste: it is derived on every epoch entry as a pure function of the
    previous epoch's on-chain closing state (types/src/gas_accumulator.rs:38-51)
    and handed to the validator at node/manager/node/start_epoch.rs:376-379,
    :422-424, so every honest validator of the epoch holds the SAME number.

    (b) KNOWN UNIFORM FEE: V1 knows that any node executing [D] produces a
    block charging [f_epoch] - AG( accepted_1(D) -> K_V1( AG( executed_2(D) ->
    ~exec_fee_2(D)<>f_epoch ) ) ). This is a fact about a REMOTE node's
    execution act and is nowhere in V1's own view. Execution copies the fee
    verbatim and re-derives nothing: payload_builder.rs:146-148
    ([let base_fee_per_gas = batch.base_fee_per_gas]) -> evm/config.rs:131-138
    ([basefee: payload.base_fee_per_gas]) -> evm/block.rs:992
    ([base_fee_per_gas: Some(evm_env.block_env.basefee())]). The transfer from
    V1's local verdict to a remote executor's header is licensed by content
    addressing (sealed_batch.rs:63-89, :116-124; handle.rs:506-516).

    (c) IGNORANCE: and yet V1 does not know whether any remote node has
    executed [D] at all - AG( accepted_1(D) -> ~K_V1(executed_2(D)) /\\
    ~K_V1(~executed_2(D)) ). V1's worker-task-local state after
    [process_report_batch] is exactly (bytes, verdict, store insert, notify own
    primary) (handler.rs:231-263); nothing reports a remote node's store or its
    engine's progress back, and the gossip prefetch is silent and best-effort,
    skipped outright when admission declines (handler.rs:167-187).

    R2/R3 witnesses. At the operative state w1 = (Well_formed, Resolved
    Accepted, Idle, Pending) the V1-view class [View_v1_seen (Accepted,
    Well_formed)] also contains w2 = (Well_formed, Resolved Accepted, Executed,
    Committed): identical V1 view, opposite [executed_2(D)]. That single pair
    discharges the non-singleton test for (b) and both halves of (c).

    Mutation pin: {!Cert_envelope_model.No_basefee_gate} adds (Authored
    Forged_fee, Unseen, v2, cert) -> (Authored Forged_fee, Resolved Accepted,
    v2, cert). Conjunct (a) then fails at every fee-forged accepted state, and
    (b) fails because the class [View_v1_seen (Accepted, Forged_fee)] contains
    (Forged_fee, Accepted, Executed, Committed) where the executed fee is off
    epoch. The antecedent stays reachable under the mutation, so the verdict is
    [Refuted], not [Vacuous_antecedent].

    Cross-refutation, reported honestly: conjunct (c) ALSO fails under
    {!Cert_envelope_model.No_recovery_gate}, because an accepted
    [Unrecoverable] batch can only ever reach [Halted], never [Executed], so
    [K_V1(~executed_2(D))] becomes TRUE across the whole (Accepted,
    Unrecoverable) class. That is a true fact about the model, not a defect:
    the recovery gate is genuinely load-bearing for V1's ignorance as well. S1
    is pinned on the basefee gate, which is the gate conjuncts (a) and (b)
    name. *)
let s1 =
  let gate =
    Formula.Ag
      (Formula.Implies (atom V1_accepted, Formula.Not (atom Content_forged_fee)))
  in
  let known_uniform_fee =
    Formula.Ag
      (Formula.Implies
         ( atom V1_accepted,
           Formula.K
             ( Validator.V1,
               Formula.Ag
                 (Formula.Implies
                    (atom V2_executed, Formula.Not (atom Exec_fee_off_epoch)))
             ) ))
  in
  let ignorance =
    Formula.Ag
      (Formula.Implies
         ( atom V1_accepted,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom V2_executed)),
               Formula.Not
                 (Formula.K (Validator.V1, Formula.Not (atom V2_executed))) ) ))
  in
  {
    name = "accepted-batch-implies-known-uniform-execution-base-fee";
    bucket = Statements.Security;
    formula = Formula.And (gate, Formula.And (known_uniform_fee, ignorance));
    antecedent = atom V1_accepted;
  }

(** S2 - accepted-batch-implies-known-recovery-safe-execution [liveness]. If
    V1's gated ingress accepted the batch behind [D], then:

    (a) GATE: [D] contains no transaction that fails signer recovery -
    AG( accepted_1(D) -> ~content(D)=unrecoverable ). [decode_transactions]
    [par_iter]s [recover_and_validate] and COLLECTS INTO a
    [BatchValidationResult], so ONE unrecoverable transaction fails the whole
    batch (validator.rs:147-156 with helper :209-215, called at :70); the
    resulting [RecoverTransaction] error carries [Penalty::Severe]
    (error.rs:88-91).

    (b) KNOWN NO REMOTE HALT: V1 knows that no remote node's engine aborts in
    the recovery phase on [D] - AG( accepted_1(D) -> K_V1( AG(~halted_2(D)) ) ).
    The validator and the engine run the SAME predicate on the SAME bytes:
    validator.rs:213 [recover_signed_transaction] -> txn_pool.rs:369-373 ->
    [reth_recover_raw_transaction::<TransactionSigned>], and the engine's phase
    1 at tn-reth/src/lib.rs:763-780 calls the same function and propagates the
    first failure with [?]. That error is fatal, not tolerated:
    payload_builder.rs:167-175 [?] -> [execute_consensus_output] returns [Err]
    -> engine/src/lib.rs:262-266 [?] exits the engine run loop -> the engine was
    spawned as a CRITICAL task (node/src/engine/inner.rs:74-87) whose contract
    is "when the task resolves, other tasks will shutdown"
    (types/src/task_manager.rs:170-179).

    (c) RESOLUTION IS NEVER THE RECOVERY ABORT: once a remote node HOLDS the
    bytes behind [D] and [D]'s certificate is committed, that node's engine
    inevitably resolves the batch, and its resolution is never the signer-
    recovery abort - AG( (accepted_1(D) /\\ holds_2(D) /\\ committed(D)) ->
    AF (executed_2(D) \\/ aborted_2(D)) ). The engine builds a block per batch
    of a committed output (payload_builder.rs:139-184) and cannot silently skip
    one: the only per-batch escapes on that path are the [?]s, each of which
    ends the run loop (engine/src/lib.rs:264). Because V1's gate re-runs the
    engine's own recovery predicate (validator.rs:209-215 ->
    txn_pool.rs:369-373 -> [reth_recover_raw_transaction], the same function the
    engine calls at tn-reth/src/lib.rs:769), a batch V1 accepted cannot be the
    one that trips phase 1. NO K wrapper here: V1's view carries no [cert] and
    no [v2] component, so [K_V1] of this is FALSE and is deliberately not
    asserted.

    WEAKENED AND RETARGETED (this is the R5 repair of an earlier revision). The
    conjunct used to read AG( (accepted_1(D) /\\ committed(D)) -> AF
    executed_2(D) ) - "a committed accepted batch inevitably becomes a block".
    That was true only of a model in which the recovery abort was the ONLY
    failure branch and delivery was forced. Both halves are false of the Rust:

    - [execute_consensus_output] has many content-independent fatal exits
      besides recovery - [ConsensusOutputUnevenBatches] (payload_builder.rs:
      56-76), [UnknownAuthority] (:104-107), [NextBlockDigestMissing]
      (:140-142), [execute_payload] (:167-175), [finish_executing_output]
      (:189-192), [finalize_block] (:193-194), and within
      [build_block_from_batch_payload] the [builder_for_next_block] /
      [apply_pre_execution_changes] failures (tn-reth/src/lib.rs:756-761), the
      non-[InvalidTx] arm (:797-798) and [builder.finish] (:802-803). The model
      now carries them all as {!Cert_envelope_model.Aborted}, always enabled
      from [(Holds, Committed)], so the old unqualified [AF executed_2(D)] is
      now FALSE in the model too - {!T_cert_envelope} asserts exactly that.
    - delivery is not guaranteed: [fetch_for_primary_inner] is an infinite
      retry loop whose exhausted-retries error is deliberately swallowed by
      [if let Ok(..)] (batch_fetcher.rs:154-210, :173-177), so "the payload
      never arrives" is a legal infinite behaviour. The model now stutters at
      [Idle], and the conjunct's antecedent was strengthened with [holds_2(D)]
      so that it never assumes delivery.

    This is the same discipline the (b) conjunct already applied when it
    narrowed the mined card's unqualified "~halted(j)" to "does not abort in
    signer recovery" (R5): what survives is the claim the Rust actually
    supports, namely that the recovery abort in particular is excluded for a
    validated batch, not that no failure of any kind occurs.

    R2 witness. At w1 = (Well_formed, Resolved Accepted, Idle, Pending) the
    class [View_v1_seen (Accepted, Well_formed)] also contains w3 =
    (Well_formed, Resolved Accepted, Idle, Committed): identical V1 view,
    opposite [committed(D)] - so the class is not a singleton and V1 genuinely
    cannot see the commit.

    R8 honesty. The [Af] is not manufactured. It is asserted only from a state
    that already holds the payload of a committed certificate, and it is
    refutable: at every [Pending] state the [cert] self-loop
    ({!Cert_envelope_model.cert_moves}) and at every [Idle] state the fetch
    self-loop ({!Cert_envelope_model.v2_moves}) give infinite runs on which
    neither disjunct ever holds. The pinning mutation removes a REAL gate (the
    collect-into-Result in [decode_transactions]) rather than a delivery path,
    and it refutes (c) by making the excluded outcome - [Halted] - reachable
    from the antecedent.

    Mutation pin: {!Cert_envelope_model.No_recovery_gate} adds (Authored
    Unrecoverable, Unseen, v2, cert) -> (Authored Unrecoverable, Resolved
    Accepted, v2, cert). All three conjuncts flip: (a) directly; (b) the class
    [View_v1_seen (Accepted, Unrecoverable)] then contains (Unrecoverable,
    Accepted, Halted, Committed); (c) at (Unrecoverable, Accepted, Holds,
    Committed) one successor is [Halted], which is terminal and satisfies
    neither disjunct, so [AF (executed_2(D) \\/ aborted_2(D))] fails. *)
let s2 =
  let gate =
    Formula.Ag
      (Formula.Implies
         (atom V1_accepted, Formula.Not (atom Content_unrecoverable)))
  in
  let known_no_remote_halt =
    Formula.Ag
      (Formula.Implies
         ( atom V1_accepted,
           Formula.K (Validator.V1, Formula.Ag (Formula.Not (atom V2_halted)))
         ))
  in
  let operative =
    Formula.And
      (atom V1_accepted, Formula.And (atom V2_holds, atom Committed_cert))
  in
  let resolution_never_recovery_abort =
    Formula.Ag
      (Formula.Implies
         ( operative,
           Formula.Af (Formula.Or (atom V2_executed, atom V2_aborted)) ))
  in
  {
    name = "accepted-batch-implies-known-recovery-safe-execution";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        ( gate,
          Formula.And (known_no_remote_halt, resolution_never_recovery_abort) );
    antecedent = operative;
  }

(** S3 - accepted-batch-implies-known-nonempty-remote-payload [safety]. If V1's
    gated ingress accepted the batch behind [D], then:

    (a) GATE: [D] carries at least one transaction -
    AG( accepted_1(D) -> ~content(D)=empty ). The sole empty-batch rejection
    anywhere in the tree is the reduce-over-empty in the size check -
    [.reduce(|total, size| total + size).ok_or(BatchValidationError::EmptyBatch)?]
    (validator.rs:127-141, called at :67). [validate_batch_gas] explicitly
    delegates emptiness to it (:167-168) and [EmptyBatch] is [Penalty::Fatal]
    (error.rs:93-102).

    (b) KNOWN NONEMPTY REMOTE PAYLOAD: V1 knows that every remote COPY of [D] -
    including copies that arrived on an ingress that never validates anything -
    carries at least one transaction - AG( accepted_1(D) -> K_V1( AG(
    holds_2(D) -> ~payload_empty_2(D) ) ) ). "Another node's possession" is the
    R1-sanctioned target. The transfer is content addressing: [Batch::digest]
    hashes the serialized batch including [transactions] and skips only
    [received_at] (sealed_batch.rs:63-89, :116-124); [read_sync_batches]
    recomputes [batch.digest()] and rejects anything not in [requested_digests]
    (handle.rs:498-523); the gossip prefetch stores exactly what
    [request_batches] returned (handler.rs:192-208) and [fetch_local] keys by
    [b.digest()] (batch_fetcher.rs:222-232).

    (c) HOLDER BLIND TO VALIDATION: symmetrically, that remote holder never
    knows that any validator accepted the bytes it holds -
    AG( holds_2(D) -> ~K_V2(accepted_1(D)) ). The ungated ingresses carry no
    provenance: [process_gossip] inserts with no [validate_batch] call and no
    record of who vouched for the bytes (handler.rs:167-223),
    [store_synced_batches] skips validation entirely when [is_certified]
    (primary.rs:104-111), and a rejection at another node is purely local (a
    peer penalty against the reporter, error.rs:76-104) with no negative cache
    anywhere.

    RETARGETED from the mined card, which asserted
    [K_V1(AG(executes(j,D) -> block_tx_count(j,D) >= 1))]. That is FALSE of the
    code, and the card missed the repair path inside its own citation set:
    tn-reth/src/lib.rs:782-800 explicitly SKIPS transactions that fail EVM
    validation ("allow transaction errors (ie - duplicates) ... it's possible
    that another worker's batch included this transaction"), so a validated
    one-transaction batch whose transaction is a duplicate executes into a
    block with ZERO transactions. The claim was therefore retargeted to the
    remote-held PAYLOAD rather than the executed block; it is pinned by the
    same real gate.

    R2/R3 witnesses. Non-singleton class for (b): at w1 = (Well_formed,
    Resolved Accepted, Idle, Pending) the class [View_v1_seen (Accepted,
    Well_formed)] also contains w4 = (Well_formed, Resolved Accepted, Holds,
    Pending) - identical V1 view, opposite [holds_2(D)]. Ignorance pair for (c):
    w4 and w5 = (Well_formed, Unseen, Holds, Pending) share V2's view
    [View_v2_bytes (Holds, Well_formed, Pending)] and disagree on
    [accepted_1(D)], which also shows the ignorance is not an artefact of
    [accepted_1(D)] being false throughout the class.

    Mutation pin: {!Cert_envelope_model.No_empty_batch_gate} adds (Authored
    Empty_payload, Unseen, v2, cert) -> (Authored Empty_payload, Resolved
    Accepted, v2, cert). Conjunct (a) fails directly; (b) fails because the
    class [View_v1_seen (Accepted, Empty_payload)] then contains (Empty_payload,
    Accepted, Holds, Pending) where the held payload is empty. Conjunct (c) is
    untouched, so the refutation is cleanly attributable to (a) and (b). *)
let s3 =
  let gate =
    Formula.Ag
      (Formula.Implies (atom V1_accepted, Formula.Not (atom Content_empty)))
  in
  let known_nonempty_remote_payload =
    Formula.Ag
      (Formula.Implies
         ( atom V1_accepted,
           Formula.K
             ( Validator.V1,
               Formula.Ag
                 (Formula.Implies
                    (atom V2_holds, Formula.Not (atom V2_payload_empty))) ) ))
  in
  let holder_blind_to_validation =
    Formula.Ag
      (Formula.Implies
         ( atom V2_holds,
           Formula.Not (Formula.K (Validator.V2, atom V1_accepted)) ))
  in
  {
    name = "accepted-batch-implies-known-nonempty-remote-payload";
    bucket = Statements.Safety;
    formula =
      Formula.And
        ( gate,
          Formula.And (known_nonempty_remote_payload, holder_blind_to_validation)
        );
    antecedent = Formula.And (atom V1_accepted, atom V2_holds);
  }

(** The family's statements: one per deleted gate of [validate_batch]. *)
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
