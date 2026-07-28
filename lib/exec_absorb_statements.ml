(** The EXEC_ABSORB statement family, encoded over the {!Exec_absorb_model}
    interpreted system. All three statements were mined from telcoin-network and
    re-grounded line by line against this checkout (git HEAD [0c59c15b]); file
    citations refer to Telcoin-Association/telcoin-network.

    What the family is about: crates/tn-reth/src/lib.rs:763-800 draws a single
    line through the executor's error space. Below the line, a transaction-level
    revm rejection is logged and [continue]d (:787-796) so the chain advances;
    above it, everything else is [Err(err) => return Err(err.into())] (:797-798)
    so the output is abandoned whole. The family says what each side of that line
    buys: S1 that the absorbed side keeps a cross-worker duplicate from halting
    the chain, S2 that the aborted side is unreachable for anything that passed
    consensus because validation and execution call the same recovery helper, and
    S3 that the aborted side is what keeps an execution failure a HALT rather
    than a silent fork.

    {b Reading guide for the K operands.} The only knowledge agents are the two
    executing nodes [Validator.V0] and [Validator.V1]; V2 through V9 are idle
    and never appear under [K]. A node's view is (batch bytes, output overlap,
    consensus status, OWN tip): the peer's tip is the single hidden component,
    because nothing on the execution path crosses a node boundary
    (crates/tn-reth/src/lib.rs:923-980, crates/tn-reth/src/payload.rs:30-70).

    - [K (V0, ~peer_omits_a_transaction)] (S3 conjunct A) is a fact about node
      V1's committed BLOCK, which V0 cannot observe. V0 infers it from shared
      content plus deterministic execution, and the inference is sound only
      because the fatal arm aborts instead of committing something partial. It is
      not rigid: [peer_omits_a_transaction] is TRUE at reachable states (any
      state where V1 committed the lean block of a duplicated output), so the
      knowledge fails there.
    - [K (V0, ~full_block_1)] (S3 conjunct A') is the same operand family from
      the other side: having committed the LEAN block, V0 knows no peer committed
      the full one, because the skip is a function of the shared output rather
      than of anything node-local. It is contingent for the sharpest possible
      reason - conjunct B asserts that the very same operand is UNKNOWN to V0 at
      the full-block states.
    - S1 and S2 carry no [K] on purpose. Their operands (this output contains a
      duplicate; these bytes decode) are literally in the executing node's view,
      so any [K] over them would be collapsed by R1. *)

open Exec_absorb_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;  (** unique across every family *)
  bucket : Statements.bucket;  (** Safety | Liveness | Fairness | Security *)
  formula : atom Formula.t;  (** the claim *)
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of an unreachable antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - cross-worker-duplicate-transaction-never-halts-execution [liveness].
    Two workers can independently include the same transaction, because nothing
    deduplicates across batches before execution. The executor absorbs that: the
    duplicate's revm rejection (its nonce is now too low) is logged and skipped,
    packing continues, and the node still commits a block. Without the skip, one
    duplicated transaction anywhere in a committed output would make the whole
    output unexecutable on every honest node simultaneously.

    Write [dup_live] for
    [batch_certified /\\ ~bytes_garbage /\\ duplicate_in_output /\\ unexecuted_0]:
    a certified, decodable output that carries a cross-worker duplicate, at a
    node that has not started it.

    (A) the skip is available: AG( dup_live -> EF lean_block_0 ).
    The tolerated arm is crates/tn-reth/src/lib.rs:787-796 -
    [Err(BlockExecutionError::Validation(BlockValidationError::InvalidTx {error,
    ..})) => { warn!(..); continue; }] - carrying the comment "allow transaction
    errors (ie - duplicates) / it's possible that another worker's batch included
    this transaction". The transaction-level error it matches is the one TN's own
    executor constructs at crates/tn-reth/src/evm/block.rs:879-882
    ([self.evm.transact(tx_env).map_err(|err| BlockExecutionError::evm(err,
    hash))]). The resulting block is the "empty block for duplicate batch" the
    repo's own integration test asserts
    ([test_execution_succeeds_with_duplicate_transactions],
    crates/engine/tests/it/main.rs:1109-1122).

    (B) the halt is not forced: AG( dup_live -> ~AF halted_0 ). A duplicate does
    not put the node on a path that inevitably aborts the output. The [~AF]
    rather than [AG ~halted_0] is the faithful form: the fatal arm at
    crates/tn-reth/src/lib.rs:797-798 also fires for genuinely node-LOCAL
    conditions (crates/tn-reth/src/evm/block.rs:819-831 constructs
    [BlockExecutionError::Internal] from an internal/registry failure), so the
    model keeps a per-node abort branch and the statement claims only that the
    duplicate is not what forces it. Claiming [AG ~halted_0] would be
    manufactured liveness (R8).

    (C) the skip really skips:
    AG( batch_certified /\\ ~bytes_garbage /\\ duplicate_in_output ->
    ~full_block_0 ). When the output carries a duplicate the committed block is
    the lean one - the absorbed transaction is genuinely dropped from the block
    rather than executed twice - which is what makes (A) a statement about the
    skip arm and not about a no-op.

    Mutation pin: {!Exec_absorb_model.Fatal_on_invalid_tx} moves the [InvalidTx]
    variant out of the tolerated arm into the fatal arm, so a [Duplicated]
    output's only execution outcome is [Halted]. [lean_block_0] becomes
    unreachable, refuting (A), and [AF halted_0] becomes true at every [dup_live]
    state, refuting (B). The antecedent stays reachable under the mutation, so
    this is a refutation and not a degradation to [Vacuous_antecedent]. No
    sibling repairs it - see the constructor's own doc comment for the full
    dedup hunt (engine walk, batch validator, pool eviction, sender sharding,
    forwarding fallback). S1 deliberately survives the other two mutations:
    under {!Exec_absorb_model.No_validation_decode} the [~bytes_garbage] conjunct
    of [dup_live] excludes the newly certified garbage batches, and under
    {!Exec_absorb_model.Commit_partial_block} node V0 never halts at all. *)
let s_1 =
  let dup_live =
    Formula.conj
      [
        atom Batch_certified;
        Formula.Not (atom Bytes_garbage);
        atom Duplicate_in_output;
        atom Node0_unexecuted;
      ]
  in
  let skip_is_available =
    Formula.Ag (Formula.Implies (dup_live, Formula.Ef (atom Node0_lean_block)))
  in
  let halt_is_not_forced =
    Formula.Ag
      (Formula.Implies (dup_live, Formula.Not (Formula.Af (atom Node0_halted))))
  in
  let skip_really_skips =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [
               atom Batch_certified;
               Formula.Not (atom Bytes_garbage);
               atom Duplicate_in_output;
             ],
           Formula.Not (atom Node0_full_block) ))
  in
  {
    name = "cross-worker-duplicate-transaction-never-halts-execution";
    bucket = Statements.Liveness;
    formula =
      Formula.conj [ skip_is_available; halt_is_not_forced; skip_really_skips ];
    antecedent = dup_live;
  }

(** S2 - certified-batch-decodes-because-validation-and-execution-share-one-recovery
    [liveness]. The receiving worker's accept-predicate and the executor's
    decode-predicate are the same function. Every transaction of a batch is
    recovered during validation, before the batch is stored or reported, using
    the same reth entry point the executor later uses. That equality is what
    makes the executor's all-or-nothing recovery abort unreachable for anything
    that reached consensus.

    (A) certification implies decodability:
    AG( batch_certified -> ~bytes_garbage ). Validation side:
    crates/batch-validator/src/validator.rs:69-70
    [let decoded_txs = self.decode_transactions(transactions, digest)?;] ->
    :147-156 [transactions.par_iter().map(|tx| Self::recover_and_validate(tx,
    digest)).collect::<BatchValidationResult<Vec<_>>>()] -> :209-215
    [recover_signed_transaction(tx).map_err(..)]. Execution side:
    crates/tn-reth/src/lib.rs:766-780
    [reth_recover_raw_transaction::<TransactionSigned>(tx_bytes)] collected with
    [?]. Both bottom out in crates/tn-reth/src/txn_pool.rs:363-373, where
    [recover_raw_transaction] and [recover_signed_transaction] are two wrappers
    around the identical [reth_recover_raw_transaction::<TransactionSigned>]
    call. An honest worker refuses a batch that fails it before storing or
    reporting it (crates/consensus/worker/src/network/handler.rs:243-260), and
    the library's committee is n = 10, f = 3, quorum = 7 (lib/validator.mli), so
    a certified batch carries at least four honest acknowledgements that each
    ran the decode.

    (B) the recovery abort is not forced:
    AG( batch_certified /\\ unexecuted_0 /\\ ~duplicate_in_output -> ~AF halted_0 ).
    The recovery phase is the harshest failure mode in the executor - it aborts
    the output before ANY transaction runs (crates/tn-reth/src/lib.rs:766-780) -
    and this conjunct says consensus never hands the executor an output on which
    it is unavoidable. The [~duplicate_in_output] guard keeps this conjunct
    scoped to the RECOVERY gate: it is deliberately silent about the tolerated
    arm, which is S1's subject, so the two statements pin different gates.

    No [K] here on purpose (R1): "these bytes decode" is locally checkable by
    every node and sits inside every executing node's view, so a knowledge claim
    over it would be collapsed. The content is the cross-crate predicate
    equality, which is faithfulness rather than epistemics.

    Mutation pin: {!Exec_absorb_model.No_validation_decode} deletes
    crates/batch-validator/src/validator.rs:70, so a [Garbage] batch is admitted:
    [batch_certified /\\ bytes_garbage] becomes reachable, refuting (A), and at
    those states the node's only execution outcome is [Halted], making
    [AF halted_0] true and refuting (B) - a uniform chain halt on every node at
    once. No sibling repairs it - the digest check hashes the same opaque bytes,
    [Batch.transactions] is [Vec<Vec<u8>>], the wire codec decodes the envelope
    and not the blobs, and a peer's batch never enters the local pool; see the
    constructor's doc comment. S2 survives the other two mutations: neither
    touches the certification gate, and under
    {!Exec_absorb_model.Fatal_on_invalid_tx} the [~duplicate_in_output] guard of
    (B) excludes exactly the states that mutation makes halt. *)
let s_2 =
  let certification_implies_decodable =
    Formula.Ag
      (Formula.Implies (atom Batch_certified, Formula.Not (atom Bytes_garbage)))
  in
  let recovery_live =
    Formula.conj
      [
        atom Batch_certified;
        atom Node0_unexecuted;
        Formula.Not (atom Duplicate_in_output);
      ]
  in
  let recovery_abort_is_not_forced =
    Formula.Ag
      (Formula.Implies
         (recovery_live, Formula.Not (Formula.Af (atom Node0_halted))))
  in
  {
    name =
      "certified-batch-decodes-because-validation-and-execution-share-one-recovery";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        (certification_implies_decodable, recovery_abort_is_not_forced);
    antecedent = recovery_live;
  }

(** S3 - block-level-failure-aborts-the-output-so-nodes-halt-rather-than-fork
    [safety]. Block construction is all-or-nothing. The recovery phase is a
    collect-or-abort over the whole batch, and any non-transaction execution
    error abandons the entire output rather than emitting a partial block. So a
    node either produces the block every other honest node produces, or it
    produces nothing and halts; it can never commit a block that silently omits a
    transaction its peers included. The knowledge conjuncts are what that buys:
    a node's own successful commit tells it something definite about every peer's
    BLOCK, and nothing at all about any peer's PROGRESS.

    (A) no peer holds a truncated block:
    AG( full_block_0 -> K_V0( ~peer_omits_a_transaction ) ). The fatal arm at
    crates/tn-reth/src/lib.rs:797-798 is what makes this inference sound: a
    node-local failure (crates/tn-reth/src/evm/block.rs:819-831 ->
    [BlockExecutionError::Internal]) aborts the output rather than skipping the
    offending transaction, and the abort happens before
    crates/engine/src/payload_builder.rs:189-194 reaches
    [finish_executing_output], so nothing is persisted
    (crates/tn-reth/src/lib.rs:941-944). Content-induced failures are a function
    of the shared output - the block gas budget check at
    crates/tn-reth/src/evm/block.rs:866-876 reads only
    [self.evm.block().gas_limit()], [self.gas_used] and the transaction's own gas
    limit - so they fire on every node or on none, which is why a node that
    committed the FULL block can conclude nothing content-induced fired anywhere.

    (B) peer progress stays opaque:
    AG( full_block_0 -> ~K_V0(full_block_1) /\\ ~K_V0(~full_block_1) ).
    Finishing execution tells a node nothing about whether any peer has got
    there. [finish_executing_output] (crates/tn-reth/src/lib.rs:923-980) writes
    to the local database and notifies the LOCAL canonical-state channel, and
    [TNPayload] carries no cross-node field at all
    (crates/tn-reth/src/payload.rs:30-70), so within one output there is no
    predicate at V0 that separates "V1 already committed" from "V1 has not
    started". R3 witness, both members reachable and sharing
    [View_node (Sound, Distinct, Certified, At_full)]:
    s_A = {bytes = Sound; overlap = Distinct; cert = Certified; t0 = At_full;
    t1 = At_full} and s_B the same with [t1 = At_parent]. [full_block_1] is true
    at s_A and false at s_B, so both knowledge directions fail.

    (A') the absorbed skip is uniform:
    AG( lean_block_0 -> K_V0( ~full_block_1 ) ). The mirror of (A) on the other
    side of the taxonomy: having committed the LEAN block, V0 knows no peer
    committed the full one, because the skipped transaction was rejected by revm
    on shared content rather than for anything node-local
    (crates/tn-reth/src/lib.rs:787-796 sits inside the same deterministic loop as
    the fatal arm). The pairing with (B) is the R2 discharge in its sharpest
    form: [~full_block_1] is the SAME operand, known to V0 at the lean-block
    states and provably unknown at the full-block states, so neither conjunct can
    be true by collapse.

    R2 non-singleton evidence for both positive [K]s: at a [full_block_0] state
    V0's class is {t1 = At_parent, t1 = Halted, t1 = At_full} and at a
    [lean_block_0] state it is {t1 = At_parent, t1 = Halted, t1 = At_lean} -
    three worlds each. test/t_exec_absorb.ml proves this rather than asserting
    it, by showing V0 cannot rule out [halted_1] at either operative state.

    Mutation pin: {!Exec_absorb_model.Commit_partial_block} turns the fatal arm
    into a skip, adding the [At_parent -> At_partial] transition. At a
    [full_block_0] state V0's class then contains a world where V1 committed a
    silently truncated block, so [peer_omits_a_transaction] holds there and (A)
    is refuted: the two nodes have divergent state roots with no reorg path
    (crates/tn-reth/src/txn_pool.rs:135). No sibling repairs it - no expected
    state root exists anywhere in [TNPayload], [builder.finish] computes a root
    with nothing to compare against, and the execution-tip machinery of other
    crates detects divergence only AFTER the commit at
    crates/tn-reth/src/lib.rs:941-944 and cannot undo it. S3 survives the other
    two mutations: {!Exec_absorb_model.Fatal_on_invalid_tx} only makes
    [lean_block_0] unreachable (so (A') is vacuously true and (A), (B) are
    untouched), and {!Exec_absorb_model.No_validation_decode} only adds states in
    which both nodes halt. *)
let s_3 =
  let no_peer_holds_a_truncated_block =
    Formula.Ag
      (Formula.Implies
         ( atom Node0_full_block,
           Formula.K
             (Validator.V0, Formula.Not (atom Peer_omits_a_transaction)) ))
  in
  let absorbed_skip_is_uniform =
    Formula.Ag
      (Formula.Implies
         ( atom Node0_lean_block,
           Formula.K (Validator.V0, Formula.Not (atom Node1_full_block)) ))
  in
  let peer_progress_is_opaque =
    Formula.Ag
      (Formula.Implies
         ( atom Node0_full_block,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V0, atom Node1_full_block)),
               Formula.Not
                 (Formula.K (Validator.V0, Formula.Not (atom Node1_full_block)))
             ) ))
  in
  {
    name = "block-level-failure-aborts-the-output-so-nodes-halt-rather-than-fork";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [
          no_peer_holds_a_truncated_block;
          absorbed_skip_is_uniform;
          peer_progress_is_opaque;
        ];
    antecedent = atom Node0_committed;
  }

(** The family's statements: two liveness statements pinned by the two absorbing
    gates and one safety statement pinned by the aborting gate. *)
let all = [ s_1; s_2; s_3 ]

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
