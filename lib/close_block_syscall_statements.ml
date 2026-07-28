(** The CLOSE_BLOCK_SYSCALL statement family, encoded over the
    {!Close_block_syscall_model} interpreted system. All three statements were
    mined from telcoin-network and re-grounded line by line against this
    checkout (git HEAD [0c59c15b], working tree). File citations refer to
    Telcoin-Association/telcoin-network.

    What the family is about: one block's execution in
    [crates/tn-reth/src/evm] is a sequence of privileged, zero-priced system
    calls interleaved with ordinary user transactions on ONE shared EVM
    instance. Three properties of that interleaving are stated here:

    - S1 is the CLOSE GATE: the epoch transition happens only inside the block
      whose context - and therefore whose header - says so, and the header
      says so publicly enough that a replay node reading an unmarked header
      knows the registry did not move.
    - S2 is the WINDOW: the privileged environment the system call installs is
      shut again before the block's user transactions run, so they still pay
      the base fee and are still nonce-checked.
    - S3 is the ADMISSION: that same privileged environment is the only thing
      that lets the epoch-closing call in at all, so deleting it does not
      degrade the close - it stops the chain.

    Reading guide for the K operands:

    - [K (V1, ~registry_epoch_advanced)] in S1 conjunct B is the REPLAY node's
      knowledge. Its view is the sealed header's [extra_data] marker and
      nothing else (config.rs:150-178 reads exactly [block.extra_data.len()]);
      the registry epoch is not a field of that view, is not carried on the
      wire and is not otherwise observable to a node that did not execute the
      block. The knowledge is an INFERENCE licensed by the marker, which is
      precisely the mechanism block.rs:970 plus config.rs:157-167 establishes -
      and it is not rigid: [registry_epoch_advanced] is true at reachable
      states, and {!Close_block_syscall_model.No_close_marker_gate} decorrelates
      the marker from the transition and destroys exactly this conjunct. The
      operative class is not a singleton either: four reachable sealed unmarked
      states share it (both contract verdicts x both transaction bodies), which
      the suite proves by exhibiting a fact the replay node cannot rule out
      there.
    - [~K (V1, close_marked(b))] in S1 conjunct C is the ignorance dual, and it
      is what makes conjunct B content rather than tautology: while the
      producer is executing the block, the replay node holds nothing at all -
      a block that halts is never assembled and never reaches it - so it
      cannot tell an epoch-closing block from an ordinary one until the marker
      is published.
    - The executing node [V0] never appears under [K]. Its view is its own
      execution state, so any positive [K_V0] would be a projection of its own
      view (R1). *)

open Close_block_syscall_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a situation that never arises *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - epoch-transition-is-confined-to-and-published-by-the-marked-block
    [safety]. The single highest-impact state change in the chain - the
    registry epoch advancing - is guarded by one [if let], and the guard's
    input is published on the header so that a node which did not execute the
    block can still tell whether it happened.

    (A) confinement: AG( registry_epoch_advanced -> close_marked(b) ). The fork
    boundary, [applyIncentives] and [concludeEpoch] all sit inside
    [if let Some(randomness) = self.ctx.close_epoch {] (block.rs:794, body
    :795-835); the calldata for the three registry calls is constructed at
    exactly one site each (block.rs:348, :399, :414) and
    [apply_consensus_block_rewards] / [apply_closing_epoch_contract_call] have
    exactly one call site each (block.rs:824, :829). [ctx.close_epoch] is
    [payload.close_epoch] on the production path (config.rs:190, from
    payload.rs:87-91) and the header's 32-byte [extra_data] on the replay path
    (config.rs:157-167), and the assembler writes that header field straight
    off the same context (block.rs:970) - so "the context said close" and "the
    header says close" are the same fact.

    (B) publication: AG( sealed(b) /\\ ~close_marked(b) ->
    K_V1( ~registry_epoch_advanced ) ). A node that only ever sees the sealed
    header - which is all [context_for_block] consumes - can read an unmarked
    header and conclude the registry did not move. That is what makes replay
    sound: the replay node reconstructs the same [close_epoch] the producer
    used, so it re-executes the same system calls (none) and computes the same
    state root. R2 is discharged in the suite: the operand is not rigid
    ([EF registry_epoch_advanced] holds) and the class at the operative state
    is not a singleton (four reachable sealed unmarked states share it).

    (C) ignorance until publication: AG( running_user_txs ->
    ~K_V1( close_marked(b) ) ). While the producer is still executing, the
    replay node holds nothing - a block whose execution halts is never
    assembled (block.rs:837-845 is only reached past the closing calls) and
    never reaches it - so the epoch boundary is genuinely hidden until the
    marker is written. R3 witness pair, both members reachable: the mid-block
    state of an epoch-closing block and the mid-block state of an ordinary one
    are [View_replay_waiting]-identical and disagree on [close_marked(b)].

    Mutation pin: {!Close_block_syscall_model.No_close_marker_gate} deletes the
    guard at block.rs:794 and runs its body in every block. (A) fails outright -
    an ordinary block's registry epoch advances - and (B) fails with it,
    because the sealed unmarked states now all carry an advanced registry, so
    reading an unmarked header no longer entails anything. No sibling path
    confines the transition: there is no second Rust route to the registry (one
    construction site per call, one call site per helper), and the only
    remaining candidate - the Solidity contract refusing a premature call - is
    carried in the model as the {!Close_block_syscall_model.Registry_reverts}
    branch rather than assumed away, where it halts the block
    (block.rs:215-219) instead of silently repairing anything. The assembler
    still reads [ctx.close_epoch] (block.rs:970-978), which is exactly why the
    marker and the transition come apart under this deletion.

    NOT pinned by a marker deletion, deliberately: the header publishes the
    close TWICE - [extra_data] at block.rs:970 and the withdrawals swing at
    block.rs:971-978 - so deleting the [extra_data] write alone would leave the
    close observable through a non-empty withdrawals root for any block with a
    non-empty reward set, i.e. every real epoch boundary. That candidate
    mutation is silently repaired and is reported rather than shipped. *)
let s1 =
  let confinement =
    Formula.Ag
      (Formula.Implies (atom Registry_concluded, atom Close_marked_block))
  in
  let publication =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Block_sealed, Formula.Not (atom Close_marked_block)),
           Formula.K
             (replay_observer, Formula.Not (atom Registry_concluded)) ))
  in
  let hidden_until_published =
    Formula.Ag
      (Formula.Implies
         ( atom Executing_user_txs,
           Formula.Not (Formula.K (replay_observer, atom Close_marked_block)) ))
  in
  {
    name = "epoch-transition-is-confined-to-and-published-by-the-marked-block";
    bucket = Statements.Safety;
    formula =
      Formula.And (confinement, Formula.And (publication, hidden_until_published));
    antecedent =
      Formula.And (atom Registry_concluded, atom Close_marked_block);
  }

(** S2 - system-call-window-shuts-before-the-user-transactions-of-the-block
    [security]. A system call rewrites the live EVM environment so a zero-priced
    privileged transaction is admitted, and the block's ordinary transactions
    run on that very same instance a moment later.

    (A) the window is shut: AG( running_user_txs -> ~basefee_env=0 /\\
    ~nonce_check_disabled ). [transact_system_call] swaps the block base fee to
    0 and [disable_nonce_check] to [true] at mod.rs:199-203, BINDS the call
    ([let res = self.transact(tx);], mod.rs:205, no [?]) and swaps all three
    back at mod.rs:207-212 before returning [res] at mod.rs:220 - so the restore
    runs on the error path too. The pre-block calls that open this window run
    before any user transaction: [apply_pre_execution_changes] (block.rs:769-785)
    calls EIP-4788 ([first_batch] only, the system call at block.rs:667-671) and
    EIP-2935 (block.rs:708-712), and the user transactions then execute on the
    same instance at block.rs:879. The environment itself is built once per
    block (factory.rs:46-64 via :148-158, [basefee: payload.base_fee_per_gas]
    at config.rs:138) and never re-derived per transaction.

    (B) the governance share still lands: AG( user_tx_executed ->
    sink_got_basefee_share ). [reward_beneficiary] pays the beneficiary
    [effective_gas_price - basefee] and the governance sink [basefee * gas_used]
    (handler.rs:148-168). With the base fee leaked to zero the first term
    absorbs the whole price and the second is zero. The conjunct is stated as
    the base-fee SHARE, not as "the sink is untouched", because the sink also
    receives the gas-limit over-estimation penalty (handler.rs:124-131,
    [calculate_gas_penalty] at evm/utils.rs:45-69) - a partial repair the model
    carries explicitly as [Sink_penalty_only] rather than omitting.

    (C) no in-block replay: AG( ~replay_executed ). [disable_nonce_check = true]
    admits a transaction whose nonce has already been consumed. Nothing else in
    the block pipeline would catch it: the payload loop skips a transaction only
    BECAUSE revm returned [InvalidTx] ([warn!(..); continue;], lib.rs:783-799)
    and keeps no set of seen nonces of its own.

    Mutation pin: {!Close_block_syscall_model.No_env_restore} deletes the three
    restore swaps at mod.rs:207-212, so the environment installed for the
    pre-block system call survives into the user transactions. (A) fails at the
    user-execution state, (B) fails because an executed transaction now credits
    the sink only the penalty, and (C) fails because the duplicate-nonce
    transaction is admitted. No sibling path re-establishes the environment:
    [transact_raw] sets only the tx env and rebuilds only the handler, which
    carries just the sink address (mod.rs:147-162, handler.rs:34-44);
    [execute_transaction_without_commit] passes only [tx_env]
    (block.rs:860-885); the EVM is created once per block (factory.rs:46-64,
    :148-158); and [disable_base_fee] does not exist anywhere in the tree, so
    there is no cfg-level fallback that re-imposes the fee. The nearby
    SYSTEM_ADDRESS early returns (handler.rs:85-87, :145-147) are not a repair:
    they only skip fee accounting for the system caller itself, whose amounts
    are zero anyway, and do nothing on a user transaction.

    The gas-limit leg of the swap (mod.rs:199/:208) is deliberately absent from
    this statement: on the shipped configuration the block gas limit already
    equals the 30M system-transaction limit (mod.rs:175), so it is a no-op and
    resting the claim on it would be dishonest. The statement rests on the base
    fee and the nonce check, which are not no-ops. *)
let s2 =
  let window_is_shut =
    Formula.Ag
      (Formula.Implies
         ( atom Executing_user_txs,
           Formula.And
             ( Formula.Not (atom Fee_env_zeroed),
               Formula.Not (atom Nonce_check_disabled) ) ))
  in
  let governance_share_lands =
    Formula.Ag
      (Formula.Implies (atom User_tx_executed, atom Sink_got_basefee_share))
  in
  let no_in_block_replay = Formula.Ag (Formula.Not (atom Replay_executed)) in
  {
    name = "system-call-window-shuts-before-the-user-transactions-of-the-block";
    bucket = Statements.Security;
    formula =
      Formula.And
        (window_is_shut, Formula.And (governance_share_lands, no_in_block_replay));
    antecedent = atom User_tx_executed;
  }

(** S3 - epoch-closing-calls-need-the-zeroed-base-fee-admission-window
    [liveness]. The mechanism that makes the epoch transition possible is an
    environment mutation, not a check - the sort of line a refactor deletes as
    redundant.

    (A) progress: AG( close_marked(b) /\\ registry_would_accept ->
    AF( registry_epoch_advanced ) ). An epoch-closing block whose registry call
    would succeed always gets it through. The system transaction is priced at
    [gas_price: 0] (mod.rs:178-180) against a block base fee that is non-zero
    and agreed - [basefee: payload.base_fee_per_gas] (config.rs:138), voter
    enforced ([if base_fee != expected_base_fee { Err(InvalidBaseFee..) }],
    batch-validator/src/validator.rs:188-195) and floored at
    [MIN_PROTOCOL_BASE_FEE] (types/src/gas_accumulator.rs:204-208) - so
    admission is bought by [core::mem::swap(&mut self.block.basefee, &mut
    basefee)] with [let mut basefee = 0] (mod.rs:195, :201) and by nothing
    else.

    The antecedent's second conjunct is what keeps this an honest [AF] rather
    than a manufactured one: the [ConsensusRegistry] Solidity is not vendored
    in this checkout, so whether it accepts is an oracle, carried as a free
    choice in the initial states. Conjunct (B) states what happens on the other
    branch.

    (B) fail loud: AG( close_marked(b) /\\ ~registry_would_accept ->
    AF( halted ) ). A refusing registry does not degrade the block, it kills
    it: [if !res.result.is_success() { .. return Err(TnRethError::EVMCustom(
    "failed to close epoch")) }] (block.rs:215-219), wrapped as
    [BlockExecutionError::Internal] (block.rs:829-831), propagated by
    [builder.finish(&state_provider)?] (lib.rs:802-803) and returned out of the
    engine's run loop by [res.map_err(Into::into).and_then(|res| res)?]
    (engine/src/lib.rs:262-264). Nothing re-queues the output.

    Mutation pin: {!Close_block_syscall_model.Nonzero_basefee_for_syscall}
    deletes the base-fee swap-in at mod.rs:201 and its mirror restore at
    mod.rs:210, leaving the real base fee in force while the zero-priced system
    transaction is validated. Every [transact_system_call] becomes
    inadmissible, so the block dies at the FIRST one - the pre-block EIP-2935
    call (block.rs:708-719) - and the epoch-closing call at block.rs:199-209 is
    a fortiori inadmissible. (A) fails: no path from an epoch-closing block
    reaches an advanced registry. (B) survives, which is the point: the failure
    mode is a fleet-wide halt, not a silent skip. No sibling path admits the
    call: [disable_base_fee] appears nowhere in the tree (the only such flag is
    [disable_nonce_check], mod.rs:196/:203/:212 and :305/:312/:321), so there
    is no cfg-level bypass; pre-funding the system caller would not help,
    because a zero gas price is below any non-zero base fee whatever the
    balance; and nothing retries - the engine propagates the failure out of
    [run()] with [?] and never re-queues (engine/src/lib.rs:262-264).

    NOT pinned by the other two mutations, and the suite asserts it survives
    both: {!Close_block_syscall_model.No_close_marker_gate} adds closing calls
    to ordinary blocks without touching the closing block's own path, and
    {!Close_block_syscall_model.No_env_restore} leaves the window open wider,
    which if anything helps the call through. *)
let s3 =
  let progress =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Close_marked_block, atom Registry_would_accept),
           Formula.Af (atom Registry_concluded) ))
  in
  let fail_loud =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             ( atom Close_marked_block,
               Formula.Not (atom Registry_would_accept) ),
           Formula.Af (atom Block_halted) ))
  in
  {
    name = "epoch-closing-calls-need-the-zeroed-base-fee-admission-window";
    bucket = Statements.Liveness;
    formula = Formula.And (progress, fail_loud);
    antecedent =
      Formula.And (atom Close_marked_block, atom Registry_would_accept);
  }

(** The family's statements: the close gate, the environment window, and the
    admission the window buys. *)
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
