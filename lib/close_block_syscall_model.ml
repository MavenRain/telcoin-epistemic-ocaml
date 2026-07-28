(** Finite interpreted system for the CLOSE_BLOCK_SYSCALL family: one block's
    execution inside [crates/tn-reth/src/evm], from the pre-block system calls
    through the user transactions to the epoch-closing calls in [finish], plus
    the replay node that later re-derives the same context from the sealed
    header. File citations refer to Telcoin-Association/telcoin-network at
    [0c59c15b] (working tree) and every one of them was opened in this checkout.

    {2 The modelled mechanism}

    ONE EVM INSTANCE PER BLOCK. [TNEvmFactory::create_evm] (factory.rs:46-64) is
    called once per block and handed to [create_executor] (factory.rs:148-158);
    the block env - including [basefee: payload.base_fee_per_gas]
    (config.rs:131-143, :138) - is built once and never re-derived per
    transaction. So the environment is shared mutable state across everything
    the block does.

    THE SYSTEM-CALL WINDOW. [TNEvm::transact_system_call] (mod.rs:164-221)
    builds a [TxEnv] with [gas_price: 0] (mod.rs:178-180) and then swaps three
    fields of that live environment IN (mod.rs:194-203):
    [core::mem::swap(&mut self.block.gas_limit, &mut gas_limit)],
    [// disable the base fee check for this call by setting the base fee to zero]
    [core::mem::swap(&mut self.block.basefee, &mut basefee)] with
    [let mut basefee = 0] at mod.rs:195, and
    [core::mem::swap(&mut self.cfg.disable_nonce_check, &mut disable_nonce_check)]
    with [let mut disable_nonce_check = true] at mod.rs:196. The call is BOUND,
    not propagated ([let res = self.transact(tx);], mod.rs:205), and all three
    are swapped back at mod.rs:207-212 before [res] is returned at mod.rs:220 -
    so the restore happens on the error path too.

    ORDER WITHIN A BLOCK. [apply_pre_execution_changes] (block.rs:769-785) runs
    the EIP-4788 consensus-root call ([first_batch] only, block.rs:642-693, the
    system call at :667-671) and the EIP-2935 blockhashes call (block.rs:696-733,
    the system call at :708-712) BEFORE any user transaction. The user
    transactions then run on the same instance
    ([self.evm.transact(tx_env)], block.rs:879). Only afterwards does [finish]
    (block.rs:787-846) run the epoch-closing calls. So the window that the user
    transactions are protected from is the PRE-BLOCK one, and this model puts
    the pre-block call first for exactly that reason.

    THE CLOSE GATE. [finish] wraps the whole epoch transition in a single
    [if let Some(randomness) = self.ctx.close_epoch {] (block.rs:794): the
    optional in-protocol registry fork (block.rs:815-822 -> :280-387),
    [apply_consensus_block_rewards] (block.rs:824-827 -> :148-190, the
    [applyIncentives] calldata at :414), [apply_closing_epoch_contract_call]
    (block.rs:829-831 -> :193-228, the [concludeEpoch] calldata at :399) and
    [merge_transitions] (block.rs:834). [ctx.close_epoch] has two independent
    derivations that must agree: production is [close_epoch: payload.close_epoch]
    (config.rs:190) from [payload.rs:87-91], replay is the header's
    [extra_data] (config.rs:154-167, [0 => None], [32 => Some(..)], any other
    length an error), and the assembler is what puts it there:
    [let extra_data = ctx.close_epoch.map(|hash| hash.to_vec().into())
    .unwrap_or_default();] (block.rs:970).

    FAIL LOUD. A rejected system call is fatal, never skipped: the transact
    error arm returns [TnRethError::EVMCustom] (block.rs:205-209, and :165-171
    for the incentives call), a non-successful result likewise (block.rs:215-219,
    :175-181), [finish] wraps it as [BlockExecutionError::Internal]
    (block.rs:829-831), [builder.finish(..)?] propagates it (lib.rs:802-803) and
    the engine's run loop returns it: [let finalized_header = res.map_err(Into::
    into).and_then(|res| res)?;] (engine/src/lib.rs:262-264). Nothing re-queues
    the output.

    {2 The sibling paths this model MUST carry (R4/R5)}

    - THE PENALTY LEG IS NOT THE BASE-FEE LEG. [TNEvmHandler::reward_beneficiary]
      splits a user transaction's fee: the priority part
      ([effective_gas_price.saturating_sub(basefee)]) to the beneficiary and
      [basefee * gas_used] to the governance sink (handler.rs:148-168). With the
      base fee leaked to zero that second credit is zero - but
      [reimburse_caller] ALSO credits the sink, with the gas-limit
      over-estimation penalty [effective_gas_price * penalty_gas]
      (handler.rs:124-131, [calculate_gas_penalty] at evm/utils.rs:45-69, which
      is non-zero exactly when usage is under 10% of an above-threshold gas
      limit). So the sink is NOT untouched under the leak. The model therefore
      carries a three-valued {!sink} and the modelled user transaction is the
      adversarial one that DOES over-estimate, so [Sink_penalty_only] is a real
      reachable value and S2 cannot be true merely because the model forgot the
      penalty leg.
    - NO CALLER-SIDE NONCE DEDUPLICATION. The only thing that rejects a
      duplicate-nonce transaction during block execution is revm's own nonce
      check. The payload builder loop matches
      [Err(BlockExecutionError::Validation(BlockValidationError::InvalidTx{..}))
      => { warn!(..); continue; }] (lib.rs:783-799) - it skips a transaction
      BECAUSE revm rejected it; it keeps no set of seen nonces and makes no
      comparison of its own. Disabling the nonce check therefore turns a skip
      into an execution with nothing to catch it.
    - NO CFG-LEVEL BASE-FEE BYPASS. [rg] over every [*.rs] in the tree returns
      [disable_base_fee] nowhere; the only such flag in the codebase is
      [disable_nonce_check], at mod.rs:196/:203/:212 and mod.rs:305/:312/:321.
      So nothing re-imposes or waives the base-fee admission check behind the
      swap. [transact_pre_genesis_create] (mod.rs:274-325) repeats the same swap
      pattern but is a distinct genesis-only entry point, not a repair.
    - NO SECOND ROUTE TO THE REGISTRY. [concludeEpochCall],
      [applyIncentivesCall] and [migrateValidatorSetsCall] are constructed at
      block.rs:399, block.rs:414 and block.rs:348 respectively - one site each,
      all three inside the [if let Some(randomness)] guard;
      [apply_consensus_block_rewards] and [apply_closing_epoch_contract_call]
      each have exactly one call site (block.rs:824, block.rs:829).
    - THE HEADER PUBLISHES THE CLOSE TWICE. Alongside [extra_data], the
      assembler also swings the withdrawals on the same [ctx.close_epoch]:
      [if ctx.close_epoch.is_some() { .. generate_withdrawals() .. } else
      { (Some(Withdrawals::default()), Some(EMPTY_WITHDRAWALS)) }]
      (block.rs:971-978, [RewardsCounter::generate_withdrawals] at
      types/src/gas_accumulator.rs:146-158). This model deliberately does NOT
      carry a "delete the [extra_data] write" mutation, because that second
      channel would silently repair the observability half of S1 for any block
      with a non-empty reward set - which is every real epoch boundary. The
      negative result is reported rather than papered over. Projecting the
      withdrawals root into the observer's view would change nothing here: in
      this model the two channels are perfectly correlated (both are
      [ctx.close_epoch]), so it refines no view class.

    {2 Components}

    - [kind] whether this block's [ctx.close_epoch] is [Some] (config.rs:190,
      :157-167). The header marker is a function of it (block.rs:970), so
      {!marker_of_kind} rather than a second field;
    - [verdict] whether the on-chain [ConsensusRegistry] would accept the
      closing calls. The Solidity is NOT vendored in this checkout
      (system_calls.rs carries only the ABI), so its accept/revert decision is
      an oracle the Rust layer neither computes nor inspects: a free choice
      fixed per run, which is what keeps S3 an honest [AF] rather than a
      manufactured one;
    - [body] the block's single user transaction: [Tx_fresh] or [Tx_replayed],
      the latter carrying an already-used nonce;
    - [phase] where block execution is;
    - [fee] / [nonce] the two live environment fields the swap touches. The
      gas-limit swap (mod.rs:199/:208) is deliberately NOT modelled: on the
      shipped configuration the block gas limit already equals the 30M system-tx
      limit (mod.rs:175), so it is a no-op and resting the statement on it would
      be dishonest;
    - [registry] whether [concludeEpoch] committed and the epoch advanced;
    - [sink] what the governance base-fee address received from the user
      transaction: nothing, the over-estimation penalty only, or the base-fee
      share (handler.rs:124-131 vs :162-168);
    - [fate] whether the user transaction was executed or skipped
      (lib.rs:783-799).

    {2 Scoping assumptions, stated so they can be attacked}

    - ONE block, ONE user transaction. The statements are all predicates over a
      single block's trace, which is the scope of the environment swap and of
      the close gate alike.
    - The block is non-genesis and prague-active, so the EIP-2935 pre-block
      call really is made (block.rs:698-706 would otherwise return early). This
      is what makes the pre-block window exist at all; on a genesis block there
      is no window and nothing to restore.
    - The registry verdict is fixed before execution rather than sampled at the
      call. Both values are carried in the initial states, so nothing is proved
      only on the happy branch.

    {2 Role mapping}

    - [V0] is the EXECUTING node ({!executor}): the producer running
      [TNBlockExecutor] over this block. Its view is its own local execution
      state - the context kind, the transaction in hand, the phase, both
      environment fields, the registry epoch, the sink and the transaction's
      fate. Everything there is its own state, so a positive [K_V0] would be a
      projection of its own view and the family never asserts one. The one
      thing outside its view is [verdict], the unvendored contract's decision.
    - [V1] is the REPLAY node ({!replay_observer}), the family's knowledge
      agent: a validator that re-executes the block from the sealed header
      ([context_for_block], config.rs:150-178). Until the block seals it has
      NOTHING - a block whose execution halted never reaches it at all - and
      once it seals it has exactly the 32-byte [extra_data] marker, which is
      the sole field [context_for_block] reads to reconstruct [close_epoch]. It
      sees no environment, no registry epoch, no sink and no transaction fate.
    - [V2] .. [V9] are idle: constant blank view, never under [K]. *)

(** Whether this block's execution context carries the epoch-closing digest:
    [Ordinary] is [ctx.close_epoch = None], [Close_marked] is [Some(digest)]
    (block.rs:69, config.rs:190 on the production path and config.rs:157-167 on
    the replay path). *)
type block_kind = Ordinary | Close_marked

(** Total order index for {!block_kind}. *)
let block_kind_index = function Ordinary -> 0 | Close_marked -> 1

(** Total order on {!block_kind}. *)
let block_kind_compare a b =
  Int.compare (block_kind_index a) (block_kind_index b)

(** [true] iff the executor's context carries the closing digest. *)
let is_close_marked = function Close_marked -> true | Ordinary -> false

(** The 32-byte [extra_data] marker on the assembled header: [Mk_absent] is the
    empty [extra_data] of an ordinary block, [Mk_present] the closing digest
    (block.rs:970). *)
type marker = Mk_absent | Mk_present

(** Total order index for {!marker}. *)
let marker_index = function Mk_absent -> 0 | Mk_present -> 1

(** Total order on {!marker}. *)
let marker_compare a b = Int.compare (marker_index a) (marker_index b)

(** The assembler writes the marker straight off the context
    ([ctx.close_epoch.map(|hash| hash.to_vec().into()).unwrap_or_default()],
    block.rs:970), so the marker is a function of the kind rather than an
    independent field. *)
let marker_of_kind = function
  | Ordinary -> Mk_absent
  | Close_marked -> Mk_present

(** What the on-chain [ConsensusRegistry] would do with the closing calls. The
    contract is not vendored in this checkout, so this is an oracle rather than
    anything the Rust layer computes. *)
type registry_verdict = Registry_accepts | Registry_reverts

(** Total order index for {!registry_verdict}. *)
let registry_verdict_index = function
  | Registry_accepts -> 0
  | Registry_reverts -> 1

(** Total order on {!registry_verdict}. *)
let registry_verdict_compare a b =
  Int.compare (registry_verdict_index a) (registry_verdict_index b)

(** [true] iff the registry would accept the closing calls. *)
let verdict_accepts = function
  | Registry_accepts -> true
  | Registry_reverts -> false

(** The block's single user transaction: [Tx_fresh] carries the sender's next
    nonce, [Tx_replayed] carries an already-used one - the duplicate the payload
    loop expects revm to reject (lib.rs:791-795). Both are modelled as
    over-estimating their gas limit, so the governance penalty leg
    (handler.rs:124-131) is live in every trace. *)
type tx_body = Tx_fresh | Tx_replayed

(** Total order index for {!tx_body}. *)
let tx_body_index = function Tx_fresh -> 0 | Tx_replayed -> 1

(** Total order on {!tx_body}. *)
let tx_body_compare a b = Int.compare (tx_body_index a) (tx_body_index b)

(** [true] iff the block's user transaction carries an already-used nonce. *)
let tx_is_replayed = function Tx_replayed -> true | Tx_fresh -> false

(** Where block execution is.

    - [Ph_pre] about to run [apply_pre_execution_changes] (block.rs:769-785);
    - [Ph_user] the pre-block system calls are done and the block's user
      transaction is about to execute (block.rs:860-885);
    - [Ph_close] the user transactions are done and [finish] is inside the
      [if let Some(randomness)] body (block.rs:794-835);
    - [Ph_sealed] [finish] returned and the block was assembled
      (block.rs:837-845, :941-1008);
    - [Ph_halted] a fatal block-execution error propagated out of the engine's
      run loop (block.rs:205-219, lib.rs:802-803, engine/src/lib.rs:262-264). *)
type phase = Ph_pre | Ph_user | Ph_close | Ph_sealed | Ph_halted

(** Total order index for {!phase}: the order execution moves through, with the
    two terminals last. *)
let phase_index = function
  | Ph_pre -> 0
  | Ph_user -> 1
  | Ph_close -> 2
  | Ph_sealed -> 3
  | Ph_halted -> 4

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** [true] iff the block's user transaction is executing now. *)
let phase_is_user = function
  | Ph_user -> true
  | Ph_pre | Ph_close | Ph_sealed | Ph_halted -> false

(** [true] iff the block was assembled. *)
let phase_is_sealed = function
  | Ph_sealed -> true
  | Ph_pre | Ph_user | Ph_close | Ph_halted -> false

(** [true] iff block execution died. *)
let phase_is_halted = function
  | Ph_halted -> true
  | Ph_pre | Ph_user | Ph_close | Ph_sealed -> false

(** The live [self.block.basefee]: [Fee_block] is the block's agreed base fee
    (config.rs:138), [Fee_zero] is the value the system-call swap installs
    (mod.rs:195, :201). *)
type fee_env = Fee_block | Fee_zero

(** Total order index for {!fee_env}. *)
let fee_env_index = function Fee_block -> 0 | Fee_zero -> 1

(** Total order on {!fee_env}. *)
let fee_env_compare a b = Int.compare (fee_env_index a) (fee_env_index b)

(** [true] iff the live base fee is the block's own, not the zeroed one. *)
let fee_is_block = function Fee_block -> true | Fee_zero -> false

(** [true] iff the live base fee has been zeroed for a system call. *)
let fee_is_zero = function Fee_zero -> true | Fee_block -> false

(** The live [self.cfg.disable_nonce_check]: [Nonce_checked] is the ordinary
    regime, [Nonce_off] the one the system-call swap installs (mod.rs:196,
    :203). *)
type nonce_env = Nonce_checked | Nonce_off

(** Total order index for {!nonce_env}. *)
let nonce_env_index = function Nonce_checked -> 0 | Nonce_off -> 1

(** Total order on {!nonce_env}. *)
let nonce_env_compare a b =
  Int.compare (nonce_env_index a) (nonce_env_index b)

(** [true] iff revm is still checking transaction nonces. *)
let nonce_is_checked = function
  | Nonce_checked -> true
  | Nonce_off -> false

(** [true] iff the nonce check is disabled. *)
let nonce_is_off = function Nonce_off -> true | Nonce_checked -> false

(** The registry epoch: [Reg_open] is the epoch still running, [Reg_concluded]
    is [concludeEpoch] committed (block.rs:829-831, :193-228). *)
type registry = Reg_open | Reg_concluded

(** Total order index for {!registry}. *)
let registry_index = function Reg_open -> 0 | Reg_concluded -> 1

(** Total order on {!registry}. *)
let registry_compare a b = Int.compare (registry_index a) (registry_index b)

(** [true] iff the epoch transition committed. *)
let registry_is_concluded = function
  | Reg_concluded -> true
  | Reg_open -> false

(** What the governance base-fee address received from the block's user
    transaction.

    - [Sink_untouched] the transaction never executed;
    - [Sink_penalty_only] it executed but the live base fee was zero, so
      [basefee * gas_used] (handler.rs:168) credited nothing and only the
      gas-limit over-estimation penalty (handler.rs:125-131) landed;
    - [Sink_basefee_share] the ordinary regime: the base-fee portion of the fee
      reached the sink. *)
type sink = Sink_untouched | Sink_penalty_only | Sink_basefee_share

(** Total order index for {!sink}, ordered by how much reached the sink. *)
let sink_index = function
  | Sink_untouched -> 0
  | Sink_penalty_only -> 1
  | Sink_basefee_share -> 2

(** Total order on {!sink}. *)
let sink_compare a b = Int.compare (sink_index a) (sink_index b)

(** [true] iff the base-fee portion of the user transaction's fee reached the
    governance sink. *)
let sink_is_basefee_share = function
  | Sink_basefee_share -> true
  | Sink_untouched | Sink_penalty_only -> false

(** What became of the block's user transaction: still pending, skipped because
    revm rejected it (lib.rs:791-795), or executed and committed. *)
type tx_fate = Tx_pending | Tx_rejected | Tx_executed

(** Total order index for {!tx_fate}. *)
let tx_fate_index = function
  | Tx_pending -> 0
  | Tx_rejected -> 1
  | Tx_executed -> 2

(** Total order on {!tx_fate}. *)
let tx_fate_compare a b = Int.compare (tx_fate_index a) (tx_fate_index b)

(** [true] iff the user transaction ran rather than being skipped. *)
let fate_is_executed = function
  | Tx_executed -> true
  | Tx_pending | Tx_rejected -> false

(** The joint global state: one block's execution context, the live EVM
    environment, and what the block did. *)
type state = {
  kind : block_kind;  (** whether [ctx.close_epoch] is [Some] *)
  verdict : registry_verdict;  (** the unvendored contract's decision *)
  body : tx_body;  (** the block's single user transaction *)
  phase : phase;  (** where block execution is *)
  fee : fee_env;  (** the live [self.block.basefee] *)
  nonce : nonce_env;  (** the live [self.cfg.disable_nonce_check] *)
  registry : registry;  (** whether the epoch transition committed *)
  sink : sink;  (** what the governance base-fee address received *)
  fate : tx_fate;  (** what became of the user transaction *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c0 = block_kind_compare s1.kind s2.kind in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = registry_verdict_compare s1.verdict s2.verdict in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = tx_body_compare s1.body s2.body in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = phase_compare s1.phase s2.phase in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = fee_env_compare s1.fee s2.fee in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = nonce_env_compare s1.nonce s2.nonce in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = registry_compare s1.registry s2.registry in
              if Bool.not (Int.equal c6 0) then c6
              else
                let c7 = sink_compare s1.sink s2.sink in
                if Bool.not (Int.equal c7 0) then c7
                else tx_fate_compare s1.fate s2.fate

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** The executing node's local view: its own execution state. [verdict] is
    absent because the contract's accept/revert decision is not something the
    Rust layer computes or reads. *)
type executor_view = {
  ev_kind : block_kind;  (** the context it built the block from *)
  ev_body : tx_body;  (** the transaction it holds *)
  ev_phase : phase;  (** where it is *)
  ev_fee : fee_env;  (** the live base fee *)
  ev_nonce : nonce_env;  (** the live nonce-check flag *)
  ev_registry : registry;  (** whether it committed the transition *)
  ev_sink : sink;  (** what it credited the governance sink *)
  ev_fate : tx_fate;  (** what it did with the transaction *)
}

(** Total deterministic comparison over ALL executor-view fields. *)
let executor_view_compare a b =
  let c0 = block_kind_compare a.ev_kind b.ev_kind in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = tx_body_compare a.ev_body b.ev_body in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = phase_compare a.ev_phase b.ev_phase in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = fee_env_compare a.ev_fee b.ev_fee in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = nonce_env_compare a.ev_nonce b.ev_nonce in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = registry_compare a.ev_registry b.ev_registry in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = sink_compare a.ev_sink b.ev_sink in
              if Bool.not (Int.equal c6 0) then c6
              else tx_fate_compare a.ev_fate b.ev_fate

(** A validator's local view.

    - [View_executor] is the producer's: its own execution state, everything
      except the unvendored contract's decision.
    - [View_replay_waiting] is the replay node's before it holds a sealed
      block. It carries NOTHING: a halted block is never assembled, never
      gossiped and never reaches it, so a node waiting on a block cannot tell a
      slow close-epoch block from an ordinary one from a block whose execution
      died.
    - [View_replay_header] is the replay node's once it holds the sealed block:
      the [extra_data] marker and nothing else, because
      [TnEvmConfig::context_for_block] (config.rs:150-178) reads exactly
      [block.extra_data.len()] to reconstruct [close_epoch] and nothing else on
      the header feeds that decision.
    - [View_idle] is the constant blank view of the eight non-participants. *)
type view =
  | View_executor of executor_view
  | View_replay_waiting
  | View_replay_header of marker
  | View_idle

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | ( View_idle,
      (View_replay_waiting | View_replay_header _ | View_executor _) ) ->
      -1
  | ( (View_replay_waiting | View_replay_header _ | View_executor _),
      View_idle ) ->
      1
  | View_replay_waiting, View_replay_waiting -> 0
  | View_replay_waiting, (View_replay_header _ | View_executor _) -> -1
  | (View_replay_header _ | View_executor _), View_replay_waiting -> 1
  | View_replay_header m1, View_replay_header m2 -> marker_compare m1 m2
  | View_replay_header _, View_executor _ -> -1
  | View_executor _, View_replay_header _ -> 1
  | View_executor e1, View_executor e2 -> executor_view_compare e1 e2

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** [V0] is the executing node: the producer running this block. *)
let executor = Validator.V0

(** [V1] is the replay node: the family's knowledge agent, whose entire input
    is the sealed header. *)
let replay_observer = Validator.V1

(** View projection. [V0] and [V1] are the two agents; [V2] .. [V9] are idle
    non-agents with the constant blank view and never appear under [K]. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_executor
        {
          ev_kind = s.kind;
          ev_body = s.body;
          ev_phase = s.phase;
          ev_fee = s.fee;
          ev_nonce = s.nonce;
          ev_registry = s.registry;
          ev_sink = s.sink;
          ev_fate = s.fate;
        }
  | Validator.V1 -> (
      match s.phase with
      | Ph_sealed -> View_replay_header (marker_of_kind s.kind)
      | Ph_pre | Ph_user | Ph_close | Ph_halted -> View_replay_waiting)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_close_marker_gate
      (** delete the [if let Some(randomness) = self.ctx.close_epoch {] guard at
          block.rs:794 (running its body unconditionally with a default
          randomness), so the fork boundary, [applyIncentives] and
          [concludeEpoch] fire in every executed block. Transition added:
          [Ph_user -> Ph_close] for an [Ordinary] block, hence a sealed block
          whose header carries no marker but whose registry epoch advanced. No
          sibling path confines the transition: [concludeEpochCall],
          [applyIncentivesCall] and [migrateValidatorSetsCall] are constructed
          at exactly one site each (block.rs:399, :414, :348), all three inside
          this one guard, and [apply_consensus_block_rewards] /
          [apply_closing_epoch_contract_call] have exactly one call site each
          (block.rs:824, :829). The Solidity registry is not vendored, so the
          possibility that IT refuses a premature call is carried as the
          {!Registry_reverts} branch rather than assumed away - and that branch
          halts the block (block.rs:215-219), so the deletion is observable
          either way. The assembler is downstream bookkeeping: it still reads
          [ctx.close_epoch] (block.rs:970-978), which is exactly why the marker
          and the transition come apart. *)
  | No_env_restore
      (** delete the three restore swaps at mod.rs:207-212, so the environment
          [transact_system_call] installed at mod.rs:199-203 survives the call.
          Transition changed: [Ph_pre -> Ph_user] now leaves [Fee_zero] and
          [Nonce_off] in place, so the block's user transaction runs inside the
          system-call window. No sibling path re-establishes the environment:
          [transact_raw] sets only the tx env and rebuilds only the handler,
          which carries just the sink address (mod.rs:147-162, handler.rs:34-44);
          [execute_transaction_without_commit] passes only [tx_env]
          (block.rs:860-885); [create_evm] runs once per block via
          [create_executor] (factory.rs:46-64, :148-158); there is no
          [disable_base_fee] flag anywhere in the tree; and the payload loop has
          no nonce bookkeeping of its own - it skips a transaction only BECAUSE
          revm rejected it (lib.rs:783-799). The one partial repair, the
          penalty credit to the same sink (handler.rs:124-131), is modelled as
          {!Sink_penalty_only} rather than omitted. *)
  | Nonzero_basefee_for_syscall
      (** delete the base-fee swap-in at mod.rs:201 (and its mirror restore at
          mod.rs:210), leaving the block's real base fee in force while the
          zero-gas-price system transaction (mod.rs:180) is validated.
          Transition changed: every [transact_system_call] is inadmissible, so
          [Ph_pre] goes straight to [Ph_halted] - the first casualty is the
          pre-block EIP-2935 call (block.rs:708-719), and the epoch-closing
          call (block.rs:199-209) is a fortiori inadmissible. No sibling path
          admits the call: [disable_base_fee] appears nowhere in the tree, so
          there is no cfg-level bypass; funding the system caller would not
          help, because a [gas_price: 0] transaction is below any non-zero base
          fee whatever the balance; the base fee is non-zero and agreed
          (config.rs:138 from payload.rs, voter-enforced at
          batch-validator/src/validator.rs:188-195, floored at
          [MIN_PROTOCOL_BASE_FEE], types/src/gas_accumulator.rs:204-208); and
          nothing retries - the engine propagates the failure out of its run
          loop with [?] (engine/src/lib.rs:262-264) and never re-queues. *)

(** [true] iff a zero-gas-price system transaction is admissible against the
    live block environment: the base-fee swap at mod.rs:201 is what buys the
    admission, so deleting it makes every system call fail. *)
let syscall_admissible mut =
  match mut with
  | Pristine | No_close_marker_gate | No_env_restore -> true
  | Nonzero_basefee_for_syscall -> false

(** The environment a system call leaves behind. Pristine and the two unrelated
    deletions restore it (mod.rs:207-212); {!No_env_restore} leaves the window
    open. *)
let env_after_syscall mut =
  match mut with
  | Pristine | No_close_marker_gate | Nonzero_basefee_for_syscall ->
      (Fee_block, Nonce_checked)
  | No_env_restore -> (Fee_zero, Nonce_off)

(** [true] iff [finish] runs its epoch-closing body for a block of this kind.
    Pristine and the two unrelated deletions consult [ctx.close_epoch]
    (block.rs:794); {!No_close_marker_gate} runs it unconditionally. *)
let close_body_runs mut kind =
  match mut with
  | Pristine | No_env_restore | Nonzero_basefee_for_syscall ->
      is_close_marked kind
  | No_close_marker_gate -> true

(** [apply_pre_execution_changes] (block.rs:769-785): the EIP-4788 and EIP-2935
    system calls open the window, run, and close it again. If the system call
    is inadmissible the block dies here (block.rs:714-719). *)
let pre_call_step mut s =
  match s.phase with
  | Ph_pre ->
      if syscall_admissible mut then
        let fee, nonce = env_after_syscall mut in
        [ { s with phase = Ph_user; fee; nonce } ]
      else [ { s with phase = Ph_halted } ]
  | Ph_user | Ph_close | Ph_sealed | Ph_halted -> []

(** The block's user transaction executes on the same EVM instance
    (block.rs:860-885). A duplicate-nonce transaction is rejected by revm and
    skipped by the payload loop (lib.rs:791-795) - unless the nonce check is
    off, in which case nothing else catches it. An executed transaction credits
    the governance sink the base-fee share under the ordinary regime
    (handler.rs:162-168) and only the over-estimation penalty when the base fee
    has leaked to zero (handler.rs:124-131). *)
let user_tx_step mut s =
  match s.phase with
  | Ph_user ->
      let rejected = tx_is_replayed s.body && nonce_is_checked s.nonce in
      let fate = if rejected then Tx_rejected else Tx_executed in
      let sink =
        if rejected then s.sink
        else if fee_is_block s.fee then Sink_basefee_share
        else Sink_penalty_only
      in
      let phase = if close_body_runs mut s.kind then Ph_close else Ph_sealed in
      [ { s with phase; fate; sink } ]
  | Ph_pre | Ph_close | Ph_sealed | Ph_halted -> []

(** The epoch-closing body of [finish] (block.rs:794-835): [applyIncentives]
    then [concludeEpoch]. A rejected call or a reverting contract is fatal
    (block.rs:205-219 -> lib.rs:802-803 -> engine/src/lib.rs:262-264), never
    skipped. *)
let close_call_step mut s =
  match s.phase with
  | Ph_close ->
      if Bool.not (syscall_admissible mut) then [ { s with phase = Ph_halted } ]
      else (
        match s.verdict with
        | Registry_accepts ->
            [ { s with phase = Ph_sealed; registry = Reg_concluded } ]
        | Registry_reverts -> [ { s with phase = Ph_halted } ])
  | Ph_pre | Ph_user | Ph_sealed | Ph_halted -> []

(** The transition relation: block execution advances one stage per step, and
    both terminals ([Ph_sealed], [Ph_halted]) have no successors. *)
let next_with mut s =
  List.concat [ pre_call_step mut s; user_tx_step mut s; close_call_step mut s ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** A block about to run its pre-execution system calls: the ordinary
    environment, an open epoch, an untouched sink and the transaction in hand. *)
let start kind verdict body =
  {
    kind;
    verdict;
    body;
    phase = Ph_pre;
    fee = Fee_block;
    nonce = Nonce_checked;
    registry = Reg_open;
    sink = Sink_untouched;
    fate = Tx_pending;
  }

(** An ordinary block, a registry that would accept, a fresh-nonce transaction.
    The canonical initial state. *)
let initial = start Ordinary Registry_accepts Tx_fresh

(** An ordinary block carrying a duplicate-nonce transaction. *)
let initial_replay = start Ordinary Registry_accepts Tx_replayed

(** An ordinary block in a world where the registry would refuse the closing
    calls; reachable only as a counterfactual, since an ordinary block never
    makes them. *)
let initial_reverts = start Ordinary Registry_reverts Tx_fresh

(** An ordinary block, refusing registry, duplicate-nonce transaction. *)
let initial_reverts_replay = start Ordinary Registry_reverts Tx_replayed

(** The epoch-closing block: [ctx.close_epoch] is [Some], the registry would
    accept, the transaction is fresh. *)
let initial_close = start Close_marked Registry_accepts Tx_fresh

(** The epoch-closing block carrying a duplicate-nonce transaction. *)
let initial_close_replay = start Close_marked Registry_accepts Tx_replayed

(** The epoch-closing block whose registry call would revert - the fail-loud
    branch (block.rs:215-219). *)
let initial_close_reverts = start Close_marked Registry_reverts Tx_fresh

(** The epoch-closing, reverting-registry block with a duplicate-nonce
    transaction. *)
let initial_close_reverts_replay = start Close_marked Registry_reverts Tx_replayed

(** Every initial state: the three free choices - context kind, contract
    verdict, transaction body - taken as a product, so nothing is proved only
    on a happy branch. *)
let inits =
  [
    initial;
    initial_replay;
    initial_reverts;
    initial_reverts_replay;
    initial_close;
    initial_close_replay;
    initial_close_reverts;
    initial_close_reverts_replay;
  ]

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Close_marked_block
      (** [ctx.close_epoch] is [Some], equivalently the assembled header
          carries the 32-byte [extra_data] marker (config.rs:190, :157-167,
          block.rs:970) *)
  | Registry_concluded
      (** [concludeEpoch] committed and the registry epoch advanced
          (block.rs:829-831 -> :193-228) *)
  | Block_sealed  (** [finish] returned and the block was assembled *)
  | Block_halted
      (** block execution returned a fatal error and the engine's run loop
          stopped (block.rs:205-219, engine/src/lib.rs:262-264) *)
  | Executing_user_txs
      (** the block's user transaction is running on the shared EVM instance
          (block.rs:860-885) *)
  | Fee_env_zeroed
      (** the live [self.block.basefee] is the zero the system-call swap
          installs (mod.rs:195, :201) *)
  | Nonce_check_disabled
      (** the live [self.cfg.disable_nonce_check] is the [true] the
          system-call swap installs (mod.rs:196, :203) *)
  | User_tx_executed
      (** the block's user transaction ran rather than being skipped
          (lib.rs:791-795) *)
  | Replay_offered
      (** the block body's user transaction carries an already-used nonce *)
  | Replay_executed
      (** a duplicate-nonce transaction was actually executed and committed *)
  | Sink_got_basefee_share
      (** the governance base-fee address received [basefee * gas_used]
          (handler.rs:162-168), not merely the over-estimation penalty *)
  | Registry_would_accept
      (** the unvendored [ConsensusRegistry] would accept this block's closing
          calls *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Close_marked_block -> is_close_marked s.kind
  | Registry_concluded -> registry_is_concluded s.registry
  | Block_sealed -> phase_is_sealed s.phase
  | Block_halted -> phase_is_halted s.phase
  | Executing_user_txs -> phase_is_user s.phase
  | Fee_env_zeroed -> fee_is_zero s.fee
  | Nonce_check_disabled -> nonce_is_off s.nonce
  | User_tx_executed -> fate_is_executed s.fate
  | Replay_offered -> tx_is_replayed s.body
  | Replay_executed -> tx_is_replayed s.body && fate_is_executed s.fate
  | Sink_got_basefee_share -> sink_is_basefee_share s.sink
  | Registry_would_accept -> verdict_accepts s.verdict

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Close_marked_block -> "close_marked(b)"
  | Registry_concluded -> "registry_epoch_advanced"
  | Block_sealed -> "sealed(b)"
  | Block_halted -> "halted"
  | Executing_user_txs -> "running_user_txs"
  | Fee_env_zeroed -> "basefee_env=0"
  | Nonce_check_disabled -> "nonce_check_disabled"
  | User_tx_executed -> "user_tx_executed"
  | Replay_offered -> "replay_offered"
  | Replay_executed -> "replay_executed"
  | Sink_got_basefee_share -> "sink_got_basefee_share"
  | Registry_would_accept -> "registry_would_accept"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every reachable
    world by test/t_close_block_syscall_topos.ml. Every transition strictly
    advances the phase and the two terminals have no successors, so reachability
    is expected to be antisymmetric - but that is settled by RUNNING the gate,
    not by this comment. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the eight initial states,
    mutation-parameterized transitions, the two-agent view, the atom
    valuation. *)
let spec_of mut = { Checker.init = inits; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
