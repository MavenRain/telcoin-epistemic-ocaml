(** Finite interpreted system for the FEE_ROUTING_SINK family: where every wei
    a telcoin-network block charges actually lands, who the payee is, and what a
    node can and cannot learn about its peers' fee-sink configuration. File
    citations refer to Telcoin-Association/telcoin-network at git HEAD
    [0c59c15b] and were opened in that checkout.

    {1 The three mechanisms this abstracts}

    {2 A. The fee split (crates/tn-reth/src/evm/handler.rs)}

    [TNEvmHandler] overrides revm's [reward_beneficiary] and [reimburse_caller]:

    - handler.rs:148-160 - [let beneficiary = context.block().beneficiary();],
      [let basefee = context.block().basefee() as u128;],
      [let coinbase_gas_price = effective_gas_price.saturating_sub(basefee);]
      then [load_account_mut(beneficiary)?.incr_balance(coinbase_gas_price *
      gas_used)]. The [saturating_sub] at handler.rs:156 is the gate: the block
      producer is credited the PRIORITY TIP only.
    - handler.rs:162-168 - [load_account_mut(self.basefee_address)?
      .incr_balance(basefee * gas_used)], under the comment "send the base fee
      portion to a basefee account for later processing (offchain)". This is
      where TN departs from stock revm, which burns the base fee.
    - handler.rs:109-131 - the over-estimation penalty
      [calculate_gas_penalty(gas_limit, gas_spent)] is subtracted from the
      caller's refund (handler.rs:112-113) and transferred to the SAME sink
      (handler.rs:125-131), a separate [incr_balance] site from the base-fee one.
    - handler.rs:30-44 - the sink is [basefee_address()] bound into the handler
      by [TNEvmHandler::new(basefee_address())].
    - handler.rs:85-87 / :145-147 - system calls are skipped entirely, so the
      only [incr_balance] sites in the whole handler are handler.rs:121 (caller
      refund), :127-130 (penalty to sink), :157-160 (tip to producer) and
      :165-168 (base fee to sink). There is no second producer credit.

    Amounts are normalized to ONE unit of gas used with
    [effective_gas_price = basefee + tip], both one unit of value, and a
    one-unit penalty when the caller over-estimated the gas limit; so the
    caller is charged 2 (efficient) or 3 (wasteful) and the two credit legs
    must sum to exactly that. The gas_penalty_split family owns the arithmetic
    of [calculate_gas_penalty] itself; here the penalty is symbolic.

    {2 B. The beneficiary binding (consensus executor -> engine -> evm)}

    - crates/consensus/executor/src/subscriber.rs:522-526 -
      [batches.push(CertifiedBatch { address:
      self.authority_execution_address(header.author())?, batches: cert_batches
      })]. The payee is looked up from committee state keyed by the CERTIFICATE
      author, and the lookup is fallible: subscriber.rs:422-434 returns
      [SubscriberError::UnexpectedAuthority] when the author is missing from the
      committee, and subscriber.rs:439-440 documents that such an error "is BAD
      and will most likely cause node shutdown" - there is NO fallback payee.
    - crates/types/src/primary/output.rs:33-40 - [CertifiedBatch.address] is
      documented as "the ECDSA address of the authority that produced the batch.
      This address is used as the block beneficiary during execution."
    - crates/engine/src/payload_builder.rs:153-164 -
      [TNPayload::new(canonical_header, cert_batch.address, ...)];
      crates/tn-reth/src/evm/config.rs:133 - [beneficiary: payload.beneficiary];
      crates/tn-reth/src/evm/block.rs:983 -
      [beneficiary: evm_env.block_env.beneficiary()] COPIES the env value into
      the assembled header rather than re-deriving it.
    - Meanwhile the proposer's own self-declared payee survives unread:
      crates/types/src/worker/sealed_batch.rs:68-70 - [Batch.beneficiary], "the
      160-bit address to which all fees collected from the successful mining of
      this batch be transferred; formally Hc", set by the worker from its own
      arguments (crates/batch-builder/src/batch.rs:49,123). The entire voter-side
      check list at crates/batch-validator/src/validator.rs:39-82 is digest,
      worker id, epoch, size in bytes, decode/recover, no-4844, total gas and
      base fee (validator.rs:188-195) - and contains NO beneficiary check. The
      field is authenticated by nothing and read by nothing.

    {2 C. The sink is a node-local immutable that no message carries}

    - crates/tn-reth/src/lib.rs:194-210 -
      [static BASEFEE_ADDRESS: OnceLock<Address>],
      [pub fn basefee_address() -> Address {
      *BASEFEE_ADDRESS.get().unwrap_or(&GOVERNANCE_SAFE_ADDRESS) }] and
      [fn set_basefee_address(address: Option<Address>) { let _ =
      BASEFEE_ADDRESS.set(address.unwrap_or(GOVERNANCE_SAFE_ADDRESS)); }], whose
      doc says verbatim "This will only work on the first call ... Calling more
      than once will do nothing, not calling early can lead to an unset basefee
      address and a chain fork."
    - crates/tn-reth/src/lib.rs:650-662 - [set_basefee_address] is called inside
      [RethEnv::new], and crates/node/src/manager/node.rs:1247-1264 constructs
      [RethEnv] (hence writes the slot) BEFORE [ExecutionNode::new], so on the
      node path no block can execute against an unwritten slot. That ordering is
      why this model's pipeline cannot leave [Booting] until both slots are
      locked.
    - crates/node/src/manager/node.rs:1253 -
      [self.builder.tn_config.parameters.basefee_address], a field of the node's
      OWN parameters file (crates/config/src/node.rs:277-278,
      [pub basefee_address: Option<Address>], defaulting to [None] at node.rs:366
      and written per node by crates/telcoin-network-cli/src/genesis/mod.rs:305).
      It is in no genesis alloc, no committee file, no [Batch]
      (sealed_batch.rs:63-89) and no [CertifiedBatch] (output.rs:33-40).
    - Because lib.rs:201 and lib.rs:209 BOTH funnel through
      [unwrap_or(GOVERNANCE_SAFE_ADDRESS)], a node that left the parameter unset
      and a node that set it explicitly to the governance safe are
      indistinguishable in every observable - that collapse is modelled as the
      two peer configurations [Peer_defaulted] and [Peer_explicit Gov].

    {2 The repair path this family MODELS rather than omits}

    A divergent sink is not invisible forever. A primary header carries the
    proposer's execution tip (crates/types/src/primary/header.rs:31,159-160,
    [latest_execution_block: BlockNumHash]) and the vote handler refuses to vote
    on a header whose tip it has not itself executed:
    crates/consensus/primary/src/network/handler.rs:639-650 calls
    [wait_for_execution(header.latest_execution_block())] and returns
    [HeaderError::UnknownExecutionResult] on failure;
    crates/consensus/primary/src/consensus_bus.rs:620-648 resolves [Ok] only if
    [recent_blocks().contains_execution_hash(block.hash)]. Since this model
    holds every other execution input fixed and shared (same consensus output,
    same batch, same base fee, same committee) the executed-block hash is a
    function of the crediting node's own fee sink alone, so that comparison is
    exactly the [Tip_match] / [Tip_mismatch] observation. Omitting it would make
    the opacity conjunct true only because the model forgot a protocol
    observable; including it is what forces the opacity claim into its honest
    form - opacity holds UNTIL the tip comparison, a match proves the sinks
    agree, and a mismatch proves they differ without ever revealing which
    address the peer used or how it was configured.

    Out of scope, and deliberately not modelled: the epoch-close incentives
    system call (crates/tn-reth/src/evm/block.rs:145-190,
    [apply_consensus_block_rewards], "increase the beneficiary account balance
    and withdraw from governance safe") credits authorities from the governance
    safe through [ConsensusRegistry]. That is issuance, not the settlement of a
    block's fee charge, it is a different value path owned by the epoch_reward
    family, and no statement here claims anything about a validator's total
    income. The empty-output path (payload_builder.rs:99-120) does its own
    committee lookup but executes zero transactions, so it routes no fees and
    cannot repair or contradict the batch path.

    {1 Components}

    - [own] - the observing node's [OnceLock<Address>], [Own_unresolved] before
      [RethEnv::new], [Own_locked Gov] after. Its config is pinned to the
      governance default; the epistemic content of this family is entirely about
      the PEER's parameter, and letting the observer's own parameter range too
      would only multiply the frame.
    - [peer] - the peer node's parameter and slot: unresolved, resolved from an
      absent parameter ([Peer_defaulted]), or resolved from an explicit
      [Some(a)] for one of the three distinguishable addresses.
    - [stage] - Booting -> Proposed -> {Certified, Aborted} -> Settled.
    - [gas] - the settled transaction's gas profile, efficient or wasteful; a
      wasteful one assesses the over-estimation penalty.
    - [producer] / [sink_take] - which legs of the charge each destination got.
    - [payee] - which address the block env named as beneficiary.
    - [obs] - the observer's comparison of the peer's [latest_execution_block].

    {1 Role mapping}

    V0 is the ONLY knowledge agent and has a real, non-constant view: its own
    slot, the pipeline stage, the settlement summary it computed locally, and
    its own tip comparison. It does NOT see [peer] - no protocol message carries
    a node's [basefee_address], so the peer's parameter is outside every
    projection. The settlement summary is shared because both nodes execute the
    same consensus output and therefore compute the same SHAPE of the routing;
    what differs between them is the IDENTITY of the credited sink, which is
    each node's own [peer]/[own] value, and that is precisely why divergence is
    invisible in the summary. V1..V9 are idle here: constant blank view, never
    under K. *)

(** A fee-sink address. [Gov] is [GOVERNANCE_SAFE_ADDRESS], the
    [unwrap_or] default of both lib.rs:201 and lib.rs:209; [Alt1] and [Alt2] are
    two distinct non-governance addresses an operator can put in
    [parameters.basefee_address] (config/src/node.rs:277-278). Two of them, not
    one, because a node that learns its peer diverged still must not learn WHICH
    address the peer used. *)
type sink = Gov | Alt1 | Alt2

(** Total order index for {!sink}. *)
let sink_index = function Gov -> 0 | Alt1 -> 1 | Alt2 -> 2

(** Total order on {!sink}. *)
let sink_compare a b = Int.compare (sink_index a) (sink_index b)

(** Equality on {!sink} via its total order; no polymorphic compare. *)
let sink_eq a b = Int.equal 0 (sink_compare a b)

(** The observing node's [BASEFEE_ADDRESS] slot (tn-reth/src/lib.rs:196-210).
    [Own_unresolved] is the window before [RethEnv::new] writes it; on the node
    path nothing can execute in that window (node.rs:1247-1264). *)
type own_slot = Own_unresolved | Own_locked of sink

(** Total order index for {!own_slot}. *)
let own_index = function Own_unresolved -> 0 | Own_locked _ -> 1

(** Total order on {!own_slot}: unresolved first, then by address. *)
let own_compare a b =
  match (a, b) with
  | Own_unresolved, Own_unresolved -> 0
  | Own_unresolved, Own_locked _ -> -1
  | Own_locked _, Own_unresolved -> 1
  | Own_locked x, Own_locked y -> sink_compare x y

(** [true] iff the observer's slot holds the governance default. *)
let own_is_gov = function
  | Own_unresolved -> false
  | Own_locked s -> sink_eq s Gov

(** The peer node's parameter and slot. [Peer_defaulted] is
    [parameters.basefee_address = None] resolving through
    [unwrap_or(GOVERNANCE_SAFE_ADDRESS)] (lib.rs:209); [Peer_explicit a] is
    [Some(a)]. [Peer_defaulted] and [Peer_explicit Gov] resolve to the SAME
    address and are indistinguishable in every observable - the collapse is the
    point, not an accident. *)
type peer_slot =
  | Peer_unresolved
  | Peer_defaulted
  | Peer_explicit of sink

(** Total order index for {!peer_slot}. *)
let peer_index = function
  | Peer_unresolved -> 0
  | Peer_defaulted -> 1
  | Peer_explicit _ -> 2

(** Total order on {!peer_slot}: every cross-constructor arm spelled. *)
let peer_compare a b =
  match (a, b) with
  | Peer_unresolved, Peer_unresolved -> 0
  | Peer_defaulted, Peer_defaulted -> 0
  | Peer_explicit x, Peer_explicit y -> sink_compare x y
  | Peer_unresolved, (Peer_defaulted | Peer_explicit _) -> -1
  | Peer_defaulted, Peer_unresolved -> 1
  | Peer_defaulted, Peer_explicit _ -> -1
  | Peer_explicit _, (Peer_unresolved | Peer_defaulted) -> 1

(** [true] iff the peer's sink came from an explicit [Some(a)] in its own
    parameters file rather than from the [unwrap_or] default. *)
let peer_is_explicit = function
  | Peer_unresolved | Peer_defaulted -> false
  | Peer_explicit _ -> true

(** [true] iff the peer resolved the first non-governance address. *)
let peer_is_alt1 = function
  | Peer_unresolved | Peer_defaulted -> false
  | Peer_explicit a -> sink_eq a Alt1

(** The pipeline position of the one block this family settles. [Aborted] is
    the [SubscriberError::UnexpectedAuthority] branch of subscriber.rs:422-434:
    the committee lookup failed, so no [CertifiedBatch] and no block. *)
type stage = Booting | Proposed | Certified | Aborted | Settled

(** Total order index for {!stage}. *)
let stage_index = function
  | Booting -> 0
  | Proposed -> 1
  | Certified -> 2
  | Aborted -> 3
  | Settled -> 4

(** Total order on {!stage}. *)
let stage_compare a b = Int.compare (stage_index a) (stage_index b)

(** [true] iff the block's charge has been routed. *)
let stage_is_settled = function
  | Booting | Proposed | Certified | Aborted -> false
  | Settled -> true

(** [true] iff the committee lookup for the certificate author failed. *)
let stage_is_aborted = function
  | Booting | Proposed | Certified | Settled -> false
  | Aborted -> true

(** The settled transaction's gas profile. [Gas_wasteful] over-estimated its
    gas limit far enough that [calculate_gas_penalty] (handler.rs:109) assesses
    a penalty. *)
type gas = Gas_pending | Gas_efficient | Gas_wasteful

(** Total order index for {!gas}. *)
let gas_index = function
  | Gas_pending -> 0
  | Gas_efficient -> 1
  | Gas_wasteful -> 2

(** Total order on {!gas}. *)
let gas_compare a b = Int.compare (gas_index a) (gas_index b)

(** [true] iff a gas-limit over-estimation penalty was assessed. *)
let gas_is_wasteful = function
  | Gas_pending | Gas_efficient -> false
  | Gas_wasteful -> true

(** What the caller was charged, in units of value: nothing before settlement,
    base fee + tip for an efficient transaction, and one more unit of penalty
    for a wasteful one. *)
let charge_amount = function
  | Gas_pending -> 0
  | Gas_efficient -> 2
  | Gas_wasteful -> 3

(** Which legs of the charge the block producer's account received.
    [Producer_tip] is the pristine [saturating_sub(basefee)] outcome of
    handler.rs:156-160. *)
type producer_leg = Producer_uncredited | Producer_tip | Producer_tip_and_basefee

(** Total order index for {!producer_leg}. *)
let producer_index = function
  | Producer_uncredited -> 0
  | Producer_tip -> 1
  | Producer_tip_and_basefee -> 2

(** Total order on {!producer_leg}. *)
let producer_compare a b = Int.compare (producer_index a) (producer_index b)

(** [true] iff the producer's credit includes the base-fee leg. *)
let producer_has_basefee = function
  | Producer_uncredited | Producer_tip -> false
  | Producer_tip_and_basefee -> true

(** Value credited to the producer. *)
let producer_amount = function
  | Producer_uncredited -> 0
  | Producer_tip -> 1
  | Producer_tip_and_basefee -> 2

(** Which legs of the charge the fee sink received. The base-fee leg
    (handler.rs:165-168) and the penalty leg (handler.rs:127-130) are SEPARATE
    [incr_balance] sites, so the model keeps them separately observable: the
    penalty arriving is not evidence that the base fee arrived. *)
type sink_leg =
  | Sink_uncredited
  | Sink_basefee
  | Sink_penalty
  | Sink_basefee_and_penalty

(** Total order index for {!sink_leg}. *)
let sink_leg_index = function
  | Sink_uncredited -> 0
  | Sink_basefee -> 1
  | Sink_penalty -> 2
  | Sink_basefee_and_penalty -> 3

(** Total order on {!sink_leg}. *)
let sink_leg_compare a b = Int.compare (sink_leg_index a) (sink_leg_index b)

(** [true] iff the base-fee leg landed at the sink. *)
let sink_has_basefee = function
  | Sink_uncredited | Sink_penalty -> false
  | Sink_basefee | Sink_basefee_and_penalty -> true

(** [true] iff the over-estimation penalty landed at the sink. *)
let sink_has_penalty = function
  | Sink_uncredited | Sink_basefee -> false
  | Sink_penalty | Sink_basefee_and_penalty -> true

(** Value credited to the sink. *)
let sink_amount = function
  | Sink_uncredited -> 0
  | Sink_basefee -> 1
  | Sink_penalty -> 1
  | Sink_basefee_and_penalty -> 2

(** Which address the block env named as beneficiary. [Payee_author] is the
    committee execution address of the certificate author (subscriber.rs:524);
    [Payee_declared] is the batch's own unauthenticated [beneficiary] field
    (sealed_batch.rs:68-70), which the pristine model never reaches. *)
type payee = Payee_unbound | Payee_author | Payee_declared

(** Total order index for {!payee}. *)
let payee_index = function
  | Payee_unbound -> 0
  | Payee_author -> 1
  | Payee_declared -> 2

(** Total order on {!payee}. *)
let payee_compare a b = Int.compare (payee_index a) (payee_index b)

(** [true] iff the beneficiary is the committee address of the cert author. *)
let payee_is_author = function
  | Payee_unbound | Payee_declared -> false
  | Payee_author -> true

(** [true] iff the beneficiary is the batch's self-declared field. *)
let payee_is_declared = function
  | Payee_unbound | Payee_author -> false
  | Payee_declared -> true

(** The observer's comparison of a peer header's [latest_execution_block]
    against its own executed blocks (handler.rs:639-650, consensus_bus.rs:
    620-648). [Obs_unchecked] is "no peer header processed yet". *)
type obs = Obs_unchecked | Obs_match | Obs_mismatch

(** Total order index for {!obs}. *)
let obs_index = function
  | Obs_unchecked -> 0
  | Obs_match -> 1
  | Obs_mismatch -> 2

(** Total order on {!obs}. *)
let obs_compare a b = Int.compare (obs_index a) (obs_index b)

(** [true] iff no peer execution tip has been compared yet. *)
let obs_is_unchecked = function
  | Obs_unchecked -> true
  | Obs_match | Obs_mismatch -> false

(** [true] iff the compared peer execution tip matched. *)
let obs_is_match = function
  | Obs_unchecked | Obs_mismatch -> false
  | Obs_match -> true

(** [true] iff the compared peer execution tip did not match. *)
let obs_is_mismatch = function
  | Obs_unchecked | Obs_match -> false
  | Obs_mismatch -> true

(** The joint global state. *)
type state = {
  own : own_slot;  (** the observer's [BASEFEE_ADDRESS] slot *)
  peer : peer_slot;  (** the peer's parameter and slot; in NO view *)
  stage : stage;  (** the pipeline position of the block being settled *)
  gas : gas;  (** the settled transaction's gas profile *)
  producer : producer_leg;  (** what the block producer's account got *)
  sink_take : sink_leg;  (** what the fee sink got *)
  payee : payee;  (** which address the block env named as beneficiary *)
  obs : obs;  (** the observer's peer-execution-tip comparison *)
}

(** Total deterministic comparison over ALL eight state fields. *)
let state_compare s1 s2 =
  let c = own_compare s1.own s2.own in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = peer_compare s1.peer s2.peer in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = stage_compare s1.stage s2.stage in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = gas_compare s1.gas s2.gas in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = producer_compare s1.producer s2.producer in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = sink_leg_compare s1.sink_take s2.sink_take in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = payee_compare s1.payee s2.payee in
              if Bool.not (Int.equal c6 0) then c6
              else obs_compare s1.obs s2.obs

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** [true] iff both slots are locked to the same address. This is the hidden
    fact the family's knowledge operands range over: it reads [peer], which
    appears in no view and in no protocol message. *)
let sinks_agree s =
  match (s.own, s.peer) with
  | Own_unresolved, (Peer_unresolved | Peer_defaulted | Peer_explicit _) -> false
  | Own_locked _, Peer_unresolved -> false
  | Own_locked a, Peer_defaulted -> sink_eq a Gov
  | Own_locked a, Peer_explicit b -> sink_eq a b

(** A validator's local view. [View_v0] is the observing node's projection -
    its own slot, the pipeline stage, the settlement summary it computed
    locally (gas profile, producer leg, sink leg, payee) and its own execution
    tip comparison. It carries NO component of [peer]: a node's
    [basefee_address] is a field of its own parameters file
    (config/src/node.rs:277-278) and is absent from genesis, the committee file,
    [Batch] and [CertifiedBatch]. [View_idle] is the constant blank view of the
    non-agents V1..V9. *)
type view =
  | View_v0 of own_slot * stage * gas * producer_leg * sink_leg * payee * obs
  | View_idle

(** Total deterministic order over ALL seven fields of the observer's view. *)
let view_v0_compare (k, st, g, p, sk, py, o) (k', st', g', p', sk', py', o') =
  let c = own_compare k k' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = stage_compare st st' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = gas_compare g g' in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = producer_compare p p' in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = sink_leg_compare sk sk' in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = payee_compare py py' in
            if Bool.not (Int.equal c5 0) then c5 else obs_compare o o'

(** Total order on views: [View_idle] < [View_v0]. Every constructor is
    spelled; no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_v0 _ -> -1
  | View_v0 _, View_idle -> 1
  | View_v0 (k, st, g, p, sk, py, o), View_v0 (k', st', g', p', sk', py', o') ->
      view_v0_compare (k, st, g, p, sk, py, o) (k', st', g', p', sk', py', o')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 is the single knowledge agent; V1..V9 are idle
    non-agents with the constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_v0 (s.own, s.stage, s.gas, s.producer, s.sink_take, s.payee, s.obs)
  | Validator.V1 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** The knowledge agent of this family, and the battery agent of its topos
    gate: the observing node, whose view is a strict projection of the state. *)
let observer = Validator.V0

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | Basefee_to_producer
      (** delete the [saturating_sub(basefee)] at
          crates/tn-reth/src/evm/handler.rs:156, crediting the beneficiary
          [effective_gas_price * gas_used] instead of
          [(effective_gas_price - basefee) * gas_used]. Transition changed: the
          settle step now produces [Producer_tip_and_basefee] instead of
          [Producer_tip], while handler.rs:165-168 STILL pays the sink its
          base-fee leg, so the two credit legs now sum to more than the caller
          was charged. No sibling path repairs it: the only [incr_balance] sites
          in the handler are handler.rs:121 (caller refund), :127-130 (penalty
          to sink), :157-160 (this one) and :165-168 (base fee to sink), so
          nothing else re-splits the charge; the producer cannot instead point
          the sink at itself because the sink is a node-local startup parameter
          (config/src/node.rs:277-278, node.rs:1253-1258, tn-reth/src/lib.rs:
          196-210) that no batch or certificate field can redirect; and it
          cannot inflate the base fee it is paid on because every voter rejects
          a batch whose base fee differs from the worker/epoch expectation
          (batch-validator/src/validator.rs:188-195). *)
  | Basefee_burned
      (** delete the sink credit at crates/tn-reth/src/evm/handler.rs:165-168,
          i.e. revert to stock revm, which burns the base fee instead of
          redirecting it. Transition changed: the settle step drops the
          base-fee leg from [sink_take], so an efficient transaction credits the
          sink nothing and a wasteful one credits it the penalty alone, and the
          two legs now sum to less than the caller was charged. No sibling path
          repairs it: the penalty transfer at handler.rs:125-131 is a SEPARATE
          [incr_balance] to the same account and carries only
          [effective_gas_price * penalty_gas], never the base fee - which is
          exactly why [sink_leg] keeps the two legs separately observable rather
          than as one balance. *)
  | Beneficiary_from_batch_field
      (** replace the committee lookup at
          crates/consensus/executor/src/subscriber.rs:524 with
          [address: batch.beneficiary], the batch's own unauthenticated field.
          Transitions changed: the certify step now binds [Payee_declared], and
          the [Aborted] branch disappears because reading a struct field cannot
          fail the way [authority_execution_address] can (subscriber.rs:
          422-434). No sibling path repairs it: the entire voter-side check list
          (batch-validator/src/validator.rs:39-82: digest, worker id, epoch,
          size in bytes, decode/recover, no-4844, total gas, base fee) contains
          NO beneficiary check, so admission never constrains the field;
          block.rs:983 copies [evm_env.block_env.beneficiary()] into the
          assembled header rather than re-deriving it, so the assembler is not a
          repair; and the empty-output committee lookup at payload_builder.rs:
          104-107 is a disjoint branch that executes no transactions. *)
  | Mutable_fee_sink
      (** replace the [OnceLock::set] once-semantics at
          crates/tn-reth/src/lib.rs:207-210 with an unconditional store, so a
          second [set_basefee_address] takes effect and the node re-resolves its
          sink mid-run. Transition added: [Own_locked Gov -> Own_locked Alt1] at
          ANY stage, so two blocks of the same epoch on the same node credit
          different addresses. Modelled one-directionally (Gov to Alt1) because
          one direction already refutes the invariant and the reverse edge would
          add no new refuting path while making the frame cyclic. No sibling
          path repairs it: [basefee_address] appears only in
          config/src/node.rs:277-278/366, node/src/manager/node.rs:1253-1258,
          telcoin-network-cli/src/genesis/mod.rs:47-53/305/333,
          tn-reth/src/lib.rs:196-210/654-662 and evm/handler.rs:5/42, and is in
          no genesis alloc, no committee file, no [Batch] and no
          [CertifiedBatch], so no protocol message can re-agree the sink; the
          execution-tip comparison the model DOES carry
          (primary/src/network/handler.rs:639-650) detects the resulting
          divergence but never restores the previous address. *)

(** The observer's own [set_basefee_address] step. Pristine the slot is written
    exactly once, from the observer's own parameters file, to the governance
    default; under [Mutable_fee_sink] a locked slot can be rewritten. *)
let sink_step mut s =
  match s.own with
  | Own_unresolved -> [ { s with own = Own_locked Gov } ]
  | Own_locked Gov -> (
      match mut with
      | Pristine | Basefee_to_producer | Basefee_burned
      | Beneficiary_from_batch_field ->
          []
      | Mutable_fee_sink -> [ { s with own = Own_locked Alt1 } ])
  | Own_locked Alt1 | Own_locked Alt2 -> []

(** The peer's [set_basefee_address] step: it boots with one of the four
    distinguishable configurations - parameter absent, or explicitly set to one
    of the three addresses. Which one is chosen is the hidden branch of this
    family. *)
let peer_step s =
  match s.peer with
  | Peer_unresolved ->
      List.map
        (fun p -> { s with peer = p })
        [ Peer_defaulted; Peer_explicit Gov; Peer_explicit Alt1;
          Peer_explicit Alt2 ]
  | Peer_defaulted | Peer_explicit _ -> []

(** What the producer's account receives at settlement. *)
let producer_credit_of = function
  | Pristine | Basefee_burned | Beneficiary_from_batch_field | Mutable_fee_sink
    ->
      Producer_tip
  | Basefee_to_producer -> Producer_tip_and_basefee

(** What the fee sink receives at settlement, per gas profile. *)
let sink_credit_of mut g =
  match (mut, g) with
  | ( ( Pristine | Basefee_to_producer | Beneficiary_from_batch_field
      | Mutable_fee_sink ),
      Gas_efficient ) ->
      Sink_basefee
  | ( ( Pristine | Basefee_to_producer | Beneficiary_from_batch_field
      | Mutable_fee_sink ),
      Gas_wasteful ) ->
      Sink_basefee_and_penalty
  | Basefee_burned, Gas_efficient -> Sink_uncredited
  | Basefee_burned, Gas_wasteful -> Sink_penalty
  | ( ( Pristine | Basefee_to_producer | Basefee_burned
      | Beneficiary_from_batch_field | Mutable_fee_sink ),
      Gas_pending ) ->
      Sink_uncredited

(** Settle the block against one gas profile: route the charge. *)
let settle mut g s =
  {
    s with
    stage = Settled;
    gas = g;
    producer = producer_credit_of mut;
    sink_take = sink_credit_of mut g;
  }

(** The observer's execution-tip comparison: [Obs_match] iff the peer's
    executed block hash is among its own, which in this model happens exactly
    when the two sinks resolved to the same address. *)
let observe s = if sinks_agree s then Obs_match else Obs_mismatch

(** The block pipeline's step. [Booting] cannot advance until BOTH slots are
    locked (node.rs:1247-1264: [RethEnv::new] writes the slot before
    [ExecutionNode::new] exists); [Proposed] either certifies with the
    committee address or aborts on [UnexpectedAuthority]; [Certified] settles
    against either gas profile; [Aborted] is terminal - there is no fallback
    payee; a settled block admits one tip comparison. *)
let pipeline_step mut s =
  match s.stage with
  | Booting -> (
      match (s.own, s.peer) with
      | Own_unresolved, (Peer_unresolved | Peer_defaulted | Peer_explicit _) ->
          []
      | Own_locked _, Peer_unresolved -> []
      | Own_locked _, (Peer_defaulted | Peer_explicit _) ->
          [ { s with stage = Proposed } ])
  | Proposed -> (
      match mut with
      | Pristine | Basefee_to_producer | Basefee_burned | Mutable_fee_sink ->
          [ { s with stage = Certified; payee = Payee_author };
            { s with stage = Aborted } ]
      | Beneficiary_from_batch_field ->
          [ { s with stage = Certified; payee = Payee_declared } ])
  | Certified -> List.map (fun g -> settle mut g s) [ Gas_efficient; Gas_wasteful ]
  | Aborted -> []
  | Settled -> (
      match s.obs with
      | Obs_unchecked -> [ { s with obs = observe s } ]
      | Obs_match | Obs_mismatch -> [])

(** The transition relation: the two nodes resolve their sinks, then the one
    block runs its pipeline. Every step strictly advances one of (own slot,
    peer slot, stage, tip comparison) along a fixed order and reverses nothing,
    so the reachability relation is acyclic under every mutation. Terminal
    states are stutter-closed by the kernel. *)
let next_with mut s = sink_step mut s @ peer_step s @ pipeline_step mut s

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: neither node has run [RethEnv::new] yet, nothing is
    proposed, nothing is credited, no tip has been compared. *)
let initial =
  {
    own = Own_unresolved;
    peer = Peer_unresolved;
    stage = Booting;
    gas = Gas_pending;
    producer = Producer_uncredited;
    sink_take = Sink_uncredited;
    payee = Payee_unbound;
    obs = Obs_unchecked;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Settled_block  (** settled(b): the block's charge has been routed *)
  | Lookup_failed
      (** unknown_author(b): the committee lookup for the certificate author
          failed, so no block exists *)
  | Producer_took_basefee
      (** credit(beneficiary) includes the base-fee leg *)
  | Basefee_at_sink  (** credit(fee_sink) includes the base-fee leg *)
  | Penalty_assessed  (** penalty_gas(tx) > 0: the caller over-estimated *)
  | Penalty_at_sink  (** credit(fee_sink) includes the penalty leg *)
  | Fees_conserved
      (** credit(beneficiary) + credit(fee_sink) = charge(tx) *)
  | Payee_is_author
      (** beneficiary(b) = committee_execution_address(author(cert(b))) *)
  | Payee_is_declared  (** beneficiary(b) = batch(b).beneficiary *)
  | Sink_locked_gov  (** sink(V0) is locked to the governance default *)
  | Sinks_agree  (** sink(V0) = sink(peer): the hidden fact *)
  | Peer_sink_explicit
      (** the peer's parameters file carried Some(addr) rather than relying on
          the unwrap_or default *)
  | Peer_sink_is_alt1  (** the peer resolved the first non-governance address *)
  | Tip_match  (** the peer's latest_execution_block matched V0's own *)
  | Tip_mismatch  (** the peer's latest_execution_block did not match *)
  | Tip_unchecked  (** V0 has not yet compared any peer execution tip *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Settled_block -> stage_is_settled s.stage
  | Lookup_failed -> stage_is_aborted s.stage
  | Producer_took_basefee -> producer_has_basefee s.producer
  | Basefee_at_sink -> sink_has_basefee s.sink_take
  | Penalty_assessed -> gas_is_wasteful s.gas
  | Penalty_at_sink -> sink_has_penalty s.sink_take
  | Fees_conserved ->
      Int.equal
        (producer_amount s.producer + sink_amount s.sink_take)
        (charge_amount s.gas)
  | Payee_is_author -> payee_is_author s.payee
  | Payee_is_declared -> payee_is_declared s.payee
  | Sink_locked_gov -> own_is_gov s.own
  | Sinks_agree -> sinks_agree s
  | Peer_sink_explicit -> peer_is_explicit s.peer
  | Peer_sink_is_alt1 -> peer_is_alt1 s.peer
  | Tip_match -> obs_is_match s.obs
  | Tip_mismatch -> obs_is_mismatch s.obs
  | Tip_unchecked -> obs_is_unchecked s.obs

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Settled_block -> "settled(b)"
  | Lookup_failed -> "unknown_author(b)"
  | Producer_took_basefee -> "basefee_in_credit(beneficiary)"
  | Basefee_at_sink -> "basefee_in_credit(fee_sink)"
  | Penalty_assessed -> "penalty_gas(tx)>0"
  | Penalty_at_sink -> "penalty_in_credit(fee_sink)"
  | Fees_conserved -> "credits=charge"
  | Payee_is_author -> "beneficiary(b)=committee_addr(author)"
  | Payee_is_declared -> "beneficiary(b)=batch.beneficiary"
  | Sink_locked_gov -> "sink(V0)=governance_safe"
  | Sinks_agree -> "sink(V0)=sink(peer)"
  | Peer_sink_explicit -> "peer_param=Some(addr)"
  | Peer_sink_is_alt1 -> "sink(peer)=alt1"
  | Tip_match -> "peer_exec_tip=own_exec_tip"
  | Tip_mismatch -> "peer_exec_tip<>own_exec_tip"
  | Tip_unchecked -> "no_peer_tip_compared"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every reachable
    world by test/t_fee_routing_sink_topos.ml. Every transition of this family
    strictly advances one component of (own slot, peer slot, stage, tip
    comparison) and reverses nothing, so reachability is antisymmetric and [W]
    is a genuine finite poset - asserted by that gate under every mutation, not
    assumed here. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state, the
    mutation-parameterized transitions, the one-agent view, the atom
    valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
