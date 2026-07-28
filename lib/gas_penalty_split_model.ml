(** Finite interpreted system for the GAS-PENALTY-SPLIT family: TN's
    over-estimation gas penalty and the three-way redistribution of the gas
    charge, as seen by a node that must admit a batch BEFORE anyone can know
    what the batch will cost to execute.

    Mechanisms modeled, keyed to Telcoin-Association/telcoin-network
    (git 0c59c15b, working tree):

    - the penalty itself is the pure two-argument function
      [pub fn calculate_gas_penalty(gas_limit: u64, gas_used: u64) -> u64]
      (crates/tn-reth/src/evm/utils.rs:45-84). It has exactly two uniform
      exemption gates and no third input: gate one at utils.rs:47-49,
      [if gas_limit <= MIN_GAS_LIMIT_THRESHOLD { return 0; }] with
      [MIN_GAS_LIMIT_THRESHOLD = 210_000] (utils.rs:6); gate two at
      utils.rs:56-62, [usage_ratio_scaled = PRECISION * gas_used /
      gas_limit] then [if usage_ratio_scaled >= THRESHOLD { return 0; }]
      with [PRECISION = 10^9] (utils.rs:9) and [THRESHOLD = 10^8]
      (utils.rs:12), i.e. exactly 10%. Only past both gates does
      utils.rs:65-71 charge
      [(inefficiency_scaled^2 * unused_gas) / THRESHOLD_SQUARED] with
      [THRESHOLD_SQUARED = 10^16] (utils.rs:15). No account, sender,
      beneficiary or validator identity is in scope of that function;
    - the single production call site is
      crates/tn-reth/src/evm/handler.rs:109,
      [let penalty_gas = calculate_gas_penalty(gas_limit, gas_spent);],
      inside the only override of [reimburse_caller]
      (handler.rs:78-134). Its argument is PRE-refund gas
      ([let gas_spent = gas.spent();], handler.rs:91), deliberately not the
      post-refund figure ([let gas_used = gas.spent_sub_refunded();],
      handler.rs:92) that the refund arithmetic uses at handler.rs:112 -
      the 15-line doc block at handler.rs:62-76 defends exactly this
      choice ("Using post-refund gas would make the penalty *larger* than
      intended whenever an EVM refund occurs");
    - the split. revm's default [deduct_caller] is NOT overridden (the two
      overridden methods are [reimburse_caller] handler.rs:78-134 and
      [reward_beneficiary] handler.rs:137-171, and the impl block ends at
      handler.rs:172), so the caller is debited [gas_limit *
      effective_gas_price] up front. TN then re-credits at exactly four
      sites, the only [incr_balance] calls in crates/tn-reth/src: the
      caller gets [unused_gas.saturating_sub(penalty_gas)]
      (handler.rs:112-113, credited at :121), the governance sink gets the
      penalty (handler.rs:125-131, credited at :130), the block
      beneficiary gets [(effective_gas_price - basefee) * gas_used]
      (handler.rs:156-160), and the governance sink again gets
      [basefee * gas_used] (handler.rs:165-168). Unlike Ethereum, the base
      fee is redirected rather than burned;
    - system calls are exempt from both overrides
      (handler.rs:85-87 and :145-147); the code's own comment at
      handler.rs:143-144 records why this cannot change any balance
      ("gas_price and basefee are both 0, so all amounts are 0"). The
      model carries that branch as a canonical single path so the
      conservation statement is not stated only over the paths that
      happen to suit it;
    - admission. The batch validator sums the DECLARED per-transaction gas
      limits and bounds the sum by [max_batch_gas(epoch)] = 30,000,000
      (crates/batch-validator/src/validator.rs:162-185, the fold at :171,
      the cap at :176-182, [max_batch_gas] at
      crates/types/src/worker/sealed_batch.rs:190-194). It applies no
      per-transaction usage-ratio filter, and its own doc comment states
      the epistemic fact this family is built on: "Actual amount of gas
      used cannot be determined until execution" (validator.rs:160),
      echoed at handler.rs:100-101 ("due to the nature of TN consensus,
      actual gas cannot be determined until after consensus").

    Components: a phase ([Proposed] -> [Admitted] -> [Executed], terminal),
    a hidden execution profile resolved at the first transition (the
    system-call branch, or a user batch of two transactions carrying a
    declared limit class, a pre-refund usage class and an EVM-refund
    choice), and the settled ledger written by the handler at execution.
    The two user transactions are TWINS: same declared limit, same
    pre-refund spend, different senders, and only transaction [a] can earn
    an EVM refund. 27 reachable states.

    Role mapping. V0 IS the admission-time batch validator, the family's
    only knowledge agent. Its view is exactly its admission record: the
    declared gas limit class of the batch it validated (validator.rs:171
    reads [tx.gas_limit()], nothing else that feeds the penalty), and
    nothing about execution - not the pre-refund spend, not the EVM
    refund, not the resulting penalty, because those do not exist until
    after consensus (validator.rs:160, handler.rs:100-101). V0 never sees
    a system call at all - system calls are injected by the block executor
    through [transact_system_call] (crates/tn-reth/src/evm/block.rs:159-163),
    never carried in a batch - so that branch collapses into V0's
    [No_batch] view. V1..V9 are idle non-agents with the constant blank
    view and never appear under K.

    Why the view projection is what it is: the whole point of the penalty
    is that the protocol must commit to admitting a batch while the only
    penalty input it can read is the declared gas limit. Gate one
    (utils.rs:47-49) is a function of that visible field alone, so V0
    KNOWS at admission that a small-limit batch will never be penalised;
    gate two (utils.rs:56-62) is a function of the invisible execution
    outcome, so at a large declared limit V0 knows nothing of the kind.
    That asymmetry is the family's epistemic content.

    Arithmetic scaling. The model runs the real formula with the real
    210,000 limit threshold and real gas figures, but rescales the
    precision constants from [PRECISION = 10^9 / THRESHOLD = 10^8 /
    THRESHOLD_SQUARED = 10^16] to [10^4 / 10^3 / 10^6] so the quadratic
    fits OCaml's 63-bit int (the real code uses u128). The shape, the two
    gates and the normalisation are unchanged, and the rescaled function
    reproduces the documented table of utils.rs:36-44 exactly: 5% usage of
    a 420,000 limit still yields a 99,750 penalty on 399,000 unused gas. *)

(** [a <= b] on machine ints, routed through {!Int.compare} so no
    polymorphic comparison operator is applied to a structured value. *)
let at_most a b = Int.compare a b <= 0

(** [0 < n] on machine ints, routed through {!Int.compare}. *)
let positive n = Int.compare n 0 > 0

(** [a < b] on machine ints, routed through {!Int.compare}. *)
let below a b = Int.compare a b < 0

(** [MIN_GAS_LIMIT_THRESHOLD] of utils.rs:6, verbatim: gate one exempts
    every transaction declaring at most this much gas. *)
let min_gas_limit_threshold = 210_000

(** [PRECISION] of utils.rs:9, rescaled 10^9 -> 10^4 (see the header). *)
let precision = 10_000

(** [THRESHOLD] of utils.rs:12, rescaled 10^8 -> 10^3: the 10% usage ratio
    below which gate two stops exempting. *)
let threshold = 1_000

(** [THRESHOLD_SQUARED] of utils.rs:15, rescaled 10^16 -> 10^6: the
    normaliser that keeps the quadratic penalty at or below unused gas. *)
let threshold_squared = 1_000_000

(** The effective gas price of the modelled transactions, in wei per gas.
    [effective_gas_price] is read once at handler.rs:94 and again at
    handler.rs:150 and multiplies every credit; fixing it to a constant is
    faithful for legacy transactions and for 1559 transactions whose max
    fee equals basefee + tip, which is the case in which revm's unmodified
    [deduct_caller] debits exactly [gas_limit * effective_gas_price]. *)
let effective_gas_price = 2

(** The block base fee in wei per gas (handler.rs:93, :149). TN redirects
    it to the governance sink (handler.rs:165-168) instead of burning it;
    the beneficiary receives the remainder (handler.rs:156-160). *)
let basefee = 1

(** The declared gas limit class of the modelled batch - the ONLY penalty
    input the batch validator can read (validator.rs:171). *)
type limit_class =
  | Lc_small
      (** exactly [MIN_GAS_LIMIT_THRESHOLD] = 210,000 gas: gate one
          (utils.rs:47-49) exempts it whatever it does at execution *)
  | Lc_big
      (** 420,000 gas: past gate one, so the outcome depends on the
          invisible execution *)

(** Total order index for {!limit_class}. *)
let limit_class_index = function Lc_small -> 0 | Lc_big -> 1

(** Total order on {!limit_class}. *)
let limit_class_compare a b =
  Int.compare (limit_class_index a) (limit_class_index b)

(** How much of its declared limit the transaction really spends, PRE
    refund ([gas.spent()], handler.rs:91) - the penalty denominator. *)
type usage =
  | U_ge10  (** exactly 10% of the limit: gate two (utils.rs:59-62) exempts *)
  | U_low5  (** 5%: the documented 25%-of-unused penalty row, utils.rs:40 *)
  | U_near0  (** 1%: deep in the quadratic, utils.rs:41-44 *)

(** Total order index for {!usage}. *)
let usage_index = function U_ge10 -> 0 | U_low5 -> 1 | U_near0 -> 2

(** Total order on {!usage}. *)
let usage_compare a b = Int.compare (usage_index a) (usage_index b)

(** Whether transaction [a] earns an EVM refund (SSTORE clearing), the
    quantity [gas.spent_sub_refunded()] subtracts at handler.rs:92. Its
    twin [b] never earns one, which is what makes the pair a controlled
    comparison. *)
type refund =
  | R_none  (** no EVM refund: [spent_sub_refunded() = spent()] *)
  | R_some  (** half the pre-refund spend comes back as an EVM refund *)

(** Total order index for {!refund}. *)
let refund_index = function R_none -> 0 | R_some -> 1

(** Total order on {!refund}. *)
let refund_compare a b = Int.compare (refund_index a) (refund_index b)

(** The hidden execution profile of the modelled batch, resolved at the
    first transition and invisible to the admission-time validator. *)
type profile =
  | Prof_unchosen  (** labels the initial state only *)
  | Prof_system
      (** the block executor's system call (block.rs:159-163), which both
          handler overrides skip outright (handler.rs:85-87, :145-147) and
          which never travels in a batch, so V0 never sees it. Canonical
          single path: none of the user-transaction fields is meaningful
          for it *)
  | Prof_user of limit_class * usage * refund
      (** a user batch of two twin transactions: same declared limit, same
          pre-refund spend, different senders, and only [a] earns the EVM
          refund *)

(** Total order index of a {!profile} constructor. *)
let profile_index = function
  | Prof_unchosen -> 0
  | Prof_system -> 1
  | Prof_user _ -> 2

(** Total order on {!profile}: every cross-constructor arm spelled. *)
let profile_compare a b =
  match (a, b) with
  | Prof_unchosen, Prof_unchosen -> 0
  | Prof_system, Prof_system -> 0
  | Prof_user (lc, u, r), Prof_user (lc', u', r') ->
      let c = limit_class_compare lc lc' in
      if Bool.not (Int.equal c 0) then c
      else
        let c1 = usage_compare u u' in
        if Bool.not (Int.equal c1 0) then c1 else refund_compare r r'
  | Prof_unchosen, (Prof_system | Prof_user _)
  | Prof_system, Prof_user _
  | Prof_user _, (Prof_unchosen | Prof_system)
  | Prof_system, Prof_unchosen ->
      Int.compare (profile_index a) (profile_index b)

(** The phase machine: a batch is proposed, the admission-time validator
    accepts it after bounding the declared limits (validator.rs:162-185),
    and only then - after consensus - does the handler execute it and
    write the ledger. [Executed] is terminal; the kernel stutter-closes
    it. *)
type phase = Proposed | Admitted | Executed

(** Total order index for {!phase}. *)
let phase_index = function Proposed -> 0 | Admitted -> 1 | Executed -> 2

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The ledger the handler writes for the whole batch: what revm's
    unmodified [deduct_caller] debited, what the four [incr_balance] sites
    of crates/tn-reth/src credited (handler.rs:121, :130, :160, :168), how
    much of that landed in the governance sink, the penalty GAS charged to
    each twin, and the pre-saturation refund of twin [a]. *)
type ledger = {
  charged : int;
      (** total wei debited up front, [gas_limit * effective_gas_price]
          per transaction, by revm's default [deduct_caller] - which TN
          does not override (handler.rs:78-172) *)
  credited : int;
      (** total wei credited back across caller, beneficiary and sink *)
  sink : int;  (** wei credited to the governance sink (handler.rs:130, :168) *)
  penalty_a : int;  (** penalty GAS charged to twin [a] (handler.rs:109) *)
  penalty_b : int;  (** penalty GAS charged to twin [b] (handler.rs:109) *)
  refund_a_raw : int;
      (** [unused_gas - penalty_gas] for twin [a] BEFORE the
          [saturating_sub] of handler.rs:113 clamps it: negative exactly
          when the penalty exceeded the unused gas *)
}

(** Total deterministic comparison over ALL ledger fields. *)
let ledger_compare l1 l2 =
  let c = Int.compare l1.charged l2.charged in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Int.compare l1.credited l2.credited in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Int.compare l1.sink l2.sink in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Int.compare l1.penalty_a l2.penalty_a in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Int.compare l1.penalty_b l2.penalty_b in
          if Bool.not (Int.equal c4 0) then c4
          else Int.compare l1.refund_a_raw l2.refund_a_raw

(** Whether the handler has run for this batch. *)
type settlement =
  | Unsettled  (** pre-execution: no balance has moved *)
  | Settled of ledger  (** the handler ran and wrote these amounts *)

(** Total order on {!settlement}: every cross-constructor arm spelled. *)
let settlement_compare a b =
  match (a, b) with
  | Unsettled, Unsettled -> 0
  | Unsettled, Settled _ -> -1
  | Settled _, Unsettled -> 1
  | Settled l1, Settled l2 -> ledger_compare l1 l2

(** The joint global state. *)
type state = { phase : phase; prof : profile; settled : settlement }

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = profile_compare s1.prof s2.prof in
    if Bool.not (Int.equal c1 0) then c1
    else settlement_compare s1.settled s2.settled

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. V0, the admission-time batch validator, sees
    exactly its admission record - the declared gas limit class it summed
    at validator.rs:171 - and nothing about execution: not the pre-refund
    spend, not the EVM refund, not the penalty, none of which exists until
    after consensus (validator.rs:160, handler.rs:100-101). It also does
    not see the phase, because nothing reports execution back to the batch
    validator. Everyone else is a non-agent. *)
type view =
  | Admission_record of limit_class
      (** V0 validated a user batch declaring this limit class *)
  | No_batch
      (** V0 has validated nothing: the initial state, and the system-call
          branch, which never travels in a batch *)
  | Idle  (** the constant blank view of the non-agents V1..V9 *)

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | Idle, Idle -> 0
  | No_batch, No_batch -> 0
  | Admission_record l1, Admission_record l2 -> limit_class_compare l1 l2
  | Idle, (No_batch | Admission_record _) -> -1
  | (No_batch | Admission_record _), Idle -> 1
  | No_batch, Admission_record _ -> -1
  | Admission_record _, No_batch -> 1

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 is the admission-time batch validator and the only
    knowledge agent; V1..V9 are idle non-agents with the constant blank
    view and never appear under K. *)
let view v s =
  match v with
  | Validator.V0 -> (
      match s.prof with
      | Prof_unchosen -> No_batch
      | Prof_system -> No_batch
      | Prof_user (lc, _, _) -> Admission_record lc)
  | Validator.V1 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      Idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | No_small_limit_exemption
      (** delete gate one of the penalty function,
          [if gas_limit <= MIN_GAS_LIMIT_THRESHOLD { return 0; }]
          (crates/tn-reth/src/evm/utils.rs:47-49). Transition changed: a
          batch declaring exactly the 210,000 threshold and then spending
          5% or 1% of it now reaches an [Executed] state carrying a
          non-zero [penalty_a]/[penalty_b] (49,875 resp. 168,399 gas),
          where pristine it reached one carrying zero. No sibling path
          repairs it: [calculate_gas_penalty] has exactly one production
          call site (handler.rs:109) and its result is consumed one line
          later by [unused_gas.saturating_sub(penalty_gas)]
          (handler.rs:113), which saturates DOWNWARD to a zero refund and
          can never restore one; the apparent clamp
          [final=penalty.min(unused_gas)] at utils.rs:78 sits inside the
          arguments of the [debug!] macro and is not what the function
          returns (the return is utils.rs:83); the admission side bounds
          only the SUM of declared limits against 30,000,000
          (validator.rs:162-185) and applies no per-transaction ratio
          filter that could keep a small-limit transaction out. Gate one
          was chosen over gate two (utils.rs:59-62) deliberately: deleting
          gate two makes [THRESHOLD - usage_ratio_scaled] underflow at
          utils.rs:66 for an efficient transaction, so its consequence
          (full forfeiture via the [unwrap_or(unused_gas)] fallback at
          utils.rs:83 in release, a subtraction panic in debug) depends on
          build profile, whereas deleting gate one is arithmetically
          unambiguous. *)
  | Refund_aware_penalty
      (** delete the pre-refund binding [let gas_spent = gas.spent();]
          (crates/tn-reth/src/evm/handler.rs:91), which forces the penalty
          call at handler.rs:109 onto the only other gas figure in scope,
          the post-refund [let gas_used = gas.spent_sub_refunded();] of
          handler.rs:92. Transition changed: twin [a], which earns an EVM
          refund, now presents a smaller numerator to the usage ratio at
          utils.rs:56 than its no-refund twin [b] does, so the [Executed]
          state it reaches carries [penalty_a > penalty_b] - a batch that
          spends exactly 10% of a 420,000 limit and refunds half of it
          goes from a zero penalty to 99,750 gas while its twin still pays
          zero. No sibling path repairs it: the EVM refund enters exactly
          two expressions in the whole handler, [unused_gas]
          (handler.rs:112) and the beneficiary reward (handler.rs:152),
          and neither feeds back into [penalty_gas];
          [calculate_gas_penalty] (utils.rs:45-84) is a pure function of
          its two arguments with no refund-aware branch; and no later
          adjustment exists, the four [incr_balance] sites of
          crates/tn-reth/src being handler.rs:121, :130, :160 and :168. *)
  | Burn_the_penalty
      (** delete the sink credit
          [if penalty_gas > 0 { ... incr_balance(penalty) }]
          (crates/tn-reth/src/evm/handler.rs:125-131), so the penalised
          wei is destroyed rather than redirected to governance.
          Transition changed: the [Executed] state of a penalised batch
          now carries [credited < charged] and a [sink] short by
          [(penalty_a + penalty_b) * effective_gas_price]. No sibling path
          repairs it: [incr_balance] occurs in crates/tn-reth/src only at
          handler.rs:121 (caller), :130 (this deletion), :160
          (beneficiary) and :168 (base fee), so there is no second credit
          site that could re-credit the penalty, and the caller's refund
          cannot absorb it because [refund_amount] is computed as
          [unused_gas.saturating_sub(penalty_gas)] at handler.rs:113,
          BEFORE and independently of the deleted credit. *)

(** [calculate_gas_penalty] of utils.rs:45-84 under a gate deletion, with
    the rescaled precision constants of the header. [gas] is whichever gas
    figure the handler passes at handler.rs:109. *)
let calculate_gas_penalty mut ~gas_limit ~gas =
  let exempt_by_limit =
    match mut with
    | Pristine | Refund_aware_penalty | Burn_the_penalty ->
        at_most gas_limit min_gas_limit_threshold
    | No_small_limit_exemption -> false
  in
  if exempt_by_limit then 0
  else
    let usage_ratio_scaled = precision * gas / gas_limit in
    if Bool.not (below usage_ratio_scaled threshold) then 0
    else
      let unused_gas = gas_limit - gas in
      let inefficiency_scaled = threshold - usage_ratio_scaled in
      inefficiency_scaled * inefficiency_scaled * unused_gas / threshold_squared

(** The gas figure handler.rs:109 hands to the penalty: the pre-refund
    [gas.spent()] of handler.rs:91 pristine, the post-refund
    [gas.spent_sub_refunded()] of handler.rs:92 once that binding is
    deleted. *)
let penalty_gas mut ~gas_limit ~gas_spent ~gas_used =
  match mut with
  | Pristine | No_small_limit_exemption | Burn_the_penalty ->
      calculate_gas_penalty mut ~gas_limit ~gas:gas_spent
  | Refund_aware_penalty -> calculate_gas_penalty mut ~gas_limit ~gas:gas_used

(** [saturating_sub] of handler.rs:113: the refund is clamped at zero, it
    never goes negative and never grows back. *)
let saturating_sub a b = if below a b then 0 else a - b

(** The declared gas limit of each twin, per limit class. *)
let gas_limit_of = function Lc_small -> min_gas_limit_threshold | Lc_big -> 420_000

(** Pre-refund gas actually spent by each twin ([gas.spent()],
    handler.rs:91): 10%, 5% or 1% of the declared limit. *)
let gas_spent_of lc u =
  match u with
  | U_ge10 -> gas_limit_of lc / 10
  | U_low5 -> gas_limit_of lc / 20
  | U_near0 -> gas_limit_of lc / 100

(** The EVM refund earned by twin [a] (half its pre-refund spend when it
    takes the gas-freeing path); twin [b] never earns one. *)
let evm_refund_of lc u r =
  match r with R_none -> 0 | R_some -> gas_spent_of lc u / 2

(** The zero ledger of the system-call path: both handler overrides
    early-return for [SYSTEM_ADDRESS] (handler.rs:85-87, :145-147), and
    nothing is charged either, because a system call's gas price and
    basefee are both zero (handler.rs:143-144). *)
let system_ledger =
  {
    charged = 0;
    credited = 0;
    sink = 0;
    penalty_a = 0;
    penalty_b = 0;
    refund_a_raw = 0;
  }

(** Run the handler over one user batch of twins: penalty (handler.rs:109),
    caller refund (handler.rs:112-113, credited :121), penalty redirect
    (handler.rs:125-131, credited :130), beneficiary tip
    (handler.rs:156-160) and base-fee redirect (handler.rs:165-168), with
    revm's unmodified up-front debit of [gas_limit * effective_gas_price]
    per transaction as the charge. *)
let user_ledger mut lc u r =
  let gas_limit = gas_limit_of lc in
  let gas_spent = gas_spent_of lc u in
  let refund_a = evm_refund_of lc u r in
  let used_a = gas_spent - refund_a in
  let used_b = gas_spent in
  let pen_a = penalty_gas mut ~gas_limit ~gas_spent ~gas_used:used_a in
  let pen_b = penalty_gas mut ~gas_limit ~gas_spent ~gas_used:used_b in
  let unused_a = gas_limit - used_a in
  let unused_b = gas_limit - used_b in
  let caller_a = saturating_sub unused_a pen_a * effective_gas_price in
  let caller_b = saturating_sub unused_b pen_b * effective_gas_price in
  let beneficiary = (effective_gas_price - basefee) * (used_a + used_b) in
  let redirected_penalty =
    match mut with
    | Pristine | No_small_limit_exemption | Refund_aware_penalty ->
        (pen_a + pen_b) * effective_gas_price
    | Burn_the_penalty -> 0
  in
  let sink = redirected_penalty + (basefee * (used_a + used_b)) in
  {
    charged = 2 * gas_limit * effective_gas_price;
    credited = caller_a + caller_b + beneficiary + sink;
    sink;
    penalty_a = pen_a;
    penalty_b = pen_b;
    refund_a_raw = unused_a - pen_a;
  }

(** The ledger the handler writes for a profile. [Prof_unchosen] is never
    reached at execution - [next_with] resolves the profile one transition
    earlier - so it settles nothing. *)
let settle mut prof =
  match prof with
  | Prof_unchosen -> Unsettled
  | Prof_system -> Settled system_ledger
  | Prof_user (lc, u, r) -> Settled (user_ledger mut lc u r)

(** Every execution profile the first transition can resolve into: the
    canonical system-call path plus the twelve user batches. *)
let profiles =
  Prof_system
  :: List.concat_map
       (fun lc ->
         List.concat_map
           (fun u ->
             List.map (fun r -> Prof_user (lc, u, r)) [ R_none; R_some ])
           [ U_ge10; U_low5; U_near0 ])
       [ Lc_small; Lc_big ]

(** The transition relation, parameterized by the gate mutation: the
    hidden execution profile is resolved as the batch is admitted
    (validator.rs:162-185 reads only the declared limits, so V0 learns
    only the limit class), then the handler settles it. [Executed] is
    terminal; the kernel stutter-closes it. *)
let next_with mut s =
  match s.phase with
  | Proposed ->
      List.map
        (fun p -> { phase = Admitted; prof = p; settled = Unsettled })
        profiles
  | Admitted -> [ { s with phase = Executed; settled = settle mut s.prof } ]
  | Executed -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: a batch is proposed, its execution profile is not
    yet resolved, no balance has moved. *)
let initial = { phase = Proposed; prof = Prof_unchosen; settled = Unsettled }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Admitted_user
      (** the validator has admitted a user batch (validator.rs:162-185)
          and execution has not happened yet *)
  | Executed_user
      (** the handler has run over a user batch (handler.rs:78-171) *)
  | Small_limit
      (** the admitted batch declares at most [MIN_GAS_LIMIT_THRESHOLD]
          gas, the field gate one reads (utils.rs:47-49) *)
  | Big_limit  (** the admitted batch declares more than that *)
  | Efficient_a
      (** twin [a] really spends at least 10% of its declared limit
          PRE-refund, the exemption of gate two (utils.rs:56-62) *)
  | Refund_earned_a
      (** twin [a] earned an EVM refund, so [gas.spent_sub_refunded()] is
          strictly below [gas.spent()] (handler.rs:91-92) *)
  | Penalty_charged_a  (** twin [a] was charged a non-zero penalty *)
  | Penalty_charged_b  (** twin [b] was charged a non-zero penalty *)
  | Penalties_equal
      (** the twins were charged the same penalty gas (trivially so before
          execution, when both are zero) *)
  | Penalty_within_unused
      (** [penalty_gas <= unused_gas] for twin [a], i.e. handler.rs:113
          did not have to saturate - the normalisation of utils.rs:65-71,
          property-tested at crates/tn-reth/tests/it/economics_props.rs:17-34 *)
  | Conserved
      (** every wei debited up front was credited back across caller,
          beneficiary and sink: nothing burned, nothing minted *)
  | Penalty_redirected
      (** the governance sink received at least the penalised wei
          (handler.rs:125-131) *)

(** Atom valuation over the global state. *)
let label a s =
  let user = match s.prof with
    | Prof_unchosen -> false
    | Prof_system -> false
    | Prof_user _ -> true
  in
  let ledger_is f =
    match s.settled with Unsettled -> false | Settled l -> f l
  in
  let ledger_or_unset f =
    match s.settled with Unsettled -> true | Settled l -> f l
  in
  match a with
  | Admitted_user -> (
      user && match s.phase with Proposed -> false | Admitted -> true | Executed -> false)
  | Executed_user -> (
      user && match s.phase with Proposed -> false | Admitted -> false | Executed -> true)
  | Small_limit -> (
      match s.prof with
      | Prof_unchosen -> false
      | Prof_system -> false
      | Prof_user (lc, _, _) -> (
          match lc with Lc_small -> true | Lc_big -> false))
  | Big_limit -> (
      match s.prof with
      | Prof_unchosen -> false
      | Prof_system -> false
      | Prof_user (lc, _, _) -> (
          match lc with Lc_small -> false | Lc_big -> true))
  | Efficient_a -> (
      match s.prof with
      | Prof_unchosen -> false
      | Prof_system -> false
      | Prof_user (_, u, _) -> (
          match u with U_ge10 -> true | U_low5 -> false | U_near0 -> false))
  | Refund_earned_a -> (
      match s.prof with
      | Prof_unchosen -> false
      | Prof_system -> false
      | Prof_user (_, _, r) -> (
          match r with R_none -> false | R_some -> true))
  | Penalty_charged_a -> ledger_is (fun l -> positive l.penalty_a)
  | Penalty_charged_b -> ledger_is (fun l -> positive l.penalty_b)
  | Penalties_equal -> ledger_or_unset (fun l -> Int.equal l.penalty_a l.penalty_b)
  | Penalty_within_unused ->
      ledger_or_unset (fun l -> Bool.not (below l.refund_a_raw 0))
  | Conserved -> ledger_or_unset (fun l -> Int.equal l.credited l.charged)
  | Penalty_redirected ->
      ledger_or_unset (fun l ->
          at_most ((l.penalty_a + l.penalty_b) * effective_gas_price) l.sink)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Admitted_user -> "admitted-user-batch"
  | Executed_user -> "executed-user-batch"
  | Small_limit -> "gas-limit<=210k"
  | Big_limit -> "gas-limit>210k"
  | Efficient_a -> "spent_a>=10%"
  | Refund_earned_a -> "evm-refund_a>0"
  | Penalty_charged_a -> "penalty_a>0"
  | Penalty_charged_b -> "penalty_b>0"
  | Penalties_equal -> "penalty_a=penalty_b"
  | Penalty_within_unused -> "penalty_a<=unused_a"
  | Conserved -> "credited=charged"
  | Penalty_redirected -> "sink>=penalty*price"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} by
    test/t_gas_penalty_split_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
