(** CTLK statements for the GAS-PENALTY-SPLIT family: the over-estimation
    penalty of crates/tn-reth/src/evm/utils.rs:45-84 and the three-way
    redistribution of the gas charge in crates/tn-reth/src/evm/handler.rs:78-171,
    mined for equal treatment (two uniform, identity-blind exemptions and a
    controlled twin comparison) and for value conservation (TN redirects the
    base fee and the penalty instead of burning them).

    What was mined. The penalty is the only place in TN where the protocol
    confiscates user funds, so the interesting questions are who can be
    charged, on what visible evidence, and where the confiscated wei goes.
    The answers are three statements: S1 the two uniform exemptions plus
    what the admission-time validator can and cannot know about them, S2
    the pre-refund denominator that stops the gas-freeing path from being
    punished, S3 the closed accounting identity across the three sinks.

    READING GUIDE for the K operands. This family has exactly one knowledge
    agent, V0, the admission-time batch validator
    (crates/batch-validator/src/validator.rs:162-185), whose view is its
    admission record - the declared gas limit class it summed at
    validator.rs:171 - and nothing about execution, because "Actual amount
    of gas used cannot be determined until execution" (validator.rs:160,
    echoed at handler.rs:100-101).

    - S1's positive [K_V0 (AG ~penalty_a>0)] is asserted only at
      [admitted-user-batch /\ gas-limit<=210k]. Its operand is NOT a
      projection of V0's own view: whether a penalty is ever charged is a
      function of the pre-refund spend, which V0 cannot see, and it is not
      rigid either - at [gas-limit>210k] states the very same operand is
      false at some reachable state, which is exactly what S1's fourth
      conjunct asserts. The knowledge holds at small limits for one
      reason only: gate one of the penalty function reads the declared
      limit and nothing else (utils.rs:47-49). Delete that gate and the
      knowledge evaporates - which is the pin.
    - S1's negative [~K_V0 (AG ~penalty_a>0)] at [gas-limit>210k] is the
      matching ignorance: the [Admission_record Lc_big] view class holds
      both a batch that spends 10% of its limit and is never penalised and
      one that spends 1% and is penalised 336,798 gas.
    - S2's negatives [~K_V0(evm-refund_a>0)] and [~K_V0(~evm-refund_a>0)]
      say the validator cannot even tell, at admission, which caller will
      take the gas-freeing path - so the penalty cannot be aimed at
      refund-earners. Witness pair: two admitted batches with the same
      declared limit, one with [R_some] and one with [R_none].
    - S3 carries no K deliberately. Value conservation is a pristine
      invariant, so [K_V0(AG conserved)] would be rigid - true at every
      reachable state for structural reasons - and R1 rejects exactly
      that. It is stated as the plain safety invariant it is. *)

open Gas_penalty_split_model

(** A statement over this family's atom vocabulary; [bucket] reuses the
    shared vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** The family's one knowledge agent: V0, the admission-time batch
    validator of crates/batch-validator/src/validator.rs:162-185. *)
let admitter = Validator.V0

(** S1 - well-estimated-transaction-is-never-penalized-under-uniform-thresholds
    [fairness].

    The over-estimation penalty is a pure function of two numbers,
    [pub fn calculate_gas_penalty(gas_limit: u64, gas_used: u64) -> u64]
    (crates/tn-reth/src/evm/utils.rs:45-84), with two uniform exemptions
    and no third input - no sender, no beneficiary, no validator, no
    account history. Conjunct by conjunct:

    - (a) [AG( executed-user-batch /\ gas-limit<=210k -> ~penalty_a>0 /\
      ~penalty_b>0 )]: gate one, [if gas_limit <=
      MIN_GAS_LIMIT_THRESHOLD { return 0; }] (utils.rs:47-49, the constant
      at utils.rs:6), exempts a batch at or below 210,000 gas whatever it
      does at execution - and it exempts BOTH twins, which is the
      identity-blindness: same declared limit, same treatment, different
      senders.
    - (b) [AG( executed-user-batch /\ spent_a>=10% -> ~penalty_a>0 /\
      ~penalty_b>0 )]: gate two, [usage_ratio_scaled = PRECISION *
      gas_used / gas_limit] then [if usage_ratio_scaled >= THRESHOLD {
      return 0; }] (utils.rs:56-62, constants at utils.rs:9 and :12),
      exempts a batch that really uses at least 10% of what it declared.
      The twins share a pre-refund spend, so gate two treats them alike
      too.
    - (c) [AG( admitted-user-batch /\ gas-limit<=210k -> K_V0 (AG
      ~penalty_a>0) )]: gate one reads the one penalty input the
      admission-time validator can see (it sums exactly [tx.gas_limit()],
      validator.rs:171), so at a small declared limit the validator
      already KNOWS no penalty will ever be charged, without knowing
      anything about the execution that has not happened yet.
    - (d) [AG( admitted-user-batch /\ gas-limit>210k -> ~K_V0 (AG
      ~penalty_a>0) )]: past gate one the exemption depends on gate two,
      whose input is invisible at admission (validator.rs:160: "Actual
      amount of gas used cannot be determined until execution"), so the
      same validator knows nothing. Ignorance witness: the
      [Admission_record Lc_big] class holds a 10%-spending batch that is
      never penalised and a 1%-spending one that is penalised.

    Mutation pin: [No_small_limit_exemption] deletes gate one
    (utils.rs:47-49). It adds an [Executed] state in which a batch
    declaring exactly 210,000 gas and spending 5% of it carries
    [penalty_a = penalty_b = 49,875] where pristine it carried zero,
    refuting (a) directly and (c) with it - the validator's admission-time
    certainty is destroyed along with the gate that grounded it. No
    sibling path repairs the deletion: the penalty has one production call
    site (handler.rs:109) whose result is consumed by a downward
    [saturating_sub] one line later (handler.rs:113), the apparent clamp
    at utils.rs:78 is inside the [debug!] arguments rather than the return
    (utils.rs:83), and the admission side bounds only the SUM of declared
    limits (validator.rs:162-185) with no per-transaction ratio filter. *)
let s1 =
  let neither_penalised =
    Formula.And
      ( Formula.Not (atom Penalty_charged_a),
        Formula.Not (atom Penalty_charged_b) )
  in
  let never_penalised = Formula.Ag (Formula.Not (atom Penalty_charged_a)) in
  let limit_exemption =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Executed_user, atom Small_limit),
           neither_penalised ))
  in
  let usage_exemption =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Executed_user, atom Efficient_a),
           neither_penalised ))
  in
  let known_at_admission =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Admitted_user, atom Small_limit),
           Formula.K (admitter, never_penalised) ))
  in
  let unknown_at_admission =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Admitted_user, atom Big_limit),
           Formula.Not (Formula.K (admitter, never_penalised)) ))
  in
  {
    name = "well-estimated-transaction-is-never-penalized-under-uniform-thresholds";
    bucket = Statements.Fairness;
    formula =
      Formula.conj
        [ limit_exemption; usage_exemption; known_at_admission;
          unknown_at_admission ];
    antecedent = Formula.And (atom Admitted_user, atom Small_limit);
  }

(** S2 - sstore-refund-never-enlarges-the-over-estimation-penalty
    [fairness].

    The penalty denominator is PRE-refund gas ([let gas_spent =
    gas.spent();], crates/tn-reth/src/evm/handler.rs:91, consumed at
    handler.rs:109) while the refund arithmetic uses post-refund gas
    ([let gas_used = gas.spent_sub_refunded();], handler.rs:92, consumed
    at handler.rs:112). The doc block at handler.rs:62-76 defends exactly
    this: "Using post-refund gas would make the penalty *larger* than
    intended whenever an EVM refund occurs (e.g. SSTORE clearing), because
    the denominator shrinks while unused gas stays the same." Conjunct by
    conjunct, over a controlled pair of twins - same declared limit, same
    pre-refund spend, different senders, only [a] earning an EVM refund:

    - (a) [AG( executed-user-batch -> penalty_a=penalty_b )]: the
      refund-earner is charged exactly what its no-refund twin is charged.
    - (b) [AG( executed-user-batch /\ evm-refund_a>0 /\ spent_a>=10% ->
      ~penalty_a>0 )]: the sharp instance. A batch that spends exactly 10%
      of a 420,000 limit and gets half of it back is at 5% post-refund -
      squarely inside the penalty band - and still pays nothing, because
      gate two sees the pre-refund figure.
    - (c) [AG( admitted-user-batch -> ~K_V0(evm-refund_a>0) /\
      ~K_V0(~evm-refund_a>0) )]: the admission-time validator cannot even
      tell which caller will take the gas-freeing path, so the charge
      cannot be aimed at refund-earners in the first place. Witness pair:
      two admitted batches with the same declared limit, one [R_some], one
      [R_none].

    Mutation pin: [Refund_aware_penalty] deletes the pre-refund binding at
    handler.rs:91, which forces handler.rs:109 onto the only other gas
    figure in scope, the post-refund one of handler.rs:92. The
    10%-spending, half-refunding batch then reaches an [Executed] state
    carrying [penalty_a = 99,750] against [penalty_b = 0], refuting (a)
    and (b) at once. No sibling path repairs it: the EVM refund enters
    exactly two expressions in the handler, [unused_gas] (handler.rs:112)
    and the beneficiary reward (handler.rs:152), and neither feeds back
    into [penalty_gas]; [calculate_gas_penalty] is pure in its two
    arguments (utils.rs:45-84); and the only credit sites in
    crates/tn-reth/src (handler.rs:121, :130, :160, :168) apply no
    post-hoc correction. *)
let s2 =
  let equal_penalties =
    Formula.Ag (Formula.Implies (atom Executed_user, atom Penalties_equal))
  in
  let refunder_still_exempt =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [ atom Executed_user; atom Refund_earned_a; atom Efficient_a ],
           Formula.Not (atom Penalty_charged_a) ))
  in
  let refund_invisible_at_admission =
    Formula.Ag
      (Formula.Implies
         ( atom Admitted_user,
           Formula.And
             ( Formula.Not (Formula.K (admitter, atom Refund_earned_a)),
               Formula.Not
                 (Formula.K (admitter, Formula.Not (atom Refund_earned_a)))
             ) ))
  in
  {
    name = "sstore-refund-never-enlarges-the-over-estimation-penalty";
    bucket = Statements.Fairness;
    formula =
      Formula.conj
        [ equal_penalties; refunder_still_exempt;
          refund_invisible_at_admission ];
    antecedent =
      Formula.conj
        [ atom Executed_user; atom Refund_earned_a; atom Efficient_a ];
  }

(** S3 - gas-charge-is-exactly-redistributed-never-burned [safety].

    revm's default [deduct_caller] is not overridden - the only two
    overrides are [reimburse_caller] (crates/tn-reth/src/evm/handler.rs:78-134)
    and [reward_beneficiary] (handler.rs:137-171), and the impl block ends
    at handler.rs:172 - so each caller is debited [gas_limit *
    effective_gas_price] up front. TN re-credits at exactly four sites,
    the only [incr_balance] calls in crates/tn-reth/src: caller
    (handler.rs:121), governance sink for the penalty (handler.rs:130),
    beneficiary for the tip (handler.rs:160), governance sink for the base
    fee (handler.rs:168). Unlike Ethereum, the base fee is redirected, not
    burned. Conjunct by conjunct:

    - (a) [AG credited=charged]: across every reachable state - including
      the system-call path, which both overrides skip (handler.rs:85-87,
      :145-147) and which charges nothing because its gas price and
      basefee are both zero (handler.rs:143-144) - the wei credited across
      the three sinks equals the wei debited. Nothing is burned and
      nothing is minted.
    - (b) [AG( executed-user-batch -> penalty_a<=unused_a )]: what makes
      the identity close. The quadratic is normalised by
      [THRESHOLD_SQUARED] (utils.rs:65-71, constant at utils.rs:15), so
      the penalty never exceeds unused gas and the [saturating_sub] at
      handler.rs:113 never has to clamp - the same property the repo
      asserts at crates/tn-reth/tests/it/economics_props.rs:17-34. Were it
      to clamp, the caller's loss and the sink's gain would stop matching
      and (a) would fail with it.
    - (c) [AG( executed-user-batch /\ penalty_a>0 -> sink>=penalty*price
      )]: the confiscated wei is redirected to governance, which is what
      distinguishes "penalty" from "burn".

    Mutation pin: [Burn_the_penalty] deletes the sink credit at
    handler.rs:125-131 while leaving the caller's reduced refund at
    handler.rs:113 untouched, so a penalised batch reaches an [Executed]
    state with [credited < charged] - refuting (a) and (c). No sibling
    path repairs it: [incr_balance] occurs in crates/tn-reth/src only at
    handler.rs:121, :130, :160 and :168, so no second credit site can
    re-credit the penalty, and the caller's refund cannot absorb it
    because [refund_amount] is computed at handler.rs:113 before and
    independently of the deleted credit. This statement carries no K on
    purpose: conservation is a pristine invariant, so knowing it would be
    rigid and R1 rejects rigid K operands. *)
let s3 =
  let conserved = Formula.Ag (atom Conserved) in
  let penalty_bounded =
    Formula.Ag
      (Formula.Implies (atom Executed_user, atom Penalty_within_unused))
  in
  let redirected =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Executed_user, atom Penalty_charged_a),
           atom Penalty_redirected ))
  in
  {
    name = "gas-charge-is-exactly-redistributed-never-burned";
    bucket = Statements.Safety;
    formula = Formula.conj [ conserved; penalty_bounded; redirected ];
    antecedent = Formula.And (atom Executed_user, atom Penalty_charged_a);
  }

(** The family's statements. *)
let all = [ s1; s2; s3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure
    degrades every row to [proved = false] rather than raising. *)
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
