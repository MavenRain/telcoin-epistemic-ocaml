(** The TX_FORWARD_ROUTE statement family: three statements about the
    observer-to-committee transaction router of crates/tn-reth/src/forward.rs,
    encoded over the {!Tx_forward_route_model} interpreted system. Every
    mechanism claim below cites a line span that was opened in the
    telcoin-network working tree at 0c59c15b.

    READING GUIDE FOR THE K OPERANDS. Two agents carry knowledge here and
    neither operand is a projection of its own knower's view.

    - [K (observer, holds(some,tx1))] (S3, conjunct c2b). The observer's view is
      its own loop state (cursor, chain position, budget burned, first contact
      per transaction, recorded [ForwardOutcome]); the operand is a fact about
      COMMITTEE POOLS, which no field of that view contains. It is not rigid
      either: [holds(some,tx1)] is false at every initial state and stays false
      for the whole {!Tx_forward_route_model.All_full} and
      {!Tx_forward_route_model.All_silent} passes and for the whole
      {!Tx_forward_route_model.Owner_rejects} pass. The knowledge is an
      INFERENCE from an acknowledged round trip, and the mutation
      {!Tx_forward_route_model.Timeout_counts_as_delivered} shows it is exactly
      that: once an elapsed round trip is allowed to count as a delivery, the
      same observer view no longer entails a holder and the conjunct is
      refuted. The conjunct is deliberately GUARDED by [elapsed(owner,tx1)] so
      that every state at which it asserts knowledge has an observer-view class
      of four or two reachable states (measured; never a singleton), which is
      the R2 obligation - the unguarded [delivered(tx1)] scope also contains
      states whose observer class happens to be a singleton, and the plain,
      non-epistemic conjunct c2a carries the claim over that wider scope
      instead.
    - [K (owning_slot, ...)] appears only NEGATED (S3, conjunct c4). V1's view
      is its own pool; the operand is another validator's possession, which V1
      never sees, because a forwarded transaction arrives as raw
      [eth_sendRawTransaction] bytes (forward.rs:162) with no marker of how it
      was routed.
    - The [~K (observer, ...)] pair of c3 is the ignorance the code itself
      names: "the transaction's fate is unknown here" (forward.rs:181-183) and
      "This endpoint gave no verdict" (forward.rs:239-241).

    No liveness is claimed for S2. Deleting the outer budget cannot make
    forwarding non-terminating, because the fallback chain
    ([owner] chained onto [fallbacks], forward.rs:142-143) is finite and each
    attempt is separately capped (forward.rs:160); the budget is a bound on
    WORK PER TRANSACTION and S2 says exactly that and no more. *)

open Tx_forward_route_model

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

(** S1 - sender-slot-owns-every-transaction-of-one-account [fairness].

    The observer's routing is a pure, stateless function of the SENDER, so one
    account's transactions never fan out across the committee.

    (c1) AG( contacted(tx1) /\ advertised(owner) -> first(tx1)=owner ) and
    (c2) the same for tx2. The owning slot is
    [(u64::from_le_bytes(sender[0..8]) % committee_size)] indexed into the
    slot-ordered BLS key vector - [owning_validator], forward.rs:218-229, gate
    verbatim at :225-228 - and the chain the loop walks puts it FIRST:
    [let ordered = owner.into_iter().chain(fallbacks.iter().cloned());]
    (forward.rs:142-143), deduplicated by [tried] (forward.rs:149-154). The slot
    vector is built once per epoch in committee order
    (crates/consensus/worker/src/worker.rs:100-105, comment at :96 "index ==
    committee slot") and reaches the forwarder through [disburse_txns]
    (worker.rs:244-277, the call at :256), the non-CVV branch of [seal]
    (worker.rs:282-285). Because the function reads only the sender, tx2 gets
    the same owner as tx1 no matter what happened to tx1 - the modelled passes
    resolve tx1 as delivered, rejected and abandoned, and c2 holds across all
    three.

    (c3) AG( contacted(tx1) /\ ~advertised(owner) -> ~first(tx1)=owner ). The
    guard on c1/c2 is LIVE, not decorative: an owning slot with no usable
    provider is stepped over without an attempt -
    [let Some(provider) = providers.get(&key) else { continue };]
    (forward.rs:155-157) - and an endpoint with an unparseable URL never reaches
    [providers] at all (forward.rs:98-106). c3 states that this really is a skip
    (the transaction is still offered to the other advertised endpoints, since
    [fallbacks] is every resolved provider, forward.rs:136) rather than a silent
    drop, which is what makes c1's guard honest rather than a way of hiding a
    counterexample.

    Mutation pin: {!Tx_forward_route_model.Round_robin_owner} deletes the
    sender-derived slot at forward.rs:227 and hands slots out in arrival order,
    so tx1's first attempt goes to slot 0 while tx2's goes to slot 1, refuting
    c1 (c2 and c3 survive, so the refutation is cleanly attributable to the
    routing rule). Nothing repairs it: the receive-side twin
    [submit_txn_if_mine] (crates/batch-validator/src/validator.rs:89-106)
    applies the identical modulo but has no production caller (only the trait
    declaration at crates/types/src/worker/sealed_batch.rs:212, this impl, the
    no-op test impl at validator.rs:229 and four tests), [fallbacks] is
    BLS-key order over a churning advertisement set and cannot re-derive the
    sender's slot, and a receiving pool can order nonces only within itself. *)
let s1 =
  let owner_first_tx1 =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Tx1_contacted, atom Owner_advertised),
           atom Tx1_first_contact_is_owner ))
  in
  let owner_first_tx2 =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Tx2_contacted, atom Owner_advertised),
           atom Tx2_first_contact_is_owner ))
  in
  let unadvertised_owner_is_skipped =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             (atom Tx1_contacted, Formula.Not (atom Owner_advertised)),
           Formula.Not (atom Tx1_first_contact_is_owner) ))
  in
  {
    name = "sender-slot-owns-every-transaction-of-one-account";
    bucket = Statements.Fairness;
    formula =
      Formula.And
        ( owner_first_tx1,
          Formula.And (owner_first_tx2, unadvertised_owner_is_skipped) );
    antecedent = Formula.And (atom Tx1_contacted, atom Owner_advertised);
  }

(** S2 - forward-budget-bounds-one-transaction [safety].

    The per-transaction budget is a bound on the WORK one transaction can
    extract from the shared forward task.

    (d1) AG( ~budget>15s ). No transaction is ever charged more than
    [FORWARD_TX_BUDGET]: the whole fallback chain of one transaction runs
    inside [timeout(FORWARD_TX_BUDGET, async { ... })] (forward.rs:148) whose
    elapse is turned into [ForwardOutcome::NoEndpointReached]
    (forward.rs:194-195). With [FORWARD_TX_BUDGET] = 15s (forward.rs:36) and
    [FORWARD_SEND_TIMEOUT] = 5s (forward.rs:30) at most three elapsed round
    trips can be charged to one transaction, since a fourth would cost 20s.
    The claim is about elapsed round trips only: the model's steps are
    completed attempts, so it does not adjudicate the tie at exactly 15s
    between the third attempt's own timeout and the outer budget. That the
    bound is on TIME and not on attempts is modelled too: an endpoint that
    answers immediately costs nothing, so the
    {!Tx_forward_route_model.All_full} pass contacts all four endpoints well
    inside the budget.

    (d2) AG( budget=15s /\ unresolved(tx1) -> AX ~unresolved(tx1) ). Once the
    budget is spent the very next thing that happens to that transaction is its
    abandonment, not another endpoint: the outer [timeout] wins the race and
    the [for] loop (forward.rs:139) proceeds to the next transaction after
    logging [ForwardOutcome::NoEndpointReached] (forward.rs:204-207).

    (d3) AG( chain_start(tx2) -> ~budget>0 ). The budget is PER TRANSACTION,
    not per pass: the [timeout] wrapper sits inside the loop body
    (forward.rs:139 then :148), so a transaction that burned the whole budget
    hands the next one a fresh one. d3 is not what the pin flips; it records
    the scoping decision that makes d1 a per-transaction bound.

    Mutation pin: {!Tx_forward_route_model.No_forward_budget} deletes the outer
    [timeout] wrapper (forward.rs:148) and its
    [.unwrap_or(ForwardOutcome::NoEndpointReached)] (forward.rs:194-195),
    keeping the per-attempt timeout. A fourth elapsed round trip is then
    charged to the same transaction, refuting d1, and the budget-exhausted
    state acquires a successor that attempts an endpoint instead of abandoning,
    refuting d2. No sibling path repairs it: the per-attempt
    [FORWARD_SEND_TIMEOUT] (forward.rs:160) is inside the loop and is precisely
    what the outer budget is documented to bound in aggregate
    (forward.rs:32-35), the spawn site (forward.rs:138) attaches no deadline,
    and the caller returns [Ok(())] without joining
    (crates/consensus/worker/src/worker.rs:253-276). *)
let s2 =
  let no_overrun = Formula.Ag (Formula.Not (atom Budget_overrun)) in
  let spent_budget_abandons =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Budget_exhausted, atom Tx1_unresolved),
           Formula.Ax (Formula.Not (atom Tx1_unresolved)) ))
  in
  let budget_is_per_transaction =
    Formula.Ag
      (Formula.Implies (atom Tx2_chain_start, Formula.Not (atom Budget_spent)))
  in
  {
    name = "forward-budget-bounds-one-transaction";
    bucket = Statements.Safety;
    formula =
      Formula.And
        (no_overrun, Formula.And (spent_budget_abandons, budget_is_per_transaction));
    antecedent = Formula.And (atom Budget_exhausted, atom Tx1_unresolved);
  }

(** S3 - endpoint-local-non-verdict-is-neither-a-delivery-nor-an-end-of-chain
    [security].

    [Disposition::TryNext] is the code's judgement that an endpoint-local
    failure says nothing about the transaction (forward.rs:239-241,
    :181-183). S3 states the three things that judgement buys and the one thing
    it costs.

    (c1) AG( full(owner) /\ room(other) -> AF delivered(tx1) ). A transient
    JSON-RPC code - [TRANSIENT_RPC_CODES] = [-32003, -32603], forward.rs:38-42,
    matched at :266-268 - keeps the chain moving (forward.rs:183-189), so a
    saturated owner does not consume the transaction while another advertised
    validator still has room. The [room(other)] guard is LOAD-BEARING, not
    decorative: in the {!Tx_forward_route_model.All_full} pass the owner is
    equally saturated but nobody has room, the chain is exhausted and the
    outcome is [ForwardOutcome::NoEndpointReached] - the same formula without
    the guard is FALSE on the pristine model, which
    test/t_tx_forward_route.ml asserts.

    (c2a) AG( delivered(tx1) -> holds(some,tx1) ) and
    (c2b) AG( elapsed(owner,tx1) /\ delivered(tx1) ->
              K_observer(holds(some,tx1)) ).
    A recorded delivery is always backed by a validator that actually
    acknowledged the transaction, because [ForwardOutcome::Delivered] is set
    only where [send_raw_transaction] returned [Ok] (forward.rs:167, :173-176)
    and an elapsed round trip is deliberately NOT that (forward.rs:165-167).
    c2b upgrades this to knowledge for the observer, and only at states whose
    observer-view class holds four or two reachable states, never a singleton.

    (c3) AG( elapsed(owner,tx1) /\ delivered(tx1) ->
             ~K_observer(holds(owner,tx1)) /\
             ~K_observer(~holds(owner,tx1)) ).
    That is what the fallthrough costs. The observer times the round trip
    (forward.rs:160-164) and learns nothing about whether the owner got the
    bytes, so the pass in which the silent owner kept the transaction and the
    pass in which it did not are the same observer view at every step; the
    observer knows a validator holds the transaction and cannot say which.

    (c4) AG( holds(owner,tx1) -> ~K_owning_slot(~holds(other,tx1)) ). The
    dual ignorance: falling through past a silently-accepting owner places a
    second copy, and the owner cannot rule that out, since a forwarded
    transaction arrives as raw bytes (forward.rs:162) with no marker of how it
    was routed and no validator sees another's pool.

    Mutation pins - two, each refuting a different conjunct.
    {!Tx_forward_route_model.No_transient_fallthrough} deletes the transient
    branch at forward.rs:266-268 so a full pool becomes
    [Disposition::Rejected] at :272-275 and stops the chain: the saturated
    owner now consumes the transaction and c1 is refuted.
    {!Tx_forward_route_model.Timeout_counts_as_delivered} deletes the
    elapsed-round-trip classification at forward.rs:165-167 and treats a
    timeout as a delivery: the pass then records a delivery no validator
    acknowledged, refuting c2a and c2b, and it also stops the chain at the
    silent owner so no second copy is ever placed, which makes
    [~holds(other,tx1)] uniform over the owner's view class and refutes c4.
    Neither is repaired: nothing re-offers a transaction this pass failed to
    place - [disburse_txns] returns [Ok(())] as soon as the task is spawned
    (worker.rs:253-276), the batch builder takes that as the seal result and
    empties the transactions out of the observer's pool
    (crates/batch-builder/src/lib.rs:187, :326-332 and
    crates/tn-reth/src/txn_pool.rs:145-168), the local-transaction backup task
    is commented out (txn_pool.rs:103-123) and the gossip route this replaced
    was deleted (forward.rs:1-12). *)
let s3 =
  let transient_owner_falls_through =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Owner_pool_full, atom Room_elsewhere),
           Formula.Af (atom Tx1_delivered) ))
  in
  let delivery_has_a_holder =
    Formula.Ag
      (Formula.Implies (atom Tx1_delivered, atom Tx1_held_by_some))
  in
  let delivery_is_known =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Owner_timed_out_tx1, atom Tx1_delivered),
           Formula.K (observer, atom Tx1_held_by_some) ))
  in
  let holder_is_unknown =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Owner_timed_out_tx1, atom Tx1_delivered),
           Formula.And
             ( Formula.Not (Formula.K (observer, atom Tx1_held_by_owner)),
               Formula.Not
                 (Formula.K
                    (observer, Formula.Not (atom Tx1_held_by_owner))) ) ))
  in
  let owner_cannot_rule_out_a_second_copy =
    Formula.Ag
      (Formula.Implies
         ( atom Tx1_held_by_owner,
           Formula.Not
             (Formula.K (owning_slot, Formula.Not (atom Tx1_held_by_other))) ))
  in
  {
    name = "endpoint-local-non-verdict-is-neither-a-delivery-nor-an-end-of-chain";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( transient_owner_falls_through,
          Formula.And
            ( delivery_has_a_holder,
              Formula.And
                ( delivery_is_known,
                  Formula.And
                    (holder_is_unknown, owner_cannot_rule_out_a_second_copy) )
            ) );
    antecedent = Formula.And (atom Owner_timed_out_tx1, atom Tx1_delivered);
  }

(** The family's statements. *)
let all = [ s1; s2; s3 ]

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
