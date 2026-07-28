(** The [tel_supply_ledger] family over the {!Tel_supply_ledger_model}
    interpreted system: three guarded writes to one ledger - the pending-mint
    pair, slot 100 ([totalSupply]) and the precompile's own native balance -
    in crates/tn-reth/src/evm/tel_precompile. File citations refer to
    Telcoin-Association/telcoin-network at HEAD 0c59c15b and every one of
    them was opened in this checkout.

    Reading guide for the [K] operands. Both knowledge agents are OBSERVERS,
    not writers, and the fact each one is asserted to know is a storage cell
    it cannot read.

    - [K_V1 (pending_slot_clear)] in S1. V1 is the off-chain event indexer;
      its view is the receipt stream alone. The pending-mint amount slot has
      NO getter - the [sol!] surface at burnable.rs:39-60 declares
      [totalSupply], [claim], [burn] and the faucet role calls and nothing
      else, and the dispatcher rejects every undeclared selector
      (mod.rs:128-164) - so [pending_slot_clear] is not a projection of V1's
      view. Nor is it rigid: it is FALSE at every state a mint leaves
      (burnable.rs:180-183) and TRUE at the genesis ledger, both reachable.
      What makes V1 know it after a [Claim] receipt is the amount clear at
      burnable.rs:267-269, and deleting exactly that write is what refutes
      the conjunct. The class is not a singleton: reachable claim receipts
      differ in slot 100 and in the precompile's balance, which the
      contingency suite witnesses with an atom that is false at the operative
      state.
    - [K_V0 (supply_slot_fell)] in S3. V0 is the on-chain supply monitor: it
      reads [totalSupply()] (a permissionless view, burnable.rs:83-96,
      mod.rs:39) and the precompile's native balance, and it sees receipts.
      [supply_slot_fell] is a DELTA, not a cell, so it is not a projection of
      that view - two states with the same slot-100 reading disagree on
      whether the last step lowered it. It is not rigid either: every mint,
      claim and reverted call leaves it false. The class is not a singleton
      because the pending pair - invisible to V0 - varies freely across
      burn receipts.
    - [~K_V1 (supply_slot_zero)] in S3, the ignorance witness. NO event
      carries a resulting cell value: [Mint] carries [(amount, unlock)]
      (burnable.rs:193-195), [Claim] the amount (:294), [Burn] the amount
      (:358). So an indexer can watch a burn commit and be unable to tell an
      exhausted supply from a surviving one - the contingency suite exhibits
      the pair.

    V2 … V9 are idle non-agents with a constant blank view and never appear
    under [K]. *)

open Tel_supply_ledger_model

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

(** Weak until [A\[p W q\]], which the kernel has no constructor for, in the
    identity the contract fixes: [~E\[~q U (~p /\ ~q)\]]. *)
let weak_until p q =
  Formula.Not
    (Formula.Eu (Formula.Not q, Formula.And (Formula.Not p, Formula.Not q)))

(** S1 - pending-mint-is-credited-at-most-once [safety]. Two conjuncts.

    (1) Replay exclusion. Once a claim has committed, no later claim commits
    until a fresh mint re-arms the slot:
    [AG( claim_committed -> AX A\[ ~claim_committed W mint_armed_slot \] )].
    [handle_claim] loads the pending amount (burnable.rs:240-244) and rejects
    zero (:246-248); a commit credits the recipient (:264) and then zeroes
    the amount slot (:267-269), so the reload a second claim performs sees
    zero. The weak-until escape is the honest one: a second [mint] legitimately
    re-arms the slot, and the write is an overwrite (burnable.rs:151, pinned
    by burnable.rs:557-571). The repo pins the same property at the unit
    layer (burnable.rs:477-488, [test_claim_already_claimed]) and end to end
    (pipeline_tel_precompile_props.rs:132-158, "second claim - should fail").

    (2) What the disarm buys an observer:
    [AG( claim_committed -> K_V1(pending_slot_clear) )]. The event indexer
    cannot read the amount slot - no getter for it exists (burnable.rs:39-60,
    mod.rs:128-164) - yet after a [Claim] receipt it knows the slot is spent.
    That inference is exactly what the amount clear underwrites.

    Mutation pin: {!No_pending_clear} deletes the amount-slot clear at
    burnable.rs:267-269. It ADDS the transition "a second claim reloads a
    still-nonzero amount and credits it again", refuting (1); and it leaves
    the slot armed at every claim receipt, refuting (2). The sibling clear of
    the TIMESTAMP slot at :270-272 does not repair either: it writes ZERO,
    and the timelock test is [current_ts < unlock_ts] (:259-261), so a zeroed
    unlock makes every later claim pass the timelock immediately - the
    two clears are not interchangeable and the amount one is the load-bearing
    half. The zero-amount rejection at :246-248 is the same slot's guard, so
    with the slot never cleared it never fires; there is no nonce, no claimed
    flag and no per-recipient counter anywhere ([rg amount_slot] gives only
    helpers.rs:21, burnable.rs:180, :240 and the deleted clear); and the
    faucet module never touches the slot (faucet.rs:87 credits balances
    directly). *)
let s_1 =
  let replay_excluded =
    Formula.Ag
      (Formula.Implies
         ( atom Claim_committed,
           Formula.Ax
             (weak_until
                (Formula.Not (atom Claim_committed))
                (atom Mint_armed_slot)) ))
  in
  let indexer_knows_disarm =
    Formula.Ag
      (Formula.Implies
         ( atom Claim_committed,
           Formula.K (Validator.V1, atom Pending_slot_clear) ))
  in
  {
    name = "pending-mint-is-credited-at-most-once";
    bucket = Statements.Safety;
    formula = Formula.And (replay_excluded, indexer_knows_disarm);
    antecedent = atom Claim_committed;
  }

(** S2 - mint-target-is-pinned-to-governance [security]. Two conjuncts.

    (1) [AG( claim_committed -> claim_credited_gov )]. On a mainnet build the
    caller of [mint] chooses only an amount: [let amount =
    U256::from_be_slice(&calldata[0..32]); let recipient =
    GOVERNANCE_SAFE_ADDRESS;] (burnable.rs:172-173), the ABI being
    [function mint(uint256 amount)] (burnable.rs:63-67) and the constant
    crates/config/src/genesis.rs:37. [handle_claim] does decode an arbitrary
    recipient (:237), but it then loads THAT address's amount slot
    (:240-244) and rejects zero (:246-248), so a claim naming any other
    address finds nothing - the negative case is pinned at
    burnable.rs:469-475. The doc states the invariant at burnable.rs:150.

    (2) The storage-level twin: [AG( ~pending_armed_other )] - the amount
    slot of a non-governance address is never armed in the first place. The
    two conjuncts are distinguishable: a change could arm a foreign slot
    without any claim ever committing against it.

    The consequence is scoping, not containment: a compromised governance key
    cannot point the 7-day pending mint at a fresh attacker address, so
    whatever is minted must surface at the one address the network watches.
    Governance can of course move the funds onward afterwards.

    Mutation pin: {!No_recipient_pin} deletes burnable.rs:173 and takes the
    recipient from calldata the way the faucet variant does (faucet.rs:84).
    It ADDS transitions arming a foreign slot, after which a claim naming
    that address commits - refuting both conjuncts. Nothing repairs it: the
    amount slot has exactly one writer besides the clear (burnable.rs:180),
    so there is no second arming route that could re-pin the destination;
    [claim] applies no address check beyond the caller's governance role
    (:230-232), so the credit follows wherever the slot was armed; the faucet
    module never uses the slot at all and is not compiled on mainnet
    (mod.rs:53-55); and genesis seeds no slot-0 entries. *)
let s_2 =
  let credit_pinned =
    Formula.Ag (Formula.Implies (atom Claim_committed, atom Claim_credited_gov))
  in
  let slot_never_foreign = Formula.Ag (Formula.Not (atom Pending_armed_other)) in
  {
    name = "mint-target-is-pinned-to-governance";
    bucket = Statements.Security;
    formula = Formula.And (credit_pinned, slot_never_foreign);
    antecedent = atom Claim_committed;
  }

(** S3 - burn-moves-both-ledger-cells-or-neither [safety]. Four conjuncts.

    A burn touches two cells that live in DIFFERENT state families - the
    precompile account's native balance and storage slot 100 - and it touches
    them in that order: [balance_decr] debits first (burnable.rs:337-339,
    guarded by [if balance < amount], helpers.rs:70-72), and only afterwards
    does [checked_sub] lower slot 100 (:342-351). The dangerous middle state
    is genuinely entered inside the handler and is unwound only because the
    underflow is raised as a precompile error, which reverts the frame's
    journal. No single write covers both cells and there is no reconciliation
    job: slot 100 has exactly three writers in the tree (burnable.rs:279-287
    up, :349-351 down, faucet.rs:94-102 up and not compiled on mainnet).

    (1) [AG( burn_committed -> balance_fell /\ supply_slot_fell )] - a
    committed burn moved both.
    (2) [AG( burn_reverted -> ~balance_fell /\ ~supply_slot_fell )] - a
    rejected burn moved neither. Together: both or neither. The end-to-end
    observation of exactly this is
    pipeline_tel_precompile_props.rs:433-473, whose own comment reads "Burn
    100 + burn_extra - balance_decr passes (precompile has plenty), then
    totalSupply underflow triggers" and which asserts both [supply_after ==
    supply_before] and [precompile_after == precompile_before].
    (3) [AG( burn_committed -> K_V0(supply_slot_fell) )] - the supply monitor,
    which reads [totalSupply()], knows the burn really did lower slot 100.
    (4) [AG( burn_committed -> ~K_V1(supply_slot_zero) )] - the event indexer
    does not know what slot 100 now holds. That is not a modelling artefact:
    the [Burn] log carries the amount and nothing else (burnable.rs:353-361),
    so no event stream determines the resulting supply.

    Conjuncts (3) and (4) are the epistemic payoff of the split: the [Burn]
    event is emitted AFTER the supply write and unconditionally on the
    committed path, so the receipt alone never certifies that slot 100 moved -
    only a reader of [totalSupply()] can tell.

    Mutation pin: {!No_supply_guard} deletes the
    [checked_sub(amount).ok_or_else(...)?] at burnable.rs:346-348 and lets
    the subtraction wrap. It ADDS the transition "a burn for more than the
    supply commits: the balance debit stands while slot 100 wraps to the
    2^256 scale", refuting (1) - balance fell, slot 100 did not - and with it
    (3), since at that very state the monitor sees a supply that did not
    fall. The balance check does NOT repair it: [balance_decr]'s
    [if balance < amount] (helpers.rs:70-72) bounds the amount by the
    precompile's native balance, an INDEPENDENT quantity from slot 100 - the
    pipeline harness runs balance 1000e18 against supply 100 exactly so that
    the balance check passes and the supply check is the only guard left
    (pipeline_tel_precompile_props.rs:435-449). Note the converse asymmetry
    that fixes the direction of this mutation: deleting the BALANCE check
    instead would be partially covered, because for an amount above the
    supply the [checked_sub] still bails. *)
let s_3 =
  let commit_moves_both =
    Formula.Ag
      (Formula.Implies
         ( atom Burn_committed,
           Formula.And (atom Balance_fell, atom Supply_slot_fell) ))
  in
  let revert_moves_neither =
    Formula.Ag
      (Formula.Implies
         ( atom Burn_reverted,
           Formula.And
             ( Formula.Not (atom Balance_fell),
               Formula.Not (atom Supply_slot_fell) ) ))
  in
  let monitor_knows_the_drop =
    Formula.Ag
      (Formula.Implies
         (atom Burn_committed, Formula.K (Validator.V0, atom Supply_slot_fell)))
  in
  let indexer_cannot_read_the_slot =
    Formula.Ag
      (Formula.Implies
         ( atom Burn_committed,
           Formula.Not (Formula.K (Validator.V1, atom Supply_slot_zero)) ))
  in
  {
    name = "burn-moves-both-ledger-cells-or-neither";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [
          commit_moves_both;
          revert_moves_neither;
          monitor_knows_the_drop;
          indexer_cannot_read_the_slot;
        ];
    antecedent = atom Burn_committed;
  }

(** The family's statements. *)
let all = [ s_1; s_2; s_3 ]

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
