(** The TEL precompile's supply ledger: the interpreted system behind the
    [tel_supply_ledger] family.

    Mechanism modeled (Telcoin-Association/telcoin-network, HEAD 0c59c15b).
    The native TEL precompile at [0x…07e1] keeps four cells under its own
    account (crates/tn-reth/src/evm/tel_precompile/mod.rs:22-32,
    :84-85, :106):

    - the pending-mint amount, [keccak256(abi.encode(recipient, 0))]
      (helpers.rs:21-26);
    - the unlock timestamp, [keccak256(abi.encode(recipient, 1))]
      (helpers.rs:33-38);
    - slot 100, [totalSupply] (mod.rs:102-106);
    - the precompile account's own native balance, moved through
      [balance_incr] / [balance_decr] (helpers.rs:43-77).

    Three governance-only handlers write those cells, and every one of them
    is a guarded write:

    - [handle_mint] (burnable.rs:154-206) arms the pending pair. The
      destination is PINNED: [let recipient = GOVERNANCE_SAFE_ADDRESS;]
      (burnable.rs:173, the constant is crates/config/src/genesis.rs:37),
      calldata supplies only the amount (the mainnet ABI is
      [function mint(uint256 amount)], burnable.rs:63-67), and the doc states
      the invariant at burnable.rs:150.
    - [handle_claim] (burnable.rs:220-309) decodes an ARBITRARY recipient
      (:237), loads that recipient's amount slot (:240-244), rejects zero
      (:246-248), rejects an unexpired timelock via [current_ts < unlock_ts]
      (:250-261), credits the recipient (:264), zeroes the amount slot
      (:267-269) and then the timestamp slot (:270-272), and finally raises
      [totalSupply] through a [checked_add] that errors on overflow
      (:274-287).
    - [handle_burn] (burnable.rs:317-377) debits the precompile's native
      balance FIRST, behind [balance_decr]'s [if balance < amount]
      (helpers.rs:70-72), and only afterwards lowers slot 100 behind a
      [checked_sub … ok_or_else(…)?] (burnable.rs:342-351). The two cells are
      different state families - a native account balance and a storage slot -
      so nothing but the frame's journal revert keeps them in step; the repo
      observes exactly that rollback end to end in
      crates/tn-reth/tests/it/pipeline_tel_precompile_props.rs:433-473.

    Components. [pending] is the amount slot collapsed to which destination
    (if any) it is armed for; [lock] is the timestamp slot read RELATIVE to
    the block timestamp, which is what burnable.rs:259 actually compares, so
    a zeroed slot is [Lock_zero] and passes the timelock trivially; [supply]
    is slot 100 as a three-level register plus the [Sup_wrapped] tag standing
    for the 2^256-scale value a wrapping subtraction would leave; [pbal] is
    the precompile's native balance in units; [last] is the receipt of the
    step that produced this state - the call kind, its status, and the topics
    of the events burnable.rs:191-203 / :289-306 / :353-374 emit; [sup_fell]
    and [bal_fell] are OBSERVATIONS, derived by {!seal} comparing the cells a
    step wrote against the cells it found, never stipulated by a handler.

    Role mapping. Only V0 and V1 are knowledge agents.

    - V0, the on-chain supply monitor: it reads what the precompile's own ABI
      exposes plus what any EVM caller can see - [totalSupply()] is a
      permissionless view (burnable.rs:83-96, dispatched at mod.rs:141-143,
      documented "Any account" at mod.rs:39) and the precompile account's
      native balance is readable with [BALANCE]. Its view is therefore
      [(supply, pbal, last)]. What it CANNOT read is the pending pair: the
      [sol!] surface at burnable.rs:39-60 declares [totalSupply], [claim],
      [burn] and the three faucet role calls and NOTHING else - there is no
      [pendingMint(address)] and no [unlockTimestamp(address)] getter, and
      the dispatcher (mod.rs:128-164) rejects every other selector. The
      pending pair is genuinely hidden from every on-chain reader.
    - V1, the event indexer: an off-chain consumer of the precompile's
      receipts and event stream (an exchange deposit listener, a supply
      dashboard) that keeps no state trie. Its view is [last] alone. No
      event carries a resulting cell value: [Mint] carries
      [(amount, unlockTimestamp)] (burnable.rs:193-195), [Claim] carries the
      amount (:294), [Burn] carries the amount (:358) - so an indexer can see
      that a burn committed and still not know what slot 100 now holds.
    - V2 … V9 are idle non-agents with the constant blank view [View_idle];
      they never appear under [K].

    Abstraction boundaries, stated so the omissions can be audited.

    - Every caller is governance. [mint] is gated by [has_mint_role]
      (burnable.rs:164, which on a non-faucet build is exactly
      [caller = GOVERNANCE_SAFE_ADDRESS], :113-129), and [claim] / [burn] by
      [has_governance_role] (:230-232, :327-329). The family says nothing
      about unauthorized callers, so the model gives every step the
      authorized caller; this can only ADD successful calls, never remove
      them.
    - One unit amount. All three handlers take a [U256] amount; the model
      fixes it at one register unit. [balance_decr]'s zero-amount
      short-circuit (helpers.rs:61-63) is therefore never taken.
    - One pending slot. The real amount slot is a mapping, so under a deleted
      destination pin two addresses could be armed at once. The single cell
      keeps the model EXACT under [Pristine] (where only the governance slot
      is ever written) and UNDER-approximates under
      {!No_recipient_pin}, where it merely loses states in which even more
      claims succeed - so the refutation that mutation produces is genuine
      and not an artifact of the collapse.
    - [mint(0)] is omitted. The code allows it as a cancel
      (burnable.rs:171 "NOTE: allow mint to be `0` to replace pending mints
      during timelock", pinned by burnable.rs:573-588); it writes ZERO to the
      amount slot and can therefore only DISARM. Adding it cannot create a
      successful claim (a claim needs a nonzero amount slot, :246-248, and
      only a nonzero mint writes one), cannot enter the [Act_claim_committed_*]
      or [Act_burn_committed] receipt classes that this family's [K] operands
      are conditioned on, and can only ENLARGE view classes, which is the
      direction that makes the family's [~K] conjunct easier - so the
      omission does not make any statement of this family true.
    - A claim naming an address OTHER than the armed one is represented only
      in the case that matters. [handle_claim] decodes an arbitrary recipient
      (burnable.rs:237) and loads that address's own slot, so naming an
      unarmed address reverts on the zero-amount rejection (:246-248); the
      model emits exactly that revert whenever the single cell is clear. What
      it does not emit is the same revert taken while some OTHER address is
      armed. Those states carry the [Act_claim_reverted] receipt, so they
      join neither the committed-claim nor the committed-burn class that this
      family's [K] operands are conditioned on, and adding them could only
      make the [AG] conjuncts harder - the omission cannot be making anything
      here true.
    - Quiet blocks are elided. {!step_tick} advances the clock only where the
      timelock verdict can change, i.e. while an unexpired unlock timestamp
      is pending; elsewhere a block that writes nothing is a stutter. *)

(** A pending-mint destination. [T_gov] is [GOVERNANCE_SAFE_ADDRESS]
    (crates/config/src/genesis.rs:37), the only destination the mainnet
    [handle_mint] can name (burnable.rs:173). *)
type target = T_gov | T_other

(** Total order index for {!target}. *)
let target_index = function T_gov -> 0 | T_other -> 1

(** Total order on {!target}. *)
let target_compare a b = Int.compare (target_index a) (target_index b)

(** The pending-mint amount slot, [keccak256(abi.encode(recipient, 0))]
    (helpers.rs:21-26), collapsed to which destination it is armed for.
    [Pending_other] is reachable only when the destination pin is deleted. *)
type pending = Pending_none | Pending_gov | Pending_other

(** Total order index for {!pending}. *)
let pending_index = function
  | Pending_none -> 0
  | Pending_gov -> 1
  | Pending_other -> 2

(** Total order on {!pending}. *)
let pending_compare a b = Int.compare (pending_index a) (pending_index b)

(** The unlock timestamp slot (helpers.rs:33-38) read RELATIVE to the block
    timestamp, which is the only thing burnable.rs:259 compares:
    [Lock_zero] is the cleared slot (value 0, so [current_ts < 0] is false
    and the timelock passes), [Lock_armed] is a future unlock, [Lock_ripe] a
    reached one. *)
type lock = Lock_zero | Lock_armed | Lock_ripe

(** Total order index for {!lock}. *)
let lock_index = function Lock_zero -> 0 | Lock_armed -> 1 | Lock_ripe -> 2

(** Total order on {!lock}. *)
let lock_compare a b = Int.compare (lock_index a) (lock_index b)

(** Slot 100, [totalSupply] (mod.rs:102-106), as a three-level register plus
    [Sup_wrapped]: the 2^256-scale value a WRAPPING subtraction leaves behind,
    and therefore the LARGEST value the register can hold. Pristine, only the
    three finite levels are reachable. *)
type sup = Sup_0 | Sup_1 | Sup_2 | Sup_wrapped

(** Tag order index for {!sup}. This is the numeric order too: [Sup_wrapped]
    is the largest value the register takes. *)
let sup_index = function
  | Sup_0 -> 0
  | Sup_1 -> 1
  | Sup_2 -> 2
  | Sup_wrapped -> 3

(** Total order on {!sup}. *)
let sup_compare a b = Int.compare (sup_index a) (sup_index b)

(** The precompile account's own native balance in units, the quantity
    [balance_decr] guards with [if balance < amount] (helpers.rs:70-72). It is
    an INDEPENDENT quantity from slot 100: the pipeline harness deliberately
    runs it at 1000e18 against a total supply of 100
    (pipeline_tel_precompile_props.rs:435-449). *)
type pbal = Pb_0 | Pb_1

(** Total order index for {!pbal}. *)
let pbal_index = function Pb_0 -> 0 | Pb_1 -> 1

(** Total order on {!pbal}. *)
let pbal_compare a b = Int.compare (pbal_index a) (pbal_index b)

(** The receipt of the step that produced a state: the call kind, its status,
    and the event topics the handlers emit (burnable.rs:191-203 [Mint],
    :289-306 [Claim]/[Transfer], :353-374 [Burn]/[Transfer]). A reverted call
    emits no logs - the frame's journal discards them - but still leaves a
    failed receipt, which is why the two [_reverted] receipts are visible. *)
type act =
  | Act_genesis  (** the initial ledger; no precompile call has run yet *)
  | Act_block_tick  (** a block that advanced the timestamp and wrote nothing *)
  | Act_mint_armed_gov
      (** [mint] wrote a nonzero amount to the governance slot and a fresh
          unlock timestamp (burnable.rs:180-189), emitting
          [Mint(gov, amount, unlock)] *)
  | Act_mint_armed_other
      (** the same write aimed at a non-governance address; reachable only
          when the destination pin at burnable.rs:173 is deleted *)
  | Act_claim_committed_gov
      (** [claim] committed and credited [GOVERNANCE_SAFE_ADDRESS] *)
  | Act_claim_committed_other
      (** [claim] committed and credited a non-governance address *)
  | Act_claim_reverted
      (** [claim] returned [Err] and the frame rolled back: zero pending
          amount (:246-248), unexpired timelock (:259-261), or the
          [checked_add] supply overflow (:284-285) *)
  | Act_burn_committed  (** [burn] returned [Ok] and its writes stood *)
  | Act_burn_reverted
      (** [burn] returned [Err] and the frame rolled back: insufficient
          precompile balance (helpers.rs:70-72) or the [checked_sub] supply
          underflow (burnable.rs:346-348) *)

(** Total order index for {!act}. *)
let act_index = function
  | Act_genesis -> 0
  | Act_block_tick -> 1
  | Act_mint_armed_gov -> 2
  | Act_mint_armed_other -> 3
  | Act_claim_committed_gov -> 4
  | Act_claim_committed_other -> 5
  | Act_claim_reverted -> 6
  | Act_burn_committed -> 7
  | Act_burn_reverted -> 8

(** Total order on {!act}. *)
let act_compare a b = Int.compare (act_index a) (act_index b)

(** The joint ledger state. *)
type state = {
  pending : pending;  (** the pending-mint amount slot *)
  lock : lock;  (** the unlock timestamp slot, read against the block clock *)
  supply : sup;  (** slot 100 *)
  pbal : pbal;  (** the precompile account's native balance *)
  last : act;  (** the receipt of the step that produced this state *)
  sup_fell : bool;  (** that step left slot 100 numerically smaller *)
  bal_fell : bool;  (** that step left the native balance numerically smaller *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = pending_compare s1.pending s2.pending in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = lock_compare s1.lock s2.lock in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = sup_compare s1.supply s2.supply in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = pbal_compare s1.pbal s2.pbal in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = act_compare s1.last s2.last in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Bool.compare s1.sup_fell s2.sup_fell in
            if Bool.not (Int.equal c5 0) then c5
            else Bool.compare s1.bal_fell s2.bal_fell

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    [View_reader] is V0, the on-chain supply monitor: [totalSupply()] is a
    permissionless view call (burnable.rs:83-96, mod.rs:39, :141-143) and the
    precompile's native balance is readable with [BALANCE], so it sees both
    cells plus the receipt stream. It does NOT see the pending pair - no
    getter for it exists in the [sol!] surface (burnable.rs:39-60) and the
    dispatcher rejects every undeclared selector (mod.rs:163).

    [View_indexer] is V1, the off-chain event indexer: it sees the receipt
    and its event topics and nothing else. No event carries a resulting cell
    value (burnable.rs:193-195, :294, :358), so it can watch a burn commit
    and still not know what slot 100 holds.

    [View_idle] is the constant blank view of V2 … V9, which are not
    knowledge agents and never appear under [K]. *)
type view =
  | View_reader of sup * pbal * act
  | View_indexer of act
  | View_idle

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_reader _ | View_indexer _) -> -1
  | (View_reader _ | View_indexer _), View_idle -> 1
  | View_indexer x, View_indexer y -> act_compare x y
  | View_indexer _, View_reader _ -> -1
  | View_reader _, View_indexer _ -> 1
  | View_reader (s, b1, a1), View_reader (s', b2, a2) ->
      let c = sup_compare s s' in
      if Bool.not (Int.equal c 0) then c
      else
        let c1 = pbal_compare b1 b2 in
        if Bool.not (Int.equal c1 0) then c1 else act_compare a1 a2

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 and V1 are the knowledge agents; V2 … V9 are idle
    non-agents with the constant blank view and never appear under [K]. *)
let view v s =
  match v with
  | Validator.V0 -> View_reader (s.supply, s.pbal, s.last)
  | Validator.V1 -> View_indexer s.last
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at HEAD 0c59c15b *)
  | No_pending_clear
      (** delete the amount-slot clear
          [internals.sstore(TELCOIN_PRECOMPILE_ADDRESS, amt_slot, U256::ZERO)]
          at burnable.rs:267-269, so a committed claim leaves the pending
          amount live. That ADDS the transition "a second claim for the same
          recipient reloads a nonzero amount and credits it again". The
          sibling clear of the timestamp slot at :270-272 does NOT repair it:
          it writes ZERO, and the timelock test is [current_ts < unlock_ts]
          (:259-261), so a zeroed unlock makes every later claim pass the
          timelock IMMEDIATELY - deleting the amount clear is strictly worse
          than deleting the timestamp clear. The zero-amount rejection at
          :246-248 is the same slot's guard, not an independent one, so with
          the slot never cleared it never fires. There is no nonce, no
          claimed flag and no per-recipient counter: [rg amount_slot] over
          the tree gives exactly helpers.rs:21 (the definition),
          burnable.rs:180 (the mint write), :240 (the claim read) and the
          clear being deleted, and the faucet module never touches the slot
          at all (faucet.rs:62-128 credits balances directly at :87). *)
  | No_recipient_pin
      (** delete the destination pin [let recipient = GOVERNANCE_SAFE_ADDRESS;]
          at burnable.rs:173 and take the recipient from calldata the way the
          faucet variant does (faucet.rs:84). That ADDS transitions arming an
          arbitrary address's pending slot, after which a claim naming that
          address commits and credits it. No sibling path repairs it: the
          amount slot has exactly one writer besides the clear
          (burnable.rs:180), so there is no second arming route to re-pin the
          destination; [claim] itself decodes an arbitrary recipient (:237)
          and applies no address check beyond the caller's governance role
          (:230-232), so the credit follows wherever the slot was armed; and
          genesis seeds no slot-0 entries - the checked-in precompile account
          carries code [0xfe] with no storage map, and the only storage the
          ceremony attaches belongs to other accounts. *)
  | No_supply_guard
      (** delete the [checked_sub(amount).ok_or_else(…)?] on slot 100 at
          burnable.rs:346-348 and subtract with wrapping semantics. That ADDS
          the transition "a burn whose amount exceeds the supply commits: the
          native balance debit at :337-339 stands while slot 100 wraps to a
          2^256-scale value", the split state the frame's journal revert
          otherwise unwinds. The balance check in [balance_decr]
          (helpers.rs:70-72) does NOT repair it: it bounds the amount by the
          precompile's NATIVE BALANCE, an independent quantity from slot 100 -
          the pipeline harness runs balance 1000e18 against supply 100
          precisely so the balance check passes and the supply check is the
          only guard left (pipeline_tel_precompile_props.rs:435-449, asserting
          both cells unchanged at :459-473). Slot 100 has exactly three
          writers in the whole tree - burnable.rs:279-287 (claim, up),
          :349-351 (burn, down) and faucet.rs:94-102 (faucet mint, up, not
          compiled on mainnet) - so there is no reconciliation job and no
          rebuild-from-balances path to restore it. *)

(** Total order index for {!mutation}, so a test can label cases. *)
let mutation_index = function
  | Pristine -> 0
  | No_pending_clear -> 1
  | No_recipient_pin -> 2
  | No_supply_guard -> 3

(** Did a slot-100 write leave a numerically SMALLER value than it found?
    This is the strict {!sup_index} order and nothing else, so a step that
    writes the value back unchanged - which is what a REVERTED call leaves -
    never registers a fall. [Sup_wrapped] stands for the 2^256-scale value a
    wrapping subtraction produces and is the register's largest value, so a
    step from a finite level INTO it is the wrap and is emphatically not a
    fall; the region above the wrap is collapsed to the single tag, which
    costs nothing here because a wrap spends the last unit of native balance
    ({!step_burn} reaches [Sup_wrapped] only from [Pb_1]), so no burn can
    ever commit again from a wrapped state. *)
let supply_fell before after =
  match (before, after) with
  | Sup_0, (Sup_0 | Sup_1 | Sup_2 | Sup_wrapped) -> false
  | Sup_1, Sup_0 -> true
  | Sup_1, (Sup_1 | Sup_2 | Sup_wrapped) -> false
  | Sup_2, (Sup_0 | Sup_1) -> true
  | Sup_2, (Sup_2 | Sup_wrapped) -> false
  | Sup_wrapped, (Sup_0 | Sup_1 | Sup_2) -> true
  | Sup_wrapped, Sup_wrapped -> false

(** Did a native-balance write leave a numerically smaller value than it
    found (helpers.rs:73-75)? *)
let balance_fell before after =
  match (before, after) with
  | Pb_0, (Pb_0 | Pb_1) -> false
  | Pb_1, Pb_0 -> true
  | Pb_1, Pb_1 -> false

(** Seal a step: stamp the receipt and DERIVE the two movement flags by
    comparing the cells the step wrote against the cells it found. Nothing
    here stipulates a flag; both are observations of the two cells. *)
let seal before after a =
  {
    after with
    last = a;
    sup_fell = supply_fell before.supply after.supply;
    bal_fell = balance_fell before.pbal after.pbal;
  }

(** The [checked_add] of the claim's supply raise (burnable.rs:283-285):
    [None] is the overflow that aborts the whole call. The wrapped value sits
    at the top of the register, so it overflows too. *)
let supply_incr = function
  | Sup_0 -> Some Sup_1
  | Sup_1 -> Some Sup_2
  | Sup_2 -> None
  | Sup_wrapped -> None

(** The [checked_sub] of the burn's supply drop (burnable.rs:346-348):
    [None] is the underflow that aborts the whole call. *)
let supply_decr_checked = function
  | Sup_0 -> None
  | Sup_1 -> Some Sup_0
  | Sup_2 -> Some Sup_1
  | Sup_wrapped -> Some Sup_wrapped

(** The same subtraction with the guard deleted: the underflow wraps to the
    2^256-scale value instead of aborting. *)
let supply_decr_wrapping = function
  | Sup_0 -> Sup_wrapped
  | Sup_1 -> Sup_0
  | Sup_2 -> Sup_1
  | Sup_wrapped -> Sup_wrapped

(** [balance_decr]'s [if balance < amount] (helpers.rs:70-72): [None] is the
    insufficient-balance rejection, which the burn handler turns into an
    error at burnable.rs:337-339. *)
let pbal_decr = function Pb_0 -> None | Pb_1 -> Some Pb_0

(** Does the timelock let a claim through? Exactly the negation of
    [current_ts < unlock_ts] (burnable.rs:258-261) - a CLEARED slot holds
    zero, so it passes trivially, which is what makes the amount clear and
    not the timestamp clear the load-bearing half of the disarm. *)
let timelock_passed = function
  | Lock_zero -> true
  | Lock_armed -> false
  | Lock_ripe -> true

(** The pending cell a mint at [t] arms. *)
let pending_of = function T_gov -> Pending_gov | T_other -> Pending_other

(** The receipt a mint at [t] leaves. *)
let mint_act = function
  | T_gov -> Act_mint_armed_gov
  | T_other -> Act_mint_armed_other

(** The receipt a committed claim to [t] leaves. *)
let claim_act = function
  | T_gov -> Act_claim_committed_gov
  | T_other -> Act_claim_committed_other

(** Which destination a live pending slot is armed for. *)
let pending_target = function
  | Pending_none -> None
  | Pending_gov -> Some T_gov
  | Pending_other -> Some T_other

(** [handle_mint] (burnable.rs:154-206): arm the pending pair. Pristine and
    under the two mutations that leave burnable.rs:173 alone, the destination
    is forced to governance; under {!No_recipient_pin} the caller chooses it,
    exactly as the faucet variant lets it (faucet.rs:84). The write is an
    OVERWRITE of both slots (burnable.rs:151, pinned by burnable.rs:557-571). *)
let step_mint mut s =
  let targets =
    match mut with
    | Pristine | No_pending_clear | No_supply_guard -> [ T_gov ]
    | No_recipient_pin -> [ T_gov; T_other ]
  in
  List.map
    (fun t ->
      seal s { s with pending = pending_of t; lock = Lock_armed } (mint_act t))
    targets

(** A block whose timestamp crosses a pending unlock. The clock is advanced
    only where the timelock verdict can change; a block that writes nothing
    else is a stutter the kernel's terminal closure already supplies. *)
let step_tick s =
  match s.lock with
  | Lock_armed -> [ seal s { s with lock = Lock_ripe } Act_block_tick ]
  | Lock_zero | Lock_ripe -> []

(** [handle_claim] (burnable.rs:220-309). The three rejections - zero pending
    amount (:246-248), unexpired timelock (:259-261) and the [checked_add]
    supply overflow (:284-285) - all return [Err], so the frame's journal
    rolls the whole call back and no cell moves. A commit credits the
    recipient (:264), clears the amount slot (:267-269, the write
    {!No_pending_clear} deletes), clears the timestamp slot (:270-272) and
    raises slot 100 (:279-287). *)
let step_claim mut s =
  let reverted = [ seal s s Act_claim_reverted ] in
  let commit t raised =
    let cleared =
      match mut with
      | Pristine | No_recipient_pin | No_supply_guard -> Pending_none
      | No_pending_clear -> s.pending
    in
    [
      seal s
        { s with pending = cleared; lock = Lock_zero; supply = raised }
        (claim_act t);
    ]
  in
  Option.fold ~none:reverted
    ~some:(fun t ->
      if Bool.not (timelock_passed s.lock) then reverted
      else Option.fold ~none:reverted ~some:(commit t) (supply_incr s.supply))
    (pending_target s.pending)

(** [handle_burn] (burnable.rs:317-377): debit the native balance first
    (:337-339, guarded by helpers.rs:70-72), then lower slot 100. Pristine the
    supply subtraction is checked (:346-348) and its failure aborts the call,
    so the already-written balance debit is unwound with it; under
    {!No_supply_guard} the subtraction wraps and the call commits with the
    balance debit standing and slot 100 raised to the 2^256 scale. *)
let step_burn mut s =
  let reverted = [ seal s s Act_burn_reverted ] in
  Option.fold ~none:reverted
    ~some:(fun debited ->
      match mut with
      | Pristine | No_pending_clear | No_recipient_pin ->
          Option.fold ~none:reverted
            ~some:(fun lowered ->
              [
                seal s { s with pbal = debited; supply = lowered }
                  Act_burn_committed;
              ])
            (supply_decr_checked s.supply)
      | No_supply_guard ->
          [
            seal s
              { s with pbal = debited; supply = supply_decr_wrapping s.supply }
              Act_burn_committed;
          ])
    (pbal_decr s.pbal)

(** The transition relation: at every state governance may call [mint],
    [claim] or [burn], and a block may cross a pending unlock. *)
let next_with mut s =
  step_mint mut s @ step_tick s @ step_claim mut s @ step_burn mut s

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial ledger: nothing pending, the timestamp slot cleared, slot 100
    at the bottom of the register and one unit of native balance held by the
    precompile - the harness shape in which the balance check passes and the
    supply check is the only guard a burn has left
    (pipeline_tel_precompile_props.rs:435-449). *)
let initial =
  {
    pending = Pending_none;
    lock = Lock_zero;
    supply = Sup_0;
    pbal = Pb_1;
    last = Act_genesis;
    sup_fell = false;
    bal_fell = false;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Claim_committed  (** the last call was a claim that committed *)
  | Claim_credited_gov
      (** … and it credited [GOVERNANCE_SAFE_ADDRESS] (burnable.rs:264) *)
  | Mint_armed_slot
      (** the last call was a mint that wrote a NONZERO pending amount
          (burnable.rs:180-183) *)
  | Burn_committed  (** the last call was a burn that committed *)
  | Burn_reverted
      (** the last call was a burn that returned [Err] and rolled back *)
  | Pending_slot_clear  (** the pending amount slot reads zero *)
  | Pending_armed_other
      (** the pending amount slot is armed for a non-governance address *)
  | Supply_slot_fell  (** this step left slot 100 numerically smaller *)
  | Balance_fell
      (** this step left the precompile's native balance numerically smaller *)
  | Supply_slot_zero  (** slot 100 reads zero *)
  | Balance_zero  (** the precompile's native balance reads zero *)

(** Atom valuation over the ledger state. *)
let label a s =
  match a with
  | Claim_committed -> (
      match s.last with
      | Act_claim_committed_gov | Act_claim_committed_other -> true
      | Act_genesis | Act_block_tick | Act_mint_armed_gov | Act_mint_armed_other
      | Act_claim_reverted | Act_burn_committed | Act_burn_reverted ->
          false)
  | Claim_credited_gov -> (
      match s.last with
      | Act_claim_committed_gov -> true
      | Act_genesis | Act_block_tick | Act_mint_armed_gov | Act_mint_armed_other
      | Act_claim_committed_other | Act_claim_reverted | Act_burn_committed
      | Act_burn_reverted ->
          false)
  | Mint_armed_slot -> (
      match s.last with
      | Act_mint_armed_gov | Act_mint_armed_other -> true
      | Act_genesis | Act_block_tick | Act_claim_committed_gov
      | Act_claim_committed_other | Act_claim_reverted | Act_burn_committed
      | Act_burn_reverted ->
          false)
  | Burn_committed -> (
      match s.last with
      | Act_burn_committed -> true
      | Act_genesis | Act_block_tick | Act_mint_armed_gov | Act_mint_armed_other
      | Act_claim_committed_gov | Act_claim_committed_other | Act_claim_reverted
      | Act_burn_reverted ->
          false)
  | Burn_reverted -> (
      match s.last with
      | Act_burn_reverted -> true
      | Act_genesis | Act_block_tick | Act_mint_armed_gov | Act_mint_armed_other
      | Act_claim_committed_gov | Act_claim_committed_other | Act_claim_reverted
      | Act_burn_committed ->
          false)
  | Pending_slot_clear -> (
      match s.pending with
      | Pending_none -> true
      | Pending_gov | Pending_other -> false)
  | Pending_armed_other -> (
      match s.pending with
      | Pending_other -> true
      | Pending_none | Pending_gov -> false)
  | Supply_slot_fell -> s.sup_fell
  | Balance_fell -> s.bal_fell
  | Supply_slot_zero -> (
      match s.supply with
      | Sup_0 -> true
      | Sup_1 | Sup_2 | Sup_wrapped -> false)
  | Balance_zero -> ( match s.pbal with Pb_0 -> true | Pb_1 -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Claim_committed -> "claim_committed"
  | Claim_credited_gov -> "claim_credited_gov"
  | Mint_armed_slot -> "mint_armed_slot"
  | Burn_committed -> "burn_committed"
  | Burn_reverted -> "burn_reverted"
  | Pending_slot_clear -> "pending_slot_clear"
  | Pending_armed_other -> "pending_armed_other"
  | Supply_slot_fell -> "supply_slot_fell"
  | Balance_fell -> "balance_fell"
  | Supply_slot_zero -> "supply_slot_zero"
  | Balance_zero -> "balance_zero"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} by
    test/t_tel_supply_ledger_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
