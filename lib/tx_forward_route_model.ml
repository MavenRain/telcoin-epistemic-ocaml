(** Finite interpreted system for the TX_FORWARD_ROUTE family: the
    observer-to-committee transaction router of
    crates/tn-reth/src/forward.rs. File citations refer to
    Telcoin-Association/telcoin-network at 0c59c15b (working tree).

    THE MODELLED MECHANISM. A non-committee ("observer") worker cannot attest,
    so on [seal] it takes the non-CVV branch
    (crates/consensus/worker/src/worker.rs:282-285) into [disburse_txns]
    (worker.rs:244-277), which discovers the advertised validator RPC endpoints
    and calls [forward_txns] (worker.rs:256). [forward_txns]
    (forward.rs:115-212) resolves the endpoints to providers
    ([cached_providers], forward.rs:77-111, which silently drops an unparseable
    URL at :98-106), builds the fallback vector [fallbacks] from the resolved
    providers (forward.rs:136) and spawns ONE background task (forward.rs:138)
    that walks the queued transactions one at a time (forward.rs:139). For each
    transaction:

    - ROUTING: the owning committee slot is a pure function of the sender -
      [owning_validator] (forward.rs:218-229) recovers the signer, takes its low
      8 bytes little-endian modulo [committee_size] and indexes the slot-ordered
      BLS key vector built once per epoch at worker.rs:100-105 (comment at :96,
      "index == committee slot"). The chain actually walked is
      [owner.into_iter().chain(fallbacks.iter().cloned())] (forward.rs:142-143),
      deduplicated by the [tried] set (forward.rs:149-154), so the owner is
      contacted FIRST and every other advertised endpoint after it.
    - SKIP: a slot with no usable provider is stepped over without an attempt -
      [let Some(provider) = providers.get(&key) else { continue }]
      (forward.rs:155-157). This is a REPAIR PATH and it is modelled
      ({!Owner_unadvertised}); statement S1's owner-first conjunct is guarded on
      it rather than omitting it.
    - PER-ATTEMPT BOUND: [timeout(FORWARD_SEND_TIMEOUT, ...)] (forward.rs:30 =
      5s, applied at :160-168). An elapsed round trip yields
      [Disposition::TryNext("send timed out")] (:166) - explicitly NOT a
      delivery, because "the transaction's fate is unknown here" (:181-183,
      :239-241).
    - PER-TRANSACTION BOUND: [timeout(FORWARD_TX_BUDGET, ...)] (forward.rs:36 =
      15s, wrapper at :148, [.unwrap_or(ForwardOutcome::NoEndpointReached)] at
      :194-195), INSIDE the per-transaction loop, so each transaction gets its
      own fresh budget. 15s / 5s = 3, so at most THREE elapsed round trips can
      ever be charged to one transaction - a fourth would cost 20s. The model's
      step granularity is one COMPLETED attempt, so it deliberately does not
      adjudicate the tie at exactly 15s between the third attempt's own timeout
      and the outer budget; what it claims is only that no fourth ELAPSED round
      trip can be charged, which the arithmetic settles outright. An endpoint
      that answers immediately (accept, full pool, considered rejection) costs
      no budget, which is why {!All_full} walks all four endpoints inside the
      budget: the gate bounds TIME, not attempts.
    - CLASSIFICATION: [classify_server_error] (forward.rs:265-276). A transient
      code ([TRANSIENT_RPC_CODES] = -32003 full pool, -32603 internal;
      forward.rs:38-42) is [TryNext] (:266-268) - the chain continues, because
      another validator may still accept. Anything else is
      [Disposition::Rejected] (:272-275), which STOPS the chain, because "every
      validator shares consensus state, so a considered rejection repeats
      everywhere" (:273). Both are modelled; the model would be unfaithful with
      only one.

    COMPONENTS. One forward pass with a queue of TWO transactions from the SAME
    externally-owned account (so both have the same sender-derived owner - the
    convergence S1 is about), a committee of four slots and the four-position
    chain (owner, then the three other advertised endpoints). The endpoint
    behaviour of a whole pass is drawn from a fixed menu of eight
    configurations ({!env}); each configuration is an initial state, so the
    model has eight inits and the environment never changes mid-pass, matching
    the fact that [providers] and [fallbacks] are captured once before the task
    is spawned (forward.rs:126-138).

    ROLE MAPPING. The committee slots are {!Validator.V0}..{!Validator.V3} in
    slot order, so the owning slot of the modelled sender is
    {!Validator.V1}. The observer is {!Validator.V4}, a NON-committee node
    (it has no slot and never appears in [committee_slots]).
    - V4 (the observer, {!observer}) is a knowledge agent. Its view is exactly
      the forwarder's own loop state: which queued transaction it is on, the
      chain position, the budget it has burned, which slot it contacted first
      for each transaction, and each transaction's recorded [ForwardOutcome].
      It does NOT contain {!env} and does NOT contain either transaction's
      holder: an elapsed round trip (forward.rs:160-168) returns no information
      about whether the endpoint received the bytes.
    - V1 (the owning slot, {!owning_slot}) is a knowledge agent. Its view is its
      own pool only - whether it holds tx1 and whether it holds tx2. A
      forwarded transaction arrives as raw bytes over
      [eth_sendRawTransaction] (forward.rs:162) and carries no marker saying
      whether it was routed here as owner or as fallback, so V1 sees nothing of
      the observer's cursor and nothing of any other validator's pool.
    - V0, V2, V3 and V5..V9 are idle non-agents with the constant blank view and
      never appear under K. The non-owner recipients are deliberately modelled
      in AGGREGATE ({!Held_other}) rather than per slot, because the fallback
      order is [providers.keys()] (forward.rs:136), i.e. BLS-key byte order,
      which has nothing to do with slot order - naming a particular fallback
      slot would be a fiction.

    DELIBERATE OMISSIONS, each checked against the code rather than assumed.
    (a) [ALREADY_KNOWN_MESSAGE] (forward.rs:44-46, :269-271) maps a duplicate to
    [Delivered]. It cannot fire in this scope: [tried] (forward.rs:152) forbids
    contacting one validator twice inside one transaction's chain, and the two
    modelled transactions are distinct, so no chain ever offers a transaction to
    a validator that already holds it. (b) [owning_validator] returning [None]
    (forward.rs:223) needs [recover_raw_transaction] to fail on bytes that the
    observer's own pool already validated and its own batch builder sealed, so
    it is unreachable on this path; [committee_slots.get(slot)] (:228) cannot
    fail either, since [committee_size] IS [committee_slots.len()]
    (forward.rs:121). (c) Re-forwarding: there is none. [disburse_txns] returns
    [Ok(())] as soon as the task is spawned (worker.rs:253-276), the batch
    builder takes that ack as the seal result and immediately removes the
    transactions from the observer's pool
    ([update_canonical_state] "update pool to remove mined transactions",
    crates/batch-builder/src/lib.rs:187 and :326-332,
    crates/tn-reth/src/txn_pool.rs:145-168), the local-transaction backup task
    is commented out (txn_pool.rs:103-123), and the gossip route this replaced
    was deleted (forward.rs:1-12, worker.rs:240-243). So a transaction that this
    single pass fails to place is never offered again by the system, and no
    sibling path repairs any of this family's gate deletions. *)

(** [true] iff [a >= b] on ints, without polymorphic comparison. *)
let int_at_least a b = Bool.not (Int.equal (Int.compare a b) (-1))

(** Chain positions walked for one transaction: the owning slot then the three
    other advertised endpoints ([owner] chained onto [fallbacks], deduplicated
    by [tried], forward.rs:142-154 with a committee of four). *)
let chain_len = 4

(** Elapsed round trips that fit in one transaction's budget:
    [FORWARD_TX_BUDGET] / [FORWARD_SEND_TIMEOUT] = 15s / 5s (forward.rs:30,
    forward.rs:36). The fourth is cut off by the outer [timeout]
    (forward.rs:148, :194-195). *)
let budget_units = 3

(** How one committee slot's endpoint answers one attempt. *)
type answer =
  | Accepts
      (** [send_raw_transaction] returns [Ok]: [Disposition::Delivered]
          (forward.rs:167, :173-176). The slot now holds the transaction. *)
  | Full_pool
      (** a transient JSON-RPC code (-32003 full pool): [Disposition::TryNext]
          (forward.rs:266-268). Immediate, so it costs no budget. *)
  | Silent_landed
      (** the round trip elapses ([Disposition::TryNext("send timed out")],
          forward.rs:166) but the endpoint DID receive and accept the bytes -
          the hidden branch the code names at forward.rs:181-183, "the
          transaction's fate is unknown here". Costs one budget unit. *)
  | Silent_lost
      (** the round trip elapses and the endpoint never got the bytes. Costs one
          budget unit. Observationally identical to {!Silent_landed}. *)
  | Refuses
      (** a considered rejection (e.g. "nonce too low", code -32000):
          [Disposition::Rejected] (forward.rs:272-275), which stops the chain
          because every validator would repeat it (:273). Immediate. *)
  | Unadvertised
      (** the slot has no usable provider, so [providers.get] is [None] and the
          loop [continue]s without an attempt (forward.rs:155-157); also covers
          an endpoint dropped for an unparseable URL (forward.rs:98-106). *)

(** The endpoint configuration of one whole forward pass. Captured before the
    task is spawned (forward.rs:126-138), so it never changes mid-pass. *)
type env =
  | All_responsive  (** every advertised endpoint accepts. *)
  | Owner_full
      (** the owning slot answers -32003; every other advertised endpoint has
          room. The premise of S3's fallthrough conjunct. *)
  | All_full
      (** every advertised endpoint answers -32003, so the chain walks all four
          positions with no budget burn and still places nothing. This is the
          "no room elsewhere" case that makes S3's [Room_elsewhere] guard
          live. *)
  | Owner_silent_landed
      (** the owning slot's round trip elapses AND it accepted the transaction;
          the other endpoints have room. *)
  | Owner_silent_lost
      (** the owning slot's round trip elapses and it never got the
          transaction; the other endpoints have room. The observer cannot
          distinguish this pass from {!Owner_silent_landed}. *)
  | All_silent
      (** every advertised endpoint accepts the connection and never answers -
          the exact scenario [FORWARD_TX_BUDGET]'s doc comment names
          (forward.rs:32-35). *)
  | Owner_rejects
      (** the owning slot returns a considered rejection, stopping the chain
          (forward.rs:177-180, :272-275). *)
  | Owner_unadvertised
      (** the owning slot has no usable provider and is skipped
          (forward.rs:155-157); the other three endpoints accept. *)

(** Total order index for {!env}. *)
let env_index = function
  | All_responsive -> 0
  | Owner_full -> 1
  | All_full -> 2
  | Owner_silent_landed -> 3
  | Owner_silent_lost -> 4
  | All_silent -> 5
  | Owner_rejects -> 6
  | Owner_unadvertised -> 7

(** Total order on {!env}. *)
let env_compare a b = Int.compare (env_index a) (env_index b)

(** How the OWNING slot's endpoint answers in this configuration. *)
let owner_answer = function
  | All_responsive -> Accepts
  | Owner_full -> Full_pool
  | All_full -> Full_pool
  | Owner_silent_landed -> Silent_landed
  | Owner_silent_lost -> Silent_lost
  | All_silent -> Silent_lost
  | Owner_rejects -> Refuses
  | Owner_unadvertised -> Unadvertised

(** How every NON-owning advertised endpoint answers in this configuration. *)
let fallback_answer = function
  | All_responsive -> Accepts
  | Owner_full -> Accepts
  | All_full -> Full_pool
  | Owner_silent_landed -> Accepts
  | Owner_silent_lost -> Accepts
  | All_silent -> Silent_lost
  | Owner_rejects -> Accepts
  | Owner_unadvertised -> Accepts

(** [true] iff the owning slot has a usable provider in this configuration. *)
let owner_is_advertised e =
  match owner_answer e with
  | Unadvertised -> false
  | Accepts | Full_pool | Silent_landed | Silent_lost | Refuses -> true

(** [true] iff the owning slot answers with the transient full-pool code. *)
let owner_answers_full e =
  match owner_answer e with
  | Full_pool -> true
  | Accepts | Silent_landed | Silent_lost | Refuses | Unadvertised -> false

(** [true] iff the owning slot's round trip elapses without a verdict. *)
let owner_is_silent e =
  match owner_answer e with
  | Silent_landed | Silent_lost -> true
  | Accepts | Full_pool | Refuses | Unadvertised -> false

(** [true] iff some NON-owning advertised endpoint would accept - the "another
    validator may still accept the transaction" premise (forward.rs:239-241). *)
let fallback_has_room e =
  match fallback_answer e with
  | Accepts -> true
  | Full_pool | Silent_landed | Silent_lost | Refuses | Unadvertised -> false

(** Which committee slot a chain position addresses. *)
type slot =
  | Owner_slot  (** the sender-derived owning slot, {!owning_slot} = V1. *)
  | Other_slot
      (** one of the three non-owning advertised endpoints, kept aggregate
          because [providers.keys()] order (forward.rs:136) is BLS-key order,
          not slot order. *)

(** Which slot a transaction's FIRST attempt went to; [No_contact] before any
    attempt (a skipped unadvertised slot is not an attempt). *)
type contact = No_contact | Contact_owner | Contact_other

(** Total order index for {!contact}. *)
let contact_index = function
  | No_contact -> 0
  | Contact_owner -> 1
  | Contact_other -> 2

(** Total order on {!contact}. *)
let contact_compare a b = Int.compare (contact_index a) (contact_index b)

(** [true] iff some attempt has been made for this transaction. *)
let contact_made = function
  | No_contact -> false
  | Contact_owner | Contact_other -> true

(** [true] iff the first attempt went to the sender-derived owning slot. *)
let contact_is_owner = function
  | Contact_owner -> true
  | No_contact | Contact_other -> false

(** The slot a contact names. *)
let contact_of_slot = function
  | Owner_slot -> Contact_owner
  | Other_slot -> Contact_other

(** Only the FIRST attempt is recorded; later ones leave it alone. *)
let keep_first existing c =
  match existing with
  | No_contact -> c
  | Contact_owner | Contact_other -> existing

(** The [ForwardOutcome] the pass records for one transaction
    (forward.rs:244-253), plus [Pending] while its chain is still running. *)
type outcome =
  | Pending  (** the chain for this transaction has not finished. *)
  | Delivered  (** [ForwardOutcome::Delivered] (forward.rs:174). *)
  | Rejected
      (** [ForwardOutcome::Rejected] - a considered rejection stopped the chain
          (forward.rs:178). *)
  | No_endpoint
      (** [ForwardOutcome::NoEndpointReached] - the chain was exhausted or the
          per-transaction budget elapsed (forward.rs:150, :195). *)

(** Total order index for {!outcome}. *)
let outcome_index = function
  | Pending -> 0
  | Delivered -> 1
  | Rejected -> 2
  | No_endpoint -> 3

(** Total order on {!outcome}. *)
let outcome_compare a b = Int.compare (outcome_index a) (outcome_index b)

(** [true] iff this transaction's chain is still running. *)
let outcome_pending = function
  | Pending -> true
  | Delivered | Rejected | No_endpoint -> false

(** [true] iff the pass recorded a delivery for this transaction. *)
let outcome_delivered = function
  | Delivered -> true
  | Pending | Rejected | No_endpoint -> false

(** Which committee pools hold one transaction. The fallback recipients are
    aggregated (see the header's role mapping). *)
type holding =
  | Held_none  (** no committee validator has the transaction. *)
  | Held_owner  (** the owning slot has it, no one else. *)
  | Held_other  (** some non-owning advertised validator has it. *)
  | Held_both
      (** BOTH - reachable exactly when an owner that silently accepted was
          then fallen through past, so the observer placed a second copy. *)

(** Total order index for {!holding}. *)
let holding_index = function
  | Held_none -> 0
  | Held_owner -> 1
  | Held_other -> 2
  | Held_both -> 3

(** Total order on {!holding}. *)
let holding_compare a b = Int.compare (holding_index a) (holding_index b)

(** [true] iff the owning slot holds the transaction. *)
let held_by_owner = function
  | Held_owner | Held_both -> true
  | Held_none | Held_other -> false

(** [true] iff some non-owning validator holds the transaction. *)
let held_by_other = function
  | Held_other | Held_both -> true
  | Held_none | Held_owner -> false

(** [true] iff some committee validator holds the transaction. *)
let held_by_some = function
  | Held_owner | Held_other | Held_both -> true
  | Held_none -> false

(** Add a slot to the set of holders. *)
let holds_add slot h =
  match (slot, h) with
  | Owner_slot, Held_none -> Held_owner
  | Owner_slot, Held_owner -> Held_owner
  | Owner_slot, Held_other -> Held_both
  | Owner_slot, Held_both -> Held_both
  | Other_slot, Held_none -> Held_other
  | Other_slot, Held_owner -> Held_both
  | Other_slot, Held_other -> Held_other
  | Other_slot, Held_both -> Held_both

(** Which queued transaction the single background task is on
    (the [for tx in &transactions] cursor, forward.rs:139). *)
type phase =
  | Tx1  (** the first queued transaction's chain is running. *)
  | Tx2  (** the first is resolved; the second's chain is running. *)
  | Done  (** both are resolved and the task has returned. *)

(** Total order index for {!phase}. *)
let phase_index = function Tx1 -> 0 | Tx2 -> 1 | Done -> 2

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** [true] iff the second queued transaction's chain is the running one. *)
let phase_is_tx2 = function Tx2 -> true | Tx1 | Done -> false

(** The joint global state of one forward pass: the endpoint configuration, the
    task's cursor over the two queued transactions, the chain position and
    budget spent on the CURRENT transaction, each transaction's first contact
    and recorded outcome, and (hidden from the observer) which committee pools
    hold each transaction. *)
type state = {
  env : env;  (** the pass's endpoint configuration, fixed at spawn. *)
  phase : phase;  (** the [for tx] cursor (forward.rs:139). *)
  pos : int;  (** next chain position for the current transaction, 0..4. *)
  burned : int;
      (** elapsed round trips charged to the CURRENT transaction's budget,
          0..4; reset when the cursor advances, because the [timeout] wrapper
          is inside the loop body (forward.rs:148). *)
  first1 : contact;  (** slot of tx1's first attempt. *)
  first2 : contact;  (** slot of tx2's first attempt. *)
  out1 : outcome;  (** tx1's [ForwardOutcome]. *)
  out2 : outcome;  (** tx2's [ForwardOutcome]. *)
  hold1 : holding;  (** which committee pools hold tx1. *)
  hold2 : holding;  (** which committee pools hold tx2. *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = env_compare s1.env s2.env in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = phase_compare s1.phase s2.phase in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Int.compare s1.pos s2.pos in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Int.compare s1.burned s2.burned in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = contact_compare s1.first1 s2.first1 in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = contact_compare s1.first2 s2.first2 in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = outcome_compare s1.out1 s2.out1 in
              if Bool.not (Int.equal c6 0) then c6
              else
                let c7 = outcome_compare s1.out2 s2.out2 in
                if Bool.not (Int.equal c7 0) then c7
                else
                  let c8 = holding_compare s1.hold1 s2.hold1 in
                  if Bool.not (Int.equal c8 0) then c8
                  else holding_compare s1.hold2 s2.hold2

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A party's local view.

    [View_observer (phase, pos, burned, first1, first2, out1, out2)] is V4's
    projection: the forwarder's own loop state and nothing else. It omits
    {!env} and both {!holding} fields - after an elapsed round trip the
    observer has no verdict at all (forward.rs:160-168, :181-183), so a pass in
    which the silent owner kept the transaction and a pass in which it did not
    are the SAME view at every step.

    [View_slot (has_tx1, has_tx2)] is V1's projection: its own pool. A forwarded
    transaction arrives as raw bytes (forward.rs:162) with no marker of how it
    was routed, so V1 sees neither the observer's cursor nor any other
    validator's pool.

    [View_idle] is the constant blank view of V0, V2, V3 and V5..V9, who are
    non-agents here and never appear under K. *)
type view =
  | View_observer of phase * int * int * contact * contact * outcome * outcome
  | View_slot of bool * bool
  | View_idle

(** Total deterministic order over ALL fields of the observer's view. *)
let view_observer_compare (ph, po, bu, f1, f2, o1, o2) (ph', po', bu', f1', f2', o1', o2')
    =
  let c = phase_compare ph ph' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Int.compare po po' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Int.compare bu bu' in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = contact_compare f1 f1' in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = contact_compare f2 f2' in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = outcome_compare o1 o1' in
            if Bool.not (Int.equal c5 0) then c5
            else outcome_compare o2 o2'

(** Total deterministic order over ALL fields of a slot's own-pool view. *)
let view_slot_compare (a1, a2) (b1, b2) =
  let c = Bool.compare a1 b1 in
  if Bool.not (Int.equal c 0) then c else Bool.compare a2 b2

(** Total order on views: [View_idle] < [View_slot] < [View_observer]. Every
    constructor pair is spelled: no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_slot _ | View_observer _) -> -1
  | (View_slot _ | View_observer _), View_idle -> 1
  | View_slot (p, q), View_slot (p', q') -> view_slot_compare (p, q) (p', q')
  | View_slot _, View_observer _ -> -1
  | View_observer _, View_slot _ -> 1
  | ( View_observer (ph, po, bu, f1, f2, o1, o2),
      View_observer (ph', po', bu', f1', f2', o1', o2') ) ->
      view_observer_compare (ph, po, bu, f1, f2, o1, o2)
        (ph', po', bu', f1', f2', o1', o2')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** The observer: a NON-committee worker with no slot, the forwarding agent of
    forward.rs:115-212. *)
let observer = Validator.V4

(** The committee slot the modelled sender's low 8 bytes select
    (forward.rs:225-228); slot 1 of the four-slot committee. *)
let owning_slot = Validator.V1

(** View projection. V4 (the observer) and V1 (the owning slot) are the
    knowledge agents; every other validator is idle with the constant blank
    view and never appears under K. *)
let view v s =
  match v with
  | Validator.V4 ->
      View_observer (s.phase, s.pos, s.burned, s.first1, s.first2, s.out1, s.out2)
  | Validator.V1 -> View_slot (held_by_owner s.hold1, held_by_owner s.hold2)
  | Validator.V0 | Validator.V2 | Validator.V3 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | Round_robin_owner
      (** delete the sender-derived slot at forward.rs:227 (the
          [% committee_size] over the signer's low 8 bytes) and hand out slots
          in arrival order instead, so the two transactions of ONE account are
          offered to two different slots first (tx1 -> slot 0, tx2 -> slot 1 =
          the owner). REMOVES the transition "tx1's first attempt goes to the
          owning slot" and ADDS "tx1's first attempt goes to a non-owner".
          No sibling path repairs it: the receive-side twin
          [submit_txn_if_mine] (crates/batch-validator/src/validator.rs:89-106)
          applies the identical modulo but has NO production caller
          (`rg submit_txn_if_mine crates/` finds only the trait declaration at
          crates/types/src/worker/sealed_batch.rs:212, this impl, the no-op test
          impl at validator.rs:229 and four tests), the worker gossip handler
          carries batch digests and not raw transactions, [fallbacks]
          (forward.rs:136) is BLS-key order over the churning advertisement
          set and cannot re-derive the sender's slot, [tried]
          (forward.rs:149-154) dedups only within one transaction, and a
          receiving pool can order nonces only within itself, never across two
          validators. *)
  | No_forward_budget
      (** delete the outer [timeout(FORWARD_TX_BUDGET, ...)] wrapper at
          forward.rs:148 together with its
          [.unwrap_or(ForwardOutcome::NoEndpointReached)] at :194-195, keeping
          the per-attempt timeout. REMOVES the transition that abandons a
          transaction once its budget is spent, so a fourth elapsed round trip
          is charged to the same transaction. No sibling path repairs it: the
          per-attempt [FORWARD_SEND_TIMEOUT] (forward.rs:160) is INSIDE the loop
          and is exactly what the outer budget is documented to bound in
          aggregate (forward.rs:32-35); the spawn site (forward.rs:138) attaches
          no deadline; the caller [disburse_txns]
          (crates/consensus/worker/src/worker.rs:244-277) spawns and returns
          [Ok(())] without joining; and the provider cache
          (forward.rs:77-111) bounds memory, not time. *)
  | No_transient_fallthrough
      (** delete the transient branch of [classify_server_error] at
          forward.rs:266-268 so a -32003 full pool falls into the else at
          :272-275 and becomes [Disposition::Rejected]. REMOVES the
          fallthrough transition out of a saturated owner and ADDS "the chain
          stops at the saturated owner", after which the transaction is in no
          pool at all. No sibling path repairs it: the pass never offers the
          transaction again (see the header's omission (c) - the ack is
          unconditional and the observer's pool is emptied at
          crates/batch-builder/src/lib.rs:326-332), the [already known] case
          (forward.rs:269-271) only helps once an attempt actually landed, which
          is exactly what did not happen, and the two timeouts bound time, not
          outcome. *)
  | Timeout_counts_as_delivered
      (** delete the elapsed-round-trip classification at forward.rs:165-167,
          which maps [Err(Elapsed)] to [Disposition::TryNext("send timed out")],
          and treat an elapsed attempt as [Disposition::Delivered] instead.
          REMOVES the fallthrough out of a silent endpoint (the chain now stops
          at it, forward.rs:173-176) and ADDS "the pass records a delivery no
          validator ever acknowledged". No sibling path repairs it: stopping the
          chain is exactly what forgoes the only other endpoints, and nothing
          re-offers the transaction (header omission (c)). This is the gate the
          code's own comments call out twice - "the transaction's fate is
          unknown here" (forward.rs:181-183) and "This endpoint gave no verdict"
          (forward.rs:239-241). *)

(** Which slot the chain's [pos]-th position addresses for the transaction the
    cursor is on. Pristine (and under every mutation that does not touch the
    routing) position 0 is the sender-derived owner and 1..3 are the other
    advertised endpoints (forward.rs:142-143). Under {!Round_robin_owner} the
    slots are handed out in arrival order, so tx1 starts at slot 0 and tx2 at
    slot 1, which is the owner. *)
let slot_at mut phase pos =
  match mut with
  | Pristine | No_forward_budget | No_transient_fallthrough
  | Timeout_counts_as_delivered ->
      if Int.equal pos 0 then Owner_slot else Other_slot
  | Round_robin_owner -> (
      match phase with
      | Tx1 -> if Int.equal pos 1 then Owner_slot else Other_slot
      | Tx2 -> if Int.equal pos 0 then Owner_slot else Other_slot
      | Done -> Other_slot)

(** How the addressed slot answers in this configuration. *)
let answer_of e slot =
  match slot with
  | Owner_slot -> owner_answer e
  | Other_slot -> fallback_answer e

(** [true] iff the per-transaction budget stops the chain here. Deleted by
    {!No_forward_budget}. *)
let budget_stops mut burned =
  match mut with
  | No_forward_budget -> false
  | Pristine | Round_robin_owner | No_transient_fallthrough
  | Timeout_counts_as_delivered ->
      int_at_least burned budget_units

(** Record an attempt against [slot] for the transaction the cursor is on;
    only the first attempt sticks. *)
let with_contact s slot =
  let c = contact_of_slot slot in
  match s.phase with
  | Tx1 -> { s with first1 = keep_first s.first1 c }
  | Tx2 -> { s with first2 = keep_first s.first2 c }
  | Done -> s

(** Add [slot] to the holders of the transaction the cursor is on. *)
let with_hold s slot =
  match s.phase with
  | Tx1 -> { s with hold1 = holds_add slot s.hold1 }
  | Tx2 -> { s with hold2 = holds_add slot s.hold2 }
  | Done -> s

(** Record the [ForwardOutcome] of the current transaction and advance the
    cursor, resetting the chain position and the budget - the [timeout] wrapper
    is inside the loop body, so the next transaction starts fresh
    (forward.rs:139, :148). *)
let resolve s o =
  match s.phase with
  | Tx1 -> { s with out1 = o; phase = Tx2; pos = 0; burned = 0 }
  | Tx2 -> { s with out2 = o; phase = Done; pos = 0; burned = 0 }
  | Done -> s

(** One step of the forward task under a mutation: either the current
    transaction's chain ends (exhausted, or the budget is spent), or the next
    chain position is attempted and classified. A [Done] state has no successor
    and is stutter-closed by the kernel. *)
let next_with mut s =
  match s.phase with
  | Done -> []
  | Tx1 | Tx2 ->
      if int_at_least s.pos chain_len then [ resolve s No_endpoint ]
      else if budget_stops mut s.burned then [ resolve s No_endpoint ]
      else
        let slot = slot_at mut s.phase s.pos in
        let stepped = { s with pos = s.pos + 1 } in
        (match answer_of s.env slot with
        | Unadvertised -> [ stepped ]
        | Accepts -> [ resolve (with_hold (with_contact s slot) slot) Delivered ]
        | Refuses -> [ resolve (with_contact s slot) Rejected ]
        | Full_pool -> (
            let contacted = with_contact s slot in
            match mut with
            | No_transient_fallthrough -> [ resolve contacted Rejected ]
            | Pristine | Round_robin_owner | No_forward_budget
            | Timeout_counts_as_delivered ->
                [ { contacted with pos = s.pos + 1 } ])
        | Silent_lost -> (
            let contacted = with_contact s slot in
            match mut with
            | Timeout_counts_as_delivered -> [ resolve contacted Delivered ]
            | Pristine | Round_robin_owner | No_forward_budget
            | No_transient_fallthrough ->
                [ { contacted with pos = s.pos + 1; burned = s.burned + 1 } ])
        | Silent_landed -> (
            let contacted = with_hold (with_contact s slot) slot in
            match mut with
            | Timeout_counts_as_delivered -> [ resolve contacted Delivered ]
            | Pristine | Round_robin_owner | No_forward_budget
            | No_transient_fallthrough ->
                [ { contacted with pos = s.pos + 1; burned = s.burned + 1 } ]))

(** The pristine transition relation. *)
let next = next_with Pristine

(** The start of a pass in a given endpoint configuration: cursor on tx1,
    nothing contacted, nothing held, nothing spent. *)
let start e =
  {
    env = e;
    phase = Tx1;
    pos = 0;
    burned = 0;
    first1 = No_contact;
    first2 = No_contact;
    out1 = Pending;
    out2 = Pending;
    hold1 = Held_none;
    hold2 = Held_none;
  }

(** The initial state: a pass in which every advertised endpoint accepts. *)
let initial = start All_responsive

(** Initial state: the owning slot's pool is full, the others have room. *)
let initial_owner_full = start Owner_full

(** Initial state: every advertised pool is full. *)
let initial_all_full = start All_full

(** Initial state: the owning slot elapses but kept the transaction. *)
let initial_owner_silent_landed = start Owner_silent_landed

(** Initial state: the owning slot elapses and never got the transaction. *)
let initial_owner_silent_lost = start Owner_silent_lost

(** Initial state: every advertised endpoint elapses. *)
let initial_all_silent = start All_silent

(** Initial state: the owning slot returns a considered rejection. *)
let initial_owner_rejects = start Owner_rejects

(** Initial state: the owning slot has no usable provider. *)
let initial_owner_unadvertised = start Owner_unadvertised

(** Every initial state: one per endpoint configuration, since the
    configuration is captured before the task is spawned (forward.rs:126-138)
    and never changes mid-pass. *)
let inits =
  [
    initial;
    initial_owner_full;
    initial_all_full;
    initial_owner_silent_landed;
    initial_owner_silent_lost;
    initial_all_silent;
    initial_owner_rejects;
    initial_owner_unadvertised;
  ]

(** The atom vocabulary this family's statements quantify over. The first three
    are the topos battery's seeds ({!Topos_gate.seeds} takes the three smallest
    atoms), so they are deliberately contingent and, in the case of the two
    holding atoms, hidden from the observer. *)
type atom =
  | Tx1_delivered  (** out1 = [ForwardOutcome::Delivered] *)
  | Tx1_held_by_owner  (** the owning slot's pool holds tx1 *)
  | Tx1_held_by_other  (** some non-owning validator's pool holds tx1 *)
  | Tx1_held_by_some  (** some committee validator holds tx1 *)
  | Tx1_unresolved  (** tx1's chain has not finished *)
  | Tx1_contacted  (** some attempt has been made for tx1 *)
  | Tx1_first_contact_is_owner  (** tx1's first attempt went to the owner *)
  | Tx2_contacted  (** some attempt has been made for tx2 *)
  | Tx2_first_contact_is_owner  (** tx2's first attempt went to the owner *)
  | Tx2_chain_start  (** the cursor has just reached tx2, before any attempt *)
  | Owner_advertised  (** the owning slot has a usable provider *)
  | Owner_pool_full  (** the owning slot answers the transient full-pool code *)
  | Owner_timed_out_tx1
      (** the owning slot's answer to tx1 is an elapsed round trip AND the
          owner has actually been attempted for tx1 *)
  | Room_elsewhere  (** some non-owning advertised endpoint would accept *)
  | Budget_spent  (** at least one budget unit is charged to the current tx *)
  | Budget_exhausted  (** the current transaction's whole budget is spent *)
  | Budget_overrun
      (** MORE than the budget has been charged to one transaction - the state
          the outer [timeout] (forward.rs:148) exists to forbid *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Tx1_delivered -> outcome_delivered s.out1
  | Tx1_held_by_owner -> held_by_owner s.hold1
  | Tx1_held_by_other -> held_by_other s.hold1
  | Tx1_held_by_some -> held_by_some s.hold1
  | Tx1_unresolved -> outcome_pending s.out1
  | Tx1_contacted -> contact_made s.first1
  | Tx1_first_contact_is_owner -> contact_is_owner s.first1
  | Tx2_contacted -> contact_made s.first2
  | Tx2_first_contact_is_owner -> contact_is_owner s.first2
  | Tx2_chain_start ->
      phase_is_tx2 s.phase && Int.equal s.pos 0 && outcome_pending s.out2
  | Owner_advertised -> owner_is_advertised s.env
  | Owner_pool_full -> owner_answers_full s.env
  | Owner_timed_out_tx1 -> owner_is_silent s.env && contact_is_owner s.first1
  | Room_elsewhere -> fallback_has_room s.env
  | Budget_spent -> int_at_least s.burned 1
  | Budget_exhausted -> int_at_least s.burned budget_units
  | Budget_overrun -> int_at_least s.burned (budget_units + 1)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Tx1_delivered -> "delivered(tx1)"
  | Tx1_held_by_owner -> "holds(owner,tx1)"
  | Tx1_held_by_other -> "holds(other,tx1)"
  | Tx1_held_by_some -> "holds(some,tx1)"
  | Tx1_unresolved -> "unresolved(tx1)"
  | Tx1_contacted -> "contacted(tx1)"
  | Tx1_first_contact_is_owner -> "first(tx1)=owner"
  | Tx2_contacted -> "contacted(tx2)"
  | Tx2_first_contact_is_owner -> "first(tx2)=owner"
  | Tx2_chain_start -> "chain_start(tx2)"
  | Owner_advertised -> "advertised(owner)"
  | Owner_pool_full -> "full(owner)"
  | Owner_timed_out_tx1 -> "elapsed(owner,tx1)"
  | Room_elsewhere -> "room(other)"
  | Budget_spent -> "budget>0"
  | Budget_exhausted -> "budget=15s"
  | Budget_overrun -> "budget>15s"

(** The CTLK checker over this family's ordered state and view: the presheaf-
    topos denotation, pinned to agree with {!System} at every reachable world by
    test/t_tx_forward_route_topos.ml. Every transition strictly advances the
    lexicographic pair (cursor, chain position) and nothing in the pass undoes
    itself, so reachability here is expected to be ANTISYMMETRIC (a poset);
    that is asserted by the gate, not assumed. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the eight endpoint configurations as
    initial states, mutation-parameterised transitions, the two-agent view and
    the atom valuation. *)
let spec_of mut = { Checker.init = inits; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
