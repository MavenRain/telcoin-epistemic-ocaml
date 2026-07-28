(** The TEL precompile's dispatch surface in telcoin-network: the three gates
    that stand between an arbitrary EVM call to [0x7e1] and the TEL token's
    global state. Every citation below was re-opened in this checkout
    (Telcoin-Association/telcoin-network, git HEAD [0c59c15b], working tree).

    {1 Mechanism}

    The precompile is installed as exactly ONE closure at
    [TELCOIN_PRECOMPILE_ADDRESS = 0x00..07e1]
    (crates/tn-reth/src/evm/tel_precompile/mod.rs:84-85 and :109-115,
    [map.apply_precompile(&TELCOIN_PRECOMPILE_ADDRESS, ..)]). There is no
    fallback handler and no proxy, so a call that reaches the address reaches
    [telcoin_precompile] and nothing else. Three gates then decide everything:

    - the SHORT-CALLDATA GATE, tel_precompile/mod.rs:121-123:
      [if input.data.len() < 4 { return Err(PrecompileError::Other("Invalid
      input: too short".into())); }], standing in front of the raw slice
      [let selector: [u8; 4] = input.data[0..4].try_into().unwrap();] at :125.
      The slice panics first on a 1-3 byte payload; the [unwrap()] is downstream
      of it and cannot save it. The sibling BLS dispatcher solves the identical
      problem STRUCTURALLY, with a total [data.split_first_chunk::<4>()] and an
      [else] arm (bls_precompile/mod.rs:102-105), and therefore carries no
      guard - the contrast is the evidence that the TEL guard is load-bearing
      rather than defensive.
    - the FAIL-CLOSED SELECTOR SET, tel_precompile/mod.rs:128-164: four mainnet
      arms (mint/claim/burn/totalSupply, :130-143), the faucet-only role arms
      behind [#[cfg(feature = "faucet")]] (:145-161), and a final
      [_ => Err(PrecompileError::Other("Unknown function selector".into()))] at
      :163. The in-tree regression test enumerates the ERC-20 / EIP-2612 surface
      this arm rejects (tests/it/tel_precompile_props.rs:309-341) and the
      randomized mirror is :259-278.
    - the ADDRESS PINNING: every state access names the constant rather than the
      executing frame - [internals.sload(TELCOIN_PRECOMPILE_ADDRESS,
      TOTAL_SUPPLY_SLOT)] (burnable.rs:91-92, :275-278, :342-345), the two mint
      [sstore]s (:181-183, :187-189), the claim loads and clears (:241-244,
      :252-255, :267-272), the burn supply write (:342-351) and the balance
      helper call [balance_decr(internals, TELCOIN_PRECOMPILE_ADDRESS, amount)]
      (:337, helpers.rs:56-77). tests/it/tel_precompile_props.rs:389-414 locks
      this in through a real [DELEGATECALL] relay
      ([RELAY_BYTECODE], :364-370: [CALLDATACOPY; DELEGATECALL; POP;
      RETURNDATACOPY; RETURN]).

    {1 Components}

    One transaction is followed end to end, in three phases:

    - {!Choose}: the attacker picks the call vector - the calldata shape and the
      caller shape. Sixteen vectors branch out of the single initial state.
    - {!Dispatched}: [telcoin_precompile] has run. Its {!verdict} and any storage
      write are fixed here.
    - {!Settled}: the transaction's own status is fixed and the block is
      produced. A reverting transaction rolls its storage writes back, which is
      modelled: this is one of the two repair paths the family carries on
      purpose (see {!caller_reverts}).

    {1 Role mapping - who is a knowledge agent and why}

    - [V1] {b the TEL dispatcher frame} ({!View_dispatcher}). Its view is exactly
      what [telcoin_precompile] reads: the calldata and its own result
      (mod.rs:120-164). It does NOT see the caller shape, because nothing the
      dispatcher reads distinguishes a [DELEGATECALL] frame from a direct
      [CALL] - the same function body is what tests/it/tel_precompile_props.rs:
      389-414 reaches through a relay. That ignorance is the security rationale
      for failing closed and is stated as such in S1.
    - [V2] {b the on-chain supply reader} ({!View_supply_reader}): a contract (or
      an [eth_call]) that reads [totalSupply()] at [0x7e1], i.e. the pinned slot
      of burnable.rs:83-96, and observes that it is executing in a produced
      block. It sees NOTHING else - in particular the EVM gives it no access to
      logs, which is why the event channel is a different agent and not a hidden
      part of this one.
    - [V3] {b the TEL event-stream consumer} ({!View_event_stream}): sees the
      precompile's own events, all of which are emitted with
      [address = TELCOIN_PRECOMPILE_ADDRESS] as a literal - [Burn(uint256)]
      (burnable.rs:353-361) and [Transfer(precompile, 0, amount)] (:363-374).
      The event PAYLOADS carry no frame identity, so V3 can see that a burn
      settled and not through what frame it was reached. V3 exists specifically
      so that the event channel is modelled rather than omitted: it is the one
      channel that survives {!Frame_scoped_storage}, and S3 names V2 rather than
      V3 for exactly that reason. (Modelling admission: a full-node indexer that
      also reads the transaction envelope's [to] field is a strictly wider
      channel than V3 and is not modelled here; V3 is the event payload
      consumer.)
    - [V0] and [V4]..[V9] are idle: the constant blank view {!View_idle}. They
      never appear under [K].

    {1 Repair paths carried on purpose (R5)}

    Two real repairs are in the model, not elided:

    - the caller-side [abi.decode] revert ({!Relay_decodes}): a caller that
      decodes a return value reverts on empty returndata, which partially masks
      {!Open_selector_fallthrough}. S1's transaction-level conjunct quantifies
      over the shapes it does NOT cover, and therefore survives it.
    - the transaction revert rollback ({!settled_of}): a reverting transaction
      undoes the precompile's storage writes, so "the precompile wrote" and "the
      supply moved" are genuinely different facts in this model. *)

(** The calldata shape as the dispatcher sees it (tel_precompile/mod.rs:120-126,
    :128-164). *)
type calldata =
  | Short
      (** a 1-3 byte payload: below the 4-byte selector width, so it is what the
          guard at mod.rs:121-123 exists to reject and what the slice at :125
          would panic on. *)
  | Sel_burn
      (** [burnCall::SELECTOR] with a full 32-byte argument: the state-mutating
          arm at mod.rs:137-139, handled at burnable.rs:317-377. *)
  | Sel_total
      (** [totalSupplyCall::SELECTOR]: the read-only arm at mod.rs:141-143,
          handled at burnable.rs:83-96, returning 32 bytes. *)
  | Sel_unknown
      (** a >= 4 byte payload whose selector is in none of the implemented arms -
          the ERC-20 / EIP-2612 surface of
          tests/it/tel_precompile_props.rs:316-328. Falls to mod.rs:163. *)

(** Total order index for {!calldata}. *)
let calldata_index = function
  | Short -> 0
  | Sel_burn -> 1
  | Sel_total -> 2
  | Sel_unknown -> 3

(** Total order on {!calldata}. *)
let calldata_compare a b = Int.compare (calldata_index a) (calldata_index b)

(** The shape of the caller that reaches [0x7e1], which decides how the
    precompile's own result becomes the transaction's status. *)
type caller_shape =
  | Eoa_direct
      (** an EOA sends the calldata straight to [0x7e1]: the transaction's status
          IS the precompile's result. This is what
          tests/it/tel_precompile_props.rs:254-256 and :330-336 exercise via
          [env.exec_default(..)] plus [assert_not_success]. *)
  | Relay_swallow
      (** the [RELAY_BYTECODE] shape of tests/it/tel_precompile_props.rs:364-370:
          [DELEGATECALL; POP]. The success flag is discarded, so the outer
          transaction succeeds whatever the precompile returned. *)
  | Relay_checked
      (** a relay that reverts unless the [DELEGATECALL] success flag is 1 - what
          Solidity's high-level call syntax compiles to. Surfaces the
          precompile's error as a failed transaction. *)
  | Relay_decodes
      (** a relay that ignores the success flag but [abi.decode]s the
          returndata, so it reverts exactly when the returndata is EMPTY. This
          is the caller-side repair path for the fail-open regression: it
          rejects an empty [Ok] as well as an [Err]. *)

(** Total order index for {!caller_shape}. *)
let caller_shape_index = function
  | Eoa_direct -> 0
  | Relay_swallow -> 1
  | Relay_checked -> 2
  | Relay_decodes -> 3

(** Total order on {!caller_shape}. *)
let caller_shape_compare a b =
  Int.compare (caller_shape_index a) (caller_shape_index b)

(** The call vector in hand, or none chosen yet. *)
type call =
  | No_call  (** the initial state, before any transaction is chosen. *)
  | Call of calldata * caller_shape
      (** calldata paired with the caller shape it arrives through. *)

(** Total order on {!call}: every cross-constructor arm spelled. *)
let call_compare a b =
  match (a, b) with
  | No_call, No_call -> 0
  | No_call, Call _ -> -1
  | Call _, No_call -> 1
  | Call (d1, s1), Call (d2, s2) ->
      let c = calldata_compare d1 d2 in
      if Bool.not (Int.equal c 0) then c else caller_shape_compare s1 s2

(** How [telcoin_precompile] itself ended (tel_precompile/mod.rs:120-164). *)
type verdict =
  | Undispatched  (** the dispatcher has not run yet. *)
  | Errored
      (** returned [Err(PrecompileError::Other _)] - either the short-calldata
          guard (mod.rs:122) or the unknown-selector arm (mod.rs:163). Precompile
          errors carry no returndata. *)
  | Returned_empty
      (** returned [Ok] with EMPTY returndata:
          [Ok(PrecompileOutput::new(GAS_COST, Bytes::new()))], the burn arm's
          success value at burnable.rs:376. *)
  | Returned_value
      (** returned [Ok] with a 32-byte body:
          [Ok(PrecompileOutput::new(GAS_COST, Bytes::from(supply.abi_encode())))],
          the totalSupply arm at burnable.rs:95. *)
  | Panicked
      (** the slice [input.data[0..4]] at mod.rs:125 panicked. Reachable only
          under {!No_short_calldata_guard}; nothing in the execution path catches
          it (the only [catch_unwind] in the repo is the ExEx task wrapper,
          node/src/manager/exex.rs:19). *)

(** Total order index for {!verdict}. *)
let verdict_index = function
  | Undispatched -> 0
  | Errored -> 1
  | Returned_empty -> 2
  | Returned_value -> 3
  | Panicked -> 4

(** Total order on {!verdict}. *)
let verdict_compare a b = Int.compare (verdict_index a) (verdict_index b)

(** Where the single modelled transaction has got to. *)
type phase =
  | Choose  (** the call vector has not been chosen yet. *)
  | Dispatched  (** [telcoin_precompile] has run; its writes are in the state. *)
  | Settled
      (** the transaction's status is fixed, a reverting transaction has rolled
          its writes back, and the block carrying it is produced. *)

(** Total order index for {!phase}. *)
let phase_index = function Choose -> 0 | Dispatched -> 1 | Settled -> 2

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The joint global state: one call vector through the dispatch surface, the
    dispatcher's own verdict, where the supply write landed, and whether the
    block carrying the transaction was produced. *)
type state = {
  phase : phase;
  call : call;
  verdict : verdict;
  burned_pinned : bool;
      (** the burn's supply decrement currently sits under
          [TELCOIN_PRECOMPILE_ADDRESS] (burnable.rs:342-351). *)
  burned_shard : bool;
      (** the burn's supply decrement currently sits under the CALLING frame's
          own storage instead - a private per-relay shard. Reachable only under
          {!Frame_scoped_storage}. *)
  produced : bool;
      (** the block carrying the transaction was produced. Execution of a failing
          transaction does not stop block production
          (tests/it/pipeline_tel_precompile_props.rs:113-114 executes the block
          with [.expect("execute unauthorized mint block")] and only then asserts
          [!env.tx_succeeded(&block, 0)]); an executor panic does. *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = call_compare s1.call s2.call in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = verdict_compare s1.verdict s2.verdict in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare s1.burned_pinned s2.burned_pinned in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.burned_shard s2.burned_shard in
          if Bool.not (Int.equal c4 0) then c4
          else Bool.compare s1.produced s2.produced

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** What the dispatcher has read out of [PrecompileInput]: the calldata, and
    nothing that distinguishes the frame the call arrived through. *)
type dispatch_input =
  | No_input  (** the dispatcher has not been entered. *)
  | Input of calldata  (** [input.data], classified by the gate at mod.rs:121. *)

(** Total order on {!dispatch_input}: every cross-constructor arm spelled. *)
let dispatch_input_compare a b =
  match (a, b) with
  | No_input, No_input -> 0
  | No_input, Input _ -> -1
  | Input _, No_input -> 1
  | Input d1, Input d2 -> calldata_compare d1 d2

(** A validator's local view.

    - {!View_dispatcher} is V1, the TEL dispatcher frame: the calldata and its
      own verdict, and nothing else. It does NOT see the caller shape (no field
      of the input it reads distinguishes [DELEGATECALL] from [CALL],
      mod.rs:120-164), where the storage write landed, or whether the block was
      produced.
    - {!View_supply_reader} is V2, an on-chain reader of [totalSupply()] at
      [0x7e1] (burnable.rs:83-96): the pinned slot's movement and the fact that
      it runs in a produced block. It does NOT see the calldata, the caller
      shape, the dispatcher's verdict, the transaction's status, or storage under
      any other address - and the EVM gives it no way to read logs.
    - {!View_event_stream} is V3, a consumer of the precompile's own events: it
      sees that a burn settled (the [Burn]/[Transfer] pair, burnable.rs:353-374)
      but not through what frame, because the payloads carry no frame identity.
    - {!View_idle} is the constant blank view of the non-agent V0. *)
type view =
  | View_dispatcher of dispatch_input * verdict
  | View_supply_reader of bool * bool
  | View_event_stream of bool * bool
  | View_idle

(** Total order on views: every constructor pairing spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_dispatcher _ | View_supply_reader _ | View_event_stream _)
    ->
      -1
  | (View_dispatcher _ | View_supply_reader _ | View_event_stream _), View_idle
    ->
      1
  | View_dispatcher (i1, v1), View_dispatcher (i2, v2) ->
      let c = dispatch_input_compare i1 i2 in
      if Bool.not (Int.equal c 0) then c else verdict_compare v1 v2
  | View_dispatcher _, (View_supply_reader _ | View_event_stream _) -> -1
  | (View_supply_reader _ | View_event_stream _), View_dispatcher _ -> 1
  | View_supply_reader (m1, p1), View_supply_reader (m2, p2) ->
      let c = Bool.compare m1 m2 in
      if Bool.not (Int.equal c 0) then c else Bool.compare p1 p2
  | View_supply_reader _, View_event_stream _ -> -1
  | View_event_stream _, View_supply_reader _ -> 1
  | View_event_stream (e1, p1), View_event_stream (e2, p2) ->
      let c = Bool.compare e1 e2 in
      if Bool.not (Int.equal c 0) then c else Bool.compare p1 p2

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at git HEAD [0c59c15b]. *)
  | No_short_calldata_guard
      (** delete [if input.data.len() < 4 { return Err(..) }],
          crates/tn-reth/src/evm/tel_precompile/mod.rs:121-123. A 1-3 byte
          payload then reaches the slice [input.data[0..4]] at :125 and panics
          the executor, so the transition [Dispatched -> Settled] is REMOVED for
          every {!Short} vector and replaced by a terminal panicked state with
          [produced = false].

          No sibling path repairs it. (a) The [try_into().unwrap()] at :125 is
          downstream of the slice on the same line, so it cannot save it - the
          slice panics first. (b) The per-handler argument-length checks
          (burnable.rs:167-169, :233-235, :330-332) are all reached only AFTER
          the selector has been extracted. (c) The BLS dispatcher's total
          [split_first_chunk::<4>()] (bls_precompile/mod.rs:102-105) is a
          different function on a different address and repairs nothing here.
          (d) The [0xfe] code byte at the precompile account
          ([PRECOMPILE_GENESIS_BYTECODE], tn-reth/src/system_calls.rs:17-19) is a
          backstop for calls that BYPASS dispatch, not for short ones that reach
          it. (e) There is no panic boundary: the only [catch_unwind] in the tree
          is the ExEx task wrapper (node/src/manager/exex.rs:19), not the
          precompile path. *)
  | Open_selector_fallthrough
      (** replace the fail-closed catch-all
          [_ => Err(PrecompileError::Other("Unknown function selector".into()))]
          at crates/tn-reth/src/evm/tel_precompile/mod.rs:163 with a silent
          success [Ok(PrecompileOutput::new(0, Bytes::new()))]. This ADDS
          transitions in which an unimplemented selector settles as a SUCCESSFUL
          transaction.

          No sibling path repairs it. (a) The only other calldata gate in the
          dispatcher is the length check at mod.rs:121-123, which passes any
          payload of 4 bytes or more regardless of selector. (b) The per-handler
          argument-length checks (burnable.rs:167-169, :233-235, :330-332) are
          reached only from an implemented arm. (c) There is no fallback handler
          and no proxy: [add_telcoin_precompile] installs exactly one closure
          (mod.rs:109-115). (d) The caller-side [abi.decode] revert IS a partial
          repair, and it is modelled here as {!Relay_decodes} rather than elided -
          which is why S1's transaction-level conjunct quantifies over the shapes
          that repair does not cover. *)
  | Frame_scoped_storage
      (** delete the explicit [TELCOIN_PRECOMPILE_ADDRESS] argument from the
          precompile's state accesses - representatively the burn supply write at
          crates/tn-reth/src/evm/tel_precompile/burnable.rs:342-351, and
          identically at :91-92, :181-183, :187-189, :241-244, :252-255,
          :267-272, :275-287 - in favour of the executing frame's address. A
          [DELEGATECALL] relay then moves its OWN storage: the transition that
          decremented the pinned supply is replaced by one that decrements a
          private per-relay shard.

          No sibling path repairs it, and that is the point: the mutation is not
          self-detecting. (a) Reads and writes move together, so every relay sees
          a coherent private shard and nothing errors. (b)
          [handle_total_supply] (burnable.rs:83-96) reads through the same
          address, so an [eth_call] to [totalSupply()] keeps returning the pinned
          slot while the shards drift - it HIDES the divergence. (c) There is no
          cross-check of the supply against the sum of balances anywhere:
          [TOTAL_SUPPLY_SLOT] occurs nowhere outside the precompile module
          itself (defined at mod.rs:106; read or written only at burnable.rs:92,
          :276, :282, :343, :350 and faucet.rs:31, :91, :97). (d) The
          access-control gates are caller-based ([has_governance_role],
          burnable.rs:136-138) and are unaffected by the storage target, so they
          do not notice either. The ONE channel that does survive is the event
          stream, whose address is a literal (burnable.rs:356, :365) - that
          channel is modelled as the agent V3, and S3 names V2 precisely because
          of it. *)

(** The dispatcher's own result for a calldata shape under a mutation
    (tel_precompile/mod.rs:120-164). *)
let verdict_of mut d =
  match d with
  | Short -> (
      match mut with
      | Pristine | Open_selector_fallthrough | Frame_scoped_storage -> Errored
      | No_short_calldata_guard -> Panicked)
  | Sel_burn -> Returned_empty
  | Sel_total -> Returned_value
  | Sel_unknown -> (
      match mut with
      | Pristine | No_short_calldata_guard | Frame_scoped_storage -> Errored
      | Open_selector_fallthrough -> Returned_empty)

(** Where the supply write lands: [(pinned, shard)]. Only the burn arm writes;
    only {!Frame_scoped_storage} can move the target off the constant, and only
    for a call that arrived through a [DELEGATECALL] relay (a direct call to the
    precompile executes in the precompile's own frame, so the two targets
    coincide there). *)
let write_of mut d sh =
  match d with
  | Short | Sel_total | Sel_unknown -> (false, false)
  | Sel_burn -> (
      match mut with
      | Pristine | No_short_calldata_guard | Open_selector_fallthrough ->
          (true, false)
      | Frame_scoped_storage -> (
          match sh with
          | Eoa_direct -> (true, false)
          | Relay_swallow | Relay_checked | Relay_decodes -> (false, true)))

(** Does the outer transaction revert, given the caller shape and the
    precompile's verdict? This is the caller-side repair surface, modelled
    rather than elided. *)
let caller_reverts sh v =
  match sh with
  | Eoa_direct | Relay_checked -> (
      match v with
      | Errored -> true
      | Undispatched | Returned_empty | Returned_value | Panicked -> false)
  | Relay_swallow -> false
  | Relay_decodes -> (
      match v with
      | Errored | Returned_empty -> true
      | Undispatched | Returned_value | Panicked -> false)

(** Will (or did) this state's transaction revert? *)
let tx_reverted_at s =
  match s.call with
  | No_call -> false
  | Call (_, sh) -> caller_reverts sh s.verdict

(** Every calldata shape the surface can be handed. *)
let all_calldata = [ Short; Sel_burn; Sel_total; Sel_unknown ]

(** Every caller shape the surface can be reached through. *)
let all_caller_shapes = [ Eoa_direct; Relay_swallow; Relay_checked; Relay_decodes ]

(** The sixteen attacker-chosen call vectors. *)
let all_call_vectors =
  List.concat_map
    (fun d -> List.map (fun sh -> (d, sh)) all_caller_shapes)
    all_calldata

(** The state after [telcoin_precompile] has run on one call vector. *)
let dispatched_of mut d sh =
  let v = verdict_of mut d in
  let pinned, shard = write_of mut d sh in
  {
    phase = Dispatched;
    call = Call (d, sh);
    verdict = v;
    burned_pinned = pinned;
    burned_shard = shard;
    produced = false;
  }

(** The state after the transaction's status is fixed and the block is produced.
    A reverting transaction rolls the precompile's storage writes back - the
    second modelled repair path. *)
let settled_of s =
  let reverted = tx_reverted_at s in
  {
    phase = Settled;
    call = s.call;
    verdict = s.verdict;
    burned_pinned = Bool.not reverted && s.burned_pinned;
    burned_shard = Bool.not reverted && s.burned_shard;
    produced = true;
  }

(** The transition relation: choose a call vector, dispatch it, settle it. A
    panicked dispatch has NO successor - the executor died, so the block is never
    produced and the terminal state stutters forever. *)
let next_with mut s =
  match s.phase with
  | Choose ->
      List.map (fun (d, sh) -> dispatched_of mut d sh) all_call_vectors
  | Dispatched -> (
      match s.verdict with
      | Panicked -> []
      | Undispatched | Errored | Returned_empty | Returned_value ->
          [ settled_of s ])
  | Settled -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: no call chosen, nothing dispatched, no block yet. *)
let initial =
  {
    phase = Choose;
    call = No_call;
    verdict = Undispatched;
    burned_pinned = false;
    burned_shard = false;
    produced = false;
  }

(** Is the call in hand carrying this calldata shape? False before a call is
    chosen. *)
let is_calldata d s =
  match s.call with
  | No_call -> false
  | Call (d', _) -> Int.equal 0 (calldata_compare d d')

(** Did the call in hand arrive through this caller shape? False before a call is
    chosen. *)
let is_shape sh s =
  match s.call with
  | No_call -> false
  | Call (_, sh') -> Int.equal 0 (caller_shape_compare sh sh')

(** Has the dispatcher been entered? *)
let dispatch_entered s =
  match s.phase with Choose -> false | Dispatched | Settled -> true

(** Has the transaction settled? *)
let has_settled s =
  match s.phase with Choose | Dispatched -> false | Settled -> true

(** A burn that reached the state and stuck: the burn arm returned its empty
    success (burnable.rs:376) and the transaction did not revert. This is exactly
    what the precompile's [Burn]/[Transfer] events record
    (burnable.rs:353-374) - a reverted transaction emits none - so it is also the
    whole content of V3's channel. *)
let burn_settled s =
  has_settled s && is_calldata Sel_burn s
  && (match s.verdict with
     | Returned_empty -> true
     | Undispatched | Errored | Returned_value | Panicked -> false)
  && Bool.not (tx_reverted_at s)

(** What the dispatcher read, as V1 sees it: [input.data] only. The caller shape
    is dropped on the floor here, and that is the whole modelling claim about
    V1 - nothing [telcoin_precompile] reads distinguishes the frame it was
    reached from (mod.rs:120-164). *)
let dispatch_input_of s =
  match s.call with No_call -> No_input | Call (d, _) -> Input d

(** View projection. V1 (dispatcher frame), V2 (on-chain supply reader) and V3
    (event-stream consumer) are the knowledge agents; V0 is an idle non-agent
    with the constant blank view and never appears under [K]. *)
let view v s =
  match v with
  | Validator.V1 -> View_dispatcher (dispatch_input_of s, s.verdict)
  | Validator.V2 -> View_supply_reader (s.burned_pinned, s.produced)
  | Validator.V3 -> View_event_stream (burn_settled s, s.produced)
  | Validator.V0 | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7
  | Validator.V8 | Validator.V9 ->
      View_idle

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Unknown_selector_call
      (** the dispatcher has in hand a >= 4 byte payload whose selector is in
          none of the implemented arms (mod.rs:128-163). *)
  | Short_calldata_call
      (** the dispatcher has in hand a 1-3 byte payload (mod.rs:121-123). *)
  | Burn_call
      (** the dispatcher has in hand [burnCall::SELECTOR] (mod.rs:137-139). *)
  | Dispatch_errored
      (** [telcoin_precompile] returned [Err(PrecompileError::Other _)]. *)
  | Dispatch_panicked
      (** the selector slice at mod.rs:125 panicked and took the executor with
          it. *)
  | Block_produced  (** the block carrying the transaction was produced. *)
  | Tx_failed  (** the transaction settled with a failed status. *)
  | Settled_phase  (** the transaction has settled. *)
  | Via_eoa_direct
      (** the call arrived as a direct [CALL] from an EOA, not through a relay. *)
  | Via_relay_swallow
      (** the call arrived through the [DELEGATECALL; POP] relay shape
          (tests/it/tel_precompile_props.rs:364-370), which discards the success
          flag. *)
  | Supply_write_pinned
      (** a supply decrement currently sits under [TELCOIN_PRECOMPILE_ADDRESS]. *)
  | Supply_write_shard
      (** a supply decrement currently sits under the calling frame's own
          storage: a private per-relay shard. *)
  | Burn_took_effect
      (** a burn settled and stuck: the state moved and the transaction did not
          revert. *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Unknown_selector_call -> dispatch_entered s && is_calldata Sel_unknown s
  | Short_calldata_call -> dispatch_entered s && is_calldata Short s
  | Burn_call -> dispatch_entered s && is_calldata Sel_burn s
  | Dispatch_errored -> (
      match s.verdict with
      | Errored -> true
      | Undispatched | Returned_empty | Returned_value | Panicked -> false)
  | Dispatch_panicked -> (
      match s.verdict with
      | Panicked -> true
      | Undispatched | Errored | Returned_empty | Returned_value -> false)
  | Block_produced -> s.produced
  | Tx_failed -> has_settled s && tx_reverted_at s
  | Settled_phase -> has_settled s
  | Via_eoa_direct -> is_shape Eoa_direct s
  | Via_relay_swallow -> is_shape Relay_swallow s
  | Supply_write_pinned -> s.burned_pinned
  | Supply_write_shard -> s.burned_shard
  | Burn_took_effect -> burn_settled s

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Unknown_selector_call -> "unknown_selector_call"
  | Short_calldata_call -> "short_calldata_call"
  | Burn_call -> "burn_call"
  | Dispatch_errored -> "dispatch_errored"
  | Dispatch_panicked -> "dispatch_panicked"
  | Block_produced -> "block_produced"
  | Tx_failed -> "tx_failed"
  | Settled_phase -> "settled"
  | Via_eoa_direct -> "via_eoa_direct"
  | Via_relay_swallow -> "via_relay_swallow"
  | Supply_write_pinned -> "supply_write_pinned"
  | Supply_write_shard -> "supply_write_shard"
  | Burn_took_effect -> "burn_took_effect"

(** The CTLK checker over this family's ordered state and view: the presheaf-topos
    denotation, pinned to agree with {!System} by
    test/t_tel_dispatch_surface_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation. One initial state: the attacker's choice
    of call vector is a transition out of it, not a family of initial states. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
