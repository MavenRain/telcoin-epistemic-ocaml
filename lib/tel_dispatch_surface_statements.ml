(** The TEL_DISPATCH_SURFACE statement family, encoded over the
    {!Tel_dispatch_surface_model} interpreted system. All three statements were
    mined from telcoin-network and re-grounded line by line against this
    checkout (git HEAD [0c59c15b], working tree). File citations refer to
    Telcoin-Association/telcoin-network and are relative to [crates/].

    What the family is about: [0x7e1] is a token-shaped endpoint that any
    contract can call with attacker-chosen calldata, through a
    [DELEGATECALL] relay if it likes. One call object - the calldata and the
    caller shape - decides all three outcomes, so the three statements share the
    vector exactly:

    - S1 is the fail-closed catch-all (tn-reth/src/evm/tel_precompile/mod.rs:163):
      an unimplemented selector cannot be made to look like a success.
    - S2 is the short-calldata guard (mod.rs:121-123): a malformed transaction
      fails ITSELF instead of taking the executor down.
    - S3 is the address pinning (burnable.rs:342-351 and its five siblings): the
      state a call moves does not depend on the frame it was reached from, which
      is what makes [totalSupply] one global number.

    {1 Reading guide for the K operands}

    - [~K (V1, ..)] in S1 conjunct D is the DISPATCHER's ignorance. V1's view is
      exactly what [telcoin_precompile] reads - [input.data] and its own result
      (mod.rs:120-164). The caller shape is not in it, and cannot be inferred
      from it, because the identical function body is what a [DELEGATECALL]
      relay reaches (tests/it/tel_precompile_props.rs:389-414). This conjunct is
      the security RATIONALE for S1 conjunct A turned into a theorem: the
      catch-all must fail closed precisely because the dispatcher cannot know
      whether its caller will notice a failure.
    - [~K (V3, ..)] in S2 conjunct D is the EVENT STREAM's ignorance. A rejected
      call emits nothing, so "too short" (mod.rs:122) and "unknown function
      selector" (mod.rs:163) are the same observation through that channel even
      though they are different error strings.
    - [K (V2, burn_call)] in S3 conjunct B is the POSITIVE one, and it is the
      on-chain reader's knowledge: a contract that watches [totalSupply()] at
      [0x7e1] (burnable.rs:83-96) and sees the number move can conclude that a
      burn was dispatched - a fact about ANOTHER party's calldata, which is not
      a component of its view and which is false at plenty of reachable states
      (every [totalSupply] read, every rejected call). It is not rigid and it is
      not a projection: it is carried entirely by the address pinning, one hop
      away from anything V2 can see, which is exactly why
      {!Tel_dispatch_surface_model.Frame_scoped_storage} destroys it.
    - [~K (V2, via_eoa_direct)] in S3 conjunct C is the other side of the same
      coin: because the pinned slot is where the write lands whatever frame
      issued it, the supply number does not leak the call scheme. Under the
      mutation it does, and the ignorance flips to knowledge - which is how a
      SAFETY property is caught by an epistemic conjunct.
    - [~K (V3, via_eoa_direct)] in S3 conjunct D is the modelled non-repair: the
      event stream survives {!Tel_dispatch_surface_model.Frame_scoped_storage}
      intact (the event address is a literal, burnable.rs:356 and :365) but it
      never carried the frame identity in the first place, so it cannot be the
      cross-check that rescues V2. This conjunct is the R4 sibling hunt written
      into the statement instead of only into a comment. *)

open Tel_dispatch_surface_model

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

(** S1 - unimplemented-selectors-fail-closed-at-the-tel-dispatcher [security].
    The TEL precompile implements a CLOSED selector set. Anything else - notably
    the ERC-20 / EIP-2612 surface a token at this address would be expected to
    expose, [transfer]/[approve]/[permit]/[transferFrom]/[allowance]/[nonces],
    enumerated at tests/it/tel_precompile_props.rs:316-328 - falls into one error
    arm and touches nothing.

    (A) the dispatcher rejects it: AG( unknown_selector_call -> dispatch_errored ).
    The final arm is verbatim
    [_ => Err(PrecompileError::Other("Unknown function selector".into()))] at
    tn-reth/src/evm/tel_precompile/mod.rs:163, and the implemented set above it
    is the four mainnet arms at :130-143 plus the [#[cfg(feature = "faucet")]]
    role arms at :145-161. The unit mirror is mod.rs:179-186 and the randomized
    mirror tests/it/tel_precompile_props.rs:259-278.

    (B) and touches nothing: AG( unknown_selector_call -> ~supply_write_pinned /\
    ~supply_write_shard ). No storage access is reached, because every one of
    them lives inside a handler and the handlers are reached only from an
    implemented arm (burnable.rs:91-92, :181-189, :241-272, :275-287, :342-351).

    (C) the caller sees the failure, unless it threw the flag away:
    AG( unknown_selector_call /\ ~via_relay_swallow -> AF tx_failed ). This is
    the conjunct that has to survive the modelled repair paths and does. A direct
    EOA call fails outright ([env.exec_default] plus [assert_not_success],
    tests/it/tel_precompile_props.rs:330-336); a relay that checks the
    [DELEGATECALL] success flag reverts; and a relay that ignores the flag but
    [abi.decode]s the returndata reverts too, because a precompile [Err] carries
    no returndata. Only the [DELEGATECALL; POP] shape
    (tests/it/tel_precompile_props.rs:364-370) swallows it, and that shape is
    excluded from the antecedent by name rather than by omission.

    (D) and the dispatcher could not have known which caller it had:
    AG( unknown_selector_call -> ~K_V1(~via_relay_swallow) ). R3 ignorance
    witness, both members reachable and asserted in the suite: at any
    unknown-selector dispatch, the state with [Eoa_direct] and the state with
    [Relay_swallow] carry the identical [input.data] and the identical result, so
    V1 cannot separate them. This is the reason (A) has to be an [Err] and not an
    empty [Ok]: the dispatcher cannot delegate the decision to the caller,
    because it cannot see the caller.

    Mutation pin: {!Tel_dispatch_surface_model.Open_selector_fallthrough} rewrites
    mod.rs:163 as [Ok(PrecompileOutput::new(0, Bytes::new()))]. (A) fails at
    every unknown-selector state and (C) fails for [Eoa_direct] and
    [Relay_checked], whose transactions now succeed - an unimplemented [approve]
    that "worked". No sibling repairs it: the only other calldata gate is the
    length check at mod.rs:121-123, which passes any payload of 4 bytes or more
    regardless of selector; the per-handler argument checks (burnable.rs:167-169,
    :233-235, :330-332) are reached only from an implemented arm; and
    [add_telcoin_precompile] installs exactly one closure with no fallback
    (mod.rs:109-115). The one genuine partial repair - a caller that
    [abi.decode]s - IS in the model as [Relay_decodes] and does still reject the
    mutated arm; (C) is stated so that it survives that repair and flips anyway.
    NOT pinned to the other two mutations, and the mutation suite asserts S1
    survives both. *)
let s1 =
  let dispatcher_rejects =
    Formula.Ag
      (Formula.Implies (atom Unknown_selector_call, atom Dispatch_errored))
  in
  let touches_nothing =
    Formula.Ag
      (Formula.Implies
         ( atom Unknown_selector_call,
           Formula.And
             ( Formula.Not (atom Supply_write_pinned),
               Formula.Not (atom Supply_write_shard) ) ))
  in
  let caller_sees_the_failure =
    Formula.leads_to
      (Formula.And
         (atom Unknown_selector_call, Formula.Not (atom Via_relay_swallow)))
      (atom Tx_failed)
  in
  let dispatcher_cannot_see_the_caller =
    Formula.Ag
      (Formula.Implies
         ( atom Unknown_selector_call,
           Formula.Not
             (Formula.K
                (Validator.V1, Formula.Not (atom Via_relay_swallow))) ))
  in
  {
    name = "unimplemented-selectors-fail-closed-at-the-tel-dispatcher";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( dispatcher_rejects,
          Formula.And
            ( touches_nothing,
              Formula.And
                (caller_sees_the_failure, dispatcher_cannot_see_the_caller) ) );
    antecedent = atom Unknown_selector_call;
  }

(** S2 -
    short-calldata-guard-is-all-that-stands-between-a-three-byte-call-and-an-executor-panic
    [liveness]. The dispatcher reads its selector by SLICING:
    [let selector: [u8; 4] = input.data[0..4].try_into().unwrap();]
    (tn-reth/src/evm/tel_precompile/mod.rs:125). That slice would panic on a 1-3
    byte payload, so the explicit length check in front of it is the only thing
    keeping a malformed transaction from taking the executor down instead of
    failing its own transaction. The contrast with the sibling precompile is the
    evidence that the guard is load-bearing rather than merely defensive: the BLS
    dispatcher solves the identical problem with a TOTAL pattern match,
    [let Some((selector, calldata)) = data.split_first_chunk::<4>() else { return
    Err(PrecompileError::Other("Invalid input: too short".into())); };]
    (tn-reth/src/evm/bls_precompile/mod.rs:102-105), and needs no guard at all.

    (A) the executor never dies: AG( ~dispatch_panicked ).

    (B) a malformed call still lets the block out:
    AG( short_calldata_call -> AF block_produced ). This is the liveness content
    and it is what the pipeline actually observes: a block containing a failing
    precompile transaction is executed successfully and only THEN is the
    transaction asserted to have failed -
    [let block = env.execute_block(vec![tx]).expect("execute unauthorized mint
    block"); assert!(!env.tx_succeeded(&block, 0), ..)]
    (tests/it/pipeline_tel_precompile_props.rs:113-114). Per-transaction failure
    is normal; per-block failure is not.

    (C) the guard's own effect: AG( short_calldata_call -> dispatch_errored ),
    mod.rs:121-123, exercised at mod.rs:172-177 and
    tests/it/tel_precompile_props.rs:236-257.

    (D) and from outside, a rejection is a rejection:
    AG( short_calldata_call /\ settled -> ~K_V3(short_calldata_call) ). R3
    ignorance witness: a rejected call emits no event, so through the event
    channel a short payload and an unimplemented selector are the same
    observation, even though mod.rs:122 and mod.rs:163 build different error
    strings. The witness pair is any settled short call and the settled
    unknown-selector call with the same caller shape.

    Mutation pin: {!Tel_dispatch_surface_model.No_short_calldata_guard} deletes
    mod.rs:121-123. A transaction carrying 1-3 calldata bytes to [0x7e1] then
    panics inside the slice at :125, and the [Dispatched -> Settled] transition
    disappears: (A) fails outright, (B) fails because the panicked state is
    terminal and [block_produced] never becomes true on that path, and (C) fails
    because the verdict is a panic rather than an error. No sibling repairs it -
    the [try_into().unwrap()] on the same line is DOWNSTREAM of the slice, the
    per-handler length checks (burnable.rs:167-169, :233-235, :330-332) are
    reached only after the selector is extracted, the BLS dispatcher's total
    [split_first_chunk] is a different function on a different address, the
    [0xfe] genesis code byte (tn-reth/src/system_calls.rs:17-19) is a backstop
    for calls that BYPASS dispatch rather than short ones that reach it, and
    there is no panic boundary anywhere on the path (the tree's only
    [catch_unwind] is the ExEx task wrapper, node/src/manager/exex.rs:19). R8:
    the deletion removes a real gate, not a sibling path the code would have
    taken anyway. NOT pinned to the other two mutations, and the mutation suite
    asserts S2 survives both. *)
let s2 =
  let executor_never_dies = Formula.Ag (Formula.Not (atom Dispatch_panicked)) in
  let block_still_produced =
    Formula.leads_to (atom Short_calldata_call) (atom Block_produced)
  in
  let guard_rejects =
    Formula.Ag
      (Formula.Implies (atom Short_calldata_call, atom Dispatch_errored))
  in
  let rejection_is_opaque_outside =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Short_calldata_call, atom Settled_phase),
           Formula.Not (Formula.K (Validator.V3, atom Short_calldata_call)) ))
  in
  {
    name =
      "short-calldata-guard-is-all-that-stands-between-a-three-byte-call-and-an-executor-panic";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        ( executor_never_dies,
          Formula.And
            ( block_still_produced,
              Formula.And (guard_rejects, rejection_is_opaque_outside) ) );
    antecedent = atom Short_calldata_call;
  }

(** S3 - precompile-state-is-address-pinned-under-delegatecall [safety]. Every
    state access in the module names the constant rather than the executing
    frame, so a contract that [DELEGATECALL]s [0x7e1] still moves the
    precompile's own slots: [msg.sender] is preserved (which is why the
    governance check behaves as expected inside the relay frame,
    tests/it/tel_precompile_props.rs:383-385) but the STATE TARGET is not. That
    is what makes [totalSupply] one global number instead of a per-caller shard.

    (A) no private shard exists: AG( ~supply_write_shard ). The burn's supply
    write is [internals.sstore(TELCOIN_PRECOMPILE_ADDRESS, TOTAL_SUPPLY_SLOT,
    new_supply)] (burnable.rs:342-351), and identically at :91-92, :181-183,
    :187-189, :241-244, :252-255, :267-272, :275-287; the balance helpers take
    the address explicitly too ([balance_decr(internals,
    TELCOIN_PRECOMPILE_ADDRESS, amount)], burnable.rs:337, helpers.rs:56-77). The
    dedicated regression test asserts the pending slot holds the amount under
    [TELCOIN_PRECOMPILE_ADDRESS] and is ZERO under the relay
    (tests/it/tel_precompile_props.rs:405-414).

    (B) the pinned slot is a sound global witness:
    AG( burn_took_effect -> K_V2(burn_call) ). This is the epistemic PAYLOAD of
    the pinning. V2 is an on-chain reader of [totalSupply()] (burnable.rs:83-96):
    the supply number and the fact that it runs in a produced block are its
    entire channel - the EVM gives a contract no access to logs. Because every
    frame writes the same slot, "the number moved" entails "a burn was
    dispatched", a fact about another party's calldata that V2 cannot see.

    R2 evidence, all three halves discharged in the suite:
    - the operand is not rigid: [EF ~burn_call] holds (every [totalSupply] read
      and every rejected call);
    - the knowledge is contingent: [EF ~K_V2(burn_call)] holds;
    - the view class at the operative state is NOT a singleton:
      [EF( burn_took_effect /\\ ~via_relay_swallow /\\ ~K_V2(~via_relay_swallow) )]
      holds, which is possible only because a second reachable state shares V2's
      view there. Concretely the class has three members - the same burn reached
      directly, through the swallowing relay, and through the flag-checking
      relay - and they are indistinguishable to V2 exactly because of (A).

    (C) and the supply does not leak the call scheme:
    AG( burn_took_effect -> ~K_V2(via_eoa_direct) ). R3 ignorance witness: the
    three states of that class disagree on [via_eoa_direct]. Stating the safety
    property this way is what makes the mutation's harm visible as an epistemic
    change rather than only as a storage-location change.

    (D) nor does the event stream, which is the channel that SURVIVES the
    mutation: AG( burn_took_effect -> ~K_V3(via_eoa_direct) ). This conjunct is
    the sibling hunt written into the statement. The precompile's events are
    emitted with [address = TELCOIN_PRECOMPILE_ADDRESS] as a literal
    ([Burn(uint256)] at burnable.rs:353-361, [Transfer(precompile, 0, amount)] at
    :363-374), so a {!Tel_dispatch_surface_model.Frame_scoped_storage} relay
    would STILL emit them - the event consumer keeps knowing that a burn
    happened. What it never knew, pristine or mutated, is through what frame:
    the payloads carry no frame identity. So the event channel cannot be the
    cross-check that rescues (B), and (B) is stated about V2 for that reason and
    not because the log path was left out of the model.

    Mutation pin: {!Tel_dispatch_surface_model.Frame_scoped_storage} deletes the
    explicit [TELCOIN_PRECOMPILE_ADDRESS] argument in favour of the executing
    frame's address. (A) fails at every relay burn. (B) fails at the relay burns,
    whose supply movement is now invisible to V2, so its class at those states
    contains [totalSupply] reads that dispatched no burn at all. (C) fails from
    the other direction, at the DIRECT burn: it becomes the only reachable state
    in which the pinned supply moves, so V2's class there collapses to a
    singleton and the ignorance turns into knowledge. That collapse is the
    cleanest statement of the harm: under frame-scoped storage the global supply
    number starts reporting the caller's frame instead of the token's state.
    No sibling repairs it and the mutation is NOT self-detecting: reads and
    writes move together so nothing errors; [handle_total_supply]
    (burnable.rs:83-96) reads through the same address and therefore HIDES the
    drift rather than exposing it; [TOTAL_SUPPLY_SLOT] is never cross-checked
    against the sum of balances anywhere; and the caller-based access control
    ([has_governance_role], burnable.rs:136-138) is indifferent to the storage
    target. The one surviving channel, the event stream, is modelled as V3 and
    conjunct (D) says exactly what it can and cannot settle. NOT pinned to the
    other two mutations, and the mutation suite asserts S3 survives both. *)
let s3 =
  let no_private_shard = Formula.Ag (Formula.Not (atom Supply_write_shard)) in
  let pinned_slot_witnesses_the_burn =
    Formula.Ag
      (Formula.Implies
         (atom Burn_took_effect, Formula.K (Validator.V2, atom Burn_call)))
  in
  let supply_hides_the_call_scheme =
    Formula.Ag
      (Formula.Implies
         ( atom Burn_took_effect,
           Formula.Not (Formula.K (Validator.V2, atom Via_eoa_direct)) ))
  in
  let events_hide_the_call_scheme =
    Formula.Ag
      (Formula.Implies
         ( atom Burn_took_effect,
           Formula.Not (Formula.K (Validator.V3, atom Via_eoa_direct)) ))
  in
  {
    name = "precompile-state-is-address-pinned-under-delegatecall";
    bucket = Statements.Safety;
    formula =
      Formula.And
        ( no_private_shard,
          Formula.And
            ( pinned_slot_witnesses_the_burn,
              Formula.And
                (supply_hides_the_call_scheme, events_hide_the_call_scheme) ) );
    antecedent = atom Burn_took_effect;
  }

(** The family's statements: the fail-closed selector set, the short-calldata
    guard, and the address pinning that makes one slot the whole supply. *)
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
