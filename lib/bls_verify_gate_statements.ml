(** The BLS_VERIFY_GATE statement family, encoded over the
    {!Bls_verify_gate_model} interpreted system. Three properties of the single
    native BLS verify entry point at 0x..b151
    (crates/tn-reth/src/evm/bls_precompile/mod.rs:93-153) and the one verifier it
    calls (crates/types/src/crypto/bls_signature.rs:190-196). File citations
    refer to Telcoin-Association/telcoin-network at git HEAD 0c59c15b.

    {1 Reading guide for the K operands}

    Two knowledge agents, each with a real non-constant view; V0 and V3..V9 are
    idle and never appear under K.

    - [K (Validator.V1, Signer_held_key)] (S3). V1 is the executing node. Its
      view is the calldata's observable byte class plus the frame's exit and
      returned boolean - never the custody of the secret key, which is a fact
      about an off-chain party. The operand is NOT a projection of that view:
      at a [Wrong_message], [Junk_length], [Undecodable_points] or
      [Pop_uncompressed] settle, a key holder and a non-holder produce
      byte-shape-identical and verdict-identical frames, so those view classes
      contain states of BOTH custodies and V1 is ignorant there. Nor is the
      operand rigid: [Signer_held_key] is false at every [No_key] state. V1's
      only channel to custody is a TRUE verdict, and that channel exists solely
      because the trailing [true] pk-validation flag at bls_signature.rs:195
      makes a true verdict imply possession. Delete that flag and the channel
      goes with it - which is exactly the S3 pin.
    - [Not (K (Validator.V1, Key_is_exclusive))] and its dual (S3). Exclusivity
      is projected into no view at all and no on-chain artifact could settle it:
      a proof of possession is a snapshot of one signing moment. The ignorance
      witness is the [Exclusive]/[Copied] sibling pair behind every settled
      frame, which is also the R2 non-singleton evidence for the positive K
      above: the operative view class has exactly two members.
    - [Not (K (Validator.V2, Verdict_is_true))] and its dual (S1). V2 is the
      receipt observer: the precompile emits no logs and its returndata is
      internal to the frame (mod.rs:129 hands bytes to the caller, not to a
      receipt), so a node reading gas accounting sees the CHARGE and nothing
      else. Because every admitted call pays the same flat 150k, the charge
      carries no verdict information - which is the fairness content stated
      epistemically rather than as an assertion about a constant.

    {1 Scope}

    Every statement is scoped to the 0x..b151 boundary - what an EVM caller sees
    from a [STATICCALL], the exact surface
    crates/tn-reth/tests/it/bls_precompile_props.rs:273-321 drives through a real
    EVM. See the {!Bls_verify_gate_model} header for why that scoping is forced:
    the ConsensusRegistry Solidity in the checked-out tn-contracts submodule
    still verifies through its own EIP-2537 pure-Solidity path
    (tn-contracts/src/consensus/ConsensusRegistry.sol:612-631) and does not
    staticcall this precompile, so it is neither a consumer nor a repair. *)

open Bls_verify_gate_model

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

(** S1 - every-verification-failure-mode-costs-the-same-and-returns-a-value
    [fairness]. Once a call clears the gas floor and ABI-decodes, there is one
    exit: the flat 150k charge and an ABI-encoded boolean.

    (A) Value exit: AG( admitted(call) -> AX exit=Ok(bool) ). The single success
    return is
    [Ok(PrecompileOutput::new(BLS_VERIFY_GAS_COST, Bytes::from(verified
    .abi_encode())))] (mod.rs:127-129); both branches of [verified] funnel
    through it because [bls_verify] is a TOTAL function - every decode failure
    is turned into a value at mod.rs:142-150, and mod.rs:132-133 states the
    intent verbatim ("Any decode or verification failure maps to `false` so bad
    input can never panic or revert the precompile"). Asserted in-repo at
    mod.rs:314-323 and through a real EVM at props :148-188.

    (B) Cost uniformity: AG( admitted(call) -> AX gas_used=150000 ). The charge
    is the constant [BLS_VERIFY_GAS_COST] (mod.rs:77) applied at mod.rs:129
    regardless of the boolean, asserted for the true case at mod.rs:303-310 and
    the false case at mod.rs:314-323 ("gas is still charged for the work
    performed"). A cryptographically valid proof, a proof against the wrong
    message, undecodable 48/96 garbage and a wrong-length point all cost
    exactly the same.

    (C) No cost side channel: AG( (settled(call) /\\ gas_used=150000) ->
    ~K_V2(blsVerify=true) /\\ ~K_V2(~blsVerify=true) ). Given (B), the receipt
    observer's flat-charge class contains both accepted and rejected frames, so
    price cannot be used to discover a verdict. Ignorance witness: a genuine
    compressed proof and a wrong-message call settle to the same charge and
    differ on the boolean.

    Scope, stated rather than assumed: (A) and (B) are guarded by
    [admitted(call)] because the pre-crypto rejects are genuinely NOT uniform -
    a short selector (mod.rs:103-105), gas under the 150k floor (mod.rs:115-117)
    and an ABI-decode failure (mod.rs:119-120) all return [Err] and burn the
    frame's forwarded gas, which the model carries as {!Pre_crypto_reject} and
    props :255-266 exercises. Removing that guard would make the statement
    false, so it is not an omission.

    Mutation pin: {!Bls_verify_gate_model.Err_on_failed_verify} deletes the two
    [else { return false; }] decode fallbacks at mod.rs:145-150 and lets the
    decoder error escape as [PrecompileError::Other]. The
    {!Undecodable_points} class then settles [Exit_err] / [Charge_forwarded]
    while {!Wrong_message} still pays the flat 150k, refuting (A) and (B) at
    once: cost and exit become dependent on which failure mode was hit. No
    sibling repairs it - [dispatch] (mod.rs:102-111) returns the handler's
    result untouched and a reverted [STATICCALL] propagates. (C) survives the
    mutation, so the refutation is attributable to the exit/cost conjuncts. *)
let s1 =
  let value_exit =
    Formula.Ag
      (Formula.Implies (atom Call_admitted, Formula.Ax (atom Exit_is_value)))
  in
  let flat_cost =
    Formula.Ag
      (Formula.Implies (atom Call_admitted, Formula.Ax (atom Charge_is_flat)))
  in
  let no_price_channel =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Settled_call, atom Charge_is_flat),
           Formula.And
             ( Formula.Not (Formula.K (Validator.V2, atom Verdict_is_true)),
               Formula.Not
                 (Formula.K
                    (Validator.V2, Formula.Not (atom Verdict_is_true))) ) ))
  in
  {
    name = "every-verification-failure-mode-costs-the-same-and-returns-a-value";
    bucket = Statements.Fairness;
    formula = Formula.And (value_exit, Formula.And (flat_cost, no_price_channel));
    antecedent = atom Call_admitted;
  }

(** S2 - compressed-encoding-is-the-only-accepted-point-form [safety]. The
    precompile accepts exactly one serialization per curve point.

    (A) Canonicity: AG( blsVerify=true -> bytes=compressed(48,96) ). The gate is
    mod.rs:142-144, verbatim
    [if compressed_sig.len() != 48 || compressed_pubkey.len() != 96 { return
    false; }]; its own doc comment at mod.rs:135-140 states why it is
    load-bearing - blst's [deserialize] accepts EITHER encoding by length, so
    without this gate a 96-byte uncompressed signature or 192-byte uncompressed
    pubkey would still decode.

    (B) Non-malleability: AG( bytes=uncompressed(96,192) -> ~blsVerify=true ).
    Feeding the precompile the valid UNCOMPRESSED encodings of the very same
    signature and key yields [false], so two distinct calldata byte-strings can
    never denote one accepted point. The load-bearing negative test is
    mod.rs:216-243, which asserts the compressed control verifies and the
    *valid* uncompressed pair does not; the same case runs through the real EVM
    at props :195-228.

    (C) No over-rejection: AG( genuine_pop(compressed) -> AX blsVerify=true ).
    The gate is a length test and nothing more - it never rejects a real proof
    in the canonical form (mod.rs:206-214, props :89-97). Without (C) the
    statement would be satisfied by a verifier that rejects everything.

    The claim is deliberately about the ACCEPTED-INPUT SET, not about a concrete
    registry exploit: the aliasing consequence is that a caller keying anything
    off the submitted bytes cannot be shown two aliases of one identity, and
    de-duplication on bytes is what this gate makes sound.

    Mutation pin: {!Bls_verify_gate_model.No_length_gate} deletes mod.rs:142-144.
    The {!Pop_uncompressed} class - the 96/192 uncompressed serialization of the
    SAME point pair - then decodes and verifies, adding a [Verdict_true] settle
    that refutes (A) and (B) together: one point pair acquires two accepted
    encodings. The two decoder-level repairs that do exist are modeled and
    survive the mutation, so the flip is not an artifact of an omitted path:
    {!Junk_length} (a non-serialization length) and {!Undecodable_points} (the
    flag-clear 96-byte pubkey named at mod.rs:138-140) stay [Verdict_false]
    because [BlsPublicKey::from_literal_bytes] (bls_public_key.rs:99-101) and
    [BlsSignature::from_bytes] (bls_signature.rs:25-29) dispatch on length
    themselves. What no decoder rejects is the valid 96/192 form. (C) survives
    the mutation. *)
let s2 =
  let canonicity =
    Formula.Ag
      (Formula.Implies (atom Verdict_is_true, atom Input_is_compressed_pair))
  in
  let non_malleability =
    Formula.Ag
      (Formula.Implies
         (atom Input_is_uncompressed_pair, Formula.Not (atom Verdict_is_true)))
  in
  let no_over_rejection =
    Formula.Ag
      (Formula.Implies
         (atom Genuine_compressed_pop, Formula.Ax (atom Verdict_is_true)))
  in
  {
    name = "compressed-encoding-is-the-only-accepted-point-form";
    bucket = Statements.Safety;
    formula =
      Formula.And (canonicity, Formula.And (non_malleability, no_over_rejection));
    antecedent = Formula.And (atom Settled_call, atom Verdict_is_true);
  }

(** S3 - accepted-pop-implies-known-key-possession-yet-exclusivity-unknown
    [security]. A true verdict is a knowledge channel about the outside world,
    and it is a snapshot.

    (A) Known possession: AG( (settled(call) /\\ blsVerify=true) ->
    K_V1(held_sk(signer)) ). When the precompile returns [true], the executing
    node knows a fact it never observes directly: somebody held the secret key
    matching the compressed G2 pubkey and signed the message binding that key to
    an execution address. The knowledge is real because mod.rs:141-153 runs the
    SAME blst path the consensus layer uses to PRODUCE signatures - the final
    call is [bls_verify_secure(&sig, &pubkey, message)] (mod.rs:152), defined at
    bls_signature.rs:190-196 as
    [signature.verify(true, message, DST_G1, &[], public_key, true)] with the
    leading [true] the signature subgroup check and the trailing [true] the
    public-key validation, so neither a small-subgroup signature nor an
    unvalidated / infinity pubkey can produce a true verdict. The message that
    binds key to address is built at bls_signature.rs:206-214 as
    [intentPrefix(3) || compressedPubkey(96) || address(20)] = 119 bytes, and the
    address-binding half is exercised end to end at props :99-114 (a proof bound
    to one address never verifies against another's message).

    The operand is deliberately about the PRODUCER of the signature, not about
    the transaction sender, and the statement would be FALSE the other way
    round: the precompile entrypoint forwards only [input.data] and [input.gas]
    (mod.rs:93-95), so the verdict is caller-blind and a relayer or a replayer
    of somebody else's genuine proof produces the same [true]. Nothing at this
    boundary distinguishes them, so nothing at this boundary may be claimed
    about them - the address binding at bls_signature.rs:206-214 ties the key to
    an execution address, not to whoever pays for the transaction.

    (B) Unknown exclusivity: AG( (settled(call) /\\ blsVerify=true) ->
    ~K_V1(exclusive(sk)) /\\ ~K_V1(~exclusive(sk)) ). This is the honest limit. A
    proof of possession is a snapshot of one signing moment; nothing in the
    calldata, the verdict or the gas distinguishes a world where the key is
    still exclusively held from one where it was copied, so V1 can neither
    confirm nor rule out exclusivity. The witness pair is the
    [Exclusive]/[Copied] sibling behind every settled frame, which is also the
    R2 evidence that (A)'s view class is not a singleton: it has exactly two
    members.

    Mutation pin: {!Bls_verify_gate_model.No_pk_validation} flips the trailing
    [true] at bls_signature.rs:195 to [false]. An unvalidated / small-subgroup /
    infinity G2 key with a fabricated matching signature then verifies, adding a
    [Verdict_true] settle whose custody is [No_key]. That state shares V1's view
    with the genuine one - same observable byte class, same [Ok] exit, same
    [true] boolean - so V1's verdict-true class now contains a state where
    [held_sk(signer)] is FALSE and (A) is refuted: the verdict stops being a
    possession channel. No sibling repairs it: [bls_verify_secure] has exactly
    two callers, and the one that validates the key first
    ([verify_proof_of_possession_bls], bls_signature.rs:171-183, the
    [public_key.validate()] at :176) is the consensus-layer path, while the
    precompile at mod.rs:141-153 never calls [validate()]; its own decoders are
    bare [from_bytes] calls (bls_public_key.rs:99-101, bls_signature.rs:25-29)
    and mod.rs:140 says the subgroup and infinity checks live at verify time. (B)
    survives, so the refutation is attributable to (A). *)
let s3 =
  let accepted = Formula.And (atom Settled_call, atom Verdict_is_true) in
  let known_possession =
    Formula.Ag
      (Formula.Implies
         (accepted, Formula.K (Validator.V1, atom Signer_held_key)))
  in
  let unknown_exclusivity =
    Formula.Ag
      (Formula.Implies
         ( accepted,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom Key_is_exclusive)),
               Formula.Not
                 (Formula.K
                    (Validator.V1, Formula.Not (atom Key_is_exclusive))) ) ))
  in
  {
    name = "accepted-pop-implies-known-key-possession-yet-exclusivity-unknown";
    bucket = Statements.Security;
    formula = Formula.And (known_possession, unknown_exclusivity);
    antecedent = accepted;
  }

(** The family's statements: the fairness, safety and security properties of the
    one native BLS verify entry point. *)
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
