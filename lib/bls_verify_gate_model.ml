(** Finite interpreted system for the BLS_VERIFY_GATE family: the native
    BLS12-381 proof-of-possession precompile registered at
    [BLS_G1_PRECOMPILE_ADDRESS] (0x..b151) and the one verifier it calls. File
    citations refer to Telcoin-Association/telcoin-network at git HEAD
    0c59c15b (working tree).

    {1 The modeled mechanism}

    One EVM [STATICCALL] to 0x..b151 is the whole object. Its life is three
    layers deep and every layer is a real gate in the Rust:

    - {b pre-crypto rejects.} [dispatch] needs a 4-byte selector
      (crates/tn-reth/src/evm/bls_precompile/mod.rs:103-110);
      [handle_bls_verify] needs [gas_limit >= BLS_VERIFY_GAS_COST]
      (mod.rs:115-117, the constant is 150_000 at mod.rs:77) and needs
      [blsVerifyCall::abi_decode_raw] to succeed (mod.rs:119-120). All three
      exit [Err(PrecompileError::_)], which in revm burns the frame's whole
      forwarded gas. They are collapsed into the single input class
      {!Pre_crypto_reject}, so the model does NOT pretend every call is cheap.
    - {b the length gate.} [bls_verify] requires exactly 48 compressed-G1
      signature bytes and 96 compressed-G2 pubkey bytes, verbatim
      [if compressed_sig.len() != 48 || compressed_pubkey.len() != 96 { return
      false; }] (mod.rs:142-144). Its own doc comment (mod.rs:135-140) states
      why it is load-bearing: blst deserializes by LENGTH, so without the gate
      the 96-byte uncompressed signature and 192-byte uncompressed pubkey of
      the very same point pair would still decode.
    - {b the decoders and the verifier.} [BlsPublicKey::from_literal_bytes]
      (crates/types/src/crypto/bls_public_key.rs:99-101, a bare
      [CorePublicKey::from_bytes(bytes).map(|key| key.into())]) and
      [BlsSignature::from_bytes] (crates/types/src/crypto/bls_signature.rs:25-29)
      are the two [else { return false; }] fallbacks at mod.rs:145-150; the
      verdict itself is [bls_verify_secure(&sig, &pubkey, message)] (mod.rs:152),
      defined verbatim at crates/types/src/crypto/bls_signature.rs:190-196 as
      [signature.verify(true, message, DST_G1, &[], public_key, true)] - leading
      [true] = signature subgroup check, trailing [true] = PUBLIC KEY
      validation.

    Whatever happens inside, [handle_bls_verify] has exactly one success exit,
    [Ok(PrecompileOutput::new(BLS_VERIFY_GAS_COST, Bytes::from(verified
    .abi_encode())))] (mod.rs:127-129): the flat 150k charge and an ABI-encoded
    boolean. That single exit is what the fairness statement is about, and the
    equal-cost pair is asserted directly in-repo at mod.rs:303-310 (valid ->
    true, [gas_used == BLS_VERIFY_GAS_COST]) and mod.rs:314-323 (invalid ->
    false, not a revert, same [gas_used]).

    {1 Components}

    - [input_class]: what an execution node can read off the calldata WITHOUT
      holding anyone's secret - six byte-shape classes, see the type.
    - [custody]: whether the party that produced the submitted signature held
      the BLS secret key matching the submitted pubkey at signing time. HIDDEN:
      projected into no view. Note the wording: this is about the PRODUCER of
      the signature, not about the transaction sender. A relayer or a replayer
      forwarding somebody else's genuine proof is [Key_holder] here, and
      correctly so - the precompile entrypoint forwards only [input.data] and
      [input.gas] (mod.rs:93-95), so the verdict is caller-blind and no claim
      about the sender could be grounded in it.
    - [excl]: whether that secret key is still held exclusively by the
      registrant or has been copied. HIDDEN: projected into no view. A proof of
      possession is a snapshot, so nothing on chain can ever settle it.
    - the call's life: [No_call] -> [Pending] (submitted, not yet executed) ->
      [Settled] (the frame returned; verdict, exit and charge are DERIVED by
      {!settle} from the input class, the custody and the mutation).

    Reachable pristine: 1 + 24 + 24 = 49 states (6 input classes x 2 custody x
    2 exclusivity submissions, each with exactly one settle step).

    {1 Role mapping}

    - {b V1 is the executing node} - the knowledge agent of the security
      statement. Its view is what it has EXECUTED: nothing before the frame
      runs, and afterwards the calldata's observable class together with the
      frame's exit and returned boolean. It does NOT see [custody] and does NOT
      see [excl]; those are facts about an off-chain party. Note the view does
      not determine [custody]: at a [Wrong_message], [Junk_length],
      [Undecodable_points] or [Pop_uncompressed] settle, a key holder and a
      non-holder produce byte-shape-identical, verdict-identical frames, so V1's
      only channel to custody is a TRUE verdict.
    - {b V2 is the receipt observer} - the knowledge agent of the fairness
      statement. The precompile emits no logs and its returndata is internal to
      the frame (mod.rs:129 returns bytes to the caller, not to a receipt), so a
      node that only reads gas accounting sees the CHARGE and nothing else. Its
      view is exactly that.
    - {b V0 and V3..V9 are idle non-agents} with the constant blank view
      {!View_idle}; they never appear under K in any statement.

    {1 Scope, and one card citation corrected}

    Every statement is scoped to the 0x..b151 boundary - what an EVM caller
    observes from a [STATICCALL], which is precisely what
    crates/tn-reth/tests/it/bls_precompile_props.rs:273-321 exercises through a
    real EVM with a relay contract. That scoping is not a convenience: the
    ConsensusRegistry Solidity in the checked-out tn-contracts submodule
    (8d4cb030) is the PRE-CHANGE path and does NOT staticcall this precompile -
    tn-contracts/src/consensus/ConsensusRegistry.sol:612-631 verifies through the
    pure-Solidity [BlsG1.verifyProofOfPossessionG1] over the EIP-2537 precompiles
    on UNCOMPRESSED points, and tn-contracts/artifacts/ConsensusRegistry.json's
    ABI still has [stake(bytes,(bytes,bytes))] with an uncompressed proof tuple.
    The candidate card asserted that the registry "does no curve arithmetic of
    its own"; at this checkout that is FALSE, and the honest consequence is that
    the registry is neither a consumer nor a repair path for the precompile here.
    What remains true, and is all the statements need, is that the precompile is
    registered unconditionally by the EVM factory
    ([add_bls_precompile], mod.rs:83-89, re-exported at
    crates/tn-reth/src/evm/mod.rs:32), so nothing sits between an arbitrary
    caller's calldata and [bls_verify]. *)

(** The observable byte-shape class of one [blsVerify] call: everything an
    execution node can read off the calldata before, or without, holding any
    secret. *)
type input_class =
  | Pop_compressed
      (** 48-byte compressed G1 signature + 96-byte compressed G2 pubkey, both
          decoding to genuine curve points, over the canonical
          proof-of-possession message [intentPrefix(3) || compressedPubkey(96)
          || address(20)] (crates/types/src/crypto/bls_signature.rs:206-214).
          This is the only class the pristine verifier can ever accept. *)
  | Pop_uncompressed
      (** The SAME point pair in the 96-byte uncompressed G1 / 192-byte
          uncompressed G2 serialization, over the same canonical message. blst
          would deserialize both by length; only the length gate at
          mod.rs:142-144 rejects them. The in-repo negative test builds exactly
          this vector - [proof.serialize()] is 96 bytes and
          [keypair.public().serialize()] is 192 (mod.rs:216-243, and through the
          real EVM at
          crates/tn-reth/tests/it/bls_precompile_props.rs:195-228). *)
  | Wrong_message
      (** 48/96 compressed points that decode fine, but the message is not the
          one the signature covers (mod.rs:245-252 same key, different address;
          crates/tn-reth/tests/it/bls_precompile_props.rs:99-114). Reaches
          [bls_verify_secure] and gets a plain [false]. *)
  | Undecodable_points
      (** 48/96-length bytes that are not valid point encodings: random garbage
          (mod.rs:272-280, props :148-160) or a 96-byte pubkey with the
          compression flag cleared, which mod.rs:138-140 names explicitly. These
          are the two [else { return false; }] fallbacks at mod.rs:145-150. *)
  | Junk_length
      (** Signature/pubkey lengths that are neither the compressed 48/96 nor the
          uncompressed 96/192 forms - 0, 32, 47, 128, 256 ... (mod.rs:282-297,
          props :162-188). Rejected by the length gate, and ALSO by the blst
          decoders' own length dispatch, which is why deleting the length gate
          does not admit them. *)
  | Pre_crypto_reject
      (** The call never reaches [bls_verify] at all: fewer than 4 bytes or an
          unknown selector (mod.rs:103-110), gas below the 150k floor
          (mod.rs:115-117), or calldata the ABI decoder rejects
          (mod.rs:119-120). All three exit [Err], burning the frame's whole
          forwarded gas. Modeling this class is what keeps the fairness
          statement honest: uniform pricing is claimed only over calls that
          clear these gates, exactly as props :255-266 shows short calldata
          failing. *)

(** Total order index for {!input_class}. *)
let input_class_index = function
  | Pop_compressed -> 0
  | Pop_uncompressed -> 1
  | Wrong_message -> 2
  | Undecodable_points -> 3
  | Junk_length -> 4
  | Pre_crypto_reject -> 5

(** Total order on {!input_class}. *)
let input_class_compare a b =
  Int.compare (input_class_index a) (input_class_index b)

(** Every input class, in canonical order. *)
let all_input_classes =
  [
    Pop_compressed;
    Pop_uncompressed;
    Wrong_message;
    Undecodable_points;
    Junk_length;
    Pre_crypto_reject;
  ]

(** [true] iff the call clears the selector split (mod.rs:103-105), the 150k gas
    floor (mod.rs:115-117) and the ABI decode (mod.rs:119-120), and therefore
    reaches [bls_verify] (mod.rs:141). *)
let reaches_verifier = function
  | Pop_compressed | Pop_uncompressed | Wrong_message | Undecodable_points
  | Junk_length ->
      true
  | Pre_crypto_reject -> false

(** [true] iff the submitted signature/pubkey bytes are the 48-byte compressed
    G1 / 96-byte compressed G2 encodings of genuine curve points: the length gate
    (mod.rs:142-144) passes AND both decoders (mod.rs:145-150) succeed. *)
let is_compressed_pair = function
  | Pop_compressed | Wrong_message -> true
  | Pop_uncompressed | Undecodable_points | Junk_length | Pre_crypto_reject ->
      false

(** [true] iff the submitted bytes are the 96/192 UNCOMPRESSED serializations of
    a point pair - the aliasing form the length gate exists to reject
    (mod.rs:135-144). *)
let is_uncompressed_pair = function
  | Pop_uncompressed -> true
  | Pop_compressed | Wrong_message | Undecodable_points | Junk_length
  | Pre_crypto_reject ->
      false

(** Custody of the BLS secret key behind the submitted pubkey, at signing time.
    HIDDEN: no view projects it. *)
type custody =
  | Key_holder
      (** The party that produced the submitted signature held the secret key
          matching the submitted pubkey. *)
  | No_key
      (** The submitter did not hold that secret key: a replayed or substituted
          pubkey with a fabricated signature (mod.rs:263-270), or an
          unvalidated / small-subgroup / infinity G2 key. *)

(** Total order index for {!custody}. *)
let custody_index = function Key_holder -> 0 | No_key -> 1

(** Total order on {!custody}. *)
let custody_compare a b = Int.compare (custody_index a) (custody_index b)

(** Every custody value, in canonical order. *)
let all_custody = [ Key_holder; No_key ]

(** [true] iff the signer held the key. *)
let custody_is_holder = function Key_holder -> true | No_key -> false

(** Whether the secret key is still held exclusively by the registrant. HIDDEN:
    no view projects it, and nothing on chain ever could - a proof of possession
    is a snapshot of one signing moment, not a continuing custody guarantee. *)
type excl =
  | Exclusive  (** The key has never left the registrant. *)
  | Copied  (** The key has been copied to at least one other party. *)

(** Total order index for {!excl}. *)
let excl_index = function Exclusive -> 0 | Copied -> 1

(** Total order on {!excl}. *)
let excl_compare a b = Int.compare (excl_index a) (excl_index b)

(** Every exclusivity value, in canonical order. *)
let all_excl = [ Exclusive; Copied ]

(** [true] iff the key is still exclusively held. *)
let excl_is_exclusive = function Exclusive -> true | Copied -> false

(** One submitted call: its observable byte class plus the two hidden facts
    about the key behind it. *)
type submission = { inp : input_class; cust : custody; exc : excl }

(** Total deterministic order over ALL submission fields. *)
let submission_compare a b =
  let c = input_class_compare a.inp b.inp in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = custody_compare a.cust b.cust in
    if Bool.not (Int.equal c1 0) then c1 else excl_compare a.exc b.exc

(** Every submission the environment may offer: 6 x 2 x 2 = 24. *)
let all_submissions =
  List.concat_map
    (fun inp ->
      List.concat_map
        (fun cust -> List.map (fun exc -> { inp; cust; exc }) all_excl)
        all_custody)
    all_input_classes

(** The boolean the precompile ABI-encodes back to the caller (mod.rs:129), or
    its absence when the frame errs. *)
type verdict =
  | Verdict_true  (** the ABI-encoded [true] *)
  | Verdict_false  (** the ABI-encoded [false] *)
  | Verdict_none  (** the frame returned [Err]: there is no boolean at all *)

(** Total order index for {!verdict}. *)
let verdict_index = function
  | Verdict_true -> 0
  | Verdict_false -> 1
  | Verdict_none -> 2

(** Total order on {!verdict}. *)
let verdict_compare a b = Int.compare (verdict_index a) (verdict_index b)

(** [true] iff the precompile returned the boolean [true]. *)
let verdict_is_true = function
  | Verdict_true -> true
  | Verdict_false | Verdict_none -> false

(** How the precompile frame exited. *)
type exit_kind =
  | Exit_value
      (** [Ok(PrecompileOutput::new(..))] carrying an ABI-encoded bool
          (mod.rs:129). *)
  | Exit_err
      (** [Err(PrecompileError::_)] (mod.rs:104, :109, :116, :120), which reverts
          the calling frame. *)

(** Total order index for {!exit_kind}. *)
let exit_kind_index = function Exit_value -> 0 | Exit_err -> 1

(** Total order on {!exit_kind}. *)
let exit_kind_compare a b = Int.compare (exit_kind_index a) (exit_kind_index b)

(** [true] iff the frame returned a value rather than reverting. *)
let exit_is_value = function Exit_value -> true | Exit_err -> false

(** What the frame cost. *)
type charge =
  | Charge_flat
      (** exactly [BLS_VERIFY_GAS_COST] = 150_000 (mod.rs:77, charged at
          mod.rs:129 and asserted at mod.rs:309 / :322). *)
  | Charge_forwarded
      (** an [Err] return: revm consumes the whole gas forwarded to the
          frame. *)

(** Total order index for {!charge}. *)
let charge_index = function Charge_flat -> 0 | Charge_forwarded -> 1

(** Total order on {!charge}. *)
let charge_compare a b = Int.compare (charge_index a) (charge_index b)

(** [true] iff the frame cost the flat 150k. *)
let charge_is_flat = function Charge_flat -> true | Charge_forwarded -> false

(** The settled result of one precompile frame. Every field is DERIVED by
    {!settle} from the input class, the custody and the active mutation - which
    is why it has to be stored in the state: [label] is mutation-blind. *)
type outcome = { vd : verdict; ex : exit_kind; ch : charge }

(** Total deterministic order over ALL outcome fields. *)
let outcome_compare a b =
  let c = verdict_compare a.vd b.vd in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = exit_kind_compare a.ex b.ex in
    if Bool.not (Int.equal c1 0) then c1 else charge_compare a.ch b.ch

(** The life of the one modeled call. *)
type call =
  | No_call  (** nothing has been submitted to 0x..b151 yet *)
  | Pending of submission
      (** submitted; V1 has not executed the frame, so it has observed nothing *)
  | Settled of submission * outcome
      (** V1 executed the frame and the precompile returned *)

(** Total order on {!call}: [No_call] < [Pending] < [Settled], field-wise
    within each constructor. Every constructor pair is spelled. *)
let call_compare a b =
  match (a, b) with
  | No_call, No_call -> 0
  | No_call, (Pending _ | Settled (_, _)) -> -1
  | (Pending _ | Settled (_, _)), No_call -> 1
  | Pending sa, Pending sb -> submission_compare sa sb
  | Pending _, Settled (_, _) -> -1
  | Settled (_, _), Pending _ -> 1
  | Settled (sa, oa), Settled (sb, ob) ->
      let c = submission_compare sa sb in
      if Bool.not (Int.equal c 0) then c else outcome_compare oa ob

(** The joint global state: the one [blsVerify] call and its life stage. *)
type state = { frame : call }

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 = call_compare s1.frame s2.frame

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    [View_exec_none] / [View_exec]: V1 the EXECUTING node. Before the frame runs
    it has observed nothing; afterwards it has the calldata's observable class,
    the frame's exit and the returned boolean. It never sees [custody] or
    [excl].

    [View_cost_pre] / [View_cost]: V2 the RECEIPT observer, which sees gas
    accounting only - no returndata, no calldata class, no hidden fact.

    [View_idle]: the constant blank view of the non-agents V0 and V3..V9. *)
type view =
  | View_exec_none
  | View_exec of input_class * exit_kind * verdict
  | View_cost_pre
  | View_cost of charge
  | View_idle

(** Total deterministic order over ALL fields of V1's settled view. *)
let exec_view_compare (i, e, v) (i', e', v') =
  let c = input_class_compare i i' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = exit_kind_compare e e' in
    if Bool.not (Int.equal c1 0) then c1 else verdict_compare v v'

(** Total order on views: [View_idle] < [View_exec_none] < [View_exec] <
    [View_cost_pre] < [View_cost], with the field-wise order inside each
    constructor. Every constructor pair is spelled: no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_exec_none | View_exec _ | View_cost_pre | View_cost _) -> -1
  | (View_exec_none | View_exec _ | View_cost_pre | View_cost _), View_idle -> 1
  | View_exec_none, View_exec_none -> 0
  | View_exec_none, (View_exec _ | View_cost_pre | View_cost _) -> -1
  | (View_exec _ | View_cost_pre | View_cost _), View_exec_none -> 1
  | View_exec (i, e, v), View_exec (i', e', v') ->
      exec_view_compare (i, e, v) (i', e', v')
  | View_exec _, (View_cost_pre | View_cost _) -> -1
  | (View_cost_pre | View_cost _), View_exec _ -> 1
  | View_cost_pre, View_cost_pre -> 0
  | View_cost_pre, View_cost _ -> -1
  | View_cost _, View_cost_pre -> 1
  | View_cost c, View_cost c' -> charge_compare c c'

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 (executing node) and V2 (receipt observer) are the
    knowledge agents, with real non-constant views; V0 and V3..V9 are idle
    non-agents with the constant blank view and never appear under K.

    V1 sees only what it EXECUTED, so the hidden [custody]/[excl] fields are
    absent from its view and so is any information about a call it has not run.
    V2 sees only the charge: the precompile emits no logs and its returndata
    stays inside the frame, so gas is all a receipt-level observer gets. *)
let view v s =
  match v with
  | Validator.V1 -> (
      match s.frame with
      | No_call -> View_exec_none
      | Pending _ -> View_exec_none
      | Settled (sub, out) -> View_exec (sub.inp, out.ex, out.vd))
  | Validator.V2 -> (
      match s.frame with
      | No_call -> View_cost_pre
      | Pending _ -> View_cost_pre
      | Settled (_, out) -> View_cost out.ch)
  | Validator.V0 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | Err_on_failed_verify
      (** Delete the two [else { return false; }] decode fallbacks at
          crates/tn-reth/src/evm/bls_precompile/mod.rs:145-150 and propagate the
          decoder errors out of [handle_bls_verify] as
          [PrecompileError::Other]. The {!Undecodable_points} class then settles
          [Exit_err] / [Charge_forwarded] instead of [Exit_value] /
          [Charge_flat], so cost and exit become verdict-class dependent while
          {!Wrong_message} and a failing {!Pop_compressed} still pay the flat
          150k.

          No sibling path repairs it. [dispatch] (mod.rs:102-111) is a bare
          selector match that returns the handler's result untouched;
          [bls_precompile] (mod.rs:93-95) only forwards [input.data] and
          [input.gas]; [add_bls_precompile] (mod.rs:83-89) wraps the closure
          without mapping errors. Nothing downstream can re-normalise an [Err]
          into an [Ok(false)], and a reverted [STATICCALL] propagates to the
          caller frame (the relay in
          crates/tn-reth/tests/it/bls_precompile_props.rs:273-321 returns the
          precompile's output verbatim). The ABI-decode failure at
          mod.rs:119-120 is ALREADY on the expensive path, which is exactly why
          the fairness statement is scoped by {!Call_admitted} rather than
          claiming uniform cost over all calldata. *)
  | No_length_gate
      (** Delete the fixed 48/96 length pin at
          crates/tn-reth/src/evm/bls_precompile/mod.rs:142-144. blst
          deserializes by length, so the {!Pop_uncompressed} class - the 96-byte
          uncompressed G1 signature and 192-byte uncompressed G2 pubkey of the
          SAME point pair - then decodes and verifies, adding
          [Pending Pop_uncompressed(Key_holder) -> Settled .. Verdict_true] and
          giving one point pair two accepted byte encodings.

          No sibling path repairs it, and the model carries the two partial
          repairs that DO exist so the claim cannot be true by omission:
          [BlsPublicKey::from_literal_bytes] (bls_public_key.rs:99-101) and
          [BlsSignature::from_bytes] (bls_signature.rs:25-29) are bare blst
          decodes that dispatch on length, so they still reject
          {!Junk_length} (a non-serialization length) and still reject
          {!Undecodable_points} (mod.rs:138-140 names the flag-clear 96-byte
          pubkey case) - both classes stay [Verdict_false] under this mutation.
          What they do NOT reject is the valid 96/192 uncompressed form; that is
          the precise content of mod.rs:135-140 and of the in-repo negative
          tests at mod.rs:216-243 and props :195-228. The ABI layer cannot help
          either: [blsVerifyCall::abi_decode_raw] (mod.rs:119) decodes [bytes]
          of any length. *)
  | No_pk_validation
      (** Flip the trailing [true] - the public-key validation flag - to [false]
          in [bls_verify_secure], crates/types/src/crypto/bls_signature.rs:195
          [signature.verify(true, message, DST_G1, &[], public_key, true)], so
          an unvalidated / small-subgroup / infinity G2 key with a fabricated
          matching signature verifies. That adds
          [Pending Pop_compressed(No_key) -> Settled .. Verdict_true]: a TRUE
          verdict no longer implies anybody held the secret key.

          No sibling path repairs it on the precompile path.
          [bls_verify_secure] has exactly two callers in the tree:
          [verify_proof_of_possession_bls] (bls_signature.rs:171-183), which
          DOES call [public_key.validate()] first at :176 - but that is the
          consensus-layer path - and the precompile at mod.rs:141-153, which
          never calls [validate()]. The precompile's own decoders are bare
          [from_bytes] calls (bls_public_key.rs:99-101,
          bls_signature.rs:25-29) that perform no subgroup or infinity check;
          mod.rs:140 says so in as many words ("Subgroup and infinity checks
          remain at verify time"). The length gate at mod.rs:142-144 is a length
          test only and passes a well-formed 96-byte small-subgroup key. So the
          [pk_validate] flag is the sole on-chain enforcement. *)

(** The precompile's derived result for one submission under one mutation: the
    frame exit, the charge and the boolean. This is [handle_bls_verify] plus
    [bls_verify] (mod.rs:114-153) as a total function. *)
let settle mut sub =
  let value vd = { vd; ex = Exit_value; ch = Charge_flat } in
  let errored = { vd = Verdict_none; ex = Exit_err; ch = Charge_forwarded } in
  let crypto cust = if custody_is_holder cust then Verdict_true else Verdict_false in
  match sub.inp with
  | Pre_crypto_reject -> errored
  | Pop_compressed -> (
      match sub.cust with
      | Key_holder -> value Verdict_true
      | No_key -> (
          match mut with
          | No_pk_validation -> value Verdict_true
          | Pristine | No_length_gate | Err_on_failed_verify ->
              value Verdict_false))
  | Pop_uncompressed -> (
      match mut with
      | No_length_gate -> value (crypto sub.cust)
      | Pristine | No_pk_validation | Err_on_failed_verify -> value Verdict_false
      )
  | Wrong_message -> value Verdict_false
  | Undecodable_points -> (
      match mut with
      | Err_on_failed_verify -> errored
      | Pristine | No_length_gate | No_pk_validation -> value Verdict_false)
  | Junk_length -> value Verdict_false

(** The transition relation: the environment offers any one of the 24
    submissions, then the frame runs exactly once and settles. [Settled] is
    terminal and the kernel stutter-closes it. *)
let next_with mut s =
  match s.frame with
  | No_call -> List.map (fun sub -> { frame = Pending sub }) all_submissions
  | Pending sub -> [ { frame = Settled (sub, settle mut sub) } ]
  | Settled (_, _) -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: nothing has been submitted to 0x..b151 yet. *)
let initial = { frame = No_call }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Call_admitted
      (** A submitted, not-yet-executed call that cleared every pre-crypto gate:
          the selector split (mod.rs:103-105), the 150k gas floor
          (mod.rs:115-117) and the ABI decode (mod.rs:119-120). This is the
          scope of the uniform-pricing claim. *)
  | Settled_call  (** the precompile frame has returned *)
  | Exit_is_value
      (** the frame exited [Ok(PrecompileOutput::new(..))] with an ABI-encoded
          bool (mod.rs:129) rather than [Err] *)
  | Charge_is_flat
      (** the frame cost exactly [BLS_VERIFY_GAS_COST] = 150_000 (mod.rs:77,
          :129) rather than the whole forwarded gas *)
  | Verdict_is_true  (** the returned boolean is [true] *)
  | Input_is_compressed_pair
      (** the submitted sig/pubkey are the 48/96 COMPRESSED encodings of genuine
          curve points: the length gate (mod.rs:142-144) passed and both
          decoders (mod.rs:145-150) succeeded *)
  | Input_is_uncompressed_pair
      (** the submitted bytes are the 96/192 UNCOMPRESSED serializations of a
          point pair - the aliasing form (mod.rs:135-140, props :207-210) *)
  | Genuine_compressed_pop
      (** a pending call carrying a real proof of possession in the canonical
          compressed form: 48/96 compressed bytes over the canonical message,
          signed by the holder of the matching secret key (the positive control
          of mod.rs:206-214 and props :89-97) *)
  | Signer_held_key
      (** HIDDEN: the party that produced the submitted signature held the BLS
          secret key matching the submitted pubkey at signing time *)
  | Key_is_exclusive
      (** HIDDEN: that secret key is still held exclusively by the registrant
          and has never been copied *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Call_admitted -> (
      match s.frame with
      | No_call -> false
      | Pending sub -> reaches_verifier sub.inp
      | Settled (_, _) -> false)
  | Settled_call -> (
      match s.frame with
      | No_call -> false
      | Pending _ -> false
      | Settled (_, _) -> true)
  | Exit_is_value -> (
      match s.frame with
      | No_call -> false
      | Pending _ -> false
      | Settled (_, out) -> exit_is_value out.ex)
  | Charge_is_flat -> (
      match s.frame with
      | No_call -> false
      | Pending _ -> false
      | Settled (_, out) -> charge_is_flat out.ch)
  | Verdict_is_true -> (
      match s.frame with
      | No_call -> false
      | Pending _ -> false
      | Settled (_, out) -> verdict_is_true out.vd)
  | Input_is_compressed_pair -> (
      match s.frame with
      | No_call -> false
      | Pending sub -> is_compressed_pair sub.inp
      | Settled (sub, _) -> is_compressed_pair sub.inp)
  | Input_is_uncompressed_pair -> (
      match s.frame with
      | No_call -> false
      | Pending sub -> is_uncompressed_pair sub.inp
      | Settled (sub, _) -> is_uncompressed_pair sub.inp)
  | Genuine_compressed_pop -> (
      match s.frame with
      | No_call -> false
      | Pending sub -> (
          match sub.inp with
          | Pop_compressed -> custody_is_holder sub.cust
          | Pop_uncompressed | Wrong_message | Undecodable_points | Junk_length
          | Pre_crypto_reject ->
              false)
      | Settled (_, _) -> false)
  | Signer_held_key -> (
      match s.frame with
      | No_call -> false
      | Pending sub -> custody_is_holder sub.cust
      | Settled (sub, _) -> custody_is_holder sub.cust)
  | Key_is_exclusive -> (
      match s.frame with
      | No_call -> false
      | Pending sub -> excl_is_exclusive sub.exc
      | Settled (sub, _) -> excl_is_exclusive sub.exc)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Call_admitted -> "admitted(call)"
  | Settled_call -> "settled(call)"
  | Exit_is_value -> "exit=Ok(bool)"
  | Charge_is_flat -> "gas_used=150000"
  | Verdict_is_true -> "blsVerify=true"
  | Input_is_compressed_pair -> "bytes=compressed(48,96)"
  | Input_is_uncompressed_pair -> "bytes=uncompressed(96,192)"
  | Genuine_compressed_pop -> "genuine_pop(compressed)"
  | Signer_held_key -> "held_sk(signer)"
  | Key_is_exclusive -> "exclusive(sk)"

(** The CTLK checker over this family's ordered state and view: the presheaf-
    topos denotation, pinned to agree with {!System} at every reachable world by
    test/t_bls_verify_gate_topos.ml.

    This family's reachability relation is a POSET: the call life
    [No_call -> Pending -> Settled] is a three-layer DAG and nothing undoes
    itself, so {!Frame.certify_functorial} certifies antisymmetry. That
    classification is pinned by the [poset] group of the topos gate. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state, mutation-
    parameterized transitions, the two-agent view, the atom valuation. *)
let spec_of mut = { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
