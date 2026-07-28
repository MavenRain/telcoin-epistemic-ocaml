(** Confirm-by-mutation pins for the TEL_DISPATCH_SURFACE family. Each statement
    is paired with the ONE gate deletion that refutes it, and the refutation is
    asserted to be a genuine [Refuted] rather than a [Vacuous_antecedent] - a
    mutation that merely made a statement's situation unreachable would otherwise
    look like a pin while proving nothing.

    - {!Tel_dispatch_surface_model.Open_selector_fallthrough} rewrites the
      fail-closed catch-all
      [_ => Err(PrecompileError::Other("Unknown function selector".into()))]
      (tn-reth/src/evm/tel_precompile/mod.rs:163) as a silent
      [Ok(PrecompileOutput::new(0, Bytes::new()))], so an unimplemented
      [approve] settles as a SUCCESSFUL transaction. No sibling repairs it: the
      only other calldata gate is the length check at mod.rs:121-123, which
      passes any payload of four bytes or more regardless of selector; the
      per-handler argument checks (burnable.rs:167-169, :233-235, :330-332) are
      reached only from an implemented arm; and [add_telcoin_precompile]
      installs exactly one closure, with no fallback and no proxy
      (mod.rs:109-115). The one genuine partial repair - a caller that
      [abi.decode]s the returndata and so rejects an empty [Ok] as well as an
      [Err] - is IN the model as
      {!Tel_dispatch_surface_model.Relay_decodes}, and S1's transaction-level
      conjunct is scoped so that it survives that repair and flips anyway.
    - {!Tel_dispatch_surface_model.No_short_calldata_guard} deletes
      [if input.data.len() < 4 { return Err(..) }] (mod.rs:121-123), so a 1-3
      byte payload reaches the slice [input.data[0..4]] at :125 and panics the
      executor, removing the [Dispatched -> Settled] transition entirely. No
      sibling repairs it: the [try_into().unwrap()] on the same line is
      DOWNSTREAM of the slice; the per-handler length checks run only after the
      selector is extracted; the BLS dispatcher's total [split_first_chunk::<4>]
      (bls_precompile/mod.rs:102-105) is a different function on a different
      address; the [0xfe] genesis code byte (tn-reth/src/system_calls.rs:17-19)
      guards calls that BYPASS dispatch, not short ones that reach it; and the
      tree's only [catch_unwind] is the ExEx task wrapper
      (node/src/manager/exex.rs:19), nowhere near this path.
    - {!Tel_dispatch_surface_model.Frame_scoped_storage} deletes the explicit
      [TELCOIN_PRECOMPILE_ADDRESS] argument from the precompile's state accesses
      (representatively burnable.rs:342-351; identically at :91-92, :181-183,
      :187-189, :241-244, :252-255, :267-272, :275-287) in favour of the
      executing frame's address. No sibling repairs it and the mutation is NOT
      self-detecting: reads and writes move together so nothing errors,
      [handle_total_supply] (burnable.rs:83-96) reads through the same address
      and therefore hides the drift, [TOTAL_SUPPLY_SLOT] is never cross-checked
      against the sum of balances, and the caller-based access control
      ([has_governance_role], burnable.rs:136-138) is indifferent to the storage
      target. The one channel that DOES survive - the event stream, whose
      address argument is a literal at burnable.rs:356 and :365 - is modelled as
      the agent V3, and S3 conjunct D states exactly what that channel can and
      cannot settle. It never carried the frame identity, so it cannot repair
      what conjunct B loses.

    The cross-attribution group is the other half of the evidence: every
    statement is asserted to SURVIVE the two mutations that are not its pin, so
    a pin cannot pass on the strength of some other statement flipping. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Tel_dispatch_surface_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Tel_dispatch_surface_model.Checker.make
       (Tel_dispatch_surface_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Tel_dispatch_surface_statements.name name))
    Tel_dispatch_surface_statements.all

(** Classify a proof outcome so a pin can insist on the reason, not just the
    failure. *)
let outcome sys st =
  Result.fold
    ~ok:(fun _ -> "proved")
    ~error:(fun e ->
      match e with
      | Tel_dispatch_surface_model.Checker.Refuted _ -> "refuted"
      | Tel_dispatch_surface_model.Checker.Vacuous_antecedent -> "vacuous")
    (Tel_dispatch_surface_statements.prove sys st)

(** The negative half of a pin: the statement is REFUTED under the mutation -
    not merely unprovable, and not vacuous. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check string)
            (name ^ " flips to refuted under the mutation")
            "refuted" (outcome sys st))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Tel_dispatch_surface_model.Pristine (fun sys ->
          Alcotest.(check string)
            (name ^ " proves on the pristine model")
            "proved" (outcome sys st))

(** Cross-attribution: the statement still proves under a mutation that is NOT
    its pin, so the pin above is attributable to the gate it deletes. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check string)
            (name ^ " still proves under the unrelated mutation")
            "proved" (outcome sys st))

(** S1's name. *)
let s1_name = "unimplemented-selectors-fail-closed-at-the-tel-dispatcher"

(** S2's name. *)
let s2_name =
  "short-calldata-guard-is-all-that-stands-between-a-three-byte-call-and-an-executor-panic"

(** S3's name. *)
let s3_name = "precompile-state-is-address-pinned-under-delegatecall"

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "tel_dispatch_surface_mutation"
    [
      ( "a fail-open catch-all makes an unimplemented approve look like a success",
        pin Tel_dispatch_surface_model.Open_selector_fallthrough s1_name );
      ( "a deleted length check turns a three-byte call into an executor panic",
        pin Tel_dispatch_surface_model.No_short_calldata_guard s2_name );
      ( "frame-scoped storage shards the supply and leaks the call scheme",
        pin Tel_dispatch_surface_model.Frame_scoped_storage s3_name );
      ( "cross-attribution: each gate carries exactly its own statement",
        [
          Alcotest.test_case "S1 survives No_short_calldata_guard" `Quick
            (survives_under Tel_dispatch_surface_model.No_short_calldata_guard
               s1_name);
          Alcotest.test_case "S1 survives Frame_scoped_storage" `Quick
            (survives_under Tel_dispatch_surface_model.Frame_scoped_storage
               s1_name);
          Alcotest.test_case "S2 survives Open_selector_fallthrough" `Quick
            (survives_under Tel_dispatch_surface_model.Open_selector_fallthrough
               s2_name);
          Alcotest.test_case "S2 survives Frame_scoped_storage" `Quick
            (survives_under Tel_dispatch_surface_model.Frame_scoped_storage
               s2_name);
          Alcotest.test_case "S3 survives Open_selector_fallthrough" `Quick
            (survives_under Tel_dispatch_surface_model.Open_selector_fallthrough
               s3_name);
          Alcotest.test_case "S3 survives No_short_calldata_guard" `Quick
            (survives_under Tel_dispatch_surface_model.No_short_calldata_guard
               s3_name);
        ] );
    ]
