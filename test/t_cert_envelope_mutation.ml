(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    CERT_ENVELOPE family. Each of the three statements rests on a DIFFERENT
    gate of [validate_batch] (crates/batch-validator/src/validator.rs:39-82),
    so each gets its own mutation constructor, and each row asserts the proof
    FLIPS to an error on the mutated model while still proving on the pristine
    one. Every mutation leaves the reachable count at 49 - it flips WHICH
    verdict one content resolves to, it never adds a component value - so the
    flips are attributable to the deleted gate and not to a changed state
    space.

    - {!Cert_envelope_model.No_basefee_gate} deletes the
      [if base_fee != expected_base_fee] rejection in [validate_basefee]
      (validator.rs:188-195, called at :80), letting a fee-forged batch into
      V1's store. NO SIBLING REPAIR: execution never re-derives the fee - it is
      copied verbatim from the batch through payload_builder.rs:147 ->
      evm/config.rs:131-138 -> evm/block.rs:992 with no comparison anywhere on
      that chain - and the only other comparison-shaped uses of
      [base_fee_per_gas] are the epoch-entry derivation (node.rs:328-343) and
      the txpool's [pending_basefee] (inner.rs:149, start_epoch.rs:414), both
      author-side admission control rather than a receiver gate. Pins S1.

    - {!Cert_envelope_model.No_recovery_gate} deletes the
      [.collect::<BatchValidationResult<Vec<_>>>()] in [decode_transactions]
      (validator.rs:147-156, called at :70) that turns one recovery failure
      into a whole-batch rejection. NO SIBLING REPAIR: the engine's tolerance
      arm at tn-reth/src/lib.rs:782-800 skips only
      [BlockExecutionError::Validation(InvalidTx)] in phase 2, AFTER recovery
      succeeded, while phase 1 at :763-780 propagates any recovery failure with
      [?]; no other production code recovers a batch's transactions. Pins S2,
      and R8 is respected because this removes a real gate rather than a
      delivery path. It refutes S2's resolution conjunct in the strong way:
      from (Unrecoverable, Accepted, Holds, Committed) one successor is the
      terminal [Halted], which satisfies NEITHER disjunct of
      [AF (executed_2 \/ aborted_2)]. The always-enabled
      {!Cert_envelope_model.Aborted} sibling does NOT repair it, precisely
      because [Halted] remains on a path of its own.

    - {!Cert_envelope_model.No_empty_batch_gate} deletes the
      [.reduce(...).ok_or(EmptyBatch)?] in [validate_batch_size_bytes]
      (validator.rs:127-141, called at :67). NO SIBLING REPAIR: [EmptyBatch] is
      constructed at exactly one place in the whole tree (validator.rs:132), and
      with a zero total every remaining gate passes - [validate_batch_gas]
      even comments at :167-168 that it DELEGATES the empty check to the size
      check. Pins S3.

    Cross-refutation, recorded honestly rather than hidden: S1 ALSO refutes
    under [No_recovery_gate]. Its ignorance conjunct
    [~K_V1(~executed_2(D))] fails once an [Unrecoverable] batch is acceptable,
    because such a batch can only ever reach [Halted], so V1 would then KNOW no
    remote node executes it. That is a true property of the model - the recovery
    gate is load-bearing for V1's ignorance too - and it does not weaken the
    pins below: each statement is pinned on the gate its own conjuncts name, and
    the other two mutations leave S2 and S3 proved, so no pin is an artefact of
    a globally destructive edit. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Cert_envelope_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Cert_envelope_model.Checker.make (Cert_envelope_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Cert_envelope_statements.name name))
    Cert_envelope_statements.all

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " flips to refuted under the mutation")
            false
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Cert_envelope_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Cert_envelope_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Cert_envelope_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The reachable count is unchanged by the mutation, so a flipped proof is
    attributable to the deleted gate and not to a resized state space. *)
let count_unchanged mut () =
  with_mut mut (fun sys ->
      Alcotest.(check int) "mutated reachable count still 49" 49
        (Cert_envelope_model.Checker.reachable_count sys))

let () =
  Alcotest.run "cert_envelope_mutation"
    [
      ( "dropped basefee gate kills known-uniform-execution-base-fee",
        pin Cert_envelope_model.No_basefee_gate
          "accepted-batch-implies-known-uniform-execution-base-fee" );
      ( "dropped recovery gate kills known-recovery-safe-execution",
        pin Cert_envelope_model.No_recovery_gate
          "accepted-batch-implies-known-recovery-safe-execution" );
      ( "dropped empty-batch gate kills known-nonempty-remote-payload",
        pin Cert_envelope_model.No_empty_batch_gate
          "accepted-batch-implies-known-nonempty-remote-payload" );
      ( "mutations do not resize the state space",
        [
          Alcotest.test_case "no-basefee-gate:count" `Quick
            (count_unchanged Cert_envelope_model.No_basefee_gate);
          Alcotest.test_case "no-recovery-gate:count" `Quick
            (count_unchanged Cert_envelope_model.No_recovery_gate);
          Alcotest.test_case "no-empty-batch-gate:count" `Quick
            (count_unchanged Cert_envelope_model.No_empty_batch_gate);
        ] );
    ]
