(** Confirm-by-mutation pins for the CLOSE_BLOCK_SYSCALL family. Each statement
    is paired with the ONE gate deletion that refutes it, and the refutation is
    asserted to be a genuine [Refuted] rather than a [Vacuous_antecedent] - a
    mutation that merely makes a statement's situation unreachable would
    otherwise look like a pin while proving nothing.

    - {!Close_block_syscall_model.No_close_marker_gate} deletes the
      [if let Some(randomness) = self.ctx.close_epoch {] guard
      (tn-reth/src/evm/block.rs:794) and runs its body in every block, so an
      ordinary block's registry epoch advances behind an unmarked header. No
      sibling confines it: [concludeEpochCall], [applyIncentivesCall] and
      [migrateValidatorSetsCall] are constructed at exactly one site each
      (block.rs:399, :414, :348), all three inside this guard, and
      [apply_consensus_block_rewards] / [apply_closing_epoch_contract_call] have
      exactly one call site each (block.rs:824, :829). The remaining candidate -
      the unvendored Solidity registry refusing a premature call - is carried as
      the {!Close_block_syscall_model.Registry_reverts} branch, where it halts
      the block (block.rs:215-219) instead of repairing anything.
    - {!Close_block_syscall_model.No_env_restore} deletes the three restore
      swaps (tn-reth/src/evm/mod.rs:207-212), so the base fee stays zeroed and
      the nonce check stays disabled into the block's user transactions. No
      sibling re-establishes the environment: [transact_raw] sets only the tx
      env (mod.rs:147-162), [execute_transaction_without_commit] passes only
      [tx_env] (block.rs:860-885), the EVM is created once per block
      (factory.rs:46-64, :148-158), [disable_base_fee] does not exist anywhere
      in the tree, and the payload loop skips a transaction only BECAUSE revm
      rejected it (lib.rs:783-799). The partial repair - the over-estimation
      penalty still crediting the same sink (handler.rs:124-131) - is modelled
      as [Sink_penalty_only] rather than omitted, and S2 still flips.
    - {!Close_block_syscall_model.Nonzero_basefee_for_syscall} deletes the
      base-fee swap-in (mod.rs:201) and its mirror restore (mod.rs:210), so a
      [gas_price: 0] system transaction (mod.rs:180) is inadmissible against the
      block's real base fee. No sibling admits it: no [disable_base_fee] flag
      exists, pre-funding cannot help a zero gas price, and nothing retries -
      the engine propagates the failure out of [run()] with [?]
      (engine/src/lib.rs:262-264).

    Two groups carry the other half of the evidence. CROSS-ATTRIBUTION asserts
    that each statement still PROVES under the mutations that are not its pin,
    so a pin cannot pass on the strength of some other statement flipping.
    COLLATERAL records, rather than hides, the one place where a mutation is so
    destructive that two statements go VACUOUS instead of surviving: deleting
    the base-fee swap kills the pre-block EIP-2935 system call
    (block.rs:708-719), so no block ever reaches its user transactions or seals
    at all, and the situations S1 and S2 are about stop arising. That is
    asserted explicitly as "vacuous" so the fact is pinned rather than papered
    over. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Close_block_syscall_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Close_block_syscall_model.Checker.make
       (Close_block_syscall_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Close_block_syscall_statements.name name))
    Close_block_syscall_statements.all

(** Classify a proof outcome so a pin can insist on the reason, not just the
    failure. *)
let outcome sys st =
  Result.fold
    ~ok:(fun _ -> "proved")
    ~error:(fun e ->
      match e with
      | Close_block_syscall_model.Checker.Refuted _ -> "refuted"
      | Close_block_syscall_model.Checker.Vacuous_antecedent -> "vacuous")
    (Close_block_syscall_statements.prove sys st)

(** Assert a named statement's verdict under a mutation. *)
let verdict_under mut name expected message () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check string) (name ^ " " ^ message) expected
            (outcome sys st))

(** The negative half of a pin: the statement is REFUTED under the mutation -
    not merely unprovable, and not vacuous. *)
let refuted_under mut name =
  verdict_under mut name "refuted" "flips to refuted under the mutation"

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name =
  verdict_under Close_block_syscall_model.Pristine name "proved"
    "proves on the pristine model"

(** Cross-attribution: the statement still proves under a mutation that is NOT
    its pin, so the pin above is attributable to the gate it deletes. *)
let survives_under mut name =
  verdict_under mut name "proved" "still proves under the unrelated mutation"

(** Collateral: the mutation is destructive enough that the statement's
    situation stops arising, so [prove_nonvacuous] refuses rather than
    certifying. Asserted, not hidden. *)
let vacuous_under mut name =
  verdict_under mut name "vacuous"
    "goes vacuous under a mutation that kills the whole block"

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** S1's name. *)
let s1_name = "epoch-transition-is-confined-to-and-published-by-the-marked-block"

(** S2's name. *)
let s2_name =
  "system-call-window-shuts-before-the-user-transactions-of-the-block"

(** S3's name. *)
let s3_name = "epoch-closing-calls-need-the-zeroed-base-fee-admission-window"

let () =
  Alcotest.run "close_block_syscall_mutation"
    [
      ( "dropped close-marker gate rotates the epoch behind an unmarked header",
        pin Close_block_syscall_model.No_close_marker_gate s1_name );
      ( "dropped environment restore leaks the system-call window into user \
         transactions",
        pin Close_block_syscall_model.No_env_restore s2_name );
      ( "base fee left in force makes every zero-priced system call \
         inadmissible",
        pin Close_block_syscall_model.Nonzero_basefee_for_syscall s3_name );
      ( "cross-attribution: each gate carries exactly its own statement",
        [
          Alcotest.test_case "S1 survives No_env_restore" `Quick
            (survives_under Close_block_syscall_model.No_env_restore s1_name);
          Alcotest.test_case "S2 survives No_close_marker_gate" `Quick
            (survives_under Close_block_syscall_model.No_close_marker_gate
               s2_name);
          Alcotest.test_case "S3 survives No_close_marker_gate" `Quick
            (survives_under Close_block_syscall_model.No_close_marker_gate
               s3_name);
          Alcotest.test_case "S3 survives No_env_restore" `Quick
            (survives_under Close_block_syscall_model.No_env_restore s3_name);
        ] );
      ( "collateral: killing every system call kills the situations S1 and S2 \
         are about",
        [
          Alcotest.test_case "S1 vacuous under Nonzero_basefee_for_syscall"
            `Quick
            (vacuous_under Close_block_syscall_model.Nonzero_basefee_for_syscall
               s1_name);
          Alcotest.test_case "S2 vacuous under Nonzero_basefee_for_syscall"
            `Quick
            (vacuous_under Close_block_syscall_model.Nonzero_basefee_for_syscall
               s2_name);
        ] );
    ]
