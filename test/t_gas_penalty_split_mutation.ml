(** Confirm-by-mutation for the GAS-PENALTY-SPLIT family: each statement is
    pinned by the gate deletion it actually depends on, and each pin
    asserts BOTH halves - proves pristine, refutes mutated - so a pin
    cannot pass because some other statement moved.

    - [No_small_limit_exemption] deletes gate one of the penalty function,
      [if gas_limit <= MIN_GAS_LIMIT_THRESHOLD { return 0; }]
      (crates/tn-reth/src/evm/utils.rs:47-49). S1 then fails on two
      conjuncts at once: a batch declaring exactly 210,000 gas and
      spending 5% of it is charged 49,875 gas, and the admission-time
      validator's [K_V0 (AG ~penalty_a>0)] at small declared limits goes
      with it. No sibling path repairs it - one production call site
      (handler.rs:109), a downward-only [saturating_sub] one line later
      (handler.rs:113), the [penalty.min(unused_gas)] at utils.rs:78
      sitting inside the [debug!] arguments rather than the return
      (utils.rs:83), and an admission side that bounds only the SUM of
      declared limits (crates/batch-validator/src/validator.rs:162-185).
    - [Refund_aware_penalty] deletes the pre-refund binding
      [let gas_spent = gas.spent();] (handler.rs:91), forcing the penalty
      call at handler.rs:109 onto the post-refund figure of
      handler.rs:92. S2 fails: the twin that earned an EVM refund is
      charged 99,750 gas where its no-refund twin is charged nothing. The
      refund reaches only [unused_gas] (handler.rs:112) and the
      beneficiary reward (handler.rs:152), neither of which feeds back
      into the penalty, so nothing re-widens the refund afterwards.
    - [Burn_the_penalty] deletes the sink credit at handler.rs:125-131.
      S3 fails: the caller's refund is still reduced by the penalty
      (handler.rs:113) but the wei is credited nowhere, so total credited
      falls below total charged. The only [incr_balance] sites in
      crates/tn-reth/src are handler.rs:121, :130, :160 and :168, so no
      second credit site can restore it. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Gas_penalty_split_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Gas_penalty_split_model.Checker.make
       (Gas_penalty_split_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Gas_penalty_split_statements.name name))
    Gas_penalty_split_statements.all

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
               (Gas_penalty_split_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine
    model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Gas_penalty_split_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Gas_penalty_split_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "gas_penalty_split_mutation"
    [
      ( "the 210k declared-limit exemption (utils.rs:47-49)",
        pin Gas_penalty_split_model.No_small_limit_exemption
          "well-estimated-transaction-is-never-penalized-under-uniform-thresholds"
      );
      ( "the pre-refund penalty denominator (handler.rs:91)",
        pin Gas_penalty_split_model.Refund_aware_penalty
          "sstore-refund-never-enlarges-the-over-estimation-penalty" );
      ( "the penalty redirect to governance (handler.rs:125-131)",
        pin Gas_penalty_split_model.Burn_the_penalty
          "gas-charge-is-exactly-redistributed-never-burned" );
    ]
