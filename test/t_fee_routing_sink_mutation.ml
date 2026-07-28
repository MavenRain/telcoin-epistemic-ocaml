(** Confirm-by-mutation for the FEE_ROUTING_SINK family. Each pin asserts BOTH
    halves: the statement proves on the pristine model and refutes under the
    gate deletion. The "attribution" group additionally asserts that every
    statement a mutation is NOT aimed at still proves under it, so no pin can
    pass merely because some other statement in the family flipped.

    The four gate deletions, and why no sibling path in telcoin-network repairs
    any of them:

    - [Basefee_to_producer] deletes the [saturating_sub(basefee)] at
      crates/tn-reth/src/evm/handler.rs:156, so the beneficiary is credited
      [effective_gas_price * gas_used]. The complete set of [incr_balance] sites
      in the handler is handler.rs:121 (caller refund), :127-130 (penalty to the
      sink), :157-160 (this one) and :165-168 (base fee to the sink), and system
      calls are skipped outright (handler.rs:85-87, :145-147), so there is no
      second producer credit to re-split the charge; the producer cannot
      redirect the sink instead, because it is a node-local startup parameter
      (crates/config/src/node.rs:277-278,
      crates/node/src/manager/node.rs:1253-1258,
      crates/tn-reth/src/lib.rs:196-210) carried by no batch or certificate
      field; and it cannot inflate the base fee it is paid on, because every
      voter rejects a batch whose base fee differs from the worker/epoch
      expectation (crates/batch-validator/src/validator.rs:188-195).
    - [Basefee_burned] deletes the sink credit at handler.rs:165-168, the stock
      revm behaviour TN deliberately departs from. The penalty transfer at
      handler.rs:125-131 is a separate [incr_balance] to the same account
      carrying only [effective_gas_price * penalty_gas], so it never re-supplies
      the base-fee leg - which is why {!Fee_routing_sink_model.sink_leg} keeps
      the two legs separately observable instead of collapsing them into one
      balance.
    - [Beneficiary_from_batch_field] replaces the committee lookup at
      crates/consensus/executor/src/subscriber.rs:524 with
      [address: batch.beneficiary]. The whole voter-side check list at
      crates/batch-validator/src/validator.rs:39-82 (digest, worker id, epoch,
      size in bytes, decode/recover, no-4844, total gas, base fee) contains no
      beneficiary check; crates/tn-reth/src/evm/block.rs:983 copies
      [evm_env.block_env.beneficiary()] into the assembled header rather than
      re-deriving it; and the empty-output committee lookup at
      crates/engine/src/payload_builder.rs:104-107 belongs to a disjoint branch
      that executes no transactions.
    - [Mutable_fee_sink] replaces the [OnceLock::set] once-semantics at
      crates/tn-reth/src/lib.rs:207-210 with an unconditional store.
      [basefee_address] occurs only in crates/config/src/node.rs:277-278/366,
      crates/node/src/manager/node.rs:1253-1258,
      crates/telcoin-network-cli/src/genesis/mod.rs:47-53/305/333,
      crates/tn-reth/src/lib.rs:196-210/654-662 and
      crates/tn-reth/src/evm/handler.rs:5/42, so no protocol message can
      re-agree the sink after the deletion. The execution-tip comparison the
      model DOES carry (crates/consensus/primary/src/network/handler.rs:639-650)
      is the one candidate repair, and it is not one: it detects the divergence
      and never restores the previous address. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Fee_routing_sink_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Fee_routing_sink_model.Checker.make
       (Fee_routing_sink_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Fee_routing_sink_statements.name name))
    Fee_routing_sink_statements.all

(** Does the statement prove under this mutation? *)
let verdict mut name k =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          k
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Fee_routing_sink_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  verdict mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " flips to refuted under the mutation")
        false proved)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  verdict Fee_routing_sink_model.Pristine name (fun proved ->
      Alcotest.(check bool) (name ^ " proves on the pristine model") true proved)

(** Attribution: a statement the mutation is not aimed at still proves under
    it, so the pin above cannot be passing for the wrong reason. *)
let survives_under mut label name () =
  verdict mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " is untouched by " ^ label)
        true proved)

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** S1's name. *)
let s1 = "block-producer-take-is-tip-only-basefee-and-penalty-go-to-governance"

(** S2's name. *)
let s2 =
  "block-beneficiary-is-the-certified-author-not-the-batch-self-declared-field"

(** S3's name. *)
let s3 = "fee-sink-is-node-local-immutable-and-peer-opaque-until-tip-comparison"

let () =
  Alcotest.run "fee_routing_sink_mutation"
    [
      ( "basefee-tip-split-gate (handler.rs:156)",
        pin Fee_routing_sink_model.Basefee_to_producer s1 );
      ( "basefee-sink-credit (handler.rs:165-168)",
        pin Fee_routing_sink_model.Basefee_burned s1 );
      ( "committee-beneficiary-lookup (subscriber.rs:524)",
        pin Fee_routing_sink_model.Beneficiary_from_batch_field s2 );
      ( "oncelock-fee-sink (lib.rs:207-210)",
        pin Fee_routing_sink_model.Mutable_fee_sink s3 );
      ( "attribution",
        [
          Alcotest.test_case "basefee-to-producer:s2-survives" `Quick
            (survives_under Fee_routing_sink_model.Basefee_to_producer
               "basefee-to-producer" s2);
          Alcotest.test_case "basefee-to-producer:s3-survives" `Quick
            (survives_under Fee_routing_sink_model.Basefee_to_producer
               "basefee-to-producer" s3);
          Alcotest.test_case "basefee-burned:s2-survives" `Quick
            (survives_under Fee_routing_sink_model.Basefee_burned
               "basefee-burned" s2);
          Alcotest.test_case "basefee-burned:s3-survives" `Quick
            (survives_under Fee_routing_sink_model.Basefee_burned
               "basefee-burned" s3);
          Alcotest.test_case "beneficiary-from-batch-field:s1-survives" `Quick
            (survives_under Fee_routing_sink_model.Beneficiary_from_batch_field
               "beneficiary-from-batch-field" s1);
          Alcotest.test_case "beneficiary-from-batch-field:s3-survives" `Quick
            (survives_under Fee_routing_sink_model.Beneficiary_from_batch_field
               "beneficiary-from-batch-field" s3);
          Alcotest.test_case "mutable-fee-sink:s1-survives" `Quick
            (survives_under Fee_routing_sink_model.Mutable_fee_sink
               "mutable-fee-sink" s1);
          Alcotest.test_case "mutable-fee-sink:s2-survives" `Quick
            (survives_under Fee_routing_sink_model.Mutable_fee_sink
               "mutable-fee-sink" s2);
        ] );
    ]
