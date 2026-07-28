(** Confirm-by-mutation for the EXEC_ABSORB family. Three gate deletions, one
    per statement, each accompanied by the cross-attribution cases that show the
    refutation belongs to exactly the gate it names.

    {!Exec_absorb_model.Fatal_on_invalid_tx} deletes the tolerated arm at
    crates/tn-reth/src/lib.rs:787-796 - the [InvalidTx] match arm whose body is
    [warn!(..); continue;] - so a cross-worker duplicate falls through to the
    fatal arm at :797-798 and the whole consensus output becomes unexecutable on
    every honest node at once. That removes the [At_parent -> At_lean] transition
    of a duplicated output and replaces it with [At_parent -> Halted], refuting
    both live conjuncts of S1. No sibling repairs it: nothing deduplicates across
    batches before execution. The engine walks [output.flatten_batches()] with no
    seen-set and hands [&batch.transactions] straight through
    (crates/engine/src/payload_builder.rs:137-184, :167-175); the batch validator
    validates each batch in isolation
    (crates/batch-validator/src/validator.rs:39-82); the pool evicts mined
    transactions only on the canonical-state notification AFTER the output
    commits (crates/tn-reth/src/txn_pool.rs:180-217); and the sender sharding of
    [submit_txn_if_mine] (crates/batch-validator/src/validator.rs:89-106) governs
    the gossip path alone, while crates/tn-reth/src/forward.rs:140-191 re-offers
    a transaction to the next validator on [Disposition::TryNext]. The nearest
    miss is the batch-stream reader's [received_digests] set
    (crates/consensus/worker/src/network/handle.rs:763-768), which rejects a
    repeated batch DIGEST and therefore does nothing about two different batches
    carrying the same transaction - the case
    [test_execution_succeeds_with_duplicate_transactions] builds explicitly
    (crates/engine/tests/it/main.rs:1322-1329).

    {!Exec_absorb_model.No_validation_decode} deletes
    crates/batch-validator/src/validator.rs:70
    ([let decoded_txs = self.decode_transactions(transactions, digest)?;] and its
    uses at :73 and :77), so undecodable bytes pass validation, get stored and
    reported (crates/consensus/worker/src/network/handler.rs:243-260), reach
    consensus, and abort the output at every node in the recovery-phase
    collect-or-abort (crates/tn-reth/src/lib.rs:766-780). That adds the
    [Proposed -> Certified] transition for a garbage batch, refuting both
    conjuncts of S2. No sibling repairs it: the digest check at
    crates/batch-validator/src/validator.rs:42-45 hashes the same opaque bytes,
    [Batch.transactions] is [Vec<Vec<u8>>]
    (crates/types/src/worker/sealed_batch.rs:63-89), the wire codec bounds the
    frame with [max_batch_size(epoch)] and decodes the envelope rather than the
    blobs (crates/consensus/worker/src/network/stream_codec.rs:27-40), and a
    peer's batch never enters the local pool, whose only external ingress is
    crates/tn-reth/src/txn_pool.rs:242-268. The batch-sync stream path is not a
    sibling either: it checks that each batch was requested and that no digest
    repeats (crates/consensus/worker/src/network/handle.rs:730-768) and never
    recovers a signer; and because the deleted line lives inside [validate_batch]
    itself, every call site loses it at once
    (crates/consensus/worker/src/network/handler.rs:245,
    crates/consensus/worker/src/network/primary.rs:108).

    {!Exec_absorb_model.Commit_partial_block} turns the fatal arm at
    crates/tn-reth/src/lib.rs:797-798 into a skip, so a node-local failure
    commits a block that silently omits a transaction its peers included. That
    adds the [At_parent -> At_partial] transition, putting a truncated-block
    world inside V0's view class at the full-block states and refuting S3
    conjunct A. No sibling repairs it: [TNPayload] carries no state root at all
    (crates/tn-reth/src/payload.rs:30-70), [builder.finish(&state_provider)]
    (crates/tn-reth/src/lib.rs:802-803) computes a root with nothing to compare
    it against, [finish_executing_output] (crates/tn-reth/src/lib.rs:923-980)
    writes and notifies without comparing, the assembler passes [state_root],
    [gas_used] and [gas_limit] through unchecked
    (crates/tn-reth/src/evm/block.rs:980-1002), and TN has no reorg path to undo
    crates/tn-reth/src/lib.rs:941-944
    (crates/tn-reth/src/txn_pool.rs:135 [unreachable!("TN reorgs are
    impossible")]).

    Cross-attribution is deliberate and asserted below: each mutation refutes
    exactly one statement and leaves the other two proved, so no pin can pass on
    the strength of some other statement flipping. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Exec_absorb_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Exec_absorb_model.Checker.make (Exec_absorb_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Exec_absorb_statements.name name))
    Exec_absorb_statements.all

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
               (Exec_absorb_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Exec_absorb_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Exec_absorb_statements.prove sys st)))

(** The cross-attribution half: a mutation that is NOT this statement's pin
    leaves it proved, so each refutation above is attributable to exactly the
    gate it names. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " still proves under the unrelated mutation")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Exec_absorb_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The statement names, spelled once. *)
let s1_name = "cross-worker-duplicate-transaction-never-halts-execution"

(** S2's name. *)
let s2_name =
  "certified-batch-decodes-because-validation-and-execution-share-one-recovery"

(** S3's name. *)
let s3_name = "block-level-failure-aborts-the-output-so-nodes-halt-rather-than-fork"

let () =
  Alcotest.run "exec_absorb_mutation"
    [
      ( "dropped tolerated arm makes a cross-worker duplicate fatal",
        pin Exec_absorb_model.Fatal_on_invalid_tx s1_name );
      ( "dropped validation decode gate halts every node on the same output",
        pin Exec_absorb_model.No_validation_decode s2_name );
      ( "committing the partial block forks the chain",
        pin Exec_absorb_model.Commit_partial_block s3_name );
      ( "cross-attribution: each gate refutes exactly its own statement",
        [
          Alcotest.test_case "S1 survives No_validation_decode" `Quick
            (survives_under Exec_absorb_model.No_validation_decode s1_name);
          Alcotest.test_case "S1 survives Commit_partial_block" `Quick
            (survives_under Exec_absorb_model.Commit_partial_block s1_name);
          Alcotest.test_case "S2 survives Fatal_on_invalid_tx" `Quick
            (survives_under Exec_absorb_model.Fatal_on_invalid_tx s2_name);
          Alcotest.test_case "S2 survives Commit_partial_block" `Quick
            (survives_under Exec_absorb_model.Commit_partial_block s2_name);
          Alcotest.test_case "S3 survives Fatal_on_invalid_tx" `Quick
            (survives_under Exec_absorb_model.Fatal_on_invalid_tx s3_name);
          Alcotest.test_case "S3 survives No_validation_decode" `Quick
            (survives_under Exec_absorb_model.No_validation_decode s3_name);
        ] );
    ]
