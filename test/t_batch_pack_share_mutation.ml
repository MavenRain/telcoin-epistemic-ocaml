(** Confirm-by-mutation for BATCH_PACK_SHARE: each statement is pinned to the
    gate it is about, so a statement that would still prove with its gate deleted
    cannot pass unnoticed.

    Every pin asserts BOTH halves - the statement proves on the pristine model and
    refutes under its own mutation - and every statement has its own mutation, so
    a pin can never pass because some other statement in the family flipped.

    - [Break_on_over_budget] (crates/batch-builder/src/batch.rs:80, [continue] ->
      [break]) pins S1. It removes the transitions in which packing resumes past a
      transaction that does not fit, so the fitting transaction of the OTHER
      sender is dropped, and the resulting batch stops being observationally
      identical to a batch that left nothing behind. Within one seal nothing
      repairs it: the loop at batch.rs:71-119 is the only place a transaction is
      appended, [exceeds_gas_limit] (crates/tn-reth/src/txn_pool.rs:331-336) is
      [mark_invalid] on the per-seal iterator and never re-admits anything, the
      byte gate at batch.rs:97-105 is an independent condition rather than a
      second admission route, and the build path's only pool mutation
      ([remove_eip4844_txs], batch.rs:126 -> txn_pool.rs:305-308) is blob-only.
      The next seal does re-read the pool (lib.rs:262-350), which is why S1 is
      about the composition of one sealed batch.
    - [No_per_sender_slot_cap] (crates/tn-reth/src/txn_pool.rs:87,98-99, dropping
      the [pool_config] that carries [max_account_slots = 256] from
      crates/tn-reth/src/lib.rs:333-337) pins S2. It adds the admission
      transitions in which one sender occupies every slot it wants. There is no
      second per-identity bound to repair it: not in the packing loop
      (batch.rs:62-67,108-118), not in a peer's [validate_batch]
      (crates/batch-validator/src/validator.rs:39-82, aggregate bounds only at
      :122-141 and :162-185), not in the gossip ingress (validator.rs:89-106
      routes by sender with no quota), and reth's own network limits are zeroed
      (crates/tn-reth/src/lib.rs:344-392).
    - [No_post_seal_nonce_hint] (crates/batch-builder/src/batch.rs:128-139
      returning an empty [changed_accounts]) pins S3. The mined hashes still reach
      the pool via lib.rs:320-332, so the sender's remainder acquires a perceived
      nonce gap and is demoted - the consequence batch.rs:26-30 documents. The one
      real repair, [process_canon_state_update]
      (crates/tn-reth/src/txn_pool.rs:183-217, [changed_accounts] recomputed from
      COMMITTED state at :191-199), is a full consensus round late; it IS present
      in this model as the step after [Pool_synced], and S3 is scoped to
      [Pool_synced] for exactly that reason. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Batch_pack_share_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Batch_pack_share_model.Checker.make
       (Batch_pack_share_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Batch_pack_share_statements.name name))
    Batch_pack_share_statements.all

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " flips to refuted under the mutation")
            false
            (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false)
               (Batch_pack_share_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Batch_pack_share_model.Pristine (fun sys ->
          Alcotest.(check bool)
            (name ^ " proves on the pristine model")
            true
            (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false)
               (Batch_pack_share_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "batch_pack_share_mutation"
    [
      ( "packing-loop-skips-and-continues",
        pin Batch_pack_share_model.Break_on_over_budget
          "gas-heavy-predecessor-starves-only-its-own-dependents" );
      ( "per-sender-pool-slot-cap",
        pin Batch_pack_share_model.No_per_sender_slot_cap
          "per-sender-slot-cap-bounds-a-share-and-makes-occupancy-peer-inferable"
      );
      ( "post-seal-nonce-hint",
        pin Batch_pack_share_model.No_post_seal_nonce_hint
          "post-seal-nonce-hint-keeps-a-remainder-pending-without-knowing-it-can-pay"
      );
    ]
