(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    EPOCH_REWARD family: each statement is pinned by exactly the gate it depends
    on, and each row asserts the proof FLIPS to an error on the mutated model
    while the pristine half still proves.

    - {!Epoch_reward_model.Credit_after_skip} moves
      [inc_leader_count] (payload_builder.rs:30) BELOW the batch-less non-closing
      early return (:84-97), so the skipped round earns nothing and S1's
      credit-precedes-skip conjunct fails at its still-reachable antecedent. No
      sibling repairs it: the only other writer, [count_leaders]
      (consensus_pack.rs:1267-1294), walks CONSENSUS headers and therefore
      CONTRADICTS the deletion on a restarted peer rather than repairing it;
      [try_restore_state] (node.rs:1272-1293) reseeds only from EXECUTED blocks,
      and the counter is a bare [HashMap] increment with no dedup
      (gas_accumulator.rs:98-107).
    - {!Epoch_reward_model.No_catchup_watermark} deletes
      [if leader_round > last_executed_round { continue; }]
      (consensus_pack.rs:1287-1289), so the crash-at-P2 rebuild counts the whole
      pack and then replays the epoch-closing output on top: a reachable
      double-credit state and a sealed peer whose ledger differs, refuting S2. No
      sibling repairs it: nothing subtracts or de-duplicates - [clear] runs only
      at the boundary (gas_accumulator.rs:109-113 from run_epoch.rs:658, after
      the seal), replay never subtracts (start_epoch.rs:71-107), and
      [get_missing_consensus] compares CONSENSUS numbers
      (state-sync/lib.rs:169-178) so it cannot see the over-count.
    - {!Epoch_reward_model.Skip_batchless_close} deletes the
      [if !output.close_epoch()] condition (payload_builder.rs:85), so the
      batch-less BOUNDARY output also takes the skip and the epoch never seals,
      refuting S3's [AF sealed] conjunct at its still-reachable antecedent
      (a genuine gate removal, not a manufactured stall: the terminal IS reached,
      just with [sealed = false]). S3's epistemic conjuncts C and D degrade to
      vacuously true there rather than adding a second refutation: with no
      closing block, no [EpochRecord.final_state] commits to a closing execution
      state (close_epoch.rs:236-245), so there is no seal for a peer's epoch vote
      to acknowledge and [saw_peer_vote] stays false. The refutation therefore
      remains attributable to the liveness conjunct alone. No sibling repairs it: no second boundary
      output is ever forwarded (run_epoch.rs:595-612, close_epoch.rs:114-162),
      re-execution's extra_data route (config.rs:150-178) is content-addressed on
      a closing block that now exists nowhere, and the close does not hang
      because [contains_consensus] tracks SKIPPED rounds too
      (recent_blocks.rs:36-60, :91-104).

    S2 is deliberately pinned to the watermark guard rather than to
    {!Epoch_reward_model.Credit_after_skip} (which also refutes it, through a
    different gate), and is NOT paired with
    {!Epoch_reward_model.Skip_batchless_close}, under which its antecedent is
    unreachable and the error would be a [Vacuous_antecedent] artifact rather
    than a real refutation. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Epoch_reward_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Epoch_reward_model.Checker.make (Epoch_reward_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Epoch_reward_statements.name name))
    Epoch_reward_statements.all

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
               (Epoch_reward_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Epoch_reward_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Epoch_reward_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The other half of attributability: a statement the mutation does NOT touch
    still proves under it, so the pinned refutation is not collateral damage. *)
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
               (Epoch_reward_statements.prove sys st)))

let () =
  Alcotest.run "epoch_reward_mutation"
    [
      ( "credit moved below the empty-output skip",
        pin Epoch_reward_model.Credit_after_skip
          "blockless-round-credits-its-leader-with-no-block" );
      ( "dropped catchup watermark guard",
        pin Epoch_reward_model.No_catchup_watermark
          "restart-rebuild-credits-each-committed-round-exactly-once" );
      ( "empty-output skip no longer spares the epoch close",
        pin Epoch_reward_model.Skip_batchless_close
          "batchless-boundary-output-inevitably-seals-the-epoch" );
      ( "attributability: unrelated gates leave the other statements standing",
        [
          Alcotest.test_case "blockless-credit survives no-catchup-watermark"
            `Quick
            (survives_under Epoch_reward_model.No_catchup_watermark
               "blockless-round-credits-its-leader-with-no-block");
          Alcotest.test_case "blockless-credit survives skip-batchless-close"
            `Quick
            (survives_under Epoch_reward_model.Skip_batchless_close
               "blockless-round-credits-its-leader-with-no-block");
          Alcotest.test_case "boundary-seal survives credit-after-skip" `Quick
            (survives_under Epoch_reward_model.Credit_after_skip
               "batchless-boundary-output-inevitably-seals-the-epoch");
          Alcotest.test_case "boundary-seal survives no-catchup-watermark" `Quick
            (survives_under Epoch_reward_model.No_catchup_watermark
               "batchless-boundary-output-inevitably-seals-the-epoch");
        ] );
    ]
