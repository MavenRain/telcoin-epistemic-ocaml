(** Confirm-by-mutation pins for the PACK_REPLAY family. Three gate deletions,
    one per statement, each asserted in BOTH directions (the statement proves
    pristine and refutes under the mutation) so that a pin cannot pass because
    some OTHER statement of the family flipped.

    - {!Pack_replay_model.No_save_before_publish} deletes
      [save_consensus(output.clone(), consensus_chain).await?;] from
      [handle_consensus_output] (subscriber.rs:286) and leaves the signature and
      [publish_consensus] (:299-313). No sibling repairs it: the shutdown
      drain's own [save_consensus] (:394-397) is a distinct call site but fires
      only for outputs still in [waiting] - outputs that never reached
      [handle_consensus_output] and were therefore never published; the
      follow-path writer [handle_sync_output] (:154) is not spawned for an
      active CVV ([NodeMode::CvvActive => {}], state-sync/src/lib.rs:67-71); and
      restart cannot retro-fill, because [get_missing_consensus] reads the pack
      (state-sync/src/lib.rs:148-182), so a never-written output is simply
      absent from it.

    - {!Pack_replay_model.No_replay_scan} deletes the
      [if last_db_block.number > last_executed_block.number { ... }] gap scan at
      state-sync/src/lib.rs:169-178, so [get_missing_consensus] always returns
      an empty vector. The one genuine sibling scanner,
      [send_leftover_consensus_output_to_engine] Phase 2
      (close_epoch.rs:133-159), reads the in-memory
      [self.last_forwarded_consensus_number] and only runs on a same-process
      non-boundary exit (run_epoch.rs:408-423), so a hard crash removes it; and
      the live forwarder cannot revisit the gap, because its watermark is primed
      from the pack tip at startup (node.rs:824-833) making those numbers
      [OutputContinuity::Stale] (run_epoch.rs:566-583, :866-891) while Bullshark
      reads its restored last-committed rounds from that same pack
      (storage/src/consensus_pack.rs:1196-1213). The last candidate is the
      state-sync FOLLOW loop, which genuinely would re-fetch the hole - it
      starts from [consensus_bus.last_consensus_block]
      (state-sync/src/lib.rs:195-197), i.e. the EXECUTION tip
      (primary/src/consensus_bus.rs:693-703) - but it is spawned only for
      [CvvInactive]/[Observer] (state-sync/src/lib.rs:67-71), and the only
      demotion of a live active CVV, [behind_consensus]
      (primary/src/network/handler.rs:137-213), triggers on a ROUND outside the
      GC window (:175) or an epoch mismatch (:179-191). A skipped number is a
      HOLE, not a lag - the node keeps executing every later output, so its
      round counters stay level (:149-163) - and the demotion never fires. No
      sibling path repairs it.

    - {!Pack_replay_model.No_boundary_recompute} deletes
      [if output.committed_at() >= self.epoch_boundary { output.set_epoch_close();
      }] from [process_output] (run_epoch.rs:536-539). A deserialized output
      cannot supply the flag ([Deserialize] hard-codes [close_epoch: false],
      types/src/primary/output.rs:94-104) and the engine cannot infer it
      (engine/src/payload_builder.rs:84-97 reads only [output.close_epoch()]).
      This mutation DOES have a real sibling and the model carries it: the live
      path calls [set_epoch_close()] itself at run_epoch.rs:603-604 before
      [process_output], so live boundary detection survives the deletion
      untouched. The "live-sibling-still-repairs" group below asserts exactly
      that, which is what makes S3's [restarted] antecedent load-bearing rather
      than decorative. What the deletion does break is the replay path
      (start_epoch.rs:89-96 hands the deserialized output straight to
      [process_output]). The other derivation of the flag,
      [context_for_block] reading a block's 32-byte [extra_data]
      (tn-reth/src/evm/config.rs:150-178), is the RE-execution path for a
      closing block that already exists; under this mutation none is ever
      produced, since production reads [payload.close_epoch] (:180-193).

    ATTRIBUTION NOTE. {!Pack_replay_model.No_save_before_publish} is pinned only
    against S1. It also makes S2 and S3 fail, but by [Vacuous_antecedent] rather
    than refutation: with the save deleted the pack tip never advances, so
    "packed(n) and not executed(n)" is reachable nowhere. Claiming insensitivity
    there would be false, so this file does not. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Pack_replay_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Pack_replay_model.Checker.make (Pack_replay_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Pack_replay_statements.name name))
    Pack_replay_statements.all

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
               (Pack_replay_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Pack_replay_model.Pristine (fun sys ->
          Alcotest.(check bool)
            (name ^ " proves on the pristine model")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Pack_replay_statements.prove sys st)))

(** A statement that must be INSENSITIVE to a mutation: the deletion belongs to
    another gate, so attribution stays clean. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " is untouched by this unrelated deletion")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Pack_replay_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The statements a given deletion must NOT disturb. *)
let insensitive mut names =
  List.map
    (fun n -> Alcotest.test_case (n ^ ":survives") `Quick (survives_under mut n))
    names

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The live boundary path still closes the epoch under
    {!Pack_replay_model.No_boundary_recompute}: [wait_for_epoch_boundary] stamps
    the flag itself at run_epoch.rs:603-604, one frame above the deleted
    recompute. This is the R4 evidence that the modelled sibling is live rather
    than omitted - S3 refutes under this mutation only on the replay path. *)
let live_sibling_still_repairs () =
  with_mut Pack_replay_model.No_boundary_recompute (fun sys ->
      Alcotest.(check bool)
        "AG(~restarted /\\ executed(n2) -> epoch_concluded) still valid" true
        (Pack_replay_model.Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 ( Formula.And (Formula.Not (f Pack_replay_model.Restarted),
                     f Pack_replay_model.Executed_2),
                   f Pack_replay_model.Epoch_concluded )))))

(** ... and the replay path really is the half that breaks: a restarted node can
    execute the boundary output with the epoch still open. *)
let replay_path_is_the_break () =
  with_mut Pack_replay_model.No_boundary_recompute (fun sys ->
      Alcotest.(check bool)
        "EF (restarted /\\ executed(n2) /\\ ~epoch_concluded)" true
        (Pack_replay_model.Checker.satisfiable sys
           (Formula.And
              ( f Pack_replay_model.Restarted,
                Formula.And
                  ( f Pack_replay_model.Executed_2,
                    Formula.Not (f Pack_replay_model.Epoch_concluded) ) ))))

(** The signed-but-unpacked state {!Pack_replay_model.No_save_before_publish}
    creates, asserted directly: without it the pin above could in principle be
    passing for an unrelated reason. *)
let deleted_save_strands_a_signature () =
  with_mut Pack_replay_model.No_save_before_publish (fun sys ->
      Alcotest.(check bool)
        "EF (observed_result(n1) /\\ ~packed(n1))" true
        (Pack_replay_model.Checker.satisfiable sys
           (Formula.And
              ( f Pack_replay_model.Received_1,
                Formula.Not (f Pack_replay_model.Saved_1) ))))

(** S1's name. *)
let s1 = "published-consensus-result-implies-persisted-not-executed"

(** S2's name. *)
let s2 = "persisted-unexecuted-output-is-inevitably-executed-after-restart"

(** S3's name. *)
let s3 = "replayed-boundary-output-still-closes-the-epoch"

let () =
  Alcotest.run "pack_replay_mutation"
    [
      ( "save-before-publish",
        pin Pack_replay_model.No_save_before_publish s1
        @ [
            Alcotest.test_case "signature-without-a-pack-entry" `Quick
              deleted_save_strands_a_signature;
          ] );
      ( "restart-replay-scan",
        pin Pack_replay_model.No_replay_scan s2
        @ insensitive Pack_replay_model.No_replay_scan [ s1 ] );
      ( "boundary-flag-recompute",
        pin Pack_replay_model.No_boundary_recompute s3
        @ insensitive Pack_replay_model.No_boundary_recompute [ s1; s2 ] );
      ( "live-sibling-still-repairs",
        [
          Alcotest.test_case "live-boundary-unaffected" `Quick
            live_sibling_still_repairs;
          Alcotest.test_case "replay-boundary-broken" `Quick
            replay_path_is_the_break;
        ] );
    ]
