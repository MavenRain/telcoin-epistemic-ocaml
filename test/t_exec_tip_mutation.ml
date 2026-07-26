(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    EXEC_TIP family. Two gate deletions, each pinning the statements that
    genuinely depend on it:

    {!Exec_tip_model.No_execution_gate} deletes the pre-vote check
    [wait_for_execution(header.latest_execution_block())] in [vote_inner]
    (handler.rs:639-650), the ONLY pre-vote inspection of that field. With it
    gone [vote_inner] falls through to [Vote::new] (handler.rs:860-872) for
    whatever tip the header carries, so a peer votes from ANY engine phase: the
    unexecuted-yet-voted state appears (refuting S1 conjunct A) and a
    certificate forms over signers that executed nothing (refuting S2 conjunct
    A's positive K). No sibling repairs it - handler.rs:494-505 and :513-565
    only replay a vote [vote_inner] already produced, the equivocation checks at
    :787-855 never look at execution, [Header::validate] (header.rs:97-132) and
    [Certificate::validate_and_verify] (certificate.rs:225-251) never touch
    [latest_execution_block], and the other [wait_for_execution] call sites
    (consensus/state.rs:421-434, state-sync/lib.rs:359-377) run after the vote
    and the certificate against the LOCAL chain only.

    {!Exec_tip_model.No_engine_spawn} deletes the idle-and-non-empty spawn step
    of the engine event loop (engine/lib.rs:227-230), removing BOTH successors
    of a queued output - the drain to [Executed] and the [?] fault at
    engine/lib.rs:264 are the two outcomes of the single task spawned at :229 -
    so every parked vote request becomes terminal, the kernel stutter-closes it
    and S3's [Af] fails at all three initial states. That is a real gate (R8),
    not a sibling: [spawn_execution_task] (engine/lib.rs:116-154) has exactly
    ONE call site, the shutdown and closed-stream branches only return once the
    queue has drained, the consensus-stream arm only enqueues, and the only live
    writer of [RecentBlocks] (node.rs:1298-1322) is fed exclusively by that
    task's completion (payload_builder.rs:186-198 -> tn-reth/lib.rs:946-973).

    Cross-attribution is deliberate: {!Exec_tip_model.No_execution_gate} leaves
    S3 PROVED (decide stays enabled and the parked view class still spans all
    three author worlds), and {!Exec_tip_model.No_engine_spawn} only degrades S1
    and S2 to [Vacuous_antecedent], so they are pinned to the execution gate
    instead. The pristine rows are the matching positive half of each pin. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Exec_tip_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Exec_tip_model.Checker.make (Exec_tip_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Exec_tip_statements.name name))
    Exec_tip_statements.all

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
               (Exec_tip_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Exec_tip_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Exec_tip_statements.prove sys st)))

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
               (Exec_tip_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "exec_tip_mutation"
    [
      ( "dropped pre-vote execution gate kills vote-implies-own-execution",
        pin Exec_tip_model.No_execution_gate
          "vote-implies-own-execution-yet-author-possession-unknown" );
      ( "dropped pre-vote execution gate kills the certified execution quorum",
        pin Exec_tip_model.No_execution_gate
          "certificate-implies-known-honest-execution-quorum" );
      ( "dropped engine spawn step kills parked-request resolution",
        pin Exec_tip_model.No_engine_spawn
          "parked-vote-request-resolves-and-ahead-claim-stays-opaque" );
      ( "cross-attribution: the execution gate is not what carries S3",
        [
          Alcotest.test_case "parked-resolution survives No_execution_gate"
            `Quick
            (survives_under Exec_tip_model.No_execution_gate
               "parked-vote-request-resolves-and-ahead-claim-stays-opaque");
        ] );
    ]
