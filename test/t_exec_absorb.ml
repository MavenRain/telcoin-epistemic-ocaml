(** The EXEC_ABSORB family (S1, S2, S3) proves on the pristine
    {!Exec_absorb_model} through [prove_nonvacuous] (so every antecedent is also
    checked reachable), the reachable graph stays in its justified band, the
    invariants the two gates enforce are genuinely unreachable-to-violate, and
    the epistemic layer is partial information rather than collapsed knowledge:
    both positive knowledge conjuncts of S3 are contingent AND their view classes
    are proved non-singleton (R2), and the ignorance conjunct has a reachable
    colliding pair behind it (R3). *)

open Telcoin_epistemic
open Exec_absorb_model

(** Build the pristine system or fail the test on an impossible [Empty_init]. *)
let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Checker.Empty_init -> Alcotest.fail "make: empty init")
    (make ())

(** Render a proof error for the assertion message. *)
let error_to_string = function
  | Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Checker.Vacuous_antecedent -> "vacuous antecedent"

(** One proof case: the statement proves on the pristine model. *)
let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Exec_absorb_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Exec_absorb_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Exec_absorb_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** Assert a formula is satisfiable on the pristine reachable set. *)
let sat_case label want formula () =
  with_sys (fun sys ->
      Alcotest.(check bool) label want (Checker.satisfiable sys formula))

(* Loose product bound: 2 byte kinds x 2 overlaps x 3 consensus statuses x 5
   tips per node = 2 * 2 * 3 * 5 * 5 = 300. The pristine reachable set is
   exactly 24: the 4 proposed initial states, the 2 rejected states reached by
   the 2 garbage initials, and for each of the 2 sound initials the 3 x 3 = 9
   combinations of the two nodes' reachable tips (At_parent, Halted, and the
   content tip At_full for Distinct or At_lean for Duplicated). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 300))

(* The exact pristine reachable count, pinned so any drift in the transition
   relation shows up here rather than silently changing what the K operators
   quantify over. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 24
        (Checker.reachable_count sys))

let () =
  Alcotest.run "exec_absorb"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Exec_absorb_statements.name `Quick
              (prove_one st))
          Exec_absorb_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          (* The validation decode gate (validator.rs:69-70): an undecodable
             batch never reaches the executor. This is the state
             [No_validation_decode] makes reachable. *)
          Alcotest.test_case "garbage-batch-never-certified" `Quick
            (sat_case "not EF (bytes_garbage /\\ batch_certified)" false
               (Formula.And (f Bytes_garbage, f Batch_certified)));
          (* ... and the gate is live rather than vacuous: the garbage branch
             genuinely exists and terminates in a refusal. *)
          Alcotest.test_case "garbage-batch-is-rejected" `Quick
            (sat_case "EF (bytes_garbage /\\ batch_rejected)" true
               (Formula.And (f Bytes_garbage, f Batch_rejected)));
          (* The fatal arm (lib.rs:797-798): no node ever commits a silently
             truncated block. This is the state [Commit_partial_block] makes
             reachable. *)
          Alcotest.test_case "no-partial-commit" `Quick
            (sat_case "not EF partial_block_0" false (f Node0_partial_block));
          (* The safety consequence of that arm: no reachable state has one node
             on the full block while its peer holds a block missing a
             transaction. This is the divergence S3 conjunct A rules out. *)
          Alcotest.test_case "no-divergent-pair" `Quick
            (sat_case "not EF (full_block_0 /\\ peer_omits_a_transaction)" false
               (Formula.And (f Node0_full_block, f Peer_omits_a_transaction)));
          (* The tolerated arm (lib.rs:787-796) really drops the duplicate: a
             duplicated output never yields the full block. *)
          Alcotest.test_case "duplicate-yields-the-lean-block" `Quick
            (sat_case "not EF (duplicate_in_output /\\ full_block_0)" false
               (Formula.And (f Duplicate_in_output, f Node0_full_block)));
          (* ... and the lean block is reachable, so S1 conjunct A is about a
             live branch. *)
          Alcotest.test_case "skip-arm-is-live" `Quick
            (sat_case "EF lean_block_0" true (f Node0_lean_block));
        ] );
      ( "contingency",
        [
          (* R2 contingency, S3 conjunct A. [K_V0(~peer_omits_a_transaction)] is
             not plain truth under V0's partition: at any state where V1 holds
             the lean block of a duplicated output the operand is false at the
             state itself, so the knowledge fails there. *)
          Alcotest.test_case "k-no-truncated-peer-block-contingent" `Quick
            (sat_case "EF ~K_v0(~peer_omits_a_transaction)" true
               (Formula.Not
                  (Formula.K
                     (Validator.V0, Formula.Not (f Peer_omits_a_transaction)))));
          (* R2 non-singleton view class, S3 conjunct A. At the operative state
             (V0 on the full block) V0 cannot rule out that its peer halted,
             which is only possible if its view class holds another world. The
             class is {t1 = At_parent, t1 = Halted, t1 = At_full}: three worlds,
             all sharing [View_node (Sound, Distinct, Certified, At_full)]. *)
          Alcotest.test_case "k-no-truncated-peer-block-class-not-singleton"
            `Quick
            (sat_case "EF (full_block_0 /\\ ~K_v0(~halted_1))" true
               (Formula.And
                  ( f Node0_full_block,
                    Formula.Not
                      (Formula.K (Validator.V0, Formula.Not (f Node1_halted)))
                  )));
          (* R2 contingency, S3 conjunct A'. [K_V0(~full_block_1)] fails at every
             distinct-output state where V1 has already committed the full
             block - which is exactly what conjunct B of S3 asserts. *)
          Alcotest.test_case "k-uniform-skip-contingent" `Quick
            (sat_case "EF ~K_v0(~full_block_1)" true
               (Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Node1_full_block)))));
          (* R2 non-singleton view class, S3 conjunct A'. At the operative state
             (V0 on the lean block) V0 cannot rule out that its peer halted, so
             the class {t1 = At_parent, t1 = Halted, t1 = At_lean} is not a
             singleton. *)
          Alcotest.test_case "k-uniform-skip-class-not-singleton" `Quick
            (sat_case "EF (lean_block_0 /\\ ~K_v0(~halted_1))" true
               (Formula.And
                  ( f Node0_lean_block,
                    Formula.Not
                      (Formula.K (Validator.V0, Formula.Not (f Node1_halted)))
                  )));
          (* R3 ignorance witness, S3 conjunct B, positive direction: at s_A the
             peer HAS committed the full block, yet V0 cannot know it because
             s_B (peer still at parent) shares V0's view. *)
          Alcotest.test_case "ignorance-peer-may-not-have-finished" `Quick
            (sat_case "EF (full_block_0 /\\ ~K_v0(full_block_1))" true
               (Formula.And
                  ( f Node0_full_block,
                    Formula.Not (Formula.K (Validator.V0, f Node1_full_block))
                  )));
          (* R3 ignorance witness, S3 conjunct B, negative direction: V0 cannot
             rule the peer's completion out either. *)
          Alcotest.test_case "ignorance-peer-may-have-finished" `Quick
            (sat_case "EF (full_block_0 /\\ ~K_v0(~full_block_1))" true
               (Formula.And
                  ( f Node0_full_block,
                    Formula.Not
                      (Formula.K
                         (Validator.V0, Formula.Not (f Node1_full_block))) )));
          (* The two concrete members of that R3 pair, named as states rather
             than as knowledge: both are reachable and both carry
             [View_node (Sound, Distinct, Certified, At_full)] for V0. *)
          Alcotest.test_case "ignorance-witness-peer-done" `Quick
            (sat_case "EF (full_block_0 /\\ full_block_1)" true
               (Formula.And (f Node0_full_block, f Node1_full_block)));
          Alcotest.test_case "ignorance-witness-peer-pending" `Quick
            (sat_case "EF (full_block_0 /\\ ~full_block_1 /\\ ~halted_1)" true
               (Formula.conj
                  [
                    f Node0_full_block;
                    Formula.Not (f Node1_full_block);
                    Formula.Not (f Node1_halted);
                  ]));
        ] );
    ]
