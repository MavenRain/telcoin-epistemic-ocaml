(** Proof suite for the OUTPUT_FORWARD_GATE family: the three statements prove
    on the pristine model, the states the two continuity arms and the FIFO
    backlog forbid are unreachable, the situations the statements are about are
    genuinely reachable (so nothing is certified on an empty case), and the
    epistemic conjuncts are contingent rather than collapsed.

    The contingency group is where R2 and R3 are discharged:
    - S3 conjunct B asserts a POSITIVE [K (V1, ..)], so this suite proves the
      knowledge is contingent, that its operand is not rigid over the reachable
      set, and that the forwarder's view class at the operative state is NOT a
      singleton (the hidden unread re-broadcast is the second member).
    - S1 conjunct C asserts an IGNORANCE [~K (V2, ..)], so this suite exhibits
      the witness pair in both directions. *)

open Telcoin_epistemic
open Output_forward_gate_model

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
        (st.Output_forward_gate_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Output_forward_gate_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Output_forward_gate_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* The pristine reachable count is exactly 48: two hidden-ring worlds over the
   pipeline (commit position x watermark x the one received message x the
   engine's two-slot backlog x execution order), with the stale-skip and the
   lagged-jump branches. The stated bound is the product ceiling this family
   promised. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        ("reachable count " ^ Int.to_string (Checker.reachable_count sys)
       ^ " <= 50")
        true
        (Checker.reachable_count sys <= 50))

(* Pinned exactly, so a model edit that silently changes the graph is caught. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 48
        (Checker.reachable_count sys))

(* The [Stale] arm's invariant (run_epoch.rs:575-583): no number at or below
   the watermark is ever handed to the engine on the live path. *)
let stale_forward_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF stale_forwarded" false
        (Checker.satisfiable sys (f Stale_forwarded)))

(* The consequence that matters (payload_builder.rs:30): no output is executed,
   and so leader-counted, twice. *)
let double_execution_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF double_executed" false
        (Checker.satisfiable sys (f Double_executed)))

(* The [Gap] arm's invariant (run_epoch.rs:584-591): no number above
   watermark + 1 is ever handed to the engine. *)
let gap_forward_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF gap_forwarded" false
        (Checker.satisfiable sys (f Gap_forwarded)))

(* The consequence: the executed chain never skips a committed consensus
   number that is not merely waiting in the engine's backlog. *)
let execution_hole_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF exec_hole" false
        (Checker.satisfiable sys (f Exec_hole)))

(* The FIFO invariant (engine/lib.rs:124, :249): first executions happen in
   consensus-number order. *)
let overtaking_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF exec_out_of_order" false
        (Checker.satisfiable sys (f Exec_out_of_order)))

(* The situation S1 is about is real: a re-broadcast of an already-forwarded
   output really does reach the live loop and really is skipped. If this were
   unreachable, S1 would be a statement about nothing. *)
let stale_skip_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF stale_skipped" true
        (Checker.satisfiable sys (f Stale_skipped)))

(* The situation S2 is about is real: the silent broadcast lag (sync.rs:205-217)
   really does put a number above watermark + 1 in the forwarder's hand. *)
let gap_delivery_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF gap_pending" true
        (Checker.satisfiable sys (f Gap_pending)))

(* And the halt it forces really happens - S2 conjunct A is not vacuously true
   for want of an [Errored] state. *)
let epoch_halt_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF epoch_errored" true
        (Checker.satisfiable sys (f Epoch_errored)))

(* The operative state of S3 conjunct B is real: the forwarder really does end
   up holding an execution receipt naming output 2. *)
let receipt_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF receipt_2" true
        (Checker.satisfiable sys (f Receipt_2)))

(* R2, contingency: the forwarder's knowledge in S3 conjunct B is not collapsed
   - there are reachable states at which it does NOT hold. *)
let k_receipt_prefix_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1 (forwarded_1 -> executed_1)" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 ( Validator.V1,
                   Formula.Implies (f Forwarded_1, f Executed_1) )))))

(* R2, non-rigidity: the K operand itself is false somewhere reachable (an
   output sitting in the engine's backlog, forwarded but not yet executed), so
   the knowledge claim is not true for structural reasons. *)
let prefix_operand_not_rigid () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~(forwarded_1 -> executed_1)" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.Implies (f Forwarded_1, f Executed_1)))))

(* R2, non-singleton view class: at an operative state where no re-broadcast is
   buffered, the forwarder cannot rule out that one IS buffered - which is only
   possible if a second reachable state shares its view there. This is the test
   the 21 -> 63 round shipped without three times. *)
let receipt_view_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (receipt_2 /\\ ~rebroadcast_unread /\\ ~K_v1 ~rebroadcast_unread)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Receipt_2, Formula.Not (f Rebroadcast_unread)),
                Formula.Not
                  (Formula.K
                     (Validator.V1, Formula.Not (f Rebroadcast_unread))) ))))

(* R3 ignorance witness for S1 conjunct C, positive direction: the forwarder has
   skipped a re-delivery and the engine cannot tell. The witness pair is that
   state and the state with the identical backlog and [parent_header] in the
   world where nothing was ever re-broadcast. *)
let engine_cannot_see_the_skip () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (stale_skipped /\\ ~K_v2 stale_skipped)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Stale_skipped,
                Formula.Not (Formula.K (Validator.V2, f Stale_skipped)) ))))

(* R3 ignorance witness, negative direction: the same pair read the other way -
   with nothing skipped, the engine cannot rule out that the forwarder skipped
   something. Its whole memory is [queued] plus [parent_header]
   (engine/lib.rs:49-80), and neither records what upstream dropped. *)
let engine_cannot_rule_out_a_skip () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (~stale_skipped /\\ ~K_v2 ~stale_skipped)" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.Not (f Stale_skipped),
                Formula.Not
                  (Formula.K (Validator.V2, Formula.Not (f Stale_skipped))) ))))

let () =
  Alcotest.run "output_forward_gate"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Output_forward_gate_statements.name `Quick
              (prove_one st))
          Output_forward_gate_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "stale-forward-unreachable" `Quick
            stale_forward_unreachable;
          Alcotest.test_case "double-execution-unreachable" `Quick
            double_execution_unreachable;
          Alcotest.test_case "gap-forward-unreachable" `Quick
            gap_forward_unreachable;
          Alcotest.test_case "execution-hole-unreachable" `Quick
            execution_hole_unreachable;
          Alcotest.test_case "overtaking-unreachable" `Quick
            overtaking_unreachable;
          Alcotest.test_case "stale-skip-reachable" `Quick stale_skip_reachable;
          Alcotest.test_case "gap-delivery-reachable" `Quick
            gap_delivery_reachable;
          Alcotest.test_case "epoch-halt-reachable" `Quick epoch_halt_reachable;
          Alcotest.test_case "receipt-reachable" `Quick receipt_reachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-receipt-prefix-contingent" `Quick
            k_receipt_prefix_contingent;
          Alcotest.test_case "prefix-operand-not-rigid" `Quick
            prefix_operand_not_rigid;
          Alcotest.test_case "receipt-view-class-not-singleton" `Quick
            receipt_view_class_not_singleton;
          Alcotest.test_case "engine-cannot-see-the-skip" `Quick
            engine_cannot_see_the_skip;
          Alcotest.test_case "engine-cannot-rule-out-a-skip" `Quick
            engine_cannot_rule_out_a_skip;
        ] );
    ]
