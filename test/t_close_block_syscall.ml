(** Proof suite for the CLOSE_BLOCK_SYSCALL family: the three statements prove
    on the pristine model, the states the close gate and the environment swap
    forbid are unreachable, the situations the statements are about really do
    arise (so nothing is certified on an empty case), and the epistemic
    conjuncts are contingent rather than collapsed.

    The contingency group is where R2 and R3 are discharged:
    - S1 conjunct B asserts a POSITIVE [K (V1, ..)], so this suite proves the
      knowledge is contingent, that its operand is not rigid over the reachable
      set, and that the replay node's view class at the operative state is NOT a
      singleton - the second member is a sealed unmarked block whose user
      transaction was a duplicate-nonce replay, a fact the replay node cannot
      read off the header;
    - S1 conjunct C asserts an IGNORANCE [~K (V1, ..)], so this suite exhibits
      the witness pair in both directions: mid-block, an epoch-closing block and
      an ordinary one are indistinguishable to a node that holds no sealed
      header. *)

open Telcoin_epistemic
open Close_block_syscall_model

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
        (st.Close_block_syscall_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Close_block_syscall_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Close_block_syscall_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* The pristine reachable count is exactly 28: eight initial worlds (context
   kind x contract verdict x transaction body) over a four- or five-stage
   block trace - pre-execution, user transactions, the closing body for a
   marked block, then sealed or halted. The stated bound is the product
   ceiling this family promised. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        ("reachable count "
        ^ Int.to_string (Checker.reachable_count sys)
        ^ " <= 40")
        true
        (Checker.reachable_count sys <= 40))

(* Pinned exactly, so a model edit that silently changes the graph is caught. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 28
        (Checker.reachable_count sys))

(* The close gate's invariant (block.rs:794): no block whose context lacks the
   closing digest ever advances the registry epoch. *)
let unmarked_transition_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (registry_advanced /\\ ~close_marked)" false
        (Checker.satisfiable sys
           (Formula.And
              (f Registry_concluded, Formula.Not (f Close_marked_block)))))

(* The restore swap's invariant, base-fee leg (mod.rs:210): no user transaction
   ever runs against a zeroed block base fee. *)
let user_tx_never_sees_zero_basefee () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (running_user_txs /\\ basefee_env=0)" false
        (Checker.satisfiable sys
           (Formula.And (f Executing_user_txs, f Fee_env_zeroed))))

(* The restore swap's invariant, nonce leg (mod.rs:212): no user transaction
   ever runs with the nonce check disabled. *)
let user_tx_never_sees_disabled_nonce_check () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (running_user_txs /\\ nonce_check_disabled)"
        false
        (Checker.satisfiable sys
           (Formula.And (f Executing_user_txs, f Nonce_check_disabled))))

(* The consequence that matters (handler.rs:162-168): every executed user
   transaction routes the base-fee portion of its fee to the governance sink. *)
let executed_tx_always_pays_the_sink () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (user_tx_executed /\\ ~sink_got_basefee_share)"
        false
        (Checker.satisfiable sys
           (Formula.And
              (f User_tx_executed, Formula.Not (f Sink_got_basefee_share)))))

(* The other consequence (lib.rs:791-795 skips only what revm rejected): a
   duplicate-nonce transaction is never executed. *)
let replay_execution_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF replay_executed" false
        (Checker.satisfiable sys (f Replay_executed)))

(* The situation S1 is about is real: an epoch really does transition. If this
   were unreachable, S1 would be a statement about nothing. *)
let epoch_transition_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF registry_epoch_advanced" true
        (Checker.satisfiable sys (f Registry_concluded)))

(* And the operative state of S1 conjunct B is real: blocks really do seal with
   an unmarked header. *)
let sealed_unmarked_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (sealed /\\ ~close_marked)" true
        (Checker.satisfiable sys
           (Formula.And (f Block_sealed, Formula.Not (f Close_marked_block)))))

(* The situation S2 is about is real: a user transaction really does execute
   inside the modelled block. *)
let user_tx_execution_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF user_tx_executed" true
        (Checker.satisfiable sys (f User_tx_executed)))

(* And the duplicate really is offered - S2 conjunct C is not vacuously true
   for want of a replayed transaction anywhere in the model. *)
let replay_offer_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF replay_offered" true
        (Checker.satisfiable sys (f Replay_offered)))

(* The fail-loud branch of S3 conjunct B is real: a refusing registry really
   does halt block execution (block.rs:215-219). *)
let halt_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF halted" true
        (Checker.satisfiable sys (f Block_halted)))

(* R2, contingency: the replay node's knowledge in S1 conjunct B is not
   collapsed - there are reachable states at which it does NOT hold (a sealed
   MARKED block, and every state before the block seals at all). *)
let k_no_transition_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1 ~registry_epoch_advanced" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 (replay_observer, Formula.Not (f Registry_concluded))))))

(* R2, non-rigidity: the K operand is false somewhere reachable, so the
   knowledge claim is not true for structural reasons. *)
let no_transition_operand_not_rigid () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~(~registry_epoch_advanced)" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.Not (f Registry_concluded)))))

(* R2, non-singleton view class: at a sealed unmarked block whose user
   transaction was fresh, the replay node cannot rule out that the block's
   transaction was a duplicate-nonce replay - which is only possible if a
   second reachable state shares its view there. The header carries no
   transaction body, so it cannot. This is the test the 21 -> 63 round shipped
   without three times. *)
let sealed_unmarked_view_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (sealed /\\ ~close_marked /\\ ~K_v1 ~replay_offered)" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Block_sealed, Formula.Not (f Close_marked_block)),
                Formula.Not
                  (Formula.K (replay_observer, Formula.Not (f Replay_offered)))
              ))))

(* R3 ignorance witness for S1 conjunct C, positive direction: the producer is
   mid-way through an epoch-closing block and the replay node cannot tell. The
   witness pair is that state and the mid-block state of an ordinary block:
   both are [View_replay_waiting] and they disagree on [close_marked]. *)
let replay_node_cannot_see_the_close_mid_block () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (running_user_txs /\\ close_marked /\\ ~K_v1 close_marked)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Executing_user_txs,
                Formula.And
                  ( f Close_marked_block,
                    Formula.Not
                      (Formula.K (replay_observer, f Close_marked_block)) ) ))))

(* R3 ignorance witness, negative direction: the same pair read the other way -
   mid-way through an ordinary block, the replay node cannot rule out that this
   is the epoch-closing one. It holds no header at all until the block seals. *)
let replay_node_cannot_rule_out_a_close_mid_block () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (running_user_txs /\\ ~close_marked /\\ ~K_v1 ~close_marked)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Executing_user_txs,
                Formula.And
                  ( Formula.Not (f Close_marked_block),
                    Formula.Not
                      (Formula.K
                         ( replay_observer,
                           Formula.Not (f Close_marked_block) )) ) ))))

let () =
  Alcotest.run "close_block_syscall"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Close_block_syscall_statements.name `Quick
              (prove_one st))
          Close_block_syscall_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "unmarked-transition-unreachable" `Quick
            unmarked_transition_unreachable;
          Alcotest.test_case "user-tx-never-sees-zero-basefee" `Quick
            user_tx_never_sees_zero_basefee;
          Alcotest.test_case "user-tx-never-sees-disabled-nonce-check" `Quick
            user_tx_never_sees_disabled_nonce_check;
          Alcotest.test_case "executed-tx-always-pays-the-sink" `Quick
            executed_tx_always_pays_the_sink;
          Alcotest.test_case "replay-execution-unreachable" `Quick
            replay_execution_unreachable;
          Alcotest.test_case "epoch-transition-reachable" `Quick
            epoch_transition_reachable;
          Alcotest.test_case "sealed-unmarked-reachable" `Quick
            sealed_unmarked_reachable;
          Alcotest.test_case "user-tx-execution-reachable" `Quick
            user_tx_execution_reachable;
          Alcotest.test_case "replay-offer-reachable" `Quick
            replay_offer_reachable;
          Alcotest.test_case "halt-reachable" `Quick halt_reachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-no-transition-contingent" `Quick
            k_no_transition_contingent;
          Alcotest.test_case "no-transition-operand-not-rigid" `Quick
            no_transition_operand_not_rigid;
          Alcotest.test_case "sealed-unmarked-view-class-not-singleton" `Quick
            sealed_unmarked_view_class_not_singleton;
          Alcotest.test_case "replay-node-cannot-see-the-close-mid-block" `Quick
            replay_node_cannot_see_the_close_mid_block;
          Alcotest.test_case "replay-node-cannot-rule-out-a-close-mid-block"
            `Quick replay_node_cannot_rule_out_a_close_mid_block;
        ] );
    ]
