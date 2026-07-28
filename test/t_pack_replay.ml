(** The PACK_REPLAY family (S1, S2, S3) proves on the pristine
    {!Pack_replay_model} through [prove_nonvacuous] (so each antecedent is also
    checked reachable), the reachable graph stays in its justified band, the
    three invariants the modelled gates enforce are unreachable-by-construction
    rather than merely unasserted, and the epistemic layer is genuinely
    partial-information: both positive knowledge operands are contingent AND
    their view classes are proved non-singleton, and every ignorance conjunct
    has a reachable witness pair in both directions. *)

open Telcoin_epistemic
open Pack_replay_model

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
        (st.Pack_replay_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Pack_replay_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Pack_replay_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** Assert a formula is satisfiable somewhere in the pristine reachable set. *)
let sat_case msg fml () =
  with_sys (fun sys ->
      Alcotest.(check bool) msg true (Checker.satisfiable sys fml))

(** Assert a formula is reachable NOWHERE in the pristine reachable set. *)
let unsat_case msg fml () =
  with_sys (fun sys ->
      Alcotest.(check bool) msg false (Checker.satisfiable sys fml))

(* Loose product bound: 3 pack tips x 3 signed tips x 3 received tips x 3
   execution tips x 3 phases x 2 epoch states = 486. The pristine reachable set
   is exactly 50: [pubd] is pinned to [saved] or one below it (the save and the
   publish of one output are consecutive steps of one function body), [rcvd] is
   capped by [pubd], [exec] is capped by [pubd] while running and by [saved]
   while replaying, [Live] is only entered with [exec = saved], and [closed] is
   determined by [exec = T2]. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 486))

(* The exact pristine count, pinned so that a silent change to the transition
   relation cannot pass unnoticed. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 50
        (Checker.reachable_count sys))

let () =
  Alcotest.run "pack_replay"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Pack_replay_statements.name `Quick
              (prove_one st))
          Pack_replay_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          (* What the save-before-publish ordering forbids: a signed
             ConsensusResult for a number the pack does not hold
             (subscriber.rs:286 before :299-313). This is exactly what
             No_save_before_publish makes reachable. *)
          Alcotest.test_case "signed-unpacked-unreachable" `Quick
            (unsat_case "not EF (signed_result(n1) /\\ ~packed(n1))"
               (Formula.And (f Published_1, Formula.Not (f Saved_1))));
          (* The same ordering seen from the execution side: nothing is ever
             executed that the pack does not already hold, because the broadcast
             for execution (subscriber.rs:317) is downstream of both. *)
          Alcotest.test_case "executed-unpacked-unreachable" `Quick
            (unsat_case "not EF (executed(n1) /\\ ~packed(n1))"
               (Formula.And (f Executed_1, Formula.Not (f Saved_1))));
          (* What the boundary recompute forbids: executing the epoch-closing
             output without concluding the epoch on chain
             (run_epoch.rs:536-539 / :603-604 -> tn-reth/src/evm/block.rs:794).
             This is exactly what No_boundary_recompute makes reachable. *)
          Alcotest.test_case "executed-boundary-without-close-unreachable"
            `Quick
            (unsat_case "not EF (executed(n2) /\\ ~epoch_concluded)"
               (Formula.And (f Executed_2, Formula.Not (f Epoch_concluded))));
          (* What the replay scan forbids: leaving the replay window with a
             committed-but-unexecuted number. This is exactly what
             No_replay_scan makes reachable. *)
          Alcotest.test_case "restart-never-strands-a-packed-number" `Quick
            (unsat_case
               "not EF (restarted /\\ packed(n1) /\\ ~executed(n1) /\\ ~AF \
                executed(n1))"
               (Formula.And
                  ( f Restarted,
                    Formula.And
                      ( f Saved_1,
                        Formula.And
                          ( Formula.Not (f Executed_1),
                            Formula.Not (Formula.Af (f Executed_1)) ) ) )));
        ] );
      ( "contingency",
        [
          (* R2, half one for K_w(packed(n1)): the operand is contingent - the
             peer does NOT know the number is packed at every reachable state,
             so the knowledge did not collapse into plain truth. *)
          Alcotest.test_case "k-w-packed1-contingent" `Quick
            (sat_case "EF ~K_w(packed(n1))"
               (Formula.Not (Formula.K (observer, f Saved_1))));
          (* R2, half two for K_w(packed(n1)): the peer's view class at the
             operative state is NOT a singleton. Where a result for n1 has been
             received but n1 is not executed, the peer still cannot rule
             execution out - only another reachable state sharing its view and
             satisfying executed(n1) makes this satisfiable. *)
          Alcotest.test_case "k-w-packed1-class-not-singleton" `Quick
            (sat_case
               "EF (observed_result(n1) /\\ ~K_w(~executed(n1))): class has >= \
                2 reachable states"
               (Formula.And
                  ( f Received_1,
                    Formula.Not
                      (Formula.K (observer, Formula.Not (f Executed_1))) )));
          (* R2, half one for K_w(packed(n2)). *)
          Alcotest.test_case "k-w-packed2-contingent" `Quick
            (sat_case "EF ~K_w(packed(n2))"
               (Formula.Not (Formula.K (observer, f Saved_2))));
          (* R2, half two for K_w(packed(n2)). *)
          Alcotest.test_case "k-w-packed2-class-not-singleton" `Quick
            (sat_case
               "EF (observed_result(n2) /\\ ~K_w(~executed(n2))): class has >= \
                2 reachable states"
               (Formula.And
                  ( f Received_2,
                    Formula.Not
                      (Formula.K (observer, Formula.Not (f Executed_2))) )));
          (* R3 for S1 conjunct B, first half: a state where the peer holds the
             signature AND the signer has executed the number, yet the peer
             cannot conclude it. *)
          Alcotest.test_case "ignorance-execution-happened" `Quick
            (sat_case
               "EF (observed_result(n1) /\\ executed(n1) /\\ \
                ~K_w(executed(n1)))"
               (Formula.And
                  ( f Received_1,
                    Formula.And
                      ( f Executed_1,
                        Formula.Not (Formula.K (observer, f Executed_1)) ) )));
          (* R3 for S1 conjunct B, second half: the twin with the identical
             received-message set and the execution tip still behind. *)
          Alcotest.test_case "ignorance-execution-not-yet" `Quick
            (sat_case
               "EF (observed_result(n1) /\\ ~executed(n1) /\\ \
                ~K_w(~executed(n1)))"
               (Formula.And
                  ( f Received_1,
                    Formula.And
                      ( Formula.Not (f Executed_1),
                        Formula.Not
                          (Formula.K (observer, Formula.Not (f Executed_1))) )
                  )));
          (* The engine-backlog fact that makes the pair above reachable at all:
             a signer can have signed and gossiped the SECOND output while its
             execution tip is still behind the FIRST
             (engine/src/lib.rs:31-38, :223-230, :245). *)
          Alcotest.test_case "execution-lags-two-signatures" `Quick
            (sat_case "EF (observed_result(n2) /\\ ~executed(n1))"
               (Formula.And (f Received_2, Formula.Not (f Executed_1))));
          (* R3 for S1 conjunct C, first half: the signer has published and the
             peer HAS received, yet the signer cannot conclude delivery -
             gossipsub returns no receipt
             (primary/src/network/mod.rs:440-451). *)
          Alcotest.test_case "ignorance-delivery-happened-n1" `Quick
            (sat_case
               "EF (signed_result(n1) /\\ observed_result(n1) /\\ \
                ~K_v(observed_result(n1)))"
               (Formula.And
                  ( f Published_1,
                    Formula.And
                      ( f Received_1,
                        Formula.Not (Formula.K (signer, f Received_1)) ) )));
          (* R3 for S1 conjunct C, second half: the twin in which delivery has
             not happened, sharing the signer's entire view. *)
          Alcotest.test_case "ignorance-delivery-not-yet-n1" `Quick
            (sat_case
               "EF (signed_result(n1) /\\ ~observed_result(n1) /\\ \
                ~K_v(~observed_result(n1)))"
               (Formula.And
                  ( f Published_1,
                    Formula.And
                      ( Formula.Not (f Received_1),
                        Formula.Not
                          (Formula.K (signer, Formula.Not (f Received_1))) ) )));
          (* R3 for S1 conjunct C at the boundary output, both directions. *)
          Alcotest.test_case "ignorance-delivery-happened-n2" `Quick
            (sat_case
               "EF (signed_result(n2) /\\ observed_result(n2) /\\ \
                ~K_v(observed_result(n2)))"
               (Formula.And
                  ( f Published_2,
                    Formula.And
                      ( f Received_2,
                        Formula.Not (Formula.K (signer, f Received_2)) ) )));
          Alcotest.test_case "ignorance-delivery-not-yet-n2" `Quick
            (sat_case
               "EF (signed_result(n2) /\\ ~observed_result(n2) /\\ \
                ~K_v(~observed_result(n2)))"
               (Formula.And
                  ( f Published_2,
                    Formula.And
                      ( Formula.Not (f Received_2),
                        Formula.Not
                          (Formula.K (signer, Formula.Not (f Received_2))) ) )));
          (* The antecedent of S2/S3 is not a formality: a restart really can
             find the epoch-closing output packed and unexecuted. *)
          Alcotest.test_case "restart-with-boundary-gap-reachable" `Quick
            (sat_case "EF (restarted /\\ packed(n2) /\\ ~executed(n2))"
               (Formula.And
                  ( f Restarted,
                    Formula.And (f Saved_2, Formula.Not (f Executed_2)) )));
        ] );
    ]
