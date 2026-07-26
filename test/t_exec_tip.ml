(** The EXEC_TIP family (S1, S2, S3) proves on the pristine {!Exec_tip_model}
    through [prove_nonvacuous] (so each antecedent is also checked reachable),
    the reachable graph stays in its justified band, the invariants the pre-vote
    execution gate enforces are genuinely unreachable-to-violate, and the
    epistemic layer is partial information rather than collapsed knowledge: the
    family's single POSITIVE knowledge conjunct is contingent AND its view class
    is proved non-singleton (R2), and every ignorance conjunct has a reachable
    colliding pair behind it (R3). *)

open Telcoin_epistemic
open Exec_tip_model

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
        (st.Exec_tip_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Exec_tip_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Exec_tip_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 3 author kinds x 3 engine phases x 3 decisions per peer
   x 2 certificate values = 3 * 3^4 * 2 = 486. The pristine reachable set is
   exactly 50: per author kind the reachable (engine, decision) pairs are
   (Queued,Undecided), (Halted,Undecided), (Executed,Undecided) and then either
   (Executed,Voted) (genuine claim) or (Executed,Rejected) (forgery), 4 per peer
   so 16 combinations, plus one Cert state for each of the two genuine-claim
   author kinds: 17 + 17 + 16 = 50. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 486))

(* The exact pristine reachable count, pinned so any drift in the transition
   relation shows up here rather than silently changing what the K operators
   quantify over. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 50
        (Checker.reachable_count sys))

(* The gate's core invariant: a vote is impossible without the voter's OWN
   execution. This is the state handler.rs:639-650 forbids, and the state
   [No_execution_gate] makes reachable. *)
let voted_without_own_execution_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (voted_1 /\\ ~executed_1)" false
        (Checker.satisfiable sys
           (Formula.And (f Voted_1, Formula.Not (f Executed_1)))))

(* The same invariant carried through certification: no certificate exists over
   a header whose second peer signer never executed the output. Together with
   the first-peer form this is the counting content of S2 conjunct A. *)
let cert_without_peer_execution_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (cert_formed /\\ ~executed_2)" false
        (Checker.satisfiable sys
           (Formula.And (f Cert_formed, Formula.Not (f Executed_2)))))

(* The value half of the gate: [contains_execution_hash] (recent_blocks.rs:81-89)
   makes a forged tip terminate [wait_for_execution] with Err, so an honest peer
   never votes for a claim that is not genuine. *)
let voted_for_forged_claim_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (voted_1 /\\ ~claim_genuine)" false
        (Checker.satisfiable sys
           (Formula.And (f Voted_1, Formula.Not (f Claim_genuine)))))

(* R2 contingency, S2 conjunct A - the family's ONLY positive knowledge claim.
   K_V3(executed_1 /\\ executed_2) is not plain truth under V3's partition: at
   every No_cert state V3's view class contains an initial state where e1 is
   still Queued, so the knowledge fails there. *)
let k_v3_quorum_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v3(executed_1 /\\ executed_2): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 (Validator.V3, Formula.And (f Executed_1, f Executed_2))))))

(* R2 non-singleton view class, S2 conjunct A. At the operative state (a
   certificate state) V3 cannot rule out [author_executed], which is only
   possible if its view class holds another world. The two concrete worlds are
   w_A = {author=Honest_executed; e1=Executed; d1=Voted; e2=Executed; d2=Voted;
   cert=Cert} and w_B = the same with author=Byz_replayed: both reachable, both
   with view [View_observer Cert], disagreeing on [author_executed]. The witness
   holds at w_B, where [author_executed] is FALSE yet unruled-out - so the class
   is not a singleton and the positive K is not trivially true. *)
let cert_view_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (cert_formed /\\ ~K_v3(~author_executed)): class has >= 2 worlds"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Cert_formed,
                Formula.Not
                  (Formula.K (Validator.V3, Formula.Not (f Author_executed)))
              ))))

(* R3 ignorance witness, S2 conjunct B (positive direction): at w_A the author
   DID execute, yet V3 - holding only the certificate - cannot know it, because
   w_B shares its view. *)
let cert_author_execution_unknown () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (cert_formed /\\ ~K_v3 author_executed)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Cert_formed,
                Formula.Not (Formula.K (Validator.V3, f Author_executed)) ))))

(* R3 ignorance witness, S1 conjunct B (positive direction). The colliding pair
   is w_A = {author=Honest_executed; e1=Executed; d1=Voted; e2=Queued;
   d2=Undecided; cert=No_cert} and w_B = the same with author=Byz_replayed: both
   reachable, both with view [View_voter (Executed, Voted, No_cert)], and
   [author_executed] true at w_A, false at w_B. *)
let voter_cannot_confirm_author_execution () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (voted_1 /\\ ~K_v1 author_executed)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Voted_1,
                Formula.Not (Formula.K (Validator.V1, f Author_executed)) ))))

(* R3 ignorance witness, S1 conjunct B (negative direction): the same colliding
   pair, read the other way - at w_B the author did NOT execute, and V1 having
   voted still cannot rule the possession in. *)
let voter_cannot_rule_out_author_execution () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (voted_1 /\\ ~K_v1 ~author_executed)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Voted_1,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Author_executed)))
              ))))

(* R3 ignorance witness, S3 conjunct B (positive direction). The colliding pair
   is the initial states u_A = {author=Honest_executed; e1=Queued;
   d1=Undecided; e2=Queued; d2=Undecided; cert=No_cert} and u_F = the same with
   author=Byz_forged: both reachable, both with view
   [View_voter (Queued, Undecided, No_cert)], and [claim_genuine] true at u_A,
   false at u_F. *)
let parked_voter_cannot_confirm_claim () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (parked_1 /\\ ~K_v1 claim_genuine)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Parked_1,
                Formula.Not (Formula.K (Validator.V1, f Claim_genuine)) ))))

(* R3 ignorance witness, S3 conjunct B (negative direction): the same pair read
   the other way - parked on a forged claim, V1 cannot rule the claim out
   either, which is exactly why [vote_inner] parks instead of rejecting. *)
let parked_voter_cannot_rule_out_claim () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (parked_1 /\\ ~K_v1 ~claim_genuine)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Parked_1,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Claim_genuine))) ))))

(* The honest admission behind S3's [halted_1] disjunct: the engine really can
   die on the [?] at engine/lib.rs:264, leaving the vote request parked forever.
   If this were unreachable the [Af] would be a stronger claim than the code
   supports, and stating it would be manufactured liveness. *)
let engine_halt_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF halted_1: the [?] fault outcome is real" true
        (Checker.satisfiable sys (f Halted_1)))

(* The rejection branch is real too: a forged tip at the claimed number
   terminates [wait_for_execution] with Err (consensus_bus.rs:640-647) and
   [vote_inner] answers [UnknownExecutionResult] (handler.rs:649). *)
let rejection_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF rejected_1: the forged-tip branch is real" true
        (Checker.satisfiable sys (f Rejected_1)))

let () =
  Alcotest.run "exec_tip"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Exec_tip_statements.name `Quick (prove_one st))
          Exec_tip_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "voted-without-own-execution-unreachable" `Quick
            voted_without_own_execution_unreachable;
          Alcotest.test_case "cert-without-peer-execution-unreachable" `Quick
            cert_without_peer_execution_unreachable;
          Alcotest.test_case "voted-for-forged-claim-unreachable" `Quick
            voted_for_forged_claim_unreachable;
          Alcotest.test_case "engine-halt-reachable" `Quick engine_halt_reachable;
          Alcotest.test_case "rejection-reachable" `Quick rejection_reachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-v3-quorum-contingent" `Quick
            k_v3_quorum_contingent;
          Alcotest.test_case "cert-view-class-not-singleton" `Quick
            cert_view_class_not_singleton;
          Alcotest.test_case "cert-author-execution-unknown" `Quick
            cert_author_execution_unknown;
          Alcotest.test_case "voter-cannot-confirm-author-execution" `Quick
            voter_cannot_confirm_author_execution;
          Alcotest.test_case "voter-cannot-rule-out-author-execution" `Quick
            voter_cannot_rule_out_author_execution;
          Alcotest.test_case "parked-voter-cannot-confirm-claim" `Quick
            parked_voter_cannot_confirm_claim;
          Alcotest.test_case "parked-voter-cannot-rule-out-claim" `Quick
            parked_voter_cannot_rule_out_claim;
        ] );
    ]
