(** The BATCH_VERDICT family (S1 anti-quorum possession opacity, S2 accepted
    report implies known possession, S3 quorum-rejected implies known permanent
    class but opaque verdict) proves on the pristine {!Batch_verdict_model}
    through [prove_nonvacuous], so every antecedent is also checked reachable.
    The reachable graph stays in its justified band, the three ordering gates
    the model encodes really do forbid the states they claim to forbid, and the
    epistemic layer is genuinely partial-information: both positive knowledge
    operands are contingent AND sit in non-singleton view classes (R2), and
    every ignorance conjunct has a reachable colliding pair (R3). *)

open Telcoin_epistemic
open Batch_verdict_model

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
        (st.Batch_verdict_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Batch_verdict_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Batch_verdict_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The operative window of S1: an anti-quorum verdict reached with V1's leg
    retry-exhausted (quorum_waiter.rs:115, :216-218, then the :241 check). *)
let anti_exhausted_window = Formula.And (f Verdict_anti, f Exhausted_v1)

(* Loose product bound: 9 leg values x 9 leg values x 5 verdicts = 405. The
   pristine reachable set is exactly 47 - 17 Waiting + 17 Timeout + 1 Quorum +
   2 Rejected + 10 Anti - because [Ack_nopossess] and [Rej_transient] are
   mutant-only, the two possession-free exhaustion causes are split across the
   legs by the documented scope cut ([Exh_transport] on leg1, [Exh_nopossess] on
   leg2), leg2 also omits [Rej_unknown], and no leg resolves twice. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 320))

(* The rejection-class gate: [rejected_stake] is incremented only by
   [WaiterError::Rejected] (quorum_waiter.rs:212-215), which [waiter] produces
   only for [NetworkError::RPCError] (:94-100), which [report_batch] produces
   only for a permanent [WorkerResponse::Error] (handle.rs:185) - transient
   responder-side conditions go to [RecoverableError] / [RPCRetryable]
   (message.rs:126-137, handle.rs:186-188). So a [QuorumRejected] state with a
   non-permanent leg is UNREACHABLE pristine; deleting the recoverable arm is
   exactly what makes it reachable. *)
let rejected_never_has_a_transient_leg () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (quorum_rejected /\\ (~permanent(V1) \\/ ~permanent(V2)))" false
        (Checker.satisfiable sys
           (Formula.And
              ( f Verdict_rejected,
                Formula.Or
                  ( Formula.Not (f Permanent_reject_v1),
                    Formula.Not (f Permanent_reject_v2) ) ))))

(* The ack-after-write ordering gate: a peer emits
   [WorkerResponse::ReportBatch] (mod.rs:490-491) only on [Ok(())] from
   [process_report_batch], which returns [Ok] at handler.rs:262 strictly after
   the [NodeBatchesCache] write at :252-254. So an accepted leg without
   possession is UNREACHABLE pristine - the state
   {!Batch_verdict_model.No_peer_store_before_ack} manufactures. *)
let accepted_leg_always_holds () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (accepted(V1) /\\ ~holds(V1))" false
        (Checker.satisfiable sys
           (Formula.And (f Accepted_v1, Formula.Not (f Holds_v1)))))

(* The quorum arithmetic: with [EQUAL_VOTING_POWER] = 1 over 4 authorities the
   threshold is 3 (committee.rs:25, 247-252, 261-263) and the author seeds only
   1 (quorum_waiter.rs:167), so [Ok(())] needs BOTH modeled peers to have
   acked - and each ack implies possession. A quorum state where some peer does
   not hold the batch is therefore unreachable. *)
let quorum_implies_both_peers_hold () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (quorum /\\ (~holds(V1) \\/ ~holds(V2)))" false
        (Checker.satisfiable sys
           (Formula.And
              ( f Verdict_quorum,
                Formula.Or (Formula.Not (f Holds_v1), Formula.Not (f Holds_v2))
              ))))

(* R2 contingency for S2 conjunct B's positive [K_V0(holds(V1))]: its
   complement is reachable, so the knowledge did not collapse into plain truth
   under the view partition. Witness: any state whose leg1 rejected - there
   [holds(V1)] is false throughout V0's class, so [K_V0(holds(V1))] fails. *)
let k_holds_v1_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v0(holds(V1)): knowledge did not collapse"
        true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f Holds_v1)))))

(* R2 non-singleton view class for S2 conjunct B's [K]. Operative state A =
   (leg1 = Ack_possess, leg2 = Exh_nopossess, Waiting), V0-view
   (Saw_accept, Saw_exhausted, Waiting), where [holds(V2)] is FALSE (V2's own
   [store.insert] failed, handler.rs:252-254 -> Internal -> RecoverableError ->
   RPCRetryable -> three retries -> Network). The class also contains world
   B = (leg1 = Ack_possess, leg2 = Exh_possess, Waiting), where V2 DID store
   the row and merely lost all three acks in transport. Both reachable, V0's
   view identical, [holds(V2)] disagreeing - so V0 cannot rule [holds(V2)] out
   at A, which is only possible if the class has a second member. *)
let k_holds_v1_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (accepted(V1) /\\ ~holds(V2) /\\ ~K_v0(~holds(V2)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Accepted_v1,
                Formula.And
                  ( Formula.Not (f Holds_v2),
                    Formula.Not
                      (Formula.K (Validator.V0, Formula.Not (f Holds_v2))) ) ))))

(* R2 contingency for S3 conjunct A's positive
   [K_V0(permanent(V1) /\\ permanent(V2))]: the operand is FALSE at the quorum
   state and at every anti-quorum and timeout state, so the knowledge is
   contingent rather than rigid. *)
let k_permanent_pair_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v0(permanent(V1) /\\ permanent(V2)): knowledge did not collapse"
        true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 ( Validator.V0,
                   Formula.And (f Permanent_reject_v1, f Permanent_reject_v2) )))))

(* R2 non-singleton view class for S3 conjunct A's [K]. Operative state A =
   (leg1 = Rej_verdict, leg2 = Rej_verdict, Rejected), V0-view
   (Saw_reject, Saw_reject, Rejected), where [unknown_requester(V1)] is FALSE.
   The class also contains world B = (leg1 = Rej_unknown, leg2 = Rej_verdict,
   Rejected), where V1's permanent error came from its network layer failing to
   map the requester (consensus.rs:1149, 1174-1177 -> mod.rs:455-456). Both
   reachable and V0-indistinguishable, so V0 cannot rule the unknown-requester
   world out at A. *)
let k_permanent_pair_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (quorum_rejected /\\ ~unknown_requester(V1) /\\ \
         ~K_v0(~unknown_requester(V1)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Verdict_rejected,
                Formula.And
                  ( Formula.Not (f Unknown_requester_v1),
                    Formula.Not
                      (Formula.K
                         (Validator.V0, Formula.Not (f Unknown_requester_v1)))
                  ) ))))

(* R3 ignorance witness for S3 conjunct B, ~K_V0(local_verdict(V1)): the same
   colliding pair (Rej_verdict, Rej_verdict, Rejected) versus (Rej_unknown,
   Rej_verdict, Rejected). The author cannot attribute the rejection to a batch
   verdict, because [WaiterError::Rejected] drops the error string
   (quorum_waiter.rs:99, 212-215). *)
let ignorance_local_verdict () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (quorum_rejected /\\ ~K_v0(local_verdict(V1)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Verdict_rejected,
                Formula.Not (Formula.K (Validator.V0, f Local_verdict_v1)) ))))

(* R3 ignorance witness for S1 conjunct 1, ~K_V0(holds(V1)): colliding pair
   (Exh_possess, Rej_verdict, Anti) - V1 wrote its row and lost all three acks
   in transport - versus (Exh_transport, Rej_verdict, Anti) - the report never
   got a response out of V1 at all, so handle.rs:175-176 propagated a
   non-[RPCError] [NetworkError] with [?] and the catch-all arm at
   quorum_waiter.rs:101-115 exhausted, with the peer holding nothing. Both
   reachable, both projecting to V0-view (Saw_exhausted, Saw_reject, Anti). *)
let ignorance_anti_holds () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (anti_quorum /\\ exhausted(V1) /\\ ~K_v0(holds(V1)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( anti_exhausted_window,
                Formula.Not (Formula.K (Validator.V0, f Holds_v1)) ))))

(* R3 ignorance witness for S1 conjunct 2, ~K_V0(~holds(V1)): the same pair
   read the other way - the possessing world keeps V0 from ruling possession
   out, which is precisely what [WaiterError::Network(deliver)] carrying only
   the stake (quorum_waiter.rs:115) and the fold discarding the error
   (:216-218) leaves undetermined. *)
let ignorance_anti_not_holds () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (anti_quorum /\\ exhausted(V1) /\\ ~K_v0(~holds(V1)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( anti_exhausted_window,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Holds_v1))) ))))

let () =
  Alcotest.run "batch_verdict"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Batch_verdict_statements.name `Quick
              (prove_one st))
          Batch_verdict_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "rejected-never-has-a-transient-leg" `Quick
            rejected_never_has_a_transient_leg;
          Alcotest.test_case "accepted-leg-always-holds" `Quick
            accepted_leg_always_holds;
          Alcotest.test_case "quorum-implies-both-peers-hold" `Quick
            quorum_implies_both_peers_hold;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-holds-v1-contingent" `Quick k_holds_v1_contingent;
          Alcotest.test_case "k-holds-v1-class-not-singleton" `Quick
            k_holds_v1_class_not_singleton;
          Alcotest.test_case "k-permanent-pair-contingent" `Quick
            k_permanent_pair_contingent;
          Alcotest.test_case "k-permanent-pair-class-not-singleton" `Quick
            k_permanent_pair_class_not_singleton;
          Alcotest.test_case "ignorance-local-verdict" `Quick
            ignorance_local_verdict;
          Alcotest.test_case "ignorance-anti-holds" `Quick ignorance_anti_holds;
          Alcotest.test_case "ignorance-anti-not-holds" `Quick
            ignorance_anti_not_holds;
        ] );
    ]
