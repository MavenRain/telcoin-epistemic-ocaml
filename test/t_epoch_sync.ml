(** The EPOCH_SYNC family (S1, S2, S3) proves on the pristine
    {!Epoch_sync_model} through [prove_nonvacuous] (so each antecedent is also
    checked reachable), the reachable graph stays in its justified band, the
    three states the adoption gate forbids are unreachable, and the epistemic
    layer is genuinely partial-information: both positive knowledge operands
    are contingent AND sit in a view class with at least two reachable members,
    and the source-blindness ignorance witnesses are reachable in both
    directions. *)

open Telcoin_epistemic
open Epoch_sync_model

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
        (st.Epoch_sync_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Epoch_sync_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Epoch_sync_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 4 phases x 4 response shapes x 3 responder roles x 3
   store values x 2 marked flags = 288. The pristine reachable set is exactly
   13: the initial Wait, six Pending states (three response shapes x two
   responder roles), two Adopted states (the genuine record from either role)
   and four Rejected states (replay and forgery from either role). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 288))

(* The exact pristine reachable count, pinned so that a silent change to the
   transition relation is caught rather than absorbed by the loose band. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 13
        (Checker.reachable_count sys))

(* S1 conjunct B's gate contract: the parent-hash conjunct (epoch.rs:100 as
   consumed at :103) keeps every adopted response one that actually answered
   for the requested epoch - a replay is rejected, never adopted. The
   No_parent_hash_check mutation makes this state reachable. *)
let adopted_always_answers_request () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (adopted /\\ ~served_requested_epoch)" false
        (Checker.satisfiable sys
           (Formula.And (f Phase_adopted, Formula.Not (f Served_requested_epoch)))))

(* S2 conjunct A's gate contract: verify_with_cert (types/primary/epoch.rs:84-88)
   keeps every record that lands in the DB quorum-certified. The
   No_cert_quorum_check mutation makes a stored-but-uncertified record
   reachable. *)
let stored_always_certified () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (holds_record /\\ ~quorum_certified(stored))"
        false
        (Checker.satisfiable sys
           (Formula.And
              (f Holds_epoch_record, Formula.Not (f Stored_quorum_certified)))))

(* S1 conjunct A's gate contract: result_epoch never advances (epoch.rs:115)
   without an entry really landing under key e. The idempotent no-op of
   save_record (epoch_records.rs:570-576) makes this the observable break under
   No_parent_hash_check. *)
let marked_implies_stored () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (marked_synced /\\ ~holds_record)" false
        (Checker.satisfiable sys
           (Formula.And
              (f Marked_epoch_synced, Formula.Not (f Holds_epoch_record)))))

(* R2 contingency, S1 conjunct B: K_V1(served_requested_epoch) has NOT
   collapsed - the operand's negation is reachable, witnessed at the
   Pending/replay and Rejected/replay states, where an older certified record
   really did arrive in answer to a request naming e. *)
let k_served_requested_epoch_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(served_requested_epoch): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Served_requested_epoch)))))

(* R2 contingency, S2 conjunct B: K_V1(quorum_certified(response)) has NOT
   collapsed - witnessed at the Pending/forged and Rejected/forged states,
   where a record whose parent hash and committee field are both correct (both
   public) arrives with a certificate no quorum signed. *)
let k_response_quorum_certified_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(quorum_certified(response)): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K (Validator.V1, f Response_quorum_certified)))))

(* R2 non-singleton view class, shared by BOTH positive K conjuncts (S1 B and
   S2 B), whose operative state is the same Adopted state. Take q =
   source_in_committee, which is FALSE at
   w2 = {Adopted; R_genuine; Src_observer; Store_genuine; marked}; the class
   also contains w1 = {Adopted; R_genuine; Src_committee; Store_genuine;
   marked}, where q is TRUE. If the class were a singleton, V1 could rule q out
   at w2; it cannot, so the class has at least two reachable members and
   neither K is trivially true. *)
let adopted_view_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (adopted /\\ ~K_v1(~source_in_committee)): class has >= 2 worlds"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Phase_adopted,
                Formula.Not
                  (Formula.K
                     (Validator.V1, Formula.Not (f Source_is_committee))) ))))

(* R3 ignorance witness for S3 conjunct A: at w2 (Adopted from Src_observer)
   V1 cannot confirm a committee source, because w1 (Adopted from
   Src_committee) shares its view (Adopted, true, true) and disagrees on the
   operand. *)
let ignorance_cannot_confirm_committee_source () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (adopted /\\ ~K_v1(source_in_committee))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Phase_adopted,
                Formula.Not (Formula.K (Validator.V1, f Source_is_committee)) ))))

(* R3 ignorance witness for S3 conjunct B: the SAME colliding pair in the other
   direction - at w1 V1 cannot rule a committee source out either. Shares its
   formula with the non-singleton-class test above by construction: one
   colliding pair discharges both obligations. *)
let ignorance_cannot_rule_out_committee_source () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (adopted /\\ ~K_v1(~source_in_committee))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Phase_adopted,
                Formula.Not
                  (Formula.K
                     (Validator.V1, Formula.Not (f Source_is_committee))) ))))

(* S3 conjunct C's substance: adoption from an unauthenticated non-committee
   observer is genuinely reachable (handler.rs:990-1003 serves any requester),
   so the EF target of the no-penalty conjunct is not vacuous. The
   Committee_targeted_fetch mutation removes exactly this state. *)
let observer_supply_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (adopted /\\ ~source_in_committee)" true
        (Checker.satisfiable sys
           (Formula.And
              (f Phase_adopted, Formula.Not (f Source_is_committee)))))

(* S3 conjunct C's antecedent: a Rejected state really is reachable, so the
   conjunct is not vacuously true - a replay and a forgery both reach it. *)
let rejection_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF rejected(V1,e)" true
        (Checker.satisfiable sys (f Phase_rejected)))

let () =
  Alcotest.run "epoch_sync"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Epoch_sync_statements.name `Quick
              (prove_one st))
          Epoch_sync_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "adopted-always-answers-request" `Quick
            adopted_always_answers_request;
          Alcotest.test_case "stored-always-certified" `Quick
            stored_always_certified;
          Alcotest.test_case "marked-implies-stored" `Quick
            marked_implies_stored;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-served-requested-epoch-contingent" `Quick
            k_served_requested_epoch_contingent;
          Alcotest.test_case "k-response-quorum-certified-contingent" `Quick
            k_response_quorum_certified_contingent;
          Alcotest.test_case "adopted-view-class-not-singleton" `Quick
            adopted_view_class_not_singleton;
          Alcotest.test_case "ignorance-cannot-confirm-committee-source" `Quick
            ignorance_cannot_confirm_committee_source;
          Alcotest.test_case "ignorance-cannot-rule-out-committee-source" `Quick
            ignorance_cannot_rule_out_committee_source;
          Alcotest.test_case "observer-supply-reachable" `Quick
            observer_supply_reachable;
          Alcotest.test_case "rejection-reachable" `Quick rejection_reachable;
        ] );
    ]
