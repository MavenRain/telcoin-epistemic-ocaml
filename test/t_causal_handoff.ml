(** The CAUSAL_HANDOFF family (S1, S2, S3) proves on the pristine
    {!Causal_handoff_model} through [prove_nonvacuous] (so each antecedent is
    also checked reachable), the reachable graph stays in its justified band,
    the two invariants the release gates enforce are unreachable-by-construction
    rather than merely unasserted, and the epistemic layer is genuinely
    partial-information: the single positive knowledge operand is contingent AND
    its view class is proved non-singleton, and every ignorance conjunct has a
    reachable witness pair. *)

open Telcoin_epistemic
open Causal_handoff_model

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
        (st.Causal_handoff_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Causal_handoff_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Causal_handoff_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 3 horizons x 2 hidden branches x 8 reachable
   (handed, queue, gc-discarded) configurations x 2 target values = 96. The
   pristine reachable set is exactly 50: the arrival configurations exist only
   on the peer-holds branch, the drain configurations only from G1 upward, and
   the target can only be dropped once one of the two exits is open. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 96))

(* The exact pristine count, pinned so that a silent change to the transition
   relation cannot pass unnoticed. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 50
        (Checker.reachable_count sys))

(* What the arrival gate forbids: consensus never raises MissingParent /
   MissingParentRound on the pristine model, so the absorbing shutdown state is
   unreachable. This is exactly what Handoff_push_back makes reachable. *)
let shutdown_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF missing_parent_shutdown" false
        (Checker.satisfiable sys (f Fatal)))

(* What the drain gate forbids: the round-(r0+2) dependent is never handed to
   consensus while the round-(r0+1) certificate it was blocked on is still
   parked. This is exactly what Release_highest_first makes reachable. *)
let child_before_blocker_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (handoff(b) /\\ ~handoff(a))" false
        (Checker.satisfiable sys
           (Formula.And (f Handed_b, Formula.Not (f Handed_a)))))

(* R2, half one - the single positive knowledge operand K_V1(~received(p)) is
   contingent: its complement is reachable, so it is not plain truth under the
   view partition. *)
let k_v1_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1(~received(p)): knowledge did not collapse"
        true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, Formula.Not (f P_received))))))

(* R2, half two - the V1-view class at the operative state is NOT a singleton.
   At a state where the target is armed and the responder has lost the
   certificate, gc_discarded(p) is false, yet V1 does not know it is false: only
   another reachable state sharing V1's view and satisfying gc_discarded(p) can
   make this satisfiable, which is precisely the non-singleton evidence. *)
let k_v1_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (target /\\ ~peer_holds /\\ ~K_v1(~gc_discarded)): class has >= 2 \
         reachable states"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Target_active,
                Formula.And
                  ( Formula.Not (f Peer_holds),
                    Formula.Not
                      (Formula.K (Validator.V1, Formula.Not (f Discarded))) ) ))))

(* The state that makes that class non-singleton in the other direction, and
   that R2 needs to exist at all: the target is still armed AFTER the
   round-(r0+1) certificate has been handed off, because update_targets only
   runs at the next attempt (certificate_fetcher.rs:259-267). *)
let target_survives_the_handoff () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (target /\\ handoff(a))" true
        (Checker.satisfiable sys (Formula.And (f Target_active, f Handed_a))))

(* R3 for S3 conjunct B, first half: a state where the fetcher is chasing a
   certificate it has not received and cannot rule the holder IN. *)
let ignorance_peer_holds () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (target /\\ ~received(p) /\\ ~K_v0(peer_holds))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Target_active,
                Formula.And
                  ( Formula.Not (f P_received),
                    Formula.Not (Formula.K (Validator.V0, f Peer_holds)) ) ))))

(* R3 for S3 conjunct B, second half: the same state cannot rule the holder OUT
   either - the twin in the other hidden branch has an identical V0 view. *)
let ignorance_peer_lost () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (target /\\ ~received(p) /\\ ~K_v0(~peer_holds))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Target_active,
                Formula.And
                  ( Formula.Not (f P_received),
                    Formula.Not
                      (Formula.K (Validator.V0, Formula.Not (f Peer_holds))) ) ))))

(* R3 for S2 conjunct B: after the drain has garbage-collected the blocked key,
   the node still cannot conclude the certificate is gone from the network. *)
let discard_is_not_evidence () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (gc_discarded(p) /\\ ~K_v0(~peer_holds))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Discarded,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Peer_holds))) ))))

let () =
  Alcotest.run "causal_handoff"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Causal_handoff_statements.name `Quick
              (prove_one st))
          Causal_handoff_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "shutdown-unreachable" `Quick shutdown_unreachable;
          Alcotest.test_case "child-before-blocker-unreachable" `Quick
            child_before_blocker_unreachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-v1-contingent" `Quick k_v1_contingent;
          Alcotest.test_case "k-v1-class-not-singleton" `Quick
            k_v1_class_not_singleton;
          Alcotest.test_case "target-survives-the-handoff" `Quick
            target_survives_the_handoff;
          Alcotest.test_case "ignorance-peer-holds" `Quick ignorance_peer_holds;
          Alcotest.test_case "ignorance-peer-lost" `Quick ignorance_peer_lost;
          Alcotest.test_case "discard-is-not-evidence" `Quick
            discard_is_not_evidence;
        ] );
    ]
