(** The CERT_ENVELOPE family (S1 base fee, S2 recovery-safe execution, S3
    nonempty remote payload) proves on the pristine {!Cert_envelope_model}
    through [prove_nonvacuous] (so each antecedent is also checked reachable),
    the reachable graph stays in its justified band, and the epistemic layer is
    genuinely partial-information.

    What this suite guards, beyond the three proofs:
    - SANITY: each of the three [validate_batch] gates really excludes its bad
      content from V1's accepted set, while that content is still REACHABLE (it
      shows up rejected), so the exclusion is the gate's doing and not an
      omission from the model;
    - NON-RIGIDITY: the three bad outcomes each K operand denies -
      off-epoch executed fee, a halted engine, an empty held payload - are all
      reachable in the UNMUTATED model through the ungated ingresses, so no
      operand is true for structural reasons (R1);
    - CONTINGENCY (R2): every positive [K] has a reachable state where it
      fails, and every positive [K]'s operative view class is proved
      NON-SINGLETON by exhibiting an atom the knower cannot rule out;
    - IGNORANCE (R3): each [~K] conjunct has its colliding pair witnessed;
    - LIVENESS HONESTY (R8): [AF (executed_2(D) \/ aborted_2(D))] is refutable,
      so S2's resolution conjunct is not rigid;
    - FAITHFULNESS OF THE FAILURE BRANCH (R5): the content-independent abort is
      really reachable, and the STRONGER unqualified form of S2 conjunct (c) -
      "a committed accepted batch inevitably becomes a block" - is asserted to
      be FALSE on this model, which is the regression guard for the defect this
      revision repairs. Nothing may quietly restore it. *)

open Telcoin_epistemic
open Cert_envelope_model

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
        (st.Cert_envelope_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Cert_envelope_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Cert_envelope_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 5 envelope values (Unauthored plus 4 contents) x 3 v1
   values x 5 v2 values x 2 cert values = 150. The pristine reachable set is
   exactly 49 = 1 root + 4 contents x 2 reachable v1 values (Unseen and the ONE
   verdict the gates dictate) x 6 reachable (v2, cert) pairs [(Idle,Pending)
   (Holds,Pending) (Idle,Committed) (Holds,Committed) (Executed|Halted,
   Committed) (Aborted,Committed)]. Every mutation flips WHICH verdict a content
   resolves to and so also reaches exactly 49, comfortably inside the ~50-state
   budget of R6. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 150))

(* The exact pristine count, pinned so a silent change to the transition
   relation cannot pass unnoticed. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 49
        (Checker.reachable_count sys))

(* The three gates of [validate_batch] (validator.rs:67, :70, :80): no reachable
   state has V1 accepting a fee-forged, unrecoverable or empty batch. This is
   exactly what each mutation deletes. *)
let gates_exclude_bad_content () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "G (accepted -> ~forged_fee /\\ ~unrecoverable /\\ ~empty)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 ( f V1_accepted,
                   Formula.And
                     ( Formula.Not (f Content_forged_fee),
                       Formula.And
                         ( Formula.Not (f Content_unrecoverable),
                           Formula.Not (f Content_empty) ) ) )))))

(* ... and the exclusion is the GATE's doing, not an omission: each bad content
   is reachable in the model, where it shows up as a rejection. Without this the
   three gate conjuncts would be vacuously true of a model that simply never
   builds a bad batch. *)
let bad_contents_are_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (rejected /\\ forged_fee), (rejected /\\ unrecoverable), (rejected \
         /\\ empty)"
        true
        (Checker.satisfiable sys
           (Formula.And (f V1_rejected, f Content_forged_fee))
        && Checker.satisfiable sys
             (Formula.And (f V1_rejected, f Content_unrecoverable))
        && Checker.satisfiable sys
             (Formula.And (f V1_rejected, f Content_empty))))

(* R1 non-rigidity of all three K operands: the bad outcomes they deny really
   are reachable in the UNMUTATED model, because a batch that V1 never accepted
   still reaches V2 through an ingress that never validates (handler.rs:201-208,
   primary.rs:104-111, batch_fetcher.rs:186-200). Witnesses: (Forged_fee,
   Unseen, Executed, Committed), (Unrecoverable, Unseen, Halted, Committed) and
   (Empty_payload, Unseen, Holds, Pending). *)
let ungated_bad_outcomes_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (executed /\\ off-epoch fee), EF halted, EF empty held payload" true
        (Checker.satisfiable sys
           (Formula.And (f V2_executed, f Exec_fee_off_epoch))
        && Checker.satisfiable sys (f V2_halted)
        && Checker.satisfiable sys (f V2_payload_empty)))

(* R2 contingency, S1 conjunct (b): V1's knowledge that an executing node
   charges the epoch fee is NOT collapsed - it fails at the V1-unseen class,
   which contains (Forged_fee, Unseen, Idle, Pending) from which an off-epoch
   executed block is reachable. *)
let k_uniform_fee_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1 (AG (executed_2 -> ~exec_fee<>f_epoch))" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 ( Validator.V1,
                   Formula.Ag
                     (Formula.Implies
                        (f V2_executed, Formula.Not (f Exec_fee_off_epoch))) )))))

(* R2 contingency, S2 conjunct (b): V1's knowledge that no remote engine aborts
   in recovery fails at the V1-unseen class, which contains (Unrecoverable,
   Unseen, Idle, Pending) from which the Halted terminal is reachable. *)
let k_no_remote_halt_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1 (AG ~halted_2)" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 (Validator.V1, Formula.Ag (Formula.Not (f V2_halted)))))))

(* R2 contingency, S3 conjunct (b): V1's knowledge that every remote copy is
   nonempty fails at the V1-unseen class, which contains (Empty_payload, Unseen,
   Holds, Pending). *)
let k_nonempty_payload_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1 (AG (holds_2 -> ~payload_empty_2))" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 ( Validator.V1,
                   Formula.Ag
                     (Formula.Implies
                        (f V2_holds, Formula.Not (f V2_payload_empty))) )))))

(* R2 non-singleton view class for S1 conjunct (b), in the STRONG form. The
   naive witness [accepted /\ ~K_v1 ~q] is NOT enough: it is already satisfied
   at a state where q is TRUE (there K trivially fails), so it passes even when
   every class is a singleton. Conjoining [~q] forces the real content - at the
   operative state w1 = (Well_formed, Resolved Accepted, Idle, Pending), where
   executed_2(D) is FALSE, V1 still cannot rule executed_2(D) out, which is
   possible ONLY if the class [View_v1_seen (Accepted, Well_formed)] holds a
   second world: w2 = (Well_formed, Resolved Accepted, Executed, Committed). *)
let class_not_singleton_executed () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (accepted /\\ ~executed_2 /\\ ~K_v1 ~executed_2)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f V1_accepted, Formula.Not (f V2_executed)),
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f V2_executed))) ))))

(* R2 non-singleton view class for S2 conjunct (b), strong form. At w1 =
   (Well_formed, Resolved Accepted, Idle, Pending), where committed(D) is
   FALSE, V1 cannot rule committed(D) out, so the class also holds w3 =
   (Well_formed, Resolved Accepted, Idle, Committed): V1's view carries no cert
   component. *)
let class_not_singleton_committed () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (accepted /\\ ~committed /\\ ~K_v1 ~committed)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f V1_accepted, Formula.Not (f Committed_cert)),
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Committed_cert))) ))))

(* R2 non-singleton view class for S3 conjunct (b), strong form. At w1 =
   (Well_formed, Resolved Accepted, Idle, Pending), where holds_2(D) is FALSE,
   V1 cannot rule holds_2(D) out, so the class also holds w4 = (Well_formed,
   Resolved Accepted, Holds, Pending). *)
let class_not_singleton_holds () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (accepted /\\ ~holds_2 /\\ ~K_v1 ~holds_2)" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f V1_accepted, Formula.Not (f V2_holds)),
                Formula.Not (Formula.K (Validator.V1, Formula.Not (f V2_holds)))
              ))))

(* R3 ignorance witness for S1 conjunct (c), first half, in the STRONG form:
   the operand is conjoined so the ignorance cannot be an artefact of the
   operand being false at the witness. At w2 = (Well_formed, Resolved Accepted,
   Executed, Committed) a remote node HAS executed D, V1 has accepted D, and
   V1 still does not know the execution happened - because w1 = (Well_formed,
   Resolved Accepted, Idle, Pending) shares V1's view and disagrees. The second
   half (~K_v1 ~executed_2) is {!class_not_singleton_executed}, witnessed by
   the same pair evaluated at w1. *)
let ignorance_remote_execution () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (accepted /\\ executed_2 /\\ ~K_v1 executed_2)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f V1_accepted, f V2_executed),
                Formula.Not (Formula.K (Validator.V1, f V2_executed)) ))))

(* R3 ignorance witness for S3 conjunct (c). The pair w4 = (Well_formed,
   Resolved Accepted, Holds, Pending) and w5 = (Well_formed, Unseen, Holds,
   Pending) share V2's view [View_v2_bytes (Holds, Well_formed, Pending)] and
   disagree on accepted_1(D). Conjoining accepted_1(D) into the witness is the
   point: it shows the ignorance is NOT the artefact of accepted_1(D) being
   false throughout the class. *)
let holder_blind_to_validation () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (holds_2 /\\ accepted /\\ ~K_v2 accepted)" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f V2_holds, f V1_accepted),
                Formula.Not (Formula.K (Validator.V2, f V1_accepted)) ))))

(* R8 honesty for S2 conjunct (c): [AF (executed_2 \/ aborted_2)] is NOT rigid.
   The cert self-loop at every Pending state gives an infinite never-committed
   run, so neither disjunct is ever reached there; the resolution conjunct is
   asserted only from a state that already holds the payload of a committed
   certificate, and the mutation that refutes it removes a real gate. *)
let liveness_not_rigid () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~AF (executed_2 \\/ aborted_2)" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.Af (Formula.Or (f V2_executed, f V2_aborted))))))

(* R5 regression guard, the whole point of this revision. The content-
   INDEPENDENT engine failure is really in the model: every fatal exit of
   [execute_consensus_output] other than the recovery abort
   (payload_builder.rs:56-76, :140-142, :167-175, :189-194;
   tn-reth/src/lib.rs:756-761, :797-798, :802-803) is reachable from
   (Holds, Committed) for ANY content, including the well-formed bytes V1
   accepted. *)
let non_recovery_abort_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (accepted_1 /\\ aborted_2)" true
        (Checker.satisfiable sys (Formula.And (f V1_accepted, f V2_aborted))))

(* R5 regression guard, negative half. The STRONGER form this conjunct used to
   assert - AG( (accepted_1 /\ committed) -> AF executed_2 ), "a committed
   accepted batch inevitably becomes a block" - must now be FALSE, because both
   of the things that used to make it true are gone: the abort branch above,
   and the forced delivery that the [Idle] fetch self-loop replaced
   (batch_fetcher.rs:154-210 is an infinite retry whose exhausted-retries error
   is swallowed at :177). If this test ever fails, some edit has quietly
   restored the unfaithful model. *)
let old_unqualified_inevitability_is_false () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "~ valid AG ((accepted_1 /\\ committed) -> AF executed_2)" false
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 ( Formula.And (f V1_accepted, f Committed_cert),
                   Formula.Af (f V2_executed) )))))

(* ... and specifically the delivery half of it: a committed certificate does
   NOT force the remote node into possession, because the fetch loop may retry
   for ever without ever succeeding. *)
let delivery_not_guaranteed () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (committed /\\ ~AF holds_2)" true
        (Checker.satisfiable sys
           (Formula.And (f Committed_cert, Formula.Not (Formula.Af (f V2_holds))))))

let () =
  Alcotest.run "cert_envelope"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Cert_envelope_statements.name `Quick
              (prove_one st))
          Cert_envelope_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact-49" `Quick reachable_exact;
          Alcotest.test_case "gates-exclude-bad-content" `Quick
            gates_exclude_bad_content;
          Alcotest.test_case "bad-contents-are-reachable" `Quick
            bad_contents_are_reachable;
          Alcotest.test_case "ungated-bad-outcomes-reachable" `Quick
            ungated_bad_outcomes_reachable;
          Alcotest.test_case "non-recovery-abort-reachable" `Quick
            non_recovery_abort_reachable;
          Alcotest.test_case "old-unqualified-inevitability-is-false" `Quick
            old_unqualified_inevitability_is_false;
          Alcotest.test_case "delivery-not-guaranteed" `Quick
            delivery_not_guaranteed;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-uniform-fee-contingent" `Quick
            k_uniform_fee_contingent;
          Alcotest.test_case "k-no-remote-halt-contingent" `Quick
            k_no_remote_halt_contingent;
          Alcotest.test_case "k-nonempty-payload-contingent" `Quick
            k_nonempty_payload_contingent;
          Alcotest.test_case "class-not-singleton-executed" `Quick
            class_not_singleton_executed;
          Alcotest.test_case "class-not-singleton-committed" `Quick
            class_not_singleton_committed;
          Alcotest.test_case "class-not-singleton-holds" `Quick
            class_not_singleton_holds;
          Alcotest.test_case "ignorance-remote-execution" `Quick
            ignorance_remote_execution;
          Alcotest.test_case "holder-blind-to-validation" `Quick
            holder_blind_to_validation;
          Alcotest.test_case "liveness-not-rigid" `Quick liveness_not_rigid;
        ] );
    ]
