(** The BLS_VERIFY_GATE family (S1 fairness, S2 safety, S3 security) proves on
    the pristine {!Bls_verify_gate_model} through [prove_nonvacuous] (so each
    antecedent is also checked reachable), the reachable graph stays in its
    justified band, the three gates' forbidden states are unreachable, and the
    epistemic layer is genuinely partial-information.

    The [contingency] group is where R2 and R3 are discharged:

    - the family's one positive knowledge operand,
      [K (V1, held_sk(signer))], is contingent - V1 is ignorant of custody
      wherever the verdict is not [true];
    - that K's view class at the operative state is NOT a singleton: at an
      accepted frame V1 does not know the key is un-copied, which is only
      possible because a second reachable state shares its view;
    - both ignorance pairs are exhibited: the executing node cannot settle
      exclusivity in either direction, and the receipt observer cannot read the
      verdict off the flat charge in either direction. *)

open Telcoin_epistemic
open Bls_verify_gate_model

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
        (st.Bls_verify_gate_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Bls_verify_gate_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Bls_verify_gate_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The operative state shape of S2's and S3's claims: a settled frame that the
    precompile accepted. *)
let accepted = Formula.And (f Settled_call, f Verdict_is_true)

(* Loose product bound: one call life of three stages over 6 input classes x 2
   custodies x 2 exclusivities = 24 submissions, so at most 1 + 24 + 24 = 49
   states, and every one of them is reachable. The pristine reachable count is
   exactly 49. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 60))

(* S3's gate contract: the trailing pk-validation [true] at
   bls_signature.rs:195 makes a [true] verdict imply that the signer held the
   secret key, so an accepted frame behind which nobody held the key is
   UNREACHABLE pristine. That is exactly what No_pk_validation makes
   reachable. *)
let accepted_implies_possession () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (blsVerify=true /\\ ~held_sk(signer))" false
        (Checker.satisfiable sys
           (Formula.And (f Verdict_is_true, Formula.Not (f Signer_held_key)))))

(* S2's gate contract: the 48/96 length pin at mod.rs:142-144 makes an accepted
   uncompressed encoding UNREACHABLE pristine, so no point pair has two
   accepted byte forms. No_length_gate makes it reachable. *)
let uncompressed_never_accepted () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (bytes=uncompressed(96,192) /\\ blsVerify=true)" false
        (Checker.satisfiable sys
           (Formula.And (f Input_is_uncompressed_pair, f Verdict_is_true))))

(* S1's gate contract: [bls_verify] is total (mod.rs:142-150), so no admitted
   call has a successor that reverts. Err_on_failed_verify makes exactly that
   successor reachable for the undecodable-points class. *)
let admitted_never_reverts () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (admitted(call) /\\ EX ~exit=Ok(bool))" false
        (Checker.satisfiable sys
           (Formula.And
              (f Call_admitted, Formula.Ex (Formula.Not (f Exit_is_value))))))

(* R2, first half. The family's one positive knowledge operand is contingent:
   somewhere reachable V1 does NOT know whether the signer held the key, so the
   K in S3 conjunct A is not collapsed into plain truth under V1's partition. *)
let k_possession_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(held_sk(signer)): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Signer_held_key)))))

(* R2, second half - the NON-SINGLETON VIEW CLASS test. At an accepted frame
   pick [exclusive(sk)], which is false at the [Copied] sibling, and assert V1
   does not know its negation there. That can only hold if a second reachable
   state shares V1's view at the operative state, i.e. the class behind
   K_v1(held_sk(signer)) has at least two members. A singleton class would make
   this false and fail the test, which is the point. *)
let k_possession_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (accepted /\\ ~K_v1(~exclusive(sk))): the V1 class is not a \
         singleton"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( accepted,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Key_is_exclusive)))
              ))))

(* R3 for S3 conjunct B, direction one: at an accepted frame whose key is still
   exclusively held, V1 cannot confirm it - the [Copied] sibling is reachable
   and view-identical. *)
let ignorance_exclusive_holds () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (accepted /\\ exclusive(sk) /\\ ~K_v1(exclusive(sk)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( accepted,
                Formula.And
                  ( f Key_is_exclusive,
                    Formula.Not (Formula.K (Validator.V1, f Key_is_exclusive))
                  ) ))))

(* R3 for S3 conjunct B, direction two: at an accepted frame whose key HAS been
   copied, V1 cannot detect it either. *)
let ignorance_exclusive_fails () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (accepted /\\ ~exclusive(sk) /\\ ~K_v1(~exclusive(sk)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( accepted,
                Formula.And
                  ( Formula.Not (f Key_is_exclusive),
                    Formula.Not
                      (Formula.K
                         (Validator.V1, Formula.Not (f Key_is_exclusive))) ) ))))

(* The evidence that [held_sk(signer)] is not a projection of V1's own view: at
   a settled frame that was REJECTED, a key holder (here a proof over the wrong
   message) and a non-holder produce byte-shape-identical, verdict-identical
   frames, so V1 is ignorant of a fact that is true there. *)
let possession_hidden_at_rejected_frames () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (settled /\\ ~blsVerify=true /\\ held_sk(signer) /\\ \
         ~K_v1(held_sk(signer)))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Settled_call,
                Formula.And
                  ( Formula.Not (f Verdict_is_true),
                    Formula.And
                      ( f Signer_held_key,
                        Formula.Not
                          (Formula.K (Validator.V1, f Signer_held_key)) ) ) ))))

(* R3 for S1 conjunct C, direction one: an accepted frame at the flat charge
   whose verdict the receipt observer cannot read off the price - a
   flat-charged rejected frame is view-identical for V2. *)
let ignorance_price_true () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (settled /\\ gas=150000 /\\ blsVerify=true /\\ \
         ~K_v2(blsVerify=true))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Settled_call,
                Formula.And
                  ( f Charge_is_flat,
                    Formula.And
                      ( f Verdict_is_true,
                        Formula.Not
                          (Formula.K (Validator.V2, f Verdict_is_true)) ) ) ))))

(* R3 for S1 conjunct C, direction two: a REJECTED frame at the flat charge is
   equally opaque - V2 cannot rule the verdict in either. *)
let ignorance_price_false () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (settled /\\ gas=150000 /\\ ~blsVerify=true /\\ \
         ~K_v2(~blsVerify=true))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Settled_call,
                Formula.And
                  ( f Charge_is_flat,
                    Formula.And
                      ( Formula.Not (f Verdict_is_true),
                        Formula.Not
                          (Formula.K
                             (Validator.V2, Formula.Not (f Verdict_is_true)))
                      ) ) ))))

let () =
  Alcotest.run "bls_verify_gate"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Bls_verify_gate_statements.name `Quick
              (prove_one st))
          Bls_verify_gate_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "accepted-implies-possession" `Quick
            accepted_implies_possession;
          Alcotest.test_case "uncompressed-never-accepted" `Quick
            uncompressed_never_accepted;
          Alcotest.test_case "admitted-never-reverts" `Quick
            admitted_never_reverts;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-possession-contingent" `Quick
            k_possession_contingent;
          Alcotest.test_case "k-possession-class-not-singleton" `Quick
            k_possession_class_not_singleton;
          Alcotest.test_case "ignorance-exclusive-holds" `Quick
            ignorance_exclusive_holds;
          Alcotest.test_case "ignorance-exclusive-fails" `Quick
            ignorance_exclusive_fails;
          Alcotest.test_case "possession-hidden-at-rejected-frames" `Quick
            possession_hidden_at_rejected_frames;
          Alcotest.test_case "ignorance-price-true" `Quick ignorance_price_true;
          Alcotest.test_case "ignorance-price-false" `Quick
            ignorance_price_false;
        ] );
    ]
