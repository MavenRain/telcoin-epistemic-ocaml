(** The identity family (DESIGN family IDENTITY #9) proves on the pristine
    {!Identity_model} through [prove_nonvacuous] (so its antecedent is also
    checked reachable), the reachable graph stays in its justified band, and
    the epistemic layer is genuinely partial-information: every positive K
    conjunct is contingent (EF ~K holds, so none has collapsed), and the
    card's false witness - a Cooperate in-flight state where V3's binding is
    signed yet unknown to V0, colliding with the Silent run where it was
    never signed - is reachable, while knowledge is also attainable at
    confirmation. *)

open Telcoin_epistemic
open Identity_model

(** Build the pristine system or fail the test on an impossible
    [Empty_init]. *)
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
        (st.Identity_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Identity_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Identity_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* One initial Propose state plus a 3-way strategy branch (Cooperate /
   Silent / Forge_record) carried deterministically through 4 phases (Vote,
   Certify, Deliver, Done) = 1 + 3*4 = 13 reachable states; 32 leaves slack
   without any hidden blow-up. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 32))

(* Every path delivers the honest committee records: V0 inevitably confirms
   V1's genuine binding (kad delivery consensus.rs:1602-1613). *)
let delivery_reached () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF confirmed_v0(p1 -> V1)" true
        (Checker.valid sys
           (Formula.Af (f (Confirmed (Validator.V0, P1, Validator.V1))))))

(* The pristine signature gate's contract: the forged (V1 @ p3) record is
   NEVER confirmed by an honest node (decode_and_verify consensus.rs:534-535)
   - the conjunct the mutation flips. *)
let gate_drops_forged () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G ~confirmed_v0(p3 -> V1)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Not (f (Confirmed (Validator.V0, P3, Validator.V1)))))))

(* Every positive K_i(op) conjunct appearing in S9: assert EF ~K_i(op) so
   none has collapsed to plain truth (the recurring K-collapse failure mode).
   The in-flight local_empty states - view-equivalent to the initial Propose
   state, whose signed set is empty - witness ~K for every binding. *)
let k_conjuncts =
  List.concat_map
    (fun i ->
      List.map
        (fun (p, v) -> (i, Signed_binding (v, p)))
        Identity_statements.confirm_targets)
    honest

let k_not_collapsed () =
  with_sys (fun sys ->
      List.iter
        (fun (i, op) ->
          Alcotest.(check bool)
            ("EF ~K_" ^ Validator.to_string i ^ "(" ^ atom_to_string op ^ ")")
            true
            (Checker.satisfiable sys (Formula.Not (Formula.K (i, f op)))))
        k_conjuncts)

(* wcheck false witness: a reachable state where V3's (V3, p3) binding IS
   signed (Cooperate branch, record still in flight) yet V0 does not know it
   - the Silent in-flight state shares V0's empty view with the operand
   false, so K_V0 rightly fails at the very state where the operand is
   true. *)
let false_witness_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (signed(V3,p3) /\\ ~K_v0 signed(V3,p3))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f (Signed_binding (Validator.V3, P3)),
                Formula.Not
                  (Formula.K
                     (Validator.V0, f (Signed_binding (Validator.V3, P3)))) ))))

(* The collision partner: the Silent run where V3 never performed the signing
   act, so the (V3, p3) binding is absent - the operand-false side of the
   colliding view that grounds V0's ignorance. *)
let no_signing_collision_partner () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~signed(V3,p3)" true
        (Checker.satisfiable sys
           (Formula.Not (f (Signed_binding (Validator.V3, P3))))))

(* Knowledge is attainable: at Cooperate confirmation V0's view grounds
   knowledge of V3's signed binding, so the ~K in the false witness is
   contingent, not vacuously true everywhere. *)
let knowledge_attainable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF K_v0 signed(V3,p3)" true
        (Checker.satisfiable sys
           (Formula.K (Validator.V0, f (Signed_binding (Validator.V3, P3))))))

let () =
  Alcotest.run "identity"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Identity_statements.name `Quick (prove_one st))
          Identity_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "delivery-reached" `Quick delivery_reached;
          Alcotest.test_case "gate-drops-forged" `Quick gate_drops_forged;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-not-collapsed" `Quick k_not_collapsed;
          Alcotest.test_case "false-witness-reachable" `Quick
            false_witness_reachable;
          Alcotest.test_case "no-signing-collision-partner" `Quick
            no_signing_collision_partner;
          Alcotest.test_case "knowledge-attainable" `Quick knowledge_attainable;
        ] );
    ]
