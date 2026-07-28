(** Proof suite for the GAS-PENALTY-SPLIT family: the three statements prove
    on the pristine model, the model stays small, the two invariants the
    penalty gates enforce are genuinely unreachable violations, and - the
    part that matters - every epistemic conjunct is discharged as
    non-degenerate.

    The contingency group is where R2 and R3 are paid for:
    - S1's positive [K_V0 (AG ~penalty_a>0)] is contingent (its negation is
      satisfiable somewhere reachable) and its view class at the operative
      state is NOT a singleton (at an admitted small-limit batch the
      validator does not know whether the batch spends at least 10% of its
      limit, which is only possible if another reachable state shares its
      admission record);
    - S1's ignorance at large declared limits has a concrete witness pair -
      one big-limit batch from which a penalty is reachable, one that is
      never penalised - and both live in the same [Admission_record Lc_big]
      class;
    - S2's two ignorance conjuncts have the same shape over the EVM refund. *)

open Telcoin_epistemic
open Gas_penalty_split_model

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
        (st.Gas_penalty_split_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Gas_penalty_split_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Gas_penalty_split_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The operand of the family's single positive K: "twin [a] is never
    charged a penalty on any future of this state". *)
let never_penalised = Formula.Ag (Formula.Not (f Penalty_charged_a))

(** Exactly 27 reachable states pristine: 1 proposed + 13 admitted
    (the canonical system-call path plus 2 limit classes x 3 usage classes
    x 2 refund choices) + the 13 executed states they settle into. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable states in bound (actual " ^ Int.to_string n ^ ")")
        true
        (1 <= n && n <= 32))

(** Gate one (utils.rs:47-49) is absolute: no execution of a batch
    declaring at most 210,000 gas ever reaches a penalised state. *)
let small_limit_never_penalised () =
  with_sys (fun sys ->
      Alcotest.(check bool) "no reachable small-limit penalty" false
        (Checker.satisfiable sys
           (Formula.conj
              [ f Executed_user; f Small_limit; f Penalty_charged_a ])))

(** The accounting identity has no reachable counterexample: no state
    credits more or less than was debited (handler.rs:112-113, :121, :130,
    :156-160, :165-168). *)
let never_burns_or_mints () =
  with_sys (fun sys ->
      Alcotest.(check bool) "no reachable non-conserving state" false
        (Checker.satisfiable sys (Formula.Not (f Conserved))))

(** R2 half one, S1's positive K: the knowledge is contingent, not
    collapsed - somewhere reachable the validator does NOT know the batch
    escapes the penalty. *)
let k_never_penalised_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v0(AG ~penalty_a): the knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, never_penalised)))))

(** R2 half two, S1's positive K: at the operative state - an admitted
    small-limit batch - the validator does not know that the batch spends
    less than 10% of its limit. That is only possible if another reachable
    state shares its [Admission_record Lc_small] view and does spend at
    least 10%, so the view class there is not a singleton and the
    knowledge asserted at it is not trivially true. *)
let operative_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (admitted /\\ small-limit /\\ ~K_v0(~spent_a>=10%))" true
        (Checker.satisfiable sys
           (Formula.conj
              [ f Admitted_user; f Small_limit;
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Efficient_a))) ])))

(** R3 witness A for S1's ignorance conjunct: a big-limit state from which
    a penalty IS reachable (5% or 1% of a 420,000 limit). *)
let big_limit_penalty_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (big-limit /\\ EF penalty_a)" true
        (Checker.satisfiable sys
           (Formula.And (f Big_limit, Formula.Ef (f Penalty_charged_a)))))

(** R3 witness B for S1's ignorance conjunct: a big-limit state that is
    never penalised (10% of the limit really spent). Same
    [Admission_record Lc_big] view as witness A, opposite truth value for
    the K operand - which is exactly why K_V0 fails there. *)
let big_limit_penalty_free_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (big-limit /\\ AG ~penalty_a)" true
        (Checker.satisfiable sys (Formula.And (f Big_limit, never_penalised))))

(** R3 witness pair for S2's ignorance conjuncts, refund side: an admitted
    batch whose twin [a] earns an EVM refund. *)
let admitted_refund_witness () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (admitted /\\ small-limit /\\ evm-refund_a>0)"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [ f Admitted_user; f Small_limit; f Refund_earned_a ])))

(** R3 witness pair for S2's ignorance conjuncts, no-refund side: the same
    admission record, no EVM refund. The two states are indistinguishable
    to V0, which is what makes both [~K_V0(evm-refund_a>0)] and
    [~K_V0(~evm-refund_a>0)] hold at each of them. *)
let admitted_no_refund_witness () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (admitted /\\ small-limit /\\ ~evm-refund_a>0)" true
        (Checker.satisfiable sys
           (Formula.conj
              [ f Admitted_user; f Small_limit;
                Formula.Not (f Refund_earned_a) ])))

let () =
  Alcotest.run "gas_penalty_split"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Gas_penalty_split_statements.name `Quick
              (prove_one st))
          Gas_penalty_split_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "small-limit-never-penalised" `Quick
            small_limit_never_penalised;
          Alcotest.test_case "never-burns-or-mints" `Quick never_burns_or_mints;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-never-penalised-contingent" `Quick
            k_never_penalised_contingent;
          Alcotest.test_case "operative-class-not-singleton" `Quick
            operative_class_not_singleton;
          Alcotest.test_case "big-limit-penalty-reachable" `Quick
            big_limit_penalty_reachable;
          Alcotest.test_case "big-limit-penalty-free-reachable" `Quick
            big_limit_penalty_free_reachable;
          Alcotest.test_case "admitted-refund-witness" `Quick
            admitted_refund_witness;
          Alcotest.test_case "admitted-no-refund-witness" `Quick
            admitted_no_refund_witness;
        ] );
    ]
