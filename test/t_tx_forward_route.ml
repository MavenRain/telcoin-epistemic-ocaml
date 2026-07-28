(** The TX_FORWARD_ROUTE family (S1 routing partition, S2 forward budget, S3
    endpoint-local non-verdict) proves on the pristine
    {!Tx_forward_route_model} through [prove_nonvacuous], so every antecedent is
    also checked reachable; the reachable graph stays in its justified band; the
    invariants the modelled gates enforce hold and the states they forbid are
    unreachable; and the epistemic layer is genuinely partial-information -
    every positive [K] is contingent AND asserted over a non-singleton view
    class, and every [~K] has a concrete disagreeing witness pair.

    The suite also pins the two places where a weaker statement would have been
    dishonest: S3's [room(other)] guard is shown to be load-bearing (the
    unguarded formula is FALSE here), and the duplication S3's c4 is about is
    shown to be reachable rather than a modelling fiction. *)

open Telcoin_epistemic
open Tx_forward_route_model

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
        (st.Tx_forward_route_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Tx_forward_route_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Tx_forward_route_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 8 endpoint configurations x 3 cursor positions x 5 chain
   positions x 5 budget values = 600 raw. The pristine reachable set is exactly
   46, because each configuration determines its whole pass: the eight passes
   contribute 3, 5, 11, 5, 5, 9, 3 and 5 states. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (Int.equal n 46))

(* The budget gate's contract (forward.rs:148, :194-195): more than
   FORWARD_TX_BUDGET's worth of elapsed round trips can never be charged to one
   transaction. This is the state No_forward_budget makes reachable. *)
let budget_overrun_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (budget>15s on one transaction)" false
        (Checker.satisfiable sys (f Budget_overrun)))

(* The routing gate's contract (forward.rs:142-143, :225-228): while the owning
   slot has a usable provider, no transaction's first attempt goes anywhere
   else. This is the state Round_robin_owner makes reachable. *)
let non_owner_first_contact_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (advertised(owner) /\\ contacted(tx1) /\\ ~first(tx1)=owner)"
        false
        (Checker.satisfiable sys
           (Formula.And
              ( f Owner_advertised,
                Formula.And
                  ( f Tx1_contacted,
                    Formula.Not (f Tx1_first_contact_is_owner) ) ))))

(* The classification gate's contract (forward.rs:165-167, :266-268): the pass
   never records a delivery that no committee validator acknowledged. This is
   the state Timeout_counts_as_delivered makes reachable. *)
let delivery_without_holder_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (delivered(tx1) /\\ ~holds(some,tx1))" false
        (Checker.satisfiable sys
           (Formula.And (f Tx1_delivered, Formula.Not (f Tx1_held_by_some)))))

(* S3's [room(other)] guard is LOAD-BEARING and not decorative: dropping it
   turns c1 into a formula that is FALSE on the pristine model, because the
   All_full pass has a saturated owner, no room anywhere else, and no delivery.
   A statement that omitted the guard would be refuted; one that omitted the
   All_full configuration would be true only by omission (R5). *)
let unguarded_fallthrough_is_false () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "AG (full(owner) -> AF delivered(tx1)) is FALSE without the room guard"
        false
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies (f Owner_pool_full, Formula.Af (f Tx1_delivered))))))

(* The premise of S3's c4: falling through past an owner that silently accepted
   really does place a second copy, so the duplication the owner cannot rule
   out is reachable rather than a modelling fiction. *)
let duplication_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (holds(owner,tx1) /\\ holds(other,tx1))" true
        (Checker.satisfiable sys
           (Formula.And (f Tx1_held_by_owner, f Tx1_held_by_other))))

(* CONTINGENCY, S3 c2b, part 1: the observer's knowledge that some validator
   holds tx1 is contingent, not collapsed - it fails somewhere reachable. *)
let k_observer_delivery_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_observer(holds(some,tx1)): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (observer, f Tx1_held_by_some)))))

(* CONTINGENCY, S3 c2b, part 2 - the R2 NON-SINGLETON obligation. At the
   operative state of c2b (an elapsed owner and a recorded delivery) the atom
   [holds(owner,tx1)] is FALSE in the Owner_silent_lost pass, yet the observer
   does not know it is false. That is only possible if another reachable state
   shares the observer's view and satisfies it - i.e. the class is not a
   singleton. Measured class sizes at the six operative states: 4, 2, 4, 4, 2,
   4. *)
let k_observer_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (elapsed(owner,tx1) /\\ delivered(tx1) /\\ \
         ~K_observer(~holds(owner,tx1)))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Owner_timed_out_tx1, f Tx1_delivered),
                Formula.Not
                  (Formula.K (observer, Formula.Not (f Tx1_held_by_owner))) ))))

(* IGNORANCE WITNESS, S3 c3: the two passes that differ only in whether the
   silent owner kept the transaction are observationally identical, so at a
   delivered state the observer can neither confirm nor rule out that the owner
   holds it. Both halves of the [~K] pair are witnessed. *)
let ignorance_witness_observer () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (elapsed(owner,tx1) /\\ delivered(tx1) /\\ holds(owner,tx1) /\\ \
         ~K_observer(holds(owner,tx1)))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Owner_timed_out_tx1, f Tx1_delivered),
                Formula.And
                  ( f Tx1_held_by_owner,
                    Formula.Not (Formula.K (observer, f Tx1_held_by_owner)) ) ))))

(* IGNORANCE WITNESS, S3 c4: a state where the owning slot holds tx1, nobody
   else does, and the owner cannot rule out that somebody else does - the
   disagreeing partner is the state one step later in the Owner_silent_landed
   pass, where the fallback has also taken a copy and V1's own-pool view is
   unchanged. *)
let ignorance_witness_owning_slot () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (holds(owner,tx1) /\\ ~holds(other,tx1) /\\ \
         ~K_owning_slot(~holds(other,tx1)))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Tx1_held_by_owner,
                Formula.And
                  ( Formula.Not (f Tx1_held_by_other),
                    Formula.Not
                      (Formula.K
                         (owning_slot, Formula.Not (f Tx1_held_by_other))) ) ))))

(* Each statement's antecedent is reachable on the pristine model, so no proof
   below is certified on a false antecedent. *)
let antecedent_reachable st () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        (st.Tx_forward_route_statements.name ^ ": antecedent reachable") true
        (Checker.satisfiable sys st.Tx_forward_route_statements.antecedent))

let () =
  Alcotest.run "tx_forward_route"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Tx_forward_route_statements.name `Quick
              (prove_one st))
          Tx_forward_route_statements.all );
      ( "sanity",
        Alcotest.test_case "reachable-bounded" `Quick reachable_bounded
        :: Alcotest.test_case "budget-overrun-unreachable" `Quick
             budget_overrun_unreachable
        :: Alcotest.test_case "non-owner-first-contact-unreachable" `Quick
             non_owner_first_contact_unreachable
        :: Alcotest.test_case "delivery-without-holder-unreachable" `Quick
             delivery_without_holder_unreachable
        :: List.map
             (fun st ->
               Alcotest.test_case
                 (st.Tx_forward_route_statements.name ^ ":antecedent")
                 `Quick (antecedent_reachable st))
             Tx_forward_route_statements.all );
      ( "contingency",
        [
          Alcotest.test_case "unguarded-fallthrough-is-false" `Quick
            unguarded_fallthrough_is_false;
          Alcotest.test_case "duplication-reachable" `Quick duplication_reachable;
          Alcotest.test_case "k-observer-delivery-contingent" `Quick
            k_observer_delivery_contingent;
          Alcotest.test_case "k-observer-class-not-singleton" `Quick
            k_observer_class_not_singleton;
          Alcotest.test_case "ignorance-witness-observer" `Quick
            ignorance_witness_observer;
          Alcotest.test_case "ignorance-witness-owning-slot" `Quick
            ignorance_witness_owning_slot;
        ] );
    ]
