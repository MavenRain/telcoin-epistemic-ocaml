(** Proof suite for the TEL_DISPATCH_SURFACE family: the three statements prove
    on the pristine model, the states the three gates forbid are unreachable, the
    situations the statements are about are genuinely reachable (so nothing is
    certified on an empty case), and the epistemic conjuncts are contingent
    rather than collapsed.

    The contingency group is where R2 and R3 are discharged:
    - S3 conjunct B asserts the family's only POSITIVE [K], [K (V2, burn_call)],
      so this suite proves the knowledge is contingent, that its operand is not
      rigid over the reachable set, and that the on-chain reader's view class at
      the operative state is NOT a singleton. That class has three members - the
      same burn reached directly, through the [DELEGATECALL; POP] relay, and
      through a flag-checking relay - and they are indistinguishable to V2
      exactly because the storage target is pinned.
    - S1 conjunct D, S2 conjunct D, S3 conjunct C and S3 conjunct D assert
      IGNORANCE, so this suite exhibits each witness pair in both directions. *)

open Telcoin_epistemic
open Tel_dispatch_surface_model

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
        (st.Tel_dispatch_surface_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Tel_dispatch_surface_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Tel_dispatch_surface_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** Ignorance shorthand: agent [i] does not know [p]. *)
let unknown_to i p = Formula.Not (Formula.K (i, p))

(* The pristine reachable count is exactly 33: the single [Choose] state, the
   sixteen dispatched call vectors (four calldata shapes x four caller shapes),
   and the sixteen settled ones. The stated bound is the product ceiling this
   family promised. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        ("reachable count "
        ^ Int.to_string (Checker.reachable_count sys)
        ^ " <= 50")
        true
        (Checker.reachable_count sys <= 50))

(* Pinned exactly, so a model edit that silently changes the graph is caught. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 33
        (Checker.reachable_count sys))

(* The fail-closed arm's invariant (tel_precompile/mod.rs:163): no call carrying
   an unimplemented selector ever leaves the dispatcher any way but as an
   [Err]. *)
let open_unknown_selector_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (unknown_selector_call /\\ ~dispatch_errored)"
        false
        (Checker.satisfiable sys
           (Formula.And
              (f Unknown_selector_call, Formula.Not (f Dispatch_errored)))))

(* The short-calldata guard's invariant (tel_precompile/mod.rs:121-123): a 1-3
   byte payload is always rejected before the slice at :125 is reached. *)
let unrejected_short_calldata_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (short_calldata_call /\\ ~dispatch_errored)"
        false
        (Checker.satisfiable sys
           (Formula.And
              (f Short_calldata_call, Formula.Not (f Dispatch_errored)))))

(* The consequence that matters for the executor: the slice never panics, so no
   transaction can take the block down with it. *)
let executor_panic_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF dispatch_panicked" false
        (Checker.satisfiable sys (f Dispatch_panicked)))

(* The address-pinning invariant (burnable.rs:342-351 and its five siblings;
   regression test tests/it/tel_precompile_props.rs:405-414): no supply write
   ever lands in a calling contract's own storage. *)
let private_shard_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF supply_write_shard" false
        (Checker.satisfiable sys (f Supply_write_shard)))

(* The situation S1 is about is real: an ERC-20-shaped selector really does
   reach the dispatcher. If this were unreachable, S1 would be about nothing. *)
let unknown_selector_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF unknown_selector_call" true
        (Checker.satisfiable sys (f Unknown_selector_call)))

(* The situation S2 is about is real: a 1-3 byte payload really does reach the
   dispatcher (any account can send one to any address). *)
let short_calldata_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF short_calldata_call" true
        (Checker.satisfiable sys (f Short_calldata_call)))

(* And the block really is produced anyway - S2 conjunct B is not vacuously true
   for want of a produced block
   (tests/it/pipeline_tel_precompile_props.rs:113-114). *)
let block_production_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF block_produced" true
        (Checker.satisfiable sys (f Block_produced)))

(* A rejected call really does fail its own transaction, so S1 conjunct C is not
   vacuously true for want of a failed transaction. *)
let tx_failure_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF tx_failed" true
        (Checker.satisfiable sys (f Tx_failed)))

(* The operative state of S3 is real: a burn really does settle and move the
   pinned slot. *)
let burn_effect_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF burn_took_effect" true
        (Checker.satisfiable sys (f Burn_took_effect)))

(* R2, contingency: the on-chain reader's knowledge in S3 conjunct B is not
   collapsed - there are reachable states at which it does NOT hold. *)
let k_burn_witness_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v2 burn_call" true
        (Checker.satisfiable sys (unknown_to Validator.V2 (f Burn_call))))

(* R2, non-rigidity: the K operand itself is false somewhere reachable - every
   [totalSupply] read and every rejected call - so the knowledge claim is not
   true for structural reasons. *)
let burn_call_operand_not_rigid () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~burn_call" true
        (Checker.satisfiable sys (Formula.Not (f Burn_call))))

(* R2, non-singleton view class. At an operative state where the burn did NOT
   come through the swallowing relay, V2 cannot rule out that it did - which is
   only possible if a second reachable state shares its view there. This is the
   test the 21 -> 63 round shipped without three times. *)
let burn_view_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (burn_took_effect /\\ ~via_relay_swallow /\\ ~K_v2 \
         ~via_relay_swallow)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And
                  (f Burn_took_effect, Formula.Not (f Via_relay_swallow)),
                unknown_to Validator.V2 (Formula.Not (f Via_relay_swallow)) ))))

(* R3 witness for S1 conjunct D, positive direction: at an unknown-selector
   dispatch the precompile cannot rule out that its caller will swallow the
   failure. The pair is that state and the [Relay_swallow] state with the
   identical [input.data] and the identical result (mod.rs:120-164). *)
let dispatcher_cannot_rule_out_a_swallowing_caller () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (unknown_selector_call /\\ ~K_v1 ~via_relay_swallow)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Unknown_selector_call,
                unknown_to Validator.V1 (Formula.Not (f Via_relay_swallow)) ))))

(* R3 witness for S1 conjunct D, negative direction: the same pair read the
   other way - with a swallowing caller in front of it, the dispatcher cannot
   tell that either. *)
let dispatcher_cannot_confirm_a_swallowing_caller () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (unknown_selector_call /\\ via_relay_swallow /\\ ~K_v1 \
         via_relay_swallow)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Unknown_selector_call, f Via_relay_swallow),
                unknown_to Validator.V1 (f Via_relay_swallow) ))))

(* R3 witness for S2 conjunct D, positive direction: a rejected call emits no
   event, so through the event channel "Invalid input: too short" (mod.rs:122)
   and "Unknown function selector" (mod.rs:163) are the same observation. *)
let events_cannot_see_a_short_payload () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (short_calldata_call /\\ settled /\\ ~K_v3 short_calldata_call)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Short_calldata_call, f Settled_phase),
                unknown_to Validator.V3 (f Short_calldata_call) ))))

(* R3 witness for S2 conjunct D, negative direction: with a well-formed but
   unimplemented selector rejected instead, the event consumer cannot rule out
   that the payload was short. *)
let events_cannot_rule_out_a_short_payload () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (~short_calldata_call /\\ settled /\\ ~K_v3 ~short_calldata_call)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And
                  (Formula.Not (f Short_calldata_call), f Settled_phase),
                unknown_to Validator.V3 (Formula.Not (f Short_calldata_call)) ))))

(* R3 witness for S3 conjunct C: at a burn that really was a direct call, the
   on-chain reader still cannot tell - the pinned slot moved the same way it
   would have through a relay. This is the safety property read as ignorance,
   and it is the conjunct {!Tel_dispatch_surface_model.Frame_scoped_storage}
   turns into knowledge. *)
let supply_hides_the_call_scheme () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (burn_took_effect /\\ via_eoa_direct /\\ ~K_v2 via_eoa_direct)" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Burn_took_effect, f Via_eoa_direct),
                unknown_to Validator.V2 (f Via_eoa_direct) ))))

(* R3 witness for S3 conjunct D: nor can the event consumer, whose channel
   survives that mutation intact - the [Burn]/[Transfer] payloads
   (burnable.rs:353-374) carry no frame identity. This is why the event stream
   cannot be the cross-check that rescues S3 conjunct B. *)
let events_hide_the_call_scheme () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (burn_took_effect /\\ via_eoa_direct /\\ ~K_v3 via_eoa_direct)" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Burn_took_effect, f Via_eoa_direct),
                unknown_to Validator.V3 (f Via_eoa_direct) ))))

let () =
  Alcotest.run "tel_dispatch_surface"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Tel_dispatch_surface_statements.name `Quick
              (prove_one st))
          Tel_dispatch_surface_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "open-unknown-selector-unreachable" `Quick
            open_unknown_selector_unreachable;
          Alcotest.test_case "unrejected-short-calldata-unreachable" `Quick
            unrejected_short_calldata_unreachable;
          Alcotest.test_case "executor-panic-unreachable" `Quick
            executor_panic_unreachable;
          Alcotest.test_case "private-shard-unreachable" `Quick
            private_shard_unreachable;
          Alcotest.test_case "unknown-selector-reachable" `Quick
            unknown_selector_reachable;
          Alcotest.test_case "short-calldata-reachable" `Quick
            short_calldata_reachable;
          Alcotest.test_case "block-production-reachable" `Quick
            block_production_reachable;
          Alcotest.test_case "tx-failure-reachable" `Quick tx_failure_reachable;
          Alcotest.test_case "burn-effect-reachable" `Quick
            burn_effect_reachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-burn-witness-contingent" `Quick
            k_burn_witness_contingent;
          Alcotest.test_case "burn-call-operand-not-rigid" `Quick
            burn_call_operand_not_rigid;
          Alcotest.test_case "burn-view-class-not-singleton" `Quick
            burn_view_class_not_singleton;
          Alcotest.test_case "dispatcher-cannot-rule-out-a-swallowing-caller"
            `Quick dispatcher_cannot_rule_out_a_swallowing_caller;
          Alcotest.test_case "dispatcher-cannot-confirm-a-swallowing-caller"
            `Quick dispatcher_cannot_confirm_a_swallowing_caller;
          Alcotest.test_case "events-cannot-see-a-short-payload" `Quick
            events_cannot_see_a_short_payload;
          Alcotest.test_case "events-cannot-rule-out-a-short-payload" `Quick
            events_cannot_rule_out_a_short_payload;
          Alcotest.test_case "supply-hides-the-call-scheme" `Quick
            supply_hides_the_call_scheme;
          Alcotest.test_case "events-hide-the-call-scheme" `Quick
            events_hide_the_call_scheme;
        ] );
    ]
