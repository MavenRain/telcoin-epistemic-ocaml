(** The [tel_supply_ledger] family proves on the pristine
    {!Tel_supply_ledger_model}, its reachable graph is the small guarded-write
    product the model claims, the three invariants really do exclude the
    states they name, and the epistemic layer is genuinely partial
    information rather than a collapsed [K].

    The contingency group is where R2 and R3 are discharged. For each
    positive [K] it shows both that the knowledge is contingent (some
    reachable state fails it) and that the knower's view class at the
    operative state is NOT a singleton - the latter by exhibiting an atom
    that is false at the operative state and which the knower nevertheless
    cannot rule out, which is only possible if another reachable state shares
    its view. For the [~K] conjunct it exhibits the ignorance pair itself. *)

open Telcoin_epistemic
open Tel_supply_ledger_model

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
        (st.Tel_supply_ledger_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Tel_supply_ledger_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Tel_supply_ledger_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** A named [satisfiable] assertion on the pristine model. *)
let sat_is name expected phi () =
  with_sys (fun sys ->
      Alcotest.(check bool) name expected (Checker.satisfiable sys phi))

(* --- sanity --- *)

(** The reachable set is the guarded-write product the model header
    describes, and it is small: the exact pristine count is 49 - one genesis
    ledger, six mint receipts, six tick receipts, four committed claims,
    fourteen rejected claims, six committed burns and twelve rejected burns.
    The band leaves slack without admitting a blow-up. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 50))

(** The mint destination pin holds at the storage level: no reachable state
    has a non-governance amount slot armed (burnable.rs:173). *)
let no_foreign_arming =
  sat_is "EF pending_armed_other" false (f Pending_armed_other)

(** … and at the credit level: no reachable claim credits anyone but
    governance (burnable.rs:240-248 loads the named recipient's own slot). *)
let no_foreign_credit =
  sat_is "EF (claim_committed /\\ ~claim_credited_gov)" false
    (Formula.And (f Claim_committed, Formula.Not (f Claim_credited_gov)))

(** The disarm is total: every committed claim leaves the amount slot clear
    (burnable.rs:267-269). *)
let claim_always_disarms =
  sat_is "EF (claim_committed /\\ ~pending_slot_clear)" false
    (Formula.And (f Claim_committed, Formula.Not (f Pending_slot_clear)))

(** The state S3 forbids - the precompile balance debited while slot 100
    stands - is not reachable pristine, in either direction. *)
let no_split_burn =
  sat_is "EF (burn_committed /\\ (~balance_fell \\/ ~supply_slot_fell))" false
    (Formula.And
       ( f Burn_committed,
         Formula.Or
           (Formula.Not (f Balance_fell), Formula.Not (f Supply_slot_fell)) ))

(** … and a rejected burn moves nothing at all: the frame's journal revert
    unwinds the balance debit that burnable.rs:337-339 already wrote. *)
let reverted_burn_moves_nothing =
  sat_is "EF (burn_reverted /\\ (balance_fell \\/ supply_slot_fell))" false
    (Formula.And
       (f Burn_reverted, Formula.Or (f Balance_fell, f Supply_slot_fell)))

(** The model is not degenerate: all four receipt classes the statements
    quantify over are actually reached, so no statement is carried by an
    empty antecedent. *)
let every_receipt_class_reached () =
  with_sys (fun sys ->
      Alcotest.(check (list bool))
        "mint / committed claim / committed burn / rejected burn all reachable"
        [ true; true; true; true ]
        (List.map (Checker.satisfiable sys)
           [
             f Mint_armed_slot;
             f Claim_committed;
             f Burn_committed;
             f Burn_reverted;
           ]))

(** The timelock transcription is the code's: a zeroed unlock slot passes
    [current_ts < unlock_ts] trivially (burnable.rs:259-261), which is what
    makes the amount clear and not the timestamp clear the load-bearing half
    of the disarm. *)
let cleared_timestamp_passes_the_timelock () =
  Alcotest.(check (list bool))
    "Lock_zero and Lock_ripe pass, Lock_armed does not" [ true; false; true ]
    (List.map timelock_passed [ Lock_zero; Lock_armed; Lock_ripe ])

(* --- contingency: R2 and R3 --- *)

(** S1's [K_V1(pending_slot_clear)] is contingent, not collapsed: there is a
    reachable state at which the indexer does NOT know the amount slot is
    clear (every state a mint leaves). *)
let indexer_knowledge_contingent =
  sat_is "EF ~K_V1(pending_slot_clear)" true
    (Formula.Not (Formula.K (Validator.V1, f Pending_slot_clear)))

(** R2 for S1: the indexer's view class at a committed claim is NOT a
    singleton. [balance_zero] is FALSE at the first committed claim, yet the
    indexer cannot rule it out - which is only possible because another
    reachable committed claim, the one after the precompile has been drained,
    shares its receipt-only view. *)
let indexer_class_not_singleton =
  sat_is "EF (claim_committed /\\ ~K_V1(~balance_zero))" true
    (Formula.And
       ( f Claim_committed,
         Formula.Not (Formula.K (Validator.V1, Formula.Not (f Balance_zero))) ))

(** Both members of that class are reachable, named directly. *)
let claim_class_members_reachable () =
  with_sys (fun sys ->
      Alcotest.(check (pair bool bool))
        "a committed claim with the precompile drained, and one without"
        (true, true)
        ( Checker.satisfiable sys
            (Formula.And (f Claim_committed, f Balance_zero)),
          Checker.satisfiable sys
            (Formula.And (f Claim_committed, Formula.Not (f Balance_zero))) ))

(** S3's [K_V0(supply_slot_fell)] is contingent, not collapsed: at every
    state a mint, a claim or a rejected call leaves, the monitor does not
    know the last step lowered slot 100 - because it did not. *)
let monitor_knowledge_contingent =
  sat_is "EF ~K_V0(supply_slot_fell)" true
    (Formula.Not (Formula.K (Validator.V0, f Supply_slot_fell)))

(** R2 for S3: the monitor's view class at a committed burn is NOT a
    singleton. [pending_slot_clear] is TRUE at the burn reached straight from
    a claim, yet the monitor cannot rule out its negation - the pending pair
    has no getter (burnable.rs:39-60, mod.rs:128-164), so the burn reached
    from a mint-armed ledger shares the monitor's [(supply, balance,
    receipt)] view exactly. *)
let monitor_class_not_singleton =
  sat_is "EF (burn_committed /\\ ~K_V0(pending_slot_clear))" true
    (Formula.And
       ( f Burn_committed,
         Formula.Not (Formula.K (Validator.V0, f Pending_slot_clear)) ))

(** Both members of that class are reachable, named directly. *)
let burn_class_members_reachable () =
  with_sys (fun sys ->
      Alcotest.(check (pair bool bool))
        "a committed burn with the slot armed, and one with it clear"
        (true, true)
        ( Checker.satisfiable sys
            (Formula.And (f Burn_committed, Formula.Not (f Pending_slot_clear))),
          Checker.satisfiable sys
            (Formula.And (f Burn_committed, f Pending_slot_clear)) ))

(** R3 for S3's [~K_V1(supply_slot_zero)]: the ignorance is real and it bites
    where it matters - there is a reachable state at which the supply IS
    exhausted and the indexer, watching the very burn that exhausted it,
    cannot tell. No event carries a resulting cell value
    (burnable.rs:353-361 emits [Burn(amount)] and nothing more). *)
let indexer_cannot_see_the_supply =
  sat_is "EF (burn_committed /\\ supply_slot_zero /\\ ~K_V1(supply_slot_zero))"
    true
    (Formula.conj
       [
         f Burn_committed;
         f Supply_slot_zero;
         Formula.Not (Formula.K (Validator.V1, f Supply_slot_zero));
       ])

(** The other member of that ignorance pair: a committed burn that left the
    supply standing. Same receipt, different slot 100. *)
let ignorance_pair_partner =
  sat_is "EF (burn_committed /\\ ~supply_slot_zero)" true
    (Formula.And (f Burn_committed, Formula.Not (f Supply_slot_zero)))

let () =
  Alcotest.run "tel_supply_ledger"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Tel_supply_ledger_statements.name `Quick
              (prove_one st))
          Tel_supply_ledger_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "no-foreign-arming" `Quick no_foreign_arming;
          Alcotest.test_case "no-foreign-credit" `Quick no_foreign_credit;
          Alcotest.test_case "claim-always-disarms" `Quick claim_always_disarms;
          Alcotest.test_case "no-split-burn" `Quick no_split_burn;
          Alcotest.test_case "reverted-burn-moves-nothing" `Quick
            reverted_burn_moves_nothing;
          Alcotest.test_case "every-receipt-class-reached" `Quick
            every_receipt_class_reached;
          Alcotest.test_case "cleared-timestamp-passes-the-timelock" `Quick
            cleared_timestamp_passes_the_timelock;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "indexer-knowledge-contingent" `Quick
            indexer_knowledge_contingent;
          Alcotest.test_case "indexer-class-not-singleton" `Quick
            indexer_class_not_singleton;
          Alcotest.test_case "claim-class-members-reachable" `Quick
            claim_class_members_reachable;
          Alcotest.test_case "monitor-knowledge-contingent" `Quick
            monitor_knowledge_contingent;
          Alcotest.test_case "monitor-class-not-singleton" `Quick
            monitor_class_not_singleton;
          Alcotest.test_case "burn-class-members-reachable" `Quick
            burn_class_members_reachable;
          Alcotest.test_case "indexer-cannot-see-the-supply" `Quick
            indexer_cannot_see_the_supply;
          Alcotest.test_case "ignorance-pair-partner" `Quick
            ignorance_pair_partner;
        ] );
    ]
