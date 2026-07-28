(** Confirm-by-mutation for the [tel_supply_ledger] family. Each of the three
    gate deletions is a real guard removed from
    crates/tn-reth/src/evm/tel_precompile, and each is paired with the hunt
    that found no sibling path repairing it.

    - {!Tel_supply_ledger_model.No_pending_clear} deletes the amount-slot
      clear at burnable.rs:267-269. Not repaired by the timestamp clear at
      :270-272: that writes ZERO and the timelock test is
      [current_ts < unlock_ts] (:259-261), so a zeroed unlock makes every
      later claim pass immediately. Not repaired by the zero-amount rejection
      at :246-248 either - that is the same slot's guard, and with the slot
      never cleared it never fires.
    - {!Tel_supply_ledger_model.No_recipient_pin} deletes
      [let recipient = GOVERNANCE_SAFE_ADDRESS;] at burnable.rs:173. The
      amount slot has exactly one writer besides the clear (:180), so there
      is no second arming route to re-pin the destination, and [claim]
      applies no address check beyond the caller's governance role
      (:230-232).
    - {!Tel_supply_ledger_model.No_supply_guard} deletes the [checked_sub …
      ok_or_else(…)?] at burnable.rs:346-348. Not repaired by
      [balance_decr]'s [if balance < amount] (helpers.rs:70-72): that bounds
      the amount by the precompile's NATIVE BALANCE, an independent quantity
      from slot 100.

    Each pin asserts the pristine proof and the mutated refutation. Beyond
    the contract's minimum this suite also asserts, per mutation, WHICH
    conjunct flips and that the other two statements are untouched - so a pin
    can never pass because some other statement in the family happened to
    break. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Tel_supply_ledger_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Tel_supply_ledger_model.Checker.make (Tel_supply_ledger_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Tel_supply_ledger_statements.name name))
    Tel_supply_ledger_statements.all

(** Assert a statement's verdict under one mutation. *)
let verdict_is mut name expected message () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool) message expected
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Tel_supply_ledger_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name =
  verdict_is mut name false (name ^ " flips to refuted under the mutation")

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name =
  verdict_is Tel_supply_ledger_model.Pristine name true
    (name ^ " proves on the pristine model")

(** The orthogonality half: this mutation leaves that statement alone, so the
    pin above cannot be passing on the strength of an unrelated break. *)
let survives_under mut name =
  verdict_is mut name true (name ^ " still proves under this unrelated deletion")

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** Assert a raw formula's validity under one mutation - the per-conjunct
    diagnostic that says the pin flipped for the reason it claims. *)
let conjunct_is mut expected message phi () =
  with_mut mut (fun sys ->
      Alcotest.(check bool) message expected
        (Tel_supply_ledger_model.Checker.valid sys phi))

(** S1's replay-exclusion conjunct, restated for a direct diagnostic. *)
let replay_excluded =
  Formula.Ag
    (Formula.Implies
       ( f Tel_supply_ledger_model.Claim_committed,
         Formula.Ax
           (Tel_supply_ledger_statements.weak_until
              (Formula.Not (f Tel_supply_ledger_model.Claim_committed))
              (f Tel_supply_ledger_model.Mint_armed_slot)) ))

(** S1's epistemic conjunct, restated for a direct diagnostic. *)
let indexer_knows_disarm =
  Formula.Ag
    (Formula.Implies
       ( f Tel_supply_ledger_model.Claim_committed,
         Formula.K (Validator.V1, f Tel_supply_ledger_model.Pending_slot_clear)
       ))

(** S2's credit-destination conjunct, restated for a direct diagnostic. *)
let credit_pinned =
  Formula.Ag
    (Formula.Implies
       ( f Tel_supply_ledger_model.Claim_committed,
         f Tel_supply_ledger_model.Claim_credited_gov ))

(** S3's both-cells conjunct, restated for a direct diagnostic. *)
let commit_moves_both =
  Formula.Ag
    (Formula.Implies
       ( f Tel_supply_ledger_model.Burn_committed,
         Formula.And
           ( f Tel_supply_ledger_model.Balance_fell,
             f Tel_supply_ledger_model.Supply_slot_fell ) ))

(** S3's epistemic conjunct, restated for a direct diagnostic. *)
let monitor_knows_the_drop =
  Formula.Ag
    (Formula.Implies
       ( f Tel_supply_ledger_model.Burn_committed,
         Formula.K (Validator.V0, f Tel_supply_ledger_model.Supply_slot_fell) ))

let () =
  Alcotest.run "tel_supply_ledger_mutation"
    [
      ( "amount-slot-clear (burnable.rs:267-269)",
        pin Tel_supply_ledger_model.No_pending_clear
          "pending-mint-is-credited-at-most-once"
        @ [
            Alcotest.test_case "replay-conjunct-flips" `Quick
              (conjunct_is Tel_supply_ledger_model.No_pending_clear false
                 "a second claim commits with no fresh mint" replay_excluded);
            Alcotest.test_case "indexer-conjunct-flips" `Quick
              (conjunct_is Tel_supply_ledger_model.No_pending_clear false
                 "the indexer's disarm inference is no longer sound"
                 indexer_knows_disarm);
            Alcotest.test_case "timestamp-clear-does-not-repair" `Quick
              (conjunct_is Tel_supply_ledger_model.No_pending_clear false
                 "the surviving timestamp clear at :270-272 zeroes the unlock \
                  and so cannot stop the replay" replay_excluded);
            Alcotest.test_case "destination-statement-untouched" `Quick
              (survives_under Tel_supply_ledger_model.No_pending_clear
                 "mint-target-is-pinned-to-governance");
            Alcotest.test_case "burn-statement-untouched" `Quick
              (survives_under Tel_supply_ledger_model.No_pending_clear
                 "burn-moves-both-ledger-cells-or-neither");
          ] );
      ( "mint destination pin (burnable.rs:173)",
        pin Tel_supply_ledger_model.No_recipient_pin
          "mint-target-is-pinned-to-governance"
        @ [
            Alcotest.test_case "credit-conjunct-flips" `Quick
              (conjunct_is Tel_supply_ledger_model.No_recipient_pin false
                 "a claim credits a non-governance address" credit_pinned);
            Alcotest.test_case "replay-statement-untouched" `Quick
              (survives_under Tel_supply_ledger_model.No_recipient_pin
                 "pending-mint-is-credited-at-most-once");
            Alcotest.test_case "burn-statement-untouched" `Quick
              (survives_under Tel_supply_ledger_model.No_recipient_pin
                 "burn-moves-both-ledger-cells-or-neither");
          ] );
      ( "supply checked_sub (burnable.rs:346-348)",
        pin Tel_supply_ledger_model.No_supply_guard
          "burn-moves-both-ledger-cells-or-neither"
        @ [
            Alcotest.test_case "atomicity-conjunct-flips" `Quick
              (conjunct_is Tel_supply_ledger_model.No_supply_guard false
                 "the balance debit stands while slot 100 wraps"
                 commit_moves_both);
            Alcotest.test_case "monitor-conjunct-flips" `Quick
              (conjunct_is Tel_supply_ledger_model.No_supply_guard false
                 "the supply monitor no longer knows the burn lowered slot 100"
                 monitor_knows_the_drop);
            Alcotest.test_case "balance-check-does-not-repair" `Quick
              (conjunct_is Tel_supply_ledger_model.No_supply_guard false
                 "helpers.rs:70-72 bounds the amount by the native balance, an \
                  independent quantity, so it does not restore atomicity"
                 commit_moves_both);
            Alcotest.test_case "replay-statement-untouched" `Quick
              (survives_under Tel_supply_ledger_model.No_supply_guard
                 "pending-mint-is-credited-at-most-once");
            Alcotest.test_case "destination-statement-untouched" `Quick
              (survives_under Tel_supply_ledger_model.No_supply_guard
                 "mint-target-is-pinned-to-governance");
          ] );
    ]
