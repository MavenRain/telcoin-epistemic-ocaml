(** Confirm-by-mutation for the TX_FORWARD_ROUTE family: every statement is
    pinned by a gate deletion taken from crates/tn-reth/src/forward.rs, and each
    row asserts the proof FLIPS to an error on the mutated model while the
    pristine half still proves.

    - S1 is pinned by {!Tx_forward_route_model.Round_robin_owner}, which deletes
      the sender-derived slot at forward.rs:227 and hands slots out in arrival
      order. Its antecedent stays reachable under the mutation, so the flip is a
      genuine refutation and not a vacuity. No sibling repairs it: the
      receive-side twin [submit_txn_if_mine]
      (crates/batch-validator/src/validator.rs:89-106) applies the same modulo
      but has no production caller, and [fallbacks] (forward.rs:136) is BLS-key
      order over a churning advertisement set, which cannot re-derive a sender's
      slot.
    - S2 is pinned by {!Tx_forward_route_model.No_forward_budget}, which deletes
      the outer [timeout(FORWARD_TX_BUDGET, ...)] (forward.rs:148) and its
      [.unwrap_or(ForwardOutcome::NoEndpointReached)] (forward.rs:194-195). The
      per-attempt [FORWARD_SEND_TIMEOUT] (forward.rs:160) is inside the loop and
      is exactly what the outer budget aggregates (forward.rs:32-35), so it does
      not repair the deletion; the spawn site attaches no deadline
      (forward.rs:138) and the caller never joins
      (crates/consensus/worker/src/worker.rs:253-276).
    - S3 is pinned TWICE, by two different deletions refuting two different
      conjuncts. {!Tx_forward_route_model.No_transient_fallthrough} deletes the
      transient branch at forward.rs:266-268 so a full pool stops the chain, and
      {!Tx_forward_route_model.Timeout_counts_as_delivered} deletes the
      elapsed-round-trip classification at forward.rs:165-167 so the pass
      records deliveries no validator acknowledged. Nothing re-offers a
      transaction the pass failed to place: [disburse_txns] acks as soon as the
      task is spawned (worker.rs:253-276), the observer's pool is emptied on
      that ack (crates/batch-builder/src/lib.rs:187, :326-332,
      crates/tn-reth/src/txn_pool.rs:145-168), the backup task is commented out
      (txn_pool.rs:103-123) and the gossip route was deleted (forward.rs:1-12).

    Attributability was checked per conjunct rather than assumed: S1 loses only
    its tx1 owner-first conjunct under [Round_robin_owner], S2 loses its overrun
    and abandonment conjuncts under [No_forward_budget], and S3 loses its
    fallthrough conjunct under [No_transient_fallthrough] and its
    delivery-has-a-holder, delivery-is-known and no-second-copy conjuncts under
    [Timeout_counts_as_delivered]. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Tx_forward_route_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Tx_forward_route_model.Checker.make (Tx_forward_route_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Tx_forward_route_statements.name name))
    Tx_forward_route_statements.all

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " flips to refuted under the mutation")
            false
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Tx_forward_route_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Tx_forward_route_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Tx_forward_route_statements.prove sys st)))

(** The flip is a REFUTATION, not a vacuity: the statement's antecedent is
    still reachable on the mutated model, so [prove_nonvacuous] failed because
    the goal is false there and not because the premise vanished. *)
let antecedent_survives mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ ": antecedent still reachable under the mutation") true
            (Tx_forward_route_model.Checker.satisfiable sys
               st.Tx_forward_route_statements.antecedent))

(** A pristine-proves plus mutated-refutes pair for one statement, with the
    non-vacuity check that makes the negative half meaningful. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
    Alcotest.test_case (name ^ ":mutated-antecedent-reachable") `Quick
      (antecedent_survives mut name);
  ]

let () =
  Alcotest.run "tx_forward_route_mutation"
    [
      ( "arrival-order routing breaks per-account convergence",
        pin Tx_forward_route_model.Round_robin_owner
          "sender-slot-owns-every-transaction-of-one-account" );
      ( "dropped per-transaction budget lets one transaction overrun",
        pin Tx_forward_route_model.No_forward_budget
          "forward-budget-bounds-one-transaction" );
      ( "dropped transient branch stops the chain at a saturated owner",
        pin Tx_forward_route_model.No_transient_fallthrough
          "endpoint-local-non-verdict-is-neither-a-delivery-nor-an-end-of-chain"
      );
      ( "an elapsed round trip counted as a delivery",
        pin Tx_forward_route_model.Timeout_counts_as_delivered
          "endpoint-local-non-verdict-is-neither-a-delivery-nor-an-end-of-chain"
      );
    ]
