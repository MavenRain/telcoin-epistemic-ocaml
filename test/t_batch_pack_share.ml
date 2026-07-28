(** The BATCH_PACK_SHARE suite: the three statements prove on the pristine
    model, the model's own gates hold as invariants, and every knowledge conjunct
    is discharged against a reachable witness rather than a degenerate view
    class.

    The [contingency] group is where R2 and R3 are paid for:

    - the single positive [K] ([K_V1(|pool inter A| = S)]) is shown contingent -
      it fails somewhere reachable - and its view class is shown non-singleton by
      exhibiting a state where V1 does not know the hidden solvency bit, which is
      only possible if a second reachable state shares its whole view;
    - each ignorance conjunct is shown together with the concrete reachable pair
      that witnesses it;
    - the positive [K] that was NOT asserted is pinned negatively: after the
      engine's canonical update the worker's class collapses to a singleton, so
      the corresponding knowledge claim would have been trivially true. That is
      recorded here so the omission cannot be mistaken for an oversight. *)

open Telcoin_epistemic
open Batch_pack_share_model

(** Build the pristine system or fail the test on an impossible [Empty_init]. *)
let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Checker.Empty_init -> Alcotest.fail "make: empty init")
    (make ())

(** Render a proof error for the assertion message. *)
let error_to_string e =
  match e with
  | Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Checker.Vacuous_antecedent -> "vacuous antecedent"

(** One proof case: the statement proves on the pristine model. *)
let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Batch_pack_share_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Batch_pack_share_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Batch_pack_share_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The exact pristine reachable count: 3 submission profiles x 2 hidden
    solvency values x 7 pipeline stages = 42, and every one of those product
    entries is reachable. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check int) "|reach| = 3 profiles x 2 solvencies x 7 stages" 42
        (Checker.reachable_count sys))

(** A named unsatisfiability assertion: the state the gate forbids. *)
let forbidden name g () =
  with_sys (fun sys ->
      Alcotest.(check bool) name false (Checker.satisfiable sys g))

(** A named satisfiability assertion: the witness the claim needs. *)
let witnessed name g () =
  with_sys (fun sys ->
      Alcotest.(check bool) name true (Checker.satisfiable sys g))

(** The pool is never mutated on the strength of a batch the peers refused:
    crates/batch-builder/src/lib.rs:199-211 returns empty vectors on
    anti-quorum/timeout/rejection and :309-316 then skips the update entirely. *)
let sync_needs_quorum =
  forbidden "no pool sync without a quorum ack"
    (Formula.And (f Pool_synced_now, Formula.Not (f Quorum_acked)))

(** The per-sender admission bound (crates/tn-reth/src/lib.rs:333-337, plumbed
    at crates/tn-reth/src/txn_pool.rs:87,98-99) is never exceeded. *)
let cap_is_never_exceeded =
  forbidden "no sender ever occupies more than S pool slots"
    (Formula.Not (f A_admission_within_cap))

(** The other half of the packing discipline: in the [heavy] profile A's third
    offer would have fitted the remaining budget, and it is dropped anyway,
    because [mark_invalid] invalidates the skipped transaction's dependents
    (crates/batch-builder/src/batch.rs:74-81). *)
let dependents_of_the_skipped_are_dropped =
  forbidden "a gas-skipped transaction's own successors never make the batch"
    (Formula.conj
       [ f Heavy_offer; f Batch_sealed; f Batch_takes_cap_many_of_a ])

(** Under the code as written no reachable seal of this family excludes the
    competing account, in any of the three submission profiles. *)
let competing_sender_always_gets_in =
  forbidden "no pristine seal leaves the competing sender out"
    (Formula.And (f Batch_sealed, Formula.Not (f B_in_batch)))

(** The operand of the positive [K] is not rigid: A sits at its admission bound
    in some reachable states and below it in others. *)
let occupancy_is_contingent_high =
  witnessed "a sender at the slot cap is reachable" (f A_admission_at_cap)

(** The other direction of the same non-rigidity check. *)
let occupancy_is_contingent_low =
  witnessed "a sender below the slot cap is reachable"
    (Formula.Not (f A_admission_at_cap))

(** R2, contingency half: the peer's knowledge of the sender's occupancy is not
    collapsed - it fails at reachable states, namely every one whose batch shows
    fewer than S transactions of that sender. *)
let peer_knowledge_is_contingent =
  witnessed "K_V1(|pool inter A| = S) fails somewhere reachable"
    (Formula.Not (Formula.K (peer, f A_admission_at_cap)))

(** R2, non-singleton half. At a [flood] sealed state with an INSOLVENT sender,
    V1 does not know that the sender is insolvent. That is only possible if
    another reachable state shares V1's entire view - here the solvent twin - so
    the class carrying the positive [K] is not a singleton. *)
let peer_class_is_not_a_singleton =
  witnessed "V1's class at a flood seal holds both solvency branches"
    (Formula.conj
       [
         f Flood_offer;
         f Batch_sealed;
         Formula.Not (f A_funded);
         Formula.Not (Formula.K (peer, Formula.Not (f A_funded)));
       ])

(** R3 for [~K_V1(left unsealed)], one half of the witness pair: in the [heavy]
    profile the seal really does leave two of A's transactions behind. *)
let heavy_leaves_transactions_behind =
  witnessed "a heavy seal leaves the sender's remainder in the pool"
    (Formula.conj [ f Heavy_offer; f Batch_sealed; f A_left_unsealed ])

(** R3, other half: in the [solo] profile nothing is left behind, and the sealed
    batch is the very same pair of transactions. *)
let solo_leaves_nothing_behind =
  witnessed "a solo seal leaves nothing behind"
    (Formula.conj
       [ f Solo_offer; f Batch_sealed; Formula.Not (f A_left_unsealed) ])

(** R3, the ignorance itself, stated from the [solo] side so that a singleton
    class would falsify it: at a solo seal V1 does NOT know that nothing was left
    behind, because the heavy seal it cannot distinguish did leave something. *)
let peer_cannot_tell_the_two_apart =
  witnessed "V1 cannot tell a fair seal from one that left a queue behind"
    (Formula.conj
       [
         f Solo_offer;
         f Batch_sealed;
         Formula.Not (Formula.K (peer, Formula.Not (f A_left_unsealed)));
       ])

(** R3 for S3's two ignorance conjuncts: at the moment the remainder is kept
    pending, the worker knows neither that the sender can pay nor that it
    cannot. *)
let worker_ignorance_at_the_sync =
  witnessed "the worker knows neither solvency nor insolvency at the sync"
    (Formula.conj
       [
         f Pool_synced_now;
         f A_left_unsealed;
         Formula.Not (Formula.K (worker, f A_funded));
         Formula.Not (Formula.K (worker, Formula.Not (f A_funded)));
       ])

(** The solvent half of that witness pair. *)
let solvent_sync_is_reachable =
  witnessed "a sync with a solvent remainder is reachable"
    (Formula.conj [ f Pool_synced_now; f A_left_unsealed; f A_funded ])

(** The insolvent half of that witness pair, observationally identical to the
    solvent one because batch.rs:137 told the pool [balance: U256::MAX]. *)
let insolvent_sync_is_reachable =
  witnessed "a sync with an insolvent remainder is reachable"
    (Formula.conj
       [ f Pool_synced_now; f A_left_unsealed; Formula.Not (f A_funded) ])

(** The positive [K] this family deliberately does NOT assert. After the
    engine's canonical update the remainder's sub-pool label is a function of the
    solvency bit, so the worker's class collapses to a singleton and
    [K_V0(balance(A) >= cost(next(A)))] would hold trivially. The probe below is
    false exactly because that class is a singleton, which is the evidence that
    dropping the claim was right rather than lazy. *)
let canon_class_collapses_to_a_singleton =
  forbidden "after the canonical update the worker's class is a singleton"
    (Formula.conj
       [
         f Canon_applied;
         f A_left_unsealed;
         f A_rest_pending;
         Formula.Not (Formula.K (worker, f A_funded));
       ])

let () =
  Alcotest.run "batch_pack_share"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Batch_pack_share_statements.name `Quick
              (prove_one st))
          Batch_pack_share_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "sync-needs-quorum" `Quick sync_needs_quorum;
          Alcotest.test_case "cap-is-never-exceeded" `Quick cap_is_never_exceeded;
          Alcotest.test_case "dependents-of-the-skipped-are-dropped" `Quick
            dependents_of_the_skipped_are_dropped;
          Alcotest.test_case "competing-sender-always-gets-in" `Quick
            competing_sender_always_gets_in;
          Alcotest.test_case "occupancy-contingent-high" `Quick
            occupancy_is_contingent_high;
          Alcotest.test_case "occupancy-contingent-low" `Quick
            occupancy_is_contingent_low;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "peer-knowledge-is-contingent" `Quick
            peer_knowledge_is_contingent;
          Alcotest.test_case "peer-class-is-not-a-singleton" `Quick
            peer_class_is_not_a_singleton;
          Alcotest.test_case "heavy-leaves-transactions-behind" `Quick
            heavy_leaves_transactions_behind;
          Alcotest.test_case "solo-leaves-nothing-behind" `Quick
            solo_leaves_nothing_behind;
          Alcotest.test_case "peer-cannot-tell-the-two-apart" `Quick
            peer_cannot_tell_the_two_apart;
          Alcotest.test_case "worker-ignorance-at-the-sync" `Quick
            worker_ignorance_at_the_sync;
          Alcotest.test_case "solvent-sync-is-reachable" `Quick
            solvent_sync_is_reachable;
          Alcotest.test_case "insolvent-sync-is-reachable" `Quick
            insolvent_sync_is_reachable;
          Alcotest.test_case "canon-class-collapses-to-a-singleton" `Quick
            canon_class_collapses_to_a_singleton;
        ] );
    ]
