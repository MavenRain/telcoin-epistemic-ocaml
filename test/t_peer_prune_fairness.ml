(** The PEER_PRUNE_FAIRNESS family proves on the pristine
    {!Peer_prune_fairness_model} through [prove_nonvacuous] (so every
    antecedent is also checked reachable), the reachable graph stays in its
    justified band, the two states the prune filter forbids are unreachable,
    and the epistemic layer is genuinely partial-information: the unidentified
    committee member and the unidentified outsider are view-identical to the
    pruning node, in both directions.

    The family asserts no positive [K], so there is no R2 non-singleton
    obligation to discharge for a positive knowledge operand. The
    corresponding evidence for the two NEGATIVE operands is stronger and is
    asserted here: a single state can satisfy [~K] trivially by falsifying the
    operand itself, so both directions of the witness pair are asserted
    separately, plus the conjunction of both [~K]s at one state - which is
    satisfiable only if the pruning node's view class at that state contains
    two reachable states disagreeing on [committee_member(x)]. *)

open Telcoin_epistemic
open Peer_prune_fairness_model

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
        (st.Peer_prune_fairness_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Peer_prune_fairness_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Peer_prune_fairness_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** Conjoin a list of formulas. *)
let all_of = Formula.conj

(* Loose product bound: 2 capacity regimes x 3 committee situations for [Px] x
   2^5 connection vectors = 192. The pristine reachable set is exactly 28: the
   three [Slack] configurations contribute 3 states each (all connected, plus
   one of the tie pair dropped), the [Tight] recognized configuration 5 (both
   tie peers then [Pc], then the round stops above target) and the two [Tight]
   unidentified configurations 7 each (the tie pair, then either of the two
   HIGH-bucket candidates, then the other). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 50))

(* The validator carve-out's forbidden state: a peer the prune filter
   recognizes as a committee validator is never dropped for excess
   (manager.rs:575). *)
let recognized_validator_never_dropped () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (is_peer_validator(x) /\\ ~connected(x))"
        false
        (Checker.satisfiable sys
           (Formula.And (f X_recognized, Formula.Not (f Conn_x)))))

(* The operator carve-out's forbidden state: the operator-allowlisted peer is
   never dropped for excess (manager.rs:575, peer.rs:401-403). *)
let allowlisted_never_dropped () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF ~connected(y)" false
        (Checker.satisfiable sys (Formula.Not (f Conn_y))))

(* The ordering gate's forbidden state: no HIGH-bucket peer is gone while a
   LOW-bucket candidate is still connected (all_peers.rs:976). *)
let high_bucket_never_first () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF ((connected(a) \\/ connected(b)) /\\ ~connected(c))" false
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.Or (f Conn_a, f Conn_b),
                Formula.Not (f Conn_c) ))))

(* Ignorance witness, member direction: a state where the node has evicted a
   GENUINE committee member it never identified, and cannot know it did. This
   is satisfiable only because the [Unconfirmed_outsider] sibling shares the
   node's view (all_peers.rs:836-845). *)
let ignorance_witness_member () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (committee_member(x) /\\ ~is_peer_validator(x) /\\ ~connected(x) \
         /\\ ~K_v0 committee_member(x))"
        true
        (Checker.satisfiable sys
           (all_of
              [
                f X_in_committee;
                Formula.Not (f X_recognized);
                Formula.Not (f Conn_x);
                Formula.Not (Formula.K (Validator.V0, f X_in_committee));
              ])))

(* Ignorance witness, outsider direction: a state where the evicted
   unidentified peer is NOT a committee member, and the node cannot rule the
   membership out either - the [Unconfirmed_member] sibling shares its view. *)
let ignorance_witness_outsider () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (~committee_member(x) /\\ ~is_peer_validator(x) /\\ ~connected(x) \
         /\\ ~K_v0 ~committee_member(x))"
        true
        (Checker.satisfiable sys
           (all_of
              [
                Formula.Not (f X_in_committee);
                Formula.Not (f X_recognized);
                Formula.Not (f Conn_x);
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f X_in_committee)));
              ])))

(* Non-singleton view class: both [~K]s hold at ONE state. A singleton class
   would force one of them false, so this is the direct evidence that the
   pruning node's view class at an eviction of an unidentified peer contains
   two reachable states disagreeing on committee membership. *)
let view_class_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (~connected(x) /\\ ~K_v0 committee_member(x) /\\ ~K_v0 \
         ~committee_member(x))"
        true
        (Checker.satisfiable sys
           (all_of
              [
                Formula.Not (f X_recognized);
                Formula.Not (f Conn_x);
                Formula.Not (Formula.K (Validator.V0, f X_in_committee));
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f X_in_committee)));
              ])))

(* The knowledge is not collapsed in the other direction either: the node's
   membership verdict is contingent across the reachable set, so
   [K_v0(committee_member(x))] is not simply everywhere true or everywhere
   false for structural reasons. *)
let committee_membership_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF committee_member(x) and EF ~committee_member(x)"
        true
        (Checker.satisfiable sys (f X_in_committee)
        && Checker.satisfiable sys (Formula.Not (f X_in_committee))))

(* S2's tie-break branches are both live: in the single-excess regime the
   round can drop either tie peer. *)
let both_tie_branches_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (excess=1 /\\ ~connected(a)) and the same for b"
        true
        (Checker.satisfiable sys
           (Formula.And (f Cap_slack, Formula.Not (f Conn_a)))
        && Checker.satisfiable sys
             (Formula.And (f Cap_slack, Formula.Not (f Conn_b)))))

(* S3 conjunct C is not vacuous: the [Tight] round really does end with every
   ordinary peer gone, the recognized validator still connected and the node
   still above target (manager.rs:564-565 vs :571-581). *)
let round_ends_above_target () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (is_peer_validator(x) /\\ ~excess=1 /\\ no ordinary peer left /\\ \
         connected(x) /\\ over_target)"
        true
        (Checker.satisfiable sys
           (all_of
              [
                f X_recognized;
                Formula.Not (f Cap_slack);
                Formula.Not (f Conn_a);
                Formula.Not (f Conn_b);
                Formula.Not (f Conn_c);
                f Conn_x;
                f Over_target;
              ])))

(* [over_target] is a real state predicate, not a rigid one: some reachable
   states are at or below target. *)
let over_target_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~over_target" true
        (Checker.satisfiable sys (Formula.Not (f Over_target))))

let () =
  Alcotest.run "peer_prune_fairness"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Peer_prune_fairness_statements.name `Quick
              (prove_one st))
          Peer_prune_fairness_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "recognized-validator-never-dropped" `Quick
            recognized_validator_never_dropped;
          Alcotest.test_case "allowlisted-never-dropped" `Quick
            allowlisted_never_dropped;
          Alcotest.test_case "high-bucket-never-first" `Quick
            high_bucket_never_first;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "ignorance-witness-member" `Quick
            ignorance_witness_member;
          Alcotest.test_case "ignorance-witness-outsider" `Quick
            ignorance_witness_outsider;
          Alcotest.test_case "view-class-not-a-singleton" `Quick
            view_class_not_a_singleton;
          Alcotest.test_case "committee-membership-is-contingent" `Quick
            committee_membership_is_contingent;
          Alcotest.test_case "both-tie-branches-reachable" `Quick
            both_tie_branches_reachable;
          Alcotest.test_case "round-ends-above-target" `Quick
            round_ends_above_target;
          Alcotest.test_case "over-target-is-contingent" `Quick
            over_target_is_contingent;
        ] );
    ]
