(** The SUBDAG_LEADER_WALK family proves on the pristine
    {!Subdag_leader_walk_model} through [prove_nonvacuous] (so every antecedent
    is also checked reachable), the reachable graph stays in its justified
    band, the structural invariants the modeled gates enforce hold, and the
    epistemic layer is genuinely partial-information: every positive [K]
    operand is contingent, every operative view class is shown NON-SINGLETON
    (R2), and the ignorance witness of S1's [~K] conjunct is reachable (R3).

    The "channel" group is the R5 receipt for S1's epistemic conjuncts: peers
    really do publish signed records of their own commits
    (subscriber.rs:296-316), the model carries that channel, and the group
    pins both halves of it - a record never arrives without the commit that
    produced it, and the commit can be in place while the record is still in
    flight. Without the second half S1's ignorance conjunct would be vacuous;
    without the first its knowledge conjunct would be unfounded. *)

open Telcoin_epistemic
open Subdag_leader_walk_model

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
        (st.Subdag_leader_walk_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Subdag_leader_walk_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Subdag_leader_walk_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 2 support levels x 2 link values x 5 progress values
   per node x 2 nodes x 2 report values = 2 * 2 * 5 * 5 * 2 = 200. The pristine
   reachable set is exactly 36: the (High, Unlinked) world is not an initial
   state (quorum intersection forbids it), the two Low worlds admit only 2
   progress values per node and the (High, Linked) world admits 4, giving 24
   commit states, and the report bit adds one state for each of the 12 of those
   in which the peer has committed an anchor. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 200))

(* Quorum intersection, the invariant that makes S1's knowledge derivable:
   f+1 support forces linkedness, because >= 2 supporters and >= 3 anchor
   parents cannot miss each other across 4 authority slots. Equivalently the
   (High, Unlinked) world does not exist. *)
let support_quorum_implies_linked () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G (support >= f+1 -> linked(A,L))" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies (f Support_quorum_high, f Linked_anchor_l)))))

(* The state the f+1 support gate forbids: NO node direct-commits L while L
   has at most f supporters. This is what No_leader_support_gate removes. *)
let unsupported_leader_never_direct_committed () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (support < f+1 /\\ some node direct-committed L)" false
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.Not (f Support_quorum_high),
                Formula.Or (f Direct_commit_l_v0, f Direct_commit_l_v3) ))))

(* The state the walk-back inclusion gate forbids: V0 never commits an anchor
   that is linked to L while leaving L out of its committed leaders. This is
   what No_walk_back_inclusion removes. *)
let linked_leader_never_skipped () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (commit_anchor_V0 /\\ linked(A,L) /\\ ~subdag_V0(leader=L))"
        false
        (Checker.satisfiable sys
           (Formula.And
              ( f Anchor_committed_v0,
                Formula.And (f Linked_anchor_l, Formula.Not (f L_subdag_v0)) ))))

(* R5 evidence, pristine half: the repair path really is in the model. Whenever
   V0 has committed the anchor in a linked world, L's CERTIFICATES are
   sequenced (utils::order_dag sweeps the anchor's ancestor closure) - so the
   naive "L's certificates commit" claim is a strictly weaker target than S3's
   leader-anchored subdag, and t_subdag_leader_walk_mutation.ml shows the naive
   one surviving the mutation that kills S3. *)
let order_dag_repair_path_present () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "G ((commit_anchor_V0 /\\ linked) -> certs(L) sequenced at V0)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 ( Formula.And (f Anchor_committed_v0, f Linked_anchor_l),
                   f L_certs_sequenced_v0 )))))

(* S1 conjunct A contingency: the peer-inclusion operand is NOT plain truth
   under the view partition - in the unlinked world the peer commits the anchor
   and excludes L, so V0's knowledge of it fails somewhere reachable. *)
let s1_knowledge_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_V0(AG(commit_anchor_V3 -> L in leaders_V3))" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 ( Validator.V0,
                   Formula.Ag
                     (Formula.Implies
                        (f Anchor_committed_v3, f L_in_leaders_v3)) )))))

(* S1 conjunct A, R2 non-singleton class. At an operative state
   (direct_commit_V0(L)) the atom commit_anchor_V3 is FALSE, yet V0 does not
   know it is false - which is only possible if another reachable state shares
   V0's view and satisfies it. So the class is not a singleton and the positive
   K above is not trivially true. *)
let s1_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (direct_commit_V0(L) /\\ ~K_V0(~commit_anchor_V3))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Direct_commit_l_v0,
                Formula.Not
                  (Formula.K
                     (Validator.V0, Formula.Not (f Anchor_committed_v3))) ))))

(* S1 conjunct B, R3 ignorance witness, first half: a reachable state where V0
   has direct-committed L and does not know whether the peer has committed its
   anchor. *)
let s1_ignorance_witness () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (direct_commit_V0(L) /\\ ~K_V0(commit_anchor_V3))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Direct_commit_l_v0,
                Formula.Not
                  (Formula.K (Validator.V0, f Anchor_committed_v3)) ))))

(* S1 conjunct B, R3 ignorance witness, second half: the two states that
   witness it. Both share V0's view (V0 direct-committed L) and disagree on the
   peer's anchor commit, which is exactly the pair the ~K needs. *)
let s1_witness_pair_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (direct_commit_V0 /\\ commit_anchor_V3) and EF (direct_commit_V0 \
         /\\ ~commit_anchor_V3)"
        true
        (Checker.satisfiable sys
           (Formula.And (f Direct_commit_l_v0, f Anchor_committed_v3))
        && Checker.satisfiable sys
             (Formula.And
                (f Direct_commit_l_v0, Formula.Not (f Anchor_committed_v3)))))

(* S1 conjunct C, R2 non-singleton class. At an operative state where V0 has
   direct-committed L and the peer's anchor record HAS arrived, the atom
   direct_commit_V3(L) is false (the peer reached the anchor by the walk-back),
   yet V0 does not know it is false: the sibling state in which the peer
   direct-committed L first and then the anchor publishes an
   indistinguishable record. So the delivered-report class is not a singleton
   and conjunct C's K is not trivially true. *)
let s1_report_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (direct_commit_V0 /\\ report /\\ ~K_V0(~direct_commit_V3))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Direct_commit_l_v0, f Peer_anchor_report_v0),
                Formula.Not
                  (Formula.K
                     (Validator.V0, Formula.Not (f Direct_commit_l_v3))) ))))

(* S2 contingency: the global negative is NOT rigid - in the supported world
   the peer really does direct-commit L, so V0's knowledge of the negative
   fails somewhere reachable. *)
let s2_knowledge_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_V0(AG ~direct_commit_V3(L))" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 ( Validator.V0,
                   Formula.Ag (Formula.Not (f Direct_commit_l_v3)) )))))

(* S2, R2 non-singleton class. At an operative skip state the atom
   commit_anchor_V3 is FALSE, yet V0 does not know it is false: another
   reachable state with the same V0 view has the peer's anchor committed. *)
let s2_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (skip /\\ ~K_V0(~commit_anchor_V3))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And
                  (f Anchor_committed_v0, Formula.Not (f L_subdag_v0)),
                Formula.Not
                  (Formula.K
                     (Validator.V0, Formula.Not (f Anchor_committed_v3))) ))))

(* S2's peer-direct-commit target is reachable at all, so the AG-negative
   operand is a real constraint and not satisfied by an empty predicate. *)
let peer_direct_commit_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF direct_commit_V3(L)" true
        (Checker.satisfiable sys (f Direct_commit_l_v3)))

(* S3's antecedent is live in the world that matters: a leader with at most f
   supporters - so no direct commit is possible anywhere - yet linked to the
   anchor, which is exactly the state the walk-back exists to serve. *)
let unsupported_but_linked_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (linked(A,L) /\\ ~support>=f+1 /\\ ~subdag_V0(leader=L))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Linked_anchor_l,
                Formula.And
                  ( Formula.Not (f Support_quorum_high),
                    Formula.Not (f L_subdag_v0) ) ))))

(* Channel soundness: a peer's anchor record never arrives without the commit
   that produced it. The publication is emitted from handle_consensus_output
   (subscriber.rs:296-316) and the receiver requires committee membership and a
   valid BLS signature (handler.rs:307-338), so the record is an attestation.
   This is what grounds S1's conjunct C. *)
let report_implies_peer_anchor_commit () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "G (anchor ConsensusResult(V3) seen -> commit_anchor_V3)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 (f Peer_anchor_report_v0, f Anchor_committed_v3)))))

(* Channel asynchrony: the record is gossip, so the peer can have committed the
   anchor while V0 has not yet received anything. This state is what makes S1's
   ignorance conjunct non-vacuous - delete it and conjunct B would hold only
   because the model gave the peer nothing to publish. *)
let commit_without_report_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (commit_anchor_V3 /\\ ~anchor ConsensusResult(V3) seen)" true
        (Checker.satisfiable sys
           (Formula.And
              (f Anchor_committed_v3, Formula.Not (f Peer_anchor_report_v0)))))

let () =
  Alcotest.run "subdag_leader_walk"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Subdag_leader_walk_statements.name `Quick
              (prove_one st))
          Subdag_leader_walk_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "support-quorum-implies-linked" `Quick
            support_quorum_implies_linked;
          Alcotest.test_case "unsupported-leader-never-direct-committed" `Quick
            unsupported_leader_never_direct_committed;
          Alcotest.test_case "linked-leader-never-skipped" `Quick
            linked_leader_never_skipped;
          Alcotest.test_case "order-dag-repair-path-present" `Quick
            order_dag_repair_path_present;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "s1-knowledge-contingent" `Quick
            s1_knowledge_contingent;
          Alcotest.test_case "s1-class-not-singleton" `Quick
            s1_class_not_singleton;
          Alcotest.test_case "s1-ignorance-witness" `Quick s1_ignorance_witness;
          Alcotest.test_case "s1-witness-pair-reachable" `Quick
            s1_witness_pair_reachable;
          Alcotest.test_case "s1-report-class-not-singleton" `Quick
            s1_report_class_not_singleton;
          Alcotest.test_case "s2-knowledge-contingent" `Quick
            s2_knowledge_contingent;
          Alcotest.test_case "s2-class-not-singleton" `Quick
            s2_class_not_singleton;
          Alcotest.test_case "peer-direct-commit-reachable" `Quick
            peer_direct_commit_reachable;
          Alcotest.test_case "unsupported-but-linked-reachable" `Quick
            unsupported_but_linked_reachable;
        ] );
      ( "channel",
        [
          Alcotest.test_case "report-implies-peer-anchor-commit" `Quick
            report_implies_peer_anchor_commit;
          Alcotest.test_case "commit-without-report-reachable" `Quick
            commit_without_report_reachable;
        ] );
    ]
