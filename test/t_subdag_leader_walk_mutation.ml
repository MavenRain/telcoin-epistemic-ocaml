(** Confirm-by-mutation for the SUBDAG_LEADER_WALK family. Two gate deletions,
    each pinned per statement so that no statement can pass on another's
    refutation:

    - {!Subdag_leader_walk_model.No_leader_support_gate} deletes the f+1
      support gate bullshark.rs:203-206, so [commit_leader] proceeds for any
      leader certificate it finds. It refutes S1 (V0 can direct-commit an
      unsupported L in the unlinked world, where the peer's walk-back
      legitimately skips it, so the quorum-intersection premise dies) and S2
      (the peer can direct-commit the very leader V0 skipped as unlinked). It
      deliberately does NOT refute S3, because it only ADDS direct commits and
      those also produce an L-led subdag - so the S3 pin cannot be borrowed
      from it. Sibling hunt: that comparison is the only support check in the
      whole path - [leader_certificate] (leader_schedule.rs:311-326) filters
      nothing, [order_leaders]' gate is linkedness and applies only to previous
      leaders (bullshark.rs:301), and [process_certificate]
      (bullshark.rs:107-171) adds no second check.
    - {!Subdag_leader_walk_model.No_walk_back_inclusion} deletes the inclusion
      block bullshark.rs:300-306, so [order_leaders] returns [[anchor]] alone.
      It refutes S3 (a linked, unsupported L never anchors a subdag of its own)
      and S1 (the peer commits an anchor with L absent from its leaders).

    The last group is the R4/R5 evidence. [utils::order_dag] (utils.rs:10-57)
    walks the anchor's whole ancestor closure, so the naive claim "a linked
    leader's certificates eventually commit" IS silently repaired by this
    mutation. The model carries that repair path, and the group below asserts
    that the naive leads-to still HOLDS under the mutation that kills S3 -
    which is exactly why S3 is phrased leader-anchored. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Subdag_leader_walk_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Subdag_leader_walk_model.Checker.make
       (Subdag_leader_walk_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Subdag_leader_walk_statements.name name))
    Subdag_leader_walk_statements.all

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
               (Subdag_leader_walk_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Subdag_leader_walk_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Subdag_leader_walk_statements.prove sys st)))

(** The attribution half of a pin: a statement this mutation must NOT touch
    still proves under it, so a green pin elsewhere cannot be an accident of a
    mutation that breaks everything. *)
let still_proves_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " still proves under this mutation")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Subdag_leader_walk_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The naive, certificate-level target that [utils::order_dag] repairs:
    whenever the anchor is linked to L and L's certificates are not yet
    sequenced at V0, they eventually are. *)
let naive_certificate_claim =
  Formula.leads_to
    (Formula.And
       ( f Subdag_leader_walk_model.Linked_anchor_l,
         Formula.Not (f Subdag_leader_walk_model.L_certs_sequenced_v0) ))
    (f Subdag_leader_walk_model.L_certs_sequenced_v0)

(* The naive claim holds on the pristine model - so it looks like a statement
   worth making. *)
let naive_claim_holds_pristine () =
  with_mut Subdag_leader_walk_model.Pristine (fun sys ->
      Alcotest.(check bool) "naive certificate-level claim holds pristine" true
        (Subdag_leader_walk_model.Checker.valid sys naive_certificate_claim))

(* ... and it STILL holds under the very mutation that refutes S3, because
   order_dag sweeps L's certificates into the anchor's closure. A family that
   had stated the naive claim would have shipped a pin that proves nothing.
   This is the R4/R5 receipt for S3's leader-anchored phrasing. *)
let naive_claim_survives_the_mutation () =
  with_mut Subdag_leader_walk_model.No_walk_back_inclusion (fun sys ->
      Alcotest.(check bool)
        "naive certificate-level claim is SILENTLY REPAIRED by order_dag" true
        (Subdag_leader_walk_model.Checker.valid sys naive_certificate_claim))

(* The mutated model really does reach the state S3 forbids: the anchor
   committed, L's certificates swept in by order_dag, and yet no subdag led by
   L. That is the concrete counterexample behind the S3 pin. *)
let leaderless_sweep_reachable_under_mutation () =
  with_mut Subdag_leader_walk_model.No_walk_back_inclusion (fun sys ->
      Alcotest.(check bool)
        "EF (commit_anchor_V0 /\\ certs(L) sequenced /\\ ~subdag_V0(leader=L))"
        true
        (Subdag_leader_walk_model.Checker.satisfiable sys
           (Formula.And
              ( f Subdag_leader_walk_model.Anchor_committed_v0,
                Formula.And
                  ( f Subdag_leader_walk_model.L_certs_sequenced_v0,
                    Formula.Not (f Subdag_leader_walk_model.L_subdag_v0) ) ))))

(* The support-gate deletion really does reach the state it is supposed to:
   L direct-committed by the peer while L has at most f supporters. *)
let unsupported_direct_commit_reachable_under_mutation () =
  with_mut Subdag_leader_walk_model.No_leader_support_gate (fun sys ->
      Alcotest.(check bool)
        "EF (~support>=f+1 /\\ direct_commit_V3(L))" true
        (Subdag_leader_walk_model.Checker.satisfiable sys
           (Formula.And
              ( Formula.Not (f Subdag_leader_walk_model.Support_quorum_high),
                f Subdag_leader_walk_model.Direct_commit_l_v3 ))))

let () =
  Alcotest.run "subdag_leader_walk_mutation"
    [
      ( "dropped f+1 support gate kills known-universal-inclusion",
        pin Subdag_leader_walk_model.No_leader_support_gate
          "supported-leader-commit-implies-known-universal-inclusion" );
      ( "dropped f+1 support gate kills the skip-implies-no-direct-commit \
         negative",
        pin Subdag_leader_walk_model.No_leader_support_gate
          "unlinked-leader-skip-implies-known-global-no-direct-commit" );
      ( "dropped walk-back inclusion kills known-universal-inclusion",
        pin Subdag_leader_walk_model.No_walk_back_inclusion
          "supported-leader-commit-implies-known-universal-inclusion" );
      ( "dropped walk-back inclusion kills per-leader subdag anchoring",
        pin Subdag_leader_walk_model.No_walk_back_inclusion
          "linked-uncommitted-leader-eventually-anchors-its-own-subdag" );
      ( "attribution: the support gate does not touch subdag anchoring",
        [
          Alcotest.test_case "s3-survives-support-gate-deletion" `Quick
            (still_proves_under Subdag_leader_walk_model.No_leader_support_gate
               "linked-uncommitted-leader-eventually-anchors-its-own-subdag");
        ] );
      ( "R4/R5 receipt: the order_dag repair path is live in the model",
        [
          Alcotest.test_case "naive-claim-holds-pristine" `Quick
            naive_claim_holds_pristine;
          Alcotest.test_case "naive-claim-survives-the-mutation" `Quick
            naive_claim_survives_the_mutation;
          Alcotest.test_case "leaderless-sweep-reachable-under-mutation" `Quick
            leaderless_sweep_reachable_under_mutation;
          Alcotest.test_case "unsupported-direct-commit-reachable" `Quick
            unsupported_direct_commit_reachable_under_mutation;
        ] );
    ]
