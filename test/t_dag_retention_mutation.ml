(** Confirm-by-mutation for the DAG_RETENTION family: each statement proves on
    the pristine model and REFUTES under the gate deletion it names, and each
    deletion is additionally shown to bite for the reason claimed rather than by
    disturbing something else.

    The three gates, and why no sibling path in the real code repairs any of
    them (each hunt is written out in full in the constructor doc comments of
    {!Dag_retention_model.mutation}):

    - {!Dag_retention_model.No_last_committed_skip} deletes the
      [last_committed] disjunct of the walk skip (utils.rs:37-40). The
      candidate repairs are [already_ordered] (per-walk only, utils.rs:16),
      [dag.retain] (purges nothing here, state.rs:182-183), the below-commit
      return of try_insert (elections only, state.rs:159-160 /
      bullshark.rs:116-119) and [save_consensus] (no uniqueness check,
      state-sync/src/lib.rs:105-114). None applies.
    - {!Dag_retention_model.No_below_commit_shortcircuit} deletes
      bullshark.rs:136-138. The candidate repairs are try_insert's below-commit
      return (A3 is ABOVE its origin's committed round so it passes),
      [wait_for_execution] (state.rs:421-434, passes because the re-committed
      leader's base block is old), the [assert_eq] at state.rs:470 (holds) and
      [save_consensus]. None applies.
    - {!Dag_retention_model.Insert_gated_on_last_committed} deletes the
      always-insert of state.rs:143-148. The candidate repairs are
      [check_parents]' horizon exemption (state.rs:195-197, round 1 only),
      [order_dag]'s tolerant [None] arm (utils.rs:46, never reached), a
      catch/retry of [ConsensusError::MissingParent] (there is none: the
      constructor at state.rs:203 is matched nowhere), crash recovery (shares
      the mutated [try_insert_in_dag] via state.rs:102) and upstream causal
      delivery (cert_manager.rs:103-124, which reads the certificate STORE, not
      the consensus dag - the model carries it as
      {!Dag_retention_model.child_upstream_ready} and it does not repair).

    The effect group is the guard against the classic false pin. A statement can
    flip because some unrelated part of the model moved; these cases assert the
    specific offending state the deletion is supposed to create - a second
    delivery of [c1], a second sub-dag anchored on L2, a dead consensus task -
    and assert it is NOT reachable on the pristine model. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Dag_retention_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Dag_retention_model.Checker.make (Dag_retention_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Dag_retention_statements.name name))
    Dag_retention_statements.all

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
               (Dag_retention_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Dag_retention_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Dag_retention_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The offending state a deletion is supposed to create: unreachable on the
    pristine model, reachable under the mutation. This is what stops a pin from
    passing because some unrelated conjunct moved. *)
let effect_pin mut label phi =
  [
    Alcotest.test_case (label ^ ":not-on-pristine") `Quick (fun () ->
        with_mut Dag_retention_model.Pristine (fun sys ->
            Alcotest.(check bool)
              (label ^ " is unreachable on the pristine model")
              false
              (Dag_retention_model.Checker.satisfiable sys phi)));
    Alcotest.test_case (label ^ ":under-mutation") `Quick (fun () ->
        with_mut mut (fun sys ->
            Alcotest.(check bool)
              (label ^ " becomes reachable under the deletion")
              true
              (Dag_retention_model.Checker.satisfiable sys phi)));
  ]

(** Atom injection shorthand. *)
let f a = Formula.Atom a

let () =
  Alcotest.run "dag_retention_mutation"
    [
      ( "dropped walk skip re-sequences an already-committed certificate",
        pin Dag_retention_model.No_last_committed_skip
          "causal-closure-certificate-sequenced-exactly-once-across-subdags"
        @ effect_pin Dag_retention_model.No_last_committed_skip "resequenced(c1)"
            (f Dag_retention_model.C1_resequenced) );
      ( "dropped leader short-circuit re-anchors a committed leader round",
        pin Dag_retention_model.No_below_commit_shortcircuit
          "committed-leader-round-never-reanchored-for-double-execution"
        @ effect_pin Dag_retention_model.No_below_commit_shortcircuit
            "reanchored(L2)" (f Dag_retention_model.Leader2_reanchored) );
      ( "dropped always-insert kills the late child and the consensus task",
        pin Dag_retention_model.Insert_gated_on_last_committed
          "below-commit-certificate-retained-so-children-stay-insertable"
        @ effect_pin Dag_retention_model.Insert_gated_on_last_committed
            "dead(consensus)" (f Dag_retention_model.Consensus_dead) );
    ]
