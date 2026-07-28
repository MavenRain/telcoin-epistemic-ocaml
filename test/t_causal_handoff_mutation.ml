(** Confirm-by-mutation pins for the CAUSAL_HANDOFF family. Three gate
    deletions, one per statement, each asserted in BOTH directions (the
    statement proves pristine and refutes under the mutation) so that a pin
    cannot pass because some OTHER statement of the family flipped.

    - {!Causal_handoff_model.Handoff_push_back} deletes the [push_front] at
      cert_manager.rs:123, so the arrival batch leaves as [a; b; p]. The
      consumer does not re-sort: [check_parents] (state.rs:187-214) returns
      [MissingParent] / [MissingParentRound], which rides [?] out of
      bullshark.rs:116 and state.rs:372-376 and kills a critical task
      (state.rs:347-349). [write_all] (cert_manager.rs:196) has already stored
      the batch before any handoff, so the store cannot repair DAG order, and
      [update_pending]'s [pop_front] (pending_cert_manager.rs:95) is not a
      second ordering gate because a key is enqueued at :122 only after its
      certificate is on the ready queue at :125. No sibling path repairs it.

    - {!Causal_handoff_model.Release_highest_first} deletes the
      [first_key_value()] at pending_cert_manager.rs:140, so the drain takes the
      HIGHEST blocked key: it force-clears a still-parked parent at :151-153 and
      releases that parent's child first. [update_pending] orders certificates
      only within one release and cannot repair the order across two
      [next_for_gc_round] iterations; the arrival-path guard at
      cert_manager.rs:108 does not govern the drain. No sibling path repairs it.

    - {!Causal_handoff_model.Target_retain_default_zero} deletes the
      [unwrap_or(gc_round)] floor at certificate_fetcher.rs:337 and leaves the
      store exit intact. Once the horizon passes the target round the store exit
      is dead anyway, because [written_rounds] is built from
      [origins_after_round(gc_round + 1)] (:365, certificate_store.rs:329-351);
      and no other write to [self.targets] removes anything - the insert at :212
      admits strictly higher rounds only, [Kick] (:181-190) never clears, there
      is no sweep and the epoch guard (:195-204) only skips ADDING. No sibling
      path repairs it. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Causal_handoff_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Causal_handoff_model.Checker.make (Causal_handoff_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Causal_handoff_statements.name name))
    Causal_handoff_statements.all

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
               (Causal_handoff_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Causal_handoff_model.Pristine (fun sys ->
          Alcotest.(check bool)
            (name ^ " proves on the pristine model")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Causal_handoff_statements.prove sys st)))

(** A statement that must be INSENSITIVE to a mutation: the deletion belongs to
    another gate, so attribution stays clean. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " is untouched by this unrelated deletion")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Causal_handoff_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The two statements a given deletion must NOT disturb. *)
let insensitive mut names =
  List.map
    (fun n -> Alcotest.test_case (n ^ ":survives") `Quick (survives_under mut n))
    names

(** Statement names, spelled once. *)
let s1 = "unlocked-parent-precedes-its-dependents-into-consensus"

(** S2's name. *)
let s2 = "gc-release-drains-the-lowest-blocked-round-first"

(** S3's name. *)
let s3 = "every-fetch-target-is-eventually-dropped-by-the-gc-floor"

let () =
  Alcotest.run "causal_handoff_mutation"
    [
      ( "arrival-release-order",
        pin Causal_handoff_model.Handoff_push_back s1
        @ insensitive Causal_handoff_model.Handoff_push_back [ s2; s3 ] );
      ( "gc-drain-key-order",
        pin Causal_handoff_model.Release_highest_first s2
        @ insensitive Causal_handoff_model.Release_highest_first [ s1; s3 ] );
      ( "fetch-target-gc-floor",
        pin Causal_handoff_model.Target_retain_default_zero s3
        @ insensitive Causal_handoff_model.Target_retain_default_zero [ s1; s2 ]
      );
    ]
