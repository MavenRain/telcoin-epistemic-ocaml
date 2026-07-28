(** Confirm-by-mutation pins for the parent-batch-forward family. Each pin
    asserts BOTH halves - the statement proves on the pristine model and
    refutes under one named gate deletion - so a pin cannot pass on the
    strength of some other statement flipping.

    The four gates, and why no sibling path in telcoin-network repairs the
    deletion at the place each claim is anchored:

    - {!Parent_batch_forward_model.No_drain} replaces the [.drain(..)] of
      aggregators/certificates.rs:98 with a clone. The header IS repaired -
      it is a [BTreeSet<HeaderDigest>] (types/src/primary/header.rs:74) filled
      by proposer.rs:213 - and the model carries that repair as
      {!Parent_batch_forward_model.hdr}, which is why the claim is anchored on
      [last_parents] instead, where [enough_votes] (proposer.rs:351-364) adds
      an origin's stake once per vector element with no de-duplication.
    - {!Parent_batch_forward_model.No_parents_forward} deletes the send at
      aggregators/certificates.rs:39-41. The only other producer on the same
      channel, state_sync/cert_validator.rs:157-158, survives the deletion and
      still fires, so the node keeps advancing rounds - but it sends
      [(vec![], ..)], which the [Greater] arm ASSIGNS (proposer.rs:407), so it
      can never make [last_parents] non-empty. The future-round quorum batch
      of {!Parent_batch_forward_model.step_future_batch} is NOT a sibling
      that repairs this: :39-41 is round-generic, so that batch is exactly
      what the deletion removes.
    - {!Parent_batch_forward_model.No_equal_arm_extend} deletes
      [self.last_parents.extend(parents);] at proposer.rs:447. The [Greater]
      arm ASSIGNS rather than extends and has already fired for the first
      batch, [Less] ignores, and the header is built only from
      [std::mem::take(&mut self.last_parents)] (proposer.rs:592) with no store
      re-scan, so nothing re-admits the late origin. This pin lands on
      conjunct (1) of S3, the admissibility [EF]; conjunct (2) of S3 is
      vacuously true under it, because the late origin never enters
      [last_parents] at all.
    - {!Parent_batch_forward_model.No_equivocation_guard} deletes
      [authorities_seen.insert] at aggregators/certificates.rs:83-85. The one
      equivocation detector in the crate, consensus/state.rs:145-157, is fed
      only after [append_certificate] has already run
      (state_sync/cert_manager.rs:205-216), so it cannot retract a batch that
      is already on the [parents] channel.

    Under every pin the statement's antecedent stays reachable, so each flip
    is a genuine refutation and not an antecedent that evaporated. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Parent_batch_forward_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Parent_batch_forward_model.Checker.make
       (Parent_batch_forward_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Parent_batch_forward_statements.name name))
    Parent_batch_forward_statements.all

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
               (Parent_batch_forward_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Parent_batch_forward_model.Pristine (fun sys ->
          Alcotest.(check bool)
            (name ^ " proves on the pristine model")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Parent_batch_forward_statements.prove sys st)))

(** The statement's antecedent is still reachable under the mutation, so the
    flip above is a refutation and not a vacuous antecedent. *)
let antecedent_survives mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " keeps a reachable antecedent under the mutation")
            true
            (Parent_batch_forward_model.Checker.satisfiable sys
               st.Parent_batch_forward_statements.antecedent))

(** A pristine-proves plus mutated-refutes pair for one statement, with the
    antecedent-survival check that keeps the flip honest. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
    Alcotest.test_case (name ^ ":antecedent-survives") `Quick
      (antecedent_survives mut name);
  ]

let () =
  Alcotest.run "parent_batch_forward_mutation"
    [
      ( "drain",
        pin Parent_batch_forward_model.No_drain
          "parent-batch-drain-keeps-last-parents-duplicate-free" );
      ( "quorum-forward",
        pin Parent_batch_forward_model.No_parents_forward
          "quorum-forward-gives-proposer-trustworthy-parents" );
      ( "equivocation-guard",
        pin Parent_batch_forward_model.No_equivocation_guard
          "quorum-forward-gives-proposer-trustworthy-parents" );
      ( "equal-arm-extend",
        pin Parent_batch_forward_model.No_equal_arm_extend
          "late-origin-admissible-and-evicted-only-by-a-future-round-jump" );
    ]
