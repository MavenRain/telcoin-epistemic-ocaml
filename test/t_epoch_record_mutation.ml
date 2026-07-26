(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    EPOCH_RECORD family: each of the three statements is pinned by its own gate
    deletion, and each row asserts the proof FLIPS to an error on the mutated
    model while still proving on the pristine one.

    - {!Epoch_record_model.No_quorum_count} deletes the
      [if auth_iter < self.super_quorum()] branch of
      [EpochRecord::verify_with_cert] (crates/types/src/primary/epoch.rs:84),
      so a Byzantine peer's sub-quorum certificate - always producible, since
      V1's own vote is gossiped in the clear (epoch_votes.rs:71) and
      [verify_secure] rejects only an EMPTY key list
      (bls_signature.rs:274-276) - is accepted and saved at epoch.rs:107.
      (E_solo, St_cert, Sg_scan1, B_spent) becomes reachable, refuting S1's
      quorum gate directly and its knowledge conjunct via the poisoned view
      class. The one genuine sibling, the producer-side count at
      epoch_votes.rs:103, is kept LIVE in the model ([Sg_tally] and
      [Sg_tally_quorum] are mutation-independent), so the refutation is
      attributable to epoch.rs:84 alone.
    - {!Epoch_record_model.Cert_conjunct_dropped} relaxes the [Some(_)]
      certificate conjunct at crates/state-sync/src/epoch.rs:61 to
      [Some((rec, _))], so the collector marks a certless record complete and
      advances the cursor over an epoch NOBODY certified.
      (E_solo, St_rec, Sg_scan2, B_avail) becomes reachable, refuting S2's
      "some record was super-quorum certified" conjunct, its knowledge
      conjunct and its divergence conjunct at once. No repair exists: the
      three in-scan cursor lowerings (epoch.rs:96, :113, :136) all sit inside
      the fetch arm the mutation bypasses, a restart re-enters the same
      relaxed skip, the epoch-pack route only covers epochs whose record is
      already stored (consensus.rs:110-135), and storage never back-fills
      (epoch_records.rs:369-377).
    - {!Epoch_record_model.Cursor_starts_at_latest} replaces
      [let mut last_epoch: Epoch = 0;] (crates/state-sync/src/epoch.rs:190)
      with the highest stored record epoch, so the [Sg_boot] step lands on
      [Sg_scan2] and the certless-but-endorsed state livelocks on its
      self-loop: S3's [Af] target is never reached. No repair exists: the
      in-scan lowerings only reach epochs the scan already visited, and the
      watch driver is monotone UP ([requested_epoch >= last_epoch] at
      epoch.rs:193, [current.max(previous_epoch)] at run_epoch.rs:461-462 and
      :479-480).

    Each pin's antecedent stays reachable under its mutation, so every
    refutation is a genuine [Refuted], never a [Vacuous_antecedent]. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Epoch_record_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Epoch_record_model.Checker.make (Epoch_record_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Epoch_record_statements.name name))
    Epoch_record_statements.all

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
               (Epoch_record_statements.prove sys st)))

(** The negative half's honesty check: the mutated refutation is a real
    [Refuted], not a [Vacuous_antecedent] - the antecedent is still reachable
    on the mutated model. *)
let antecedent_reachable_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " antecedent is still reachable under the mutation")
            true
            (Epoch_record_model.Checker.satisfiable sys
               st.Epoch_record_statements.antecedent))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Epoch_record_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Epoch_record_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement, with the
    non-vacuity check that keeps the refutation meaningful. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
    Alcotest.test_case (name ^ ":mutated-nonvacuous") `Quick
      (antecedent_reachable_under mut name);
  ]

let () =
  Alcotest.run "epoch_record_mutation"
    [
      ( "dropped super-quorum count kills certified-implies-known-quorum",
        pin Epoch_record_model.No_quorum_count
          "epoch-cert-implies-known-super-quorum-endorsement" );
      ( "dropped certificate conjunct kills cursor-implies-certified-and-known",
        pin Epoch_record_model.Cert_conjunct_dropped
          "uncertified-epoch-record-implies-ignorance-until-cert" );
      ( "cursor starting at latest kills the restart back-fill",
        pin Epoch_record_model.Cursor_starts_at_latest
          "restart-rescan-from-zero-recovers-certified-record-gap" );
    ]
