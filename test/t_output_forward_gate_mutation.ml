(** Confirm-by-mutation pins for the OUTPUT_FORWARD_GATE family. Each statement
    is paired with the ONE gate deletion that refutes it, and the refutation is
    asserted to be a genuine [Refuted] rather than a [Vacuous_antecedent] - a
    mutation that merely makes a statement's situation unreachable would
    otherwise look like a pin while proving nothing.

    - {!Output_forward_gate_model.No_stale_arm} deletes the
      [OutputContinuity::Stale] arm (run_epoch.rs:575-583), so a re-delivery at
      or below the watermark reaches the engine and executes a second time. No
      sibling repairs it: the engine's whole state is [queued] plus
      [parent_header] (engine/lib.rs:49-80), it makes no number or hash
      comparison (engine/lib.rs:227-252, payload_builder.rs:51-76), and the
      leader count is incremented unconditionally per delivered output
      (payload_builder.rs:30) even on the empty-output early return (:84-97).
    - {!Output_forward_gate_model.No_gap_arm} deletes the
      [OutputContinuity::Gap] arm (run_epoch.rs:584-591), so a silently lagged
      delivery (sync.rs:205-217) is forwarded and the executed chain acquires a
      hole. No sibling notices: [output.parent_hash()] is used once, as a
      tracing span field (payload_builder.rs:41).
    - {!Output_forward_gate_model.Queue_pop_back} replaces [pop_front()] with
      [pop_back()] (engine/lib.rs:124), so a later-numbered output overtakes an
      earlier queued one. No sibling re-orders it: the upstream mpsc is FIFO but
      only feeds [push_back] (engine/lib.rs:249, node.rs:838) and
      [check_output_continuity] runs before the send (run_epoch.rs:574).

    The cross-attribution group is the other half of the evidence: every
    statement is asserted to SURVIVE the two mutations that are not its pin, so
    a pin cannot pass on the strength of some other statement flipping. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Output_forward_gate_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Output_forward_gate_model.Checker.make
       (Output_forward_gate_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Output_forward_gate_statements.name name))
    Output_forward_gate_statements.all

(** Classify a proof outcome so a pin can insist on the reason, not just the
    failure. *)
let outcome sys st =
  Result.fold
    ~ok:(fun _ -> "proved")
    ~error:(fun e ->
      match e with
      | Output_forward_gate_model.Checker.Refuted _ -> "refuted"
      | Output_forward_gate_model.Checker.Vacuous_antecedent -> "vacuous")
    (Output_forward_gate_statements.prove sys st)

(** The negative half of a pin: the statement is REFUTED under the mutation -
    not merely unprovable, and not vacuous. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check string)
            (name ^ " flips to refuted under the mutation")
            "refuted" (outcome sys st))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Output_forward_gate_model.Pristine (fun sys ->
          Alcotest.(check string)
            (name ^ " proves on the pristine model")
            "proved" (outcome sys st))

(** Cross-attribution: the statement still proves under a mutation that is NOT
    its pin, so the pin above is attributable to the gate it deletes. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check string)
            (name ^ " still proves under the unrelated mutation")
            "proved" (outcome sys st))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** S1's name. *)
let s1_name =
  "live-forwarder-skips-stale-redelivery-so-no-output-executes-twice"

(** S2's name. *)
let s2_name = "lagged-output-gap-halts-the-epoch-instead-of-executing-a-hole"

(** S3's name. *)
let s3_name =
  "committed-outputs-execute-in-order-so-one-receipt-certifies-the-prefix"

let () =
  Alcotest.run "output_forward_gate_mutation"
    [
      ( "dropped Stale arm double-executes an already-forwarded output",
        pin Output_forward_gate_model.No_stale_arm s1_name );
      ( "dropped Gap arm executes a hole instead of halting the epoch",
        pin Output_forward_gate_model.No_gap_arm s2_name );
      ( "dropped FIFO discipline overtakes an earlier committed output",
        pin Output_forward_gate_model.Queue_pop_back s3_name );
      ( "cross-attribution: each gate carries exactly its own statement",
        [
          Alcotest.test_case "S1 survives No_gap_arm" `Quick
            (survives_under Output_forward_gate_model.No_gap_arm s1_name);
          Alcotest.test_case "S1 survives Queue_pop_back" `Quick
            (survives_under Output_forward_gate_model.Queue_pop_back s1_name);
          Alcotest.test_case "S2 survives No_stale_arm" `Quick
            (survives_under Output_forward_gate_model.No_stale_arm s2_name);
          Alcotest.test_case "S2 survives Queue_pop_back" `Quick
            (survives_under Output_forward_gate_model.Queue_pop_back s2_name);
          Alcotest.test_case "S3 survives No_stale_arm" `Quick
            (survives_under Output_forward_gate_model.No_stale_arm s3_name);
          Alcotest.test_case "S3 survives No_gap_arm" `Quick
            (survives_under Output_forward_gate_model.No_gap_arm s3_name);
        ] );
    ]
