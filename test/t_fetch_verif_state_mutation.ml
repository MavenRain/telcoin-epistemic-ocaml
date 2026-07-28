(** Confirm-by-mutation pins for the FETCH_VERIF_STATE family. Each group
    deletes ONE gate of the bulk certificate-fetch pipeline and asserts the
    per-statement verdict on both sides, so a pin cannot pass because some
    OTHER statement happened to flip.

    - {!Fetch_verif_state_model.No_periodic_anchor} deletes the periodic
      disjunct [|| cert.header().round().is_multiple_of(...)] at
      crates/consensus/primary/src/state_sync/cert_validator.rs:309-311. The
      surviving leaf test at :308 is a real partial sibling and IS modelled - it
      still routes the leaf C52 through the aggregate check - which is why the
      statements it pins are about the ANCHOR's own aggregate and the SPACING of
      anchors, not about "something was verified". Nothing re-verifies a stored
      certificate afterwards: [verify_signature] returns [Ok] forever on
      [VerifiedIndirectly] (crates/types/src/primary/certificate.rs:271-274),
      [verify_cert] (:253-266) has only the gossip caller
      (network/handler.rs:252), [Certificate::signed_authorities] (:352-354) has
      no non-test caller in the tree, and cert_manager's [is_verified] gate
      (state_sync/cert_manager.rs:88-93) is exactly what [VerifiedIndirectly]
      satisfies (certificate.rs:356-364).
    - {!Fetch_verif_state_model.No_wire_state_reset} deletes the
      [validate_fetched_certificate] map at certificate_fetcher.rs:494-505. The
      two other wire-state resets in the tree - the gossip one at
      network/handler.rs:246 (and inside [verify_cert] at certificate.rs:256)
      and the vote-supplied-parent one at network/handler.rs:670-682 - are on
      routes unreachable from [fetch_and_process_certificates]
      (certificate_fetcher.rs:386-441), so neither repairs it.
    - {!Fetch_verif_state_model.No_chunk_abort} deletes the [??] error
      propagation at cert_validator.rs:337-343. The one partial sibling,
      cert_manager's [if !cert.is_verified()] at cert_manager.rs:88-93, IS
      modelled - it stops the still-[Unverified] members, which is why the
      mutated store is [St_low_only] and not [St_all] - but it cannot stop the
      already-stamped C49.

    Verified attribution (the conjunct that actually fails, checked
    conjunct-by-conjunct while authoring): [No_periodic_anchor] breaks S1's
    known-anchor-quorum, S2's no-adjacent-pair and S3's stamp-window;
    [No_wire_state_reset] breaks only S1's known-anchor-quorum;
    [No_chunk_abort] breaks only S3's quarantine. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Fetch_verif_state_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Fetch_verif_state_model.Checker.make
       (Fetch_verif_state_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Fetch_verif_state_statements.name name))
    Fetch_verif_state_statements.all

(** Does the named statement prove under this mutation? *)
let proves_under mut name k =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          k
            (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false)
               (Fetch_verif_state_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " flips to refuted under the mutation")
        false proved)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  proves_under Fetch_verif_state_model.Pristine name (fun proved ->
      Alcotest.(check bool) (name ^ " proves on the pristine model") true proved)

(** A statement the mutation must NOT break: clean attribution means every other
    statement of the family still proves under it. *)
let survives_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " still proves under the mutation")
        true proved)

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** A survivor case: the mutation leaves this statement proved. *)
let survivor mut name =
  [ Alcotest.test_case (name ^ ":survives") `Quick (survives_under mut name) ]

(** S1's name. *)
let s1_name =
  "anchored-round-certificate-carries-known-quorum-its-neighbour-does-not"

(** S2's name. *)
let s2_name = "fetched-chain-never-runs-two-unchecked-rounds-in-a-row"

(** S3's name. *)
let s3_name = "failed-anchor-quarantines-the-pre-stamped-chain"

let () =
  Alcotest.run "fetch_verif_state_mutation"
    [
      ( "periodic-anchor-disjunct (cert_validator.rs:309-311)",
        pin Fetch_verif_state_model.No_periodic_anchor s1_name
        @ pin Fetch_verif_state_model.No_periodic_anchor s2_name
        @ pin Fetch_verif_state_model.No_periodic_anchor s3_name );
      ( "ingress-wire-state-reset (certificate_fetcher.rs:494-505)",
        pin Fetch_verif_state_model.No_wire_state_reset s1_name
        @ survivor Fetch_verif_state_model.No_wire_state_reset s2_name
        @ survivor Fetch_verif_state_model.No_wire_state_reset s3_name );
      ( "chunk-error-propagation (cert_validator.rs:337-343)",
        pin Fetch_verif_state_model.No_chunk_abort s3_name
        @ survivor Fetch_verif_state_model.No_chunk_abort s1_name
        @ survivor Fetch_verif_state_model.No_chunk_abort s2_name );
    ]
