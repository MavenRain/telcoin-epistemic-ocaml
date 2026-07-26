(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    EXEX_LIFE family: each of the three statements is pinned by its OWN gate
    deletion, and each row asserts the proof FLIPS to an error on the mutated
    model while the matching pristine row stays proved.

    - {!Exex_life_model.No_epoch_window} deletes all THREE textual copies of the
      [leader_epoch() > epoch -> bail] window (subscriber.rs:143-147,
      state-sync/src/lib.rs:324-327 immediately before the sole
      [sync_output().send] at :380, and the caller's re-test at :231-233). Three
      sites, because the state-sync copy is a REAL sibling that would silently
      repair a one-site deletion; three further routes (the single
      [notify_exex_consensus_output] call site, the single [sync_output] sender,
      and the replay seam that yields only [ChainExecuted]) are ruled out. A
      fourth, the ExEx's read-only [ConsensusChain], is NOT ruled out as a data
      path - the closed-epoch pack fetchers write it and the forward drain reads
      outputs back OUT of it (state-sync/src/lib.rs:305-310) before testing the
      window at :324-327 - but it emits no [TnExExNotification], and the modeled
      atom is the notification (MODELLING SCOPE in {!Exex_life_model}). The
      mutation adds an epoch-(E+1) ExEx delivery to a host still at epoch E,
      refuting S1 conjunct A while leaving S1's B and C conjuncts intact.

    - {!Exex_life_model.No_committee_gate} deletes the
      [if let Some(committee) = self.get_committee(epoch).await] Option gate
      (handler.rs:251, else arm :280-286), so an unevaluable certificate is
      forwarded to the ExEx. No sibling repairs it: [notify_exex_certificate] is
      the sole [CertificateAccepted] producer with one call site,
      [validate_received] verifies nothing, and both the state-sync hand-off and
      the storage write sit inside the [Some] arm, so no route emits a
      [CertificateAccepted] for an unevaluable certificate. The third source of
      [get_committee] - the epoch-record fallback of handler.rs:221 - is not a
      repair either but it IS now modeled explicitly (the epoch-record branch of
      [t_cert_arrive] and the relaxed [t_cert_regossip] guard), so the mutation
      is evaluated against a model that already contains it. It refutes S2
      conjunct A while leaving S2's B and C ignorance conjuncts intact.

    - {!Exex_life_model.Spawn_exex_critical} deletes the shipped
      [exex_critical = false] default by always taking [spawn_critical_task]
      (node.rs:945-952 over :953-957, plus the manager's copy at :976-989).
      Deleting the [catch_unwind] or the critical [Err] arm instead would be
      silently repaired (task_manager.rs:470-472 and :457-466 respectively),
      which is why the spawn BRANCH is the gate. It freezes every V1-local
      transition while [t_net] keeps running, so the host never crosses the epoch
      boundary (refuting S3 conjunct A) and V2's silent-view class becomes
      uniformly dead (refuting S3 conjunct B). *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Exex_life_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Exex_life_model.Checker.make (Exex_life_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Exex_life_statements.name name))
    Exex_life_statements.all

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
               (Exex_life_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Exex_life_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Exex_life_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "exex_life_mutation"
    [
      ( "dropped epoch window lets ExEx output outrun its host",
        pin Exex_life_model.No_epoch_window
          "exex-output-window-is-a-lower-bound-that-hides-a-two-epoch-network-lead-until-a-cert-verifies"
      );
      ( "dropped committee gate leaks an unverifiable certificate to the ExEx",
        pin Exex_life_model.No_committee_gate
          "unknown-committee-blocks-the-exex-certificate-signal-and-leaves-genuineness-unknown"
      );
      ( "critical ExEx spawn halts the host and becomes internode visible",
        pin Exex_life_model.Spawn_exex_critical
          "isolated-exex-failure-never-halts-the-host-and-is-internode-opaque" );
    ]
