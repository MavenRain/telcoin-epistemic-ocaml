(** Confirm-by-mutation for the WORKER_STREAM_QUOTA family. Each pin asserts
    BOTH halves - the statement proves on the pristine model and refutes under
    the gate deletion - so a pin can never pass because some other statement
    flipped.

    THE THREE GATES, AND WHY NO SIBLING PATH REPAIRS ANY OF THEM (the full
    hunts are on the {!Worker_stream_quota_model.mutation} constructors).

    - {!Worker_stream_quota_model.No_legacy_per_peer_cap} deletes the per-peer
      refusal of [try_admit_legacy] (network/mod.rs:280-289). [try_admit_sync]
      keeps its identical check (:239-243) and is left intact in the model, but
      it gates only the SYNC path, and a legacy flood is routed to
      [process_request_batches_stream] (:438-446, :576-587), which never
      traverses it. The global semaphore survives and is modelled - it is
      peer-blind, which is what a single flooder drains.
      [cleanup_stale_pending_requests] (:803-809) is modelled and only expires
      entries, so it refuses no admission.
    - {!Worker_stream_quota_model.No_serving_guard} deletes the
      [LegacyStreamGuard::admit] half of [begin_serving_legacy]
      (network/mod.rs:330). The surviving [OwnedSemaphorePermit] inside the
      removed [PendingBatchStream] (:94-96) IS kept in the model, so the
      mutation is no stronger than the real defect; it bounds the pool and not
      the peer. [sync_stream_peers] (:353-359) counts sync streams only, and
      the cleanup retains over a map the entry has already left. This is the
      shape of GHSA-h9fv-qwvh-jv37, named at :860-863 and :907-910.
    - {!Worker_stream_quota_model.No_pre_read_sync_shed} deletes the early shed
      arm (network/mod.rs:704-722) so a refused stream reaches the request
      read at :728-739 first. The wire answer is byte-identical, so the
      victim's view and the reachable denied states are unchanged - only the
      responder's knowledge changes.

    WHICH CONJUNCT EACH DELETION KILLS (verified, not assumed). Deleting the
    legacy per-peer gate refutes S1's quota and two-holders conjuncts and S2's
    no-re-arm conjunct, but leaves S2's no-vanishing-count conjunct and ALL of
    S3 intact. Deleting the serving guard refutes all four counting conjuncts
    and still leaves all of S3 intact. Deleting the pre-read shed refutes
    EXACTLY S3's first conjunct and nothing else in the family - the counting
    statements are untouched by it. So each pin below flips for its own
    reason. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Worker_stream_quota_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Worker_stream_quota_model.Checker.make
       (Worker_stream_quota_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Worker_stream_quota_statements.name name))
    Worker_stream_quota_statements.all

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " flips to refuted under the mutation")
            false
            (Result.fold ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Worker_stream_quota_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Worker_stream_quota_model.Pristine (fun sys ->
          Alcotest.(check bool)
            (name ^ " proves on the pristine model")
            true
            (Result.fold ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Worker_stream_quota_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The deletion must not disturb a statement it has no business disturbing:
    the sync-shed deletion leaves the two counting statements standing, so its
    pin on S3 is specific and not a side effect of a smaller reachable set. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " still proves under the unrelated mutation")
            true
            (Result.fold ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Worker_stream_quota_statements.prove sys st)))

let () =
  Alcotest.run "worker_stream_quota_mutation"
    [
      ( "legacy-per-peer-gate",
        pin Worker_stream_quota_model.No_legacy_per_peer_cap
          "per-peer-stream-cap-reserves-capacity-for-every-peer"
        @ pin Worker_stream_quota_model.No_legacy_per_peer_cap
            "serving-legacy-stream-stays-charged-to-its-peer"
        @ [
            Alcotest.test_case "sync-shed-statement:unaffected" `Quick
              (survives_under Worker_stream_quota_model.No_legacy_per_peer_cap
                 "sync-shed-conceals-request-and-saturation");
          ] );
      ( "pending-to-serving-handoff",
        pin Worker_stream_quota_model.No_serving_guard
          "serving-legacy-stream-stays-charged-to-its-peer"
        @ pin Worker_stream_quota_model.No_serving_guard
            "per-peer-stream-cap-reserves-capacity-for-every-peer"
        @ [
            Alcotest.test_case "sync-shed-statement:unaffected" `Quick
              (survives_under Worker_stream_quota_model.No_serving_guard
                 "sync-shed-conceals-request-and-saturation");
          ] );
      ( "sync-shed-before-read",
        pin Worker_stream_quota_model.No_pre_read_sync_shed
          "sync-shed-conceals-request-and-saturation"
        @ [
            Alcotest.test_case "quota-statement:unaffected" `Quick
              (survives_under Worker_stream_quota_model.No_pre_read_sync_shed
                 "per-peer-stream-cap-reserves-capacity-for-every-peer");
            Alcotest.test_case "handoff-statement:unaffected" `Quick
              (survives_under Worker_stream_quota_model.No_pre_read_sync_shed
                 "serving-legacy-stream-stays-charged-to-its-peer");
          ] );
    ]
