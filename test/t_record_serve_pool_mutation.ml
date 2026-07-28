(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    RECORD_SERVE_POOL family. Each statement has its OWN gate deletion, and each
    row asserts the proof flips to an error on the mutated model while the
    pristine row is the matching positive half.

    - S1 is pinned by {!Record_serve_pool_model.No_per_peer_record_cap}, which
      deletes the [count < MAX_PENDING_REQUESTS_PER_PEER] conjunct of
      [try_admit_epoch_record] (network/mod.rs:359). One requester then takes a
      third, fourth and fifth slot, so the table [(0,0,5)] is reachable and both
      conjuncts fail at once: occupancy 5 with a single holder, and a requester
      over the per-peer cap. The global permit at :356 is untouched, so S2's
      bound and S3's dispatch keep proving and the refutation is attributable to
      the deleted conjunct alone. No sibling limiter repairs it (the libp2p
      per-peer inbound window is a 256/second RATE on streams, [try_admit_sync]
      guards a different semaphore and counter, and the request-response/QUIC
      defaults are 100 per peer and 10_000 streams).
    - S2 is pinned by {!Record_serve_pool_model.No_record_admission_gate}, which
      deletes the [try_admit_epoch_record] call and its [else { return; }] arm
      (network/mod.rs:1602-1613) so a serve task is spawned for every request.
      Occupancy passes the cap, refuting the bound; and because the shed branch
      vanishes with the gate, "sent and nothing back" can only be a running
      serve, so the requester's serve-opacity conjunct is refuted too. Nothing
      else bounds this task family: [task_spawner.spawn_task] is an unbounded
      spawn and the deleted call is the crate's only epoch-record limiter.
    - S3 is pinned by
      {!Record_serve_pool_model.No_unaddressed_request_reject}, which deletes
      the [(None, None) => return Err(PrimaryNetworkError::InvalidEpochRequest)]
      arm (handler.rs:999) and serves the latest record as the request type's
      own doc comment specifies (network/message.rs:73-74). The admitted
      unaddressed serve then reaches a delivered response with no Medium charge
      recorded, refuting the "never answered without the charge" conjunct.
      Nothing else
      charges it: [InvalidEpochRequest] is constructed at handler.rs:999 and
      nowhere else, no caller-side validation exists, and the shed path drops
      the channel without penalty strictly before the dispatch match.

    Every antecedent stays REACHABLE under the mutation that pins its statement
    ([occupancy = 5] under the first, [serving(P)] under the second,
    [serving_unaddressed(P)] under the third), so no row flips merely because
    [prove_nonvacuous] found a vacuous antecedent. The cross rows below assert
    the two statements a mutation is NOT meant to touch still prove under it,
    which is what makes each pin attributable. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Record_serve_pool_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Record_serve_pool_model.Checker.make
       (Record_serve_pool_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Record_serve_pool_statements.name name))
    Record_serve_pool_statements.all

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
               (Record_serve_pool_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Record_serve_pool_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Record_serve_pool_statements.prove sys st)))

(** Attribution: a statement the mutation is NOT aimed at still proves under it,
    so the pinned row's flip cannot be some other statement's collapse. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " still proves under this unrelated mutation")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Record_serve_pool_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The exhaustion statement's name. *)
let s1_name = "record-serve-pool-exhaustion-needs-three-distinct-requesters"

(** The bound-and-blind-requester statement's name. *)
let s2_name =
  "epoch-record-serve-bounded-and-shed-invisible-to-the-shed-requester"

(** The penalty-split statement's name. *)
let s3_name =
  "unaddressed-epoch-record-request-is-charged-only-when-the-pool-had-room"

let () =
  Alcotest.run "record_serve_pool_mutation"
    [
      ( "dropped per-peer cap lets one requester monopolise the pool",
        pin Record_serve_pool_model.No_per_peer_record_cap s1_name );
      ( "dropped admission gate breaks the pool bound and the requester's \
         blindness",
        pin Record_serve_pool_model.No_record_admission_gate s2_name );
      ( "dropped unaddressed-request rejection removes the Medium charge",
        pin Record_serve_pool_model.No_unaddressed_request_reject s3_name );
      ( "attribution: the per-peer-cap deletion touches nothing else",
        [
          Alcotest.test_case (s2_name ^ ":survives") `Quick
            (survives_under Record_serve_pool_model.No_per_peer_record_cap
               s2_name);
          Alcotest.test_case (s3_name ^ ":survives") `Quick
            (survives_under Record_serve_pool_model.No_per_peer_record_cap
               s3_name);
        ] );
      ( "attribution: the unaddressed-reject deletion touches nothing else",
        [
          Alcotest.test_case (s1_name ^ ":survives") `Quick
            (survives_under Record_serve_pool_model.No_unaddressed_request_reject
               s1_name);
          Alcotest.test_case (s2_name ^ ":survives") `Quick
            (survives_under Record_serve_pool_model.No_unaddressed_request_reject
               s2_name);
        ] );
      ( "attribution: the admission-gate deletion leaves the dispatch arm alone",
        [
          Alcotest.test_case (s3_name ^ ":survives") `Quick
            (survives_under Record_serve_pool_model.No_record_admission_gate
               s3_name);
        ] );
    ]
