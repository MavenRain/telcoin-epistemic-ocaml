(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    BATCH_VERDICT family. Two real gate deletions pin all three statements, and
    every statement appears in at least one pin.

    ATTRIBUTION IS ASYMMETRIC BY DESIGN. S1 is pinned by the store gate ONLY.
    The 2026-07 adversarial review confirmed that the second gate does not break
    S1 in the real system - deleting the [RecoverableError] arm removes only the
    responder-side store-failure cause of a possession-free exhaustion, while a
    transport failure bypasses that match entirely ([?] at handle.rs:175-176)
    and still exhausts at quorum_waiter.rs:101-115 with the peer holding
    nothing. The model now carries that branch ([Exh_transport] on leg1), and
    the corresponding row below is a SURVIVES control rather than a pin. A pin
    that a mutation passes only because the abstraction folded the survivor away
    is not evidence, so this control is the load-bearing regression guard for
    that repair: reinstating the fold makes it fail.

    {!Batch_verdict_model.No_peer_store_before_ack} deletes the durable write
    [store.insert::<NodeBatchesCache>(&digest, &batch)] at handler.rs:252-254,
    the write that strictly precedes the primary report (:257-260) and the [Ok]
    ack (:262). The peer still validates and still acks, so V0's view is
    unchanged - only possession disappears. It refutes S2 (the quorum state no
    longer has both peers holding, and no accept state supports
    [K_V0(holds(V1))]) and S1's second ignorance conjunct (with the write gone
    NO peer ever takes possession, [Exh_possess] is unreachable, so
    [K_V0(~holds(V1))] becomes TRUE). It leaves S3's
    two reachable rejected states untouched, so S3 still proves under it and
    the attributions stay clean. No sibling repairs it: the three other
    [insert::<NodeBatchesCache>] sites are all closed on a batch that never
    reached quorum (the gossip prefetch at handler.rs:202-208 fires only after
    the author's publish at worker.rs:320, which sits inside the quorum-success
    arm; batch_fetcher.rs:190-196 can only serve a batch some node already
    stored; network/primary.rs:104-129 writes only digests the local primary
    asked to synchronize (:114) and only batches fetched from a peer that
    already held them; and
    worker.rs:359 is the author's own post-quorum write), and the read side
    cannot manufacture possession either (batch_fetcher.rs:58-68).

    {!Batch_verdict_model.No_recoverable_class} deletes the
    [WorkerResponse::RecoverableError => Err(NetworkError::RPCRetryable)] arm of
    [report_batch] (handle.rs:186-188), so a peer's momentary
    [NodeBatchesCache] write failure (handler.rs:252-254 -> [Internal] ->
    [RecoverableError], message.rs:128-137) arrives as an explicit rejection.
    It refutes S3: V2's exhausted-without-possession leg is reclassified as a
    no-retry rejection, and one such leg beside a genuine permanent rejection on
    V1 already reaches [rejected_stake] = 2 > [max_rejected_stake] = 1 and
    breaks [QuorumRejected] at :236-239 with
    [permanent_reject(V1) /\\ permanent_reject(V2)] FALSE at that very state.
    It leaves S1 AND S2 untouched - S1 because the arm is not on the transport
    path (see the attribution note above), S2 because possession still precedes
    every ack. No sibling repairs it: the [RPCError] arm returns at
    quorum_waiter.rs:99 before any retry, [report_batch] has exactly one call
    site (quorum_waiter.rs:92), the responder-side label at message.rs:125-155
    is no longer consulted downstream, the caller side only renames
    (worker.rs:327-342, batch-builder lib.rs:199-210 collapsing all six
    non-fatal variants), and the same split on the batch-request-stream path
    never feeds [rejected_stake].

    Each row asserts the proof FLIPS to an error on the mutated model; the
    pristine rows are the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Batch_verdict_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Batch_verdict_model.Checker.make (Batch_verdict_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Batch_verdict_statements.name name))
    Batch_verdict_statements.all

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
               (Batch_verdict_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Batch_verdict_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Batch_verdict_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The negative-control half of a pin: the statement is NOT pinned by this
    gate and must still prove under it, which is what makes the other gate's
    refutation cleanly attributable. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " is untouched by this gate and still proves")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Batch_verdict_statements.prove sys st)))

let () =
  Alcotest.run "batch_verdict_mutation"
    [
      ( "dropped peer store-before-ack kills known peer possession",
        pin Batch_verdict_model.No_peer_store_before_ack
          "accepted-report-implies-known-peer-possession" );
      ( "dropped peer store-before-ack collapses anti-quorum possession \
         ignorance",
        pin Batch_verdict_model.No_peer_store_before_ack
          "anti-quorum-leaves-peer-possession-unknown" );
      ( "dropped recoverable error class kills known permanent rejection",
        pin Batch_verdict_model.No_recoverable_class
          "quorum-rejected-implies-known-permanent-but-opaque-verdict" );
      ( "attribution controls: each gate leaves the other's statements alone",
        [
          Alcotest.test_case
            "quorum-rejected-...-opaque-verdict:survives-store-gate" `Quick
            (survives_under Batch_verdict_model.No_peer_store_before_ack
               "quorum-rejected-implies-known-permanent-but-opaque-verdict");
          Alcotest.test_case
            "accepted-report-...-peer-possession:survives-recoverable-gate"
            `Quick
            (survives_under Batch_verdict_model.No_recoverable_class
               "accepted-report-implies-known-peer-possession");
          (* The regression guard for the 2026-07 faithfulness repair: the
             recoverable-class deletion does NOT reach the transport path
             (handle.rs:175-176 unwraps with [?] before the [WorkerResponse]
             match at :177-189), so an exhausted leg is still
             possession-opaque under it and S1 must keep proving. This case
             fails the moment [Exh_transport] is folded back out of leg1. *)
          Alcotest.test_case
            "anti-quorum-...-possession-unknown:survives-recoverable-gate"
            `Quick
            (survives_under Batch_verdict_model.No_recoverable_class
               "anti-quorum-leaves-peer-possession-unknown");
        ] );
    ]
