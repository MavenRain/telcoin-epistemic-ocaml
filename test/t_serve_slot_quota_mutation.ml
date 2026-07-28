(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    SERVE_SLOT_QUOTA family. Each statement has its OWN gate deletion, and each
    row asserts the proof flips to an error on the mutated model while the
    pristine row is the matching positive half. Citations are
    [crates/consensus/primary/src/network/mod.rs] at git HEAD 0c59c15b.

    - S1 is pinned by {!Serve_slot_quota_model.Shared_permit_pool}, which
      deletes the dedicated epoch-record budget - the field
      [epoch_record_semaphore] (mod.rs:1375) and its construction
      [Arc::new(Semaphore::new(MAX_CONCURRENT_EPOCH_RECORD_REQUESTS))]
      (mod.rs:1413) - and routes the admission call at mod.rs:1602-1603 at
      [epoch_stream_semaphore] instead. At a stream-exhausted state
      [try_admit_epoch_record] then returns [None] and the request is shed at
      mod.rs:1612, so no successor answers Q and conjunct A's [EX] fails. The
      per-peer stream gates are untouched, which is why S2 and S3 keep proving
      under it and the flip is attributable to the collapsed budget alone. No
      sibling repairs it inside this responder: the shed sends nothing over the
      wire (mod.rs:1605-1611), the serve holds its permit for its whole lifetime
      (mod.rs:1619-1622), and the rotation the code names (mod.rs:1607-1609)
      moves the requester to a DIFFERENT peer. The 30s pending sweep
      (mod.rs:1451-1456) would eventually free a stream permit, but conjunct A
      is evaluated AT the exhausted state, so a later release cannot repair it.
    - S2 is pinned by {!Serve_slot_quota_model.No_cross_path_count}, which
      deletes only the CROSS terms of the per-peer count - [+ sync_count] at
      mod.rs:1665-1666 and [legacy_count +] at mod.rs:334-337 - and leaves both
      caps and the semaphore in place. P then holds two legacy entries under its
      legacy-only count plus one sync stream under its sync-only count, so the
      state (p_leg = 2, p_syn = 1, t_str = 0) is reachable: conjunct A's cap
      invariant fails there and conjunct B's exhausted pool has a single holder.
      This is the minimal deletion that separates "there is a cap" from "the cap
      spans both paths", which is what the statement is about.
    - S3 is pinned by {!Serve_slot_quota_model.No_per_peer_stream_cap}, which
      deletes the per-peer refusal outright on both stream paths (the [if
      peer_count >= MAX_PENDING_REQUESTS_PER_PEER { ... return false; }] block at
      mod.rs:1667-1676 and the [(... < MAX_PENDING_REQUESTS_PER_PEER)] guard at
      mod.rs:337). P alone takes all three permits, so (p_leg = 3, t_str = 0, Q
      denied) is reachable, the knowledge operand is false there, and because
      that state shares V2's view with every other denied state the knowledge
      collapses at all of them. Note what the mutation does NOT touch: the
      [Deny(DenyReason::AtCapacity)] frame still goes out (mod.rs:1892-1906), so
      the pin removes the INFERENCE and not the message.

    Sibling-repair hunt shared by the two stream mutations: mod.rs:1665-1666 and
    mod.rs:334-337 are the only sites where the two per-peer counters are
    summed; the semaphore taken at mod.rs:332 and mod.rs:1654 is a global bound
    that does not distinguish peers and is exactly what one peer would
    monopolise; [PeerSlotPermit]'s [Drop] (mod.rs:305-315) decrements the same
    counter its admission incremented and cannot re-couple them; the primary's
    pending entry holds its permit from acceptance through service
    (mod.rs:206-208) so unlike the worker there is no pending -> serving handoff
    site that could re-check a cap; and the libp2p per-peer limiter
    ([inbound_rate_limited], crates/network-libp2p/src/stream/behavior.rs:281-
    290) is a RATE of [MAX_INBOUND_PER_WINDOW = 256] per one-second window
    (behavior.rs:42-45) that neither reserves nor releases a concurrency slot -
    it is the one genuine partial sibling here and it delays a monopolisation
    without preventing one.

    Every antecedent stays REACHABLE under the mutation that pins its statement
    ([record_request_outstanding(Q) /\ stream_permits_taken = 3] under the
    first, [stream_permits_taken = 3] under the second,
    [denied_at_capacity(Q)] under the third), so no row flips merely because
    [prove_nonvacuous] found a vacuous antecedent. The cross rows below assert
    the statements a mutation is NOT meant to touch still prove under it, which
    is what makes each pin attributable. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Serve_slot_quota_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Serve_slot_quota_model.Checker.make
       (Serve_slot_quota_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Serve_slot_quota_statements.name name))
    Serve_slot_quota_statements.all

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
               (Serve_slot_quota_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Serve_slot_quota_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Serve_slot_quota_statements.prove sys st)))

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
               (Serve_slot_quota_statements.prove sys st)))

(** The refutation is a refutation, not a vacuity: the pinned statement's
    antecedent is still reachable on the mutated model, so [prove_nonvacuous]
    reached the formula. *)
let antecedent_still_reachable mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ ": antecedent still reachable under the mutation")
            true
            (Serve_slot_quota_model.Checker.satisfiable sys
               st.Serve_slot_quota_statements.antecedent))

(** A pristine-proves plus mutated-refutes pair for one statement, with the
    non-vacuity guard that makes the negative half meaningful. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
    Alcotest.test_case (name ^ ":antecedent-alive") `Quick
      (antecedent_still_reachable mut name);
  ]

(** The class-isolation statement's name. *)
let s1_name = "record-admission-survives-a-saturated-stream-pool"

(** The union-cap statement's name. *)
let s2_name = "stream-slots-are-capped-per-peer-across-both-admission-paths"

(** The denial-knowledge statement's name. *)
let s3_name =
  "a-capacity-denial-tells-a-slotless-requester-two-peers-are-served"

let () =
  Alcotest.run "serve_slot_quota_mutation"
    [
      ( "collapsing the two class budgets lets a stream flood block a record \
         serve",
        pin Serve_slot_quota_model.Shared_permit_pool s1_name );
      ( "dropping the cross-path term lets one peer hold three stream slots",
        pin Serve_slot_quota_model.No_cross_path_count s2_name );
      ( "dropping the per-peer cap makes a denial uninformative",
        pin Serve_slot_quota_model.No_per_peer_stream_cap s3_name );
      ( "attribution: the collapsed budget touches neither stream gate",
        [
          Alcotest.test_case (s2_name ^ ":survives") `Quick
            (survives_under Serve_slot_quota_model.Shared_permit_pool s2_name);
          Alcotest.test_case (s3_name ^ ":survives") `Quick
            (survives_under Serve_slot_quota_model.Shared_permit_pool s3_name);
        ] );
      ( "attribution: the cross-path deletion leaves the record budget alone",
        [
          Alcotest.test_case (s1_name ^ ":survives") `Quick
            (survives_under Serve_slot_quota_model.No_cross_path_count s1_name);
        ] );
      ( "attribution: the per-peer-cap deletion leaves the record budget alone",
        [
          Alcotest.test_case (s1_name ^ ":survives") `Quick
            (survives_under Serve_slot_quota_model.No_per_peer_stream_cap
               s1_name);
        ] );
    ]
