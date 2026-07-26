(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    PENDING_GC family. Each of the three statements is pinned by at least one
    gate deletion, and every row asserts the proof FLIPS to an error on the
    mutated model while the matching pristine row still proves.

    - {!Pending_gc_model.No_parent_check} deletes the missing-parent
      precondition on acceptance (cert_manager.rs:109-117), so [deliver_c]
      accepts unconditionally and (C_accepted, D_absent, H_below) becomes
      reachable: S1's causal-order conjunct is REFUTED at a state where the
      certificate was accepted parentless while the horizon was still below the
      parent's round. No second parent-presence check exists anywhere on the
      acceptance funnel (cert_validator.rs:88-130, :133-226, :235-243 all
      funnel into the same command, and accept_verified_certificates,
      cert_manager.rs:189-220, has no parent precondition), so the deletion is
      not silently repaired.

    - {!Pending_gc_model.No_gc_release} deletes the garbage-collection release
      route - the process_gc_round drain loop (cert_manager.rs:235-238) and the
      update_pending effect it consumes (pending_cert_manager.rs:97-131) -
      TOGETHER WITH its sibling horizon skip
      (cert_manager.rs:108) - deleting only the first would leave a
      post-horizon arrival accepted parentless anyway. A parked certificate then
      waits for its literal parent forever, so (C_pending, D_lost, H_past) is a
      reachable terminal stutter and S2's [Af] is REFUTED. Three further repair
      paths were hunted and none reopens it: re-delivery hits the [is_pending]
      early return (cert_manager.rs:96-101); the Ancestors fetch is bounded
      strictly above [gc_round] (certificate_fetcher.rs:258-286, :350-379) with
      [TooOld] on the direct path (cert_validator.rs:114-125); and recover_state
      re-appends only STORED certificates (cert_manager.rs:244-258). The one
      real hole - indirect verification inside a peer-volunteered batch
      (cert_validator.rs:288-324) - is MODELED (deliver_d stays enabled past the
      horizon) and the pin survives it via the [lose_d] branch, so this is not a
      manufactured-liveness pin (R8). The anchor above is the REPAIRED one: an
      earlier revision pinned the release on next_for_gc_round's
      [round > gc_round] bound and its [missing_parent_digests.clear()]
      (pending_cert_manager.rs:143-153), and a review showed the bound is only
      the loop's termination test (deleting it releases MORE eagerly) and the
      [clear()] is unreachable, [pending] being keyed by parked-certificate
      digests while [missing_for_pending] is keyed by
      [(parent_round, parent_digest)]. The MODELLED gate ({!gc_release} deleting
      the release wholesale) was correct throughout; only the file:line moved.

    - {!Pending_gc_model.No_pending_filter} deletes the retain in
      filter_unknown_digests (pending_cert_manager.rs:171-173), adding the edge
      (C_pending, *, *, R_open) -> (C_pending, *, *, R_missing): S3's conjunct A
      [Ax] is REFUTED. The reachable SET is unchanged (48 either way), so only
      the edge relation moved - the reason the statement is an [Ax]. Neither the
      [requested_parents] filter (handler.rs:875-924, Vacant on the first
      request for the key) nor the storage pre-filter (a pending certificate is
      not in the store, cert_manager.rs:196) re-hides the digest.

    - {!Pending_gc_model.No_parent_wait} deletes the blocking notify_read before
      voting (handler.rs:688-693), adding
      (C_pending, *, *, R_open) -> (C_pending, *, *, R_voted): V0's voted view
      class gains a state whose certificate is still parked, so S3's conjunct B
      [K (V0, accepted_v(c))] is REFUTED. The parent quorum check
      (handler.rs:700-738) does not repair it, because a header carrying all
      four round-r parents still musters 2f+1 from the three stored ones
      (handler.rs:632-637), which is the header shape this family is scoped to.

    S3 is pinned TWICE, once per conjunct, so neither half can rot silently
    behind the other. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Pending_gc_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Pending_gc_model.Checker.make (Pending_gc_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Pending_gc_statements.name name))
    Pending_gc_statements.all

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
               (Pending_gc_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Pending_gc_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Pending_gc_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "pending_gc_mutation"
    [
      ( "dropped missing-parent check kills the causal-order horizon gate",
        pin Pending_gc_model.No_parent_check
          "gc-horizon-acceptance-forfeits-parent-knowledge" );
      ( "dropped gc release kills pending-certificate liveness",
        pin Pending_gc_model.No_gc_release "pending-certificate-always-released"
      );
      ( "dropped pending filter kills the vote-round pending guard",
        pin Pending_gc_model.No_pending_filter
          "vote-round-respects-pending-parent-state" );
      ( "dropped parent wait kills vote-as-proof-of-possession",
        pin Pending_gc_model.No_parent_wait
          "vote-round-respects-pending-parent-state" );
    ]
