(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    GOSSIP_REJECT family. Each of the three statements is pinned by its OWN
    gate deletion, and each row asserts the proof FLIPS to an error on the
    mutated model while the pristine row is the matching positive half.

    - {!Gossip_reject_model.No_receive_size_gate} deletes the receive-side size
      check at the head of [verify_gossip] (consensus.rs:1491-1497) from the
      SHARED binary. An honest node then Accepts an oversized payload, and
      [Accept] is the only [report_message_validation_result] arm that
      forwards, so an honest relayer can deliver oversized bytes: the oversized
      view class gains a non-deviating world and S1's attribution conjunct
      dies; the verdict also falls through to the publisher check, so oversized
      deliveries from denied authors charge the AUTHOR and S1's author-spared
      conjunct dies too. Sibling hunt: libp2p's own [max_transmit_size] default
      of 65536 sits above the modelled 12_001..65_535 band and TN never sets
      it; the origination guard (consensus.rs:782-798) never runs on a forward;
      [TNCodec]'s bound governs request/response only. No repair. PINS S1.
    - {!Gossip_reject_model.No_reject_attribution_split} deletes the two
      [RejectReason::UnauthorizedAuthor] arms (consensus.rs:2094-2095) so every
      reject falls through to [FatalRelayer], making the forwarder the penalty
      target and killing S2's forwarder-spared conjunct. Sibling hunt:
      gossipsub-internal peer scoring is not configured at all; rejects never
      reach the application layer (only the [Accept] arm calls [try_send]); the
      committee exemption suppresses a score EFFECT but not the charge, and
      S2's atom is the [RejectPenalty] target rather than the ban, chosen
      precisely so that sibling cannot repair the deletion. No repair. PINS S2.
    - {!Gossip_reject_model.No_committee_exemption} deletes the [TrustBasis]
      bypass in [Peer::apply_penalty] (peer.rs:218-233), so the [Fatal] lands
      on tracked committee authors too and S3's never-both invariant fails at
      the [Settled] state. Sibling hunt: the one real repair -
      [apply_committee_membership]'s unban and [reset_score_to_max]
      (all_peers.rs:1180-1239, driven from :1102-1122) - is MODELLED as the
      mandatory [Rotated] step and stays LIVE under the mutation; it repairs
      only one step after the ban, which is why the statement is an
      AG-never-both invariant. The temporarily-banned cache and the heartbeat
      decay are the same later-repair shape and are folded into that step. No
      repair. PINS S3.

    NOTE, so it is never mistaken for a second pin: [No_reject_attribution_split]
    ALSO errors S3, but through [Vacuous_antecedent] rather than refutation - by
    routing every charge to the relayer it makes [charged(A)] unreachable, so
    S3's antecedent disappears. That is a scope collapse, not evidence for S3,
    and it is deliberately not asserted here. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Gossip_reject_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Gossip_reject_model.Checker.make (Gossip_reject_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Gossip_reject_statements.name name))
    Gossip_reject_statements.all

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
               (Gossip_reject_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Gossip_reject_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Gossip_reject_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "gossip_reject_mutation"
    [
      ( "dropped receive-side size gate kills knowable relayer guilt",
        pin Gossip_reject_model.No_receive_size_gate
          "oversized-gossip-receipt-implies-known-relayer-deviation" );
      ( "dropped unauthorized-author arms charge the forwarder",
        pin Gossip_reject_model.No_reject_attribution_split
          "unauthorized-author-reject-spares-and-cannot-judge-the-forwarder" );
      ( "dropped committee exemption bans the tracked author",
        pin Gossip_reject_model.No_committee_exemption
          "committee-author-charged-under-ignorance-is-never-banned" );
    ]
