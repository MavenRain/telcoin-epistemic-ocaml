(** Confirm-by-mutation for the BOOT-ORDER family. Each gate deletion removes
    exactly one call of the real startup sequence and the mutated row asserts
    that the statement depending on it FLIPS to an error; the pristine row is
    the matching positive half.

    - [No_marker_heal] deletes crates/node/src/manager/node.rs:864
      ([heal_finalized_to_persisted_tip]), the SOLE production call site of
      the single definition at crates/tn-reth/src/lib.rs:885. No other marker
      reader re-derives the marker from the tip
      (crates/node/src/engine/inner.rs:242-260, :263-276, :150) and the
      cross-view guard at node.rs:209-220 fires only across an epoch boundary,
      so nothing repairs it. Pins S1.
    - [No_recent_blocks_prime] deletes node.rs:906 ([try_restore_state]), the
      only thing that seeds the window the replay watermark is read from
      (consensus_bus.rs:672-688 -> state-sync/src/lib.rs:154-155). The engine
      has no idempotence check (crates/engine/src/lib.rs:196-286) and
      [check_output_continuity] is by design not applied to replay
      (run_epoch.rs:878-891), so nothing repairs it. Pins S2.
    - [Initial_only_network_gate] deletes the [|| !self.network_initialized]
      disjunct at run_epoch.rs:255. [start_listening] has exactly two non-test
      call sites (start_epoch.rs:514, :675), both under the same gate, and
      crates/network-libp2p has no relay/dcutr transport, so nothing repairs
      it. Pins S3's [AF (listener-bound)].
    - [Rebind_on_replay] inserts the naive fix - a bind on the
      replay-and-close early-return path (run_epoch.rs:225-231) - and nothing
      unbinds or dedups a duplicate listener. Pins S3's
      [AG (listener-bound -> AG (bound-exactly-once))].

    Two extra groups keep the pins honest. The {b targeting} group asserts
    that each deletion leaves the OTHER statements proving, so no pin can pass
    because some unrelated statement collapsed. The {b sibling-repair} group
    discharges the standing objection to S1 - that [run_epoch]'s epoch-entry
    re-derivation of worker count and base fees (run_epoch.rs:166-192) makes
    the restore redundant - by showing that under [No_marker_heal] that repair
    still runs ([fees-reseeded]) while the totals the restore rebuilds stay
    short. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail on an impossible [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Boot_order_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Boot_order_model.Checker.make (Boot_order_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Boot_order_statements.name name))
    Boot_order_statements.all

(** Does the named statement prove under [mut]. *)
let proves_under mut name k =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          k
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Boot_order_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " flips to refuted under the mutation")
        false proved)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  proves_under Boot_order_model.Pristine name (fun proved ->
      Alcotest.(check bool) (name ^ " proves on pristine") true proved)

(** A statement untouched by this mutation still proves under it. *)
let survives_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " still proves under an unrelated gate deletion")
        true proved)

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** One [satisfiable] assertion on the system built under [mut]. *)
let sat_under mut label expected formula () =
  with_mut mut (fun sys ->
      Alcotest.(check bool) label expected
        (Boot_order_model.Checker.satisfiable sys formula))

(** The names, spelled once. *)
let s1_name = "finalized-marker-heal-precedes-every-startup-state-rebuild"

(** The name of the recent-blocks ordering statement. *)
let s2_name = "recent-blocks-restore-precedes-the-replay-watermark"

(** The name of the swarm-listener statement. *)
let s3_name =
  "swarm-listener-binds-exactly-once-even-when-startup-replays-and-closes"

(** The epoch-entry seeding still repairs the fees while the restore's totals
    stay short: the acknowledged partial repair does not cover what S1 is
    about. *)
let fees_repair_does_not_cover_totals =
  Formula.And
    (f Boot_order_model.Fees_reseeded,
     Formula.Not (f Boot_order_model.Totals_complete))

let () =
  Alcotest.run "boot_order_mutation"
    [
      ( "deleting the startup heal leaves the restore scanning to a stale \
         marker",
        pin Boot_order_model.No_marker_heal s1_name );
      ( "deleting the recent-blocks priming collapses the replay watermark",
        pin Boot_order_model.No_recent_blocks_prime s2_name );
      ( "gating the one-time network setup on the Initial epoch alone loses \
         the bind",
        pin Boot_order_model.Initial_only_network_gate s3_name );
      ( "binding on the replay-and-close path breaks once-only setup",
        pin Boot_order_model.Rebind_on_replay s3_name );
      ( "targeting: each deletion refutes only its own statement",
        [
          Alcotest.test_case "no-marker-heal:s2" `Quick
            (survives_under Boot_order_model.No_marker_heal s2_name);
          Alcotest.test_case "no-marker-heal:s3" `Quick
            (survives_under Boot_order_model.No_marker_heal s3_name);
          Alcotest.test_case "no-recent-blocks-prime:s1" `Quick
            (survives_under Boot_order_model.No_recent_blocks_prime s1_name);
          Alcotest.test_case "no-recent-blocks-prime:s3" `Quick
            (survives_under Boot_order_model.No_recent_blocks_prime s3_name);
          Alcotest.test_case "initial-only-network-gate:s1" `Quick
            (survives_under Boot_order_model.Initial_only_network_gate s1_name);
          Alcotest.test_case "initial-only-network-gate:s2" `Quick
            (survives_under Boot_order_model.Initial_only_network_gate s2_name);
          Alcotest.test_case "rebind-on-replay:s1" `Quick
            (survives_under Boot_order_model.Rebind_on_replay s1_name);
          Alcotest.test_case "rebind-on-replay:s2" `Quick
            (survives_under Boot_order_model.Rebind_on_replay s2_name);
        ] );
      ( "the acknowledged sibling repair does not cover the restore",
        [
          Alcotest.test_case "fees-reseeded-while-totals-short" `Quick
            (sat_under Boot_order_model.No_marker_heal
               "EF (fees-reseeded /\\ ~totals-complete) under No_marker_heal"
               true fees_repair_does_not_cover_totals);
          Alcotest.test_case "pristine-has-no-short-totals" `Quick
            (sat_under Boot_order_model.Pristine
               "EF (fees-reseeded /\\ ~totals-complete) on pristine" false
               fees_repair_does_not_cover_totals);
        ] );
    ]
