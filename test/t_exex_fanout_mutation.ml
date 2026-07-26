(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    EXEX_FANOUT family. Three gates, five pins; every statement appears in at
    least one, and every pin asserts the proof FLIPS specifically to
    [Refuted] - never to [Vacuous_antecedent] - on the mutated model while the
    pristine half still proves. The distinction matters: a statement whose
    antecedent the mutation made unreachable "fails" without telling you the
    gate did any work.

    {!Exex_fanout_model.No_canon_gap_marker} deletes the [canon_gap] marker
    fan-out inside [handle_canon_commit] (manager.rs:345-353) so the commit falls
    straight through to [fan_out(&ChainExecuted)] at manager.rs:354. It ADDS a
    transition in which a payload lands in an empty channel while a loss is
    still un-signalled, refuting the safety statement, and it strands a
    post-baseline canonical obligation that no [dropped > 0] pre-send can
    discharge, refuting the security statement's delivery conjunct. Both
    refutations are confined to states with a canonical baseline, which
    {!silent_hole_needs_a_baseline} asserts as an invariant of the mutant: at
    [last_canon_tip = None] the deletion changes nothing, because [canon_gap]
    already returns [None] there (manager.rs:449-452, pinned by the crate's own
    unit test at manager.rs:528-534). No sibling repairs it:
    [deliver_broadcast]'s [Lagged] arm (manager.rs:294-307) covers only the two
    [BroadcastStream]s - the canonical stream is mapped through
    [RouterEvent::Canon], which carries no [Result] (manager.rs:189-191,
    :235-236) - and it is modelled as {!Exex_fanout_model.In_cert_lag} and left
    INTACT here; the [dropped > 0] pre-send cannot fire because the manager
    received the commit and had room; the degraded [Reorg] arm
    (manager.rs:327-335) routes through the same [handle_canon_commit];
    [dedup_chain_executed] (context.rs:218-223) and [ReplayStream]
    (replay.rs:39-61) never synthesise a marker.

    {!Exex_fanout_model.No_lagged_presend} deletes the [dropped > 0] pre-send
    block in [ExExHandle::send] (manager.rs:64-85). It REMOVES the
    marker-recovery transition and ADDS an unmarked payload delivery after a
    downstream drop, refuting BOTH the safety statement and the delivery
    conjunct of the security statement. No sibling repairs it: [canon_gap] and
    [deliver_broadcast] mark only UPSTREAM gaps and are both modelled and left
    intact; [dropped] is otherwise only [warn!]-logged (manager.rs:91-96) and
    [TnExExManagerHandle] exposes nothing but [min_finished_height]
    (manager.rs:398-412).

    {!Exex_fanout_model.Blocking_send} replaces the non-blocking [try_send]
    (manager.rs:65, :87) by an awaited [send], deleting the delivery contract
    stated at manager.rs:9 and :11-17. With the stalled sibling's channel full
    the single synchronous router fold (manager.rs:209-220, :286-290) is parked
    for the node's lifetime, so it REMOVES every delivery into the live ExEx's
    channel while the separately-spawned consumer task
    (crates/node/src/manager/node.rs:927-960) keeps polling - refuting the
    fairness statement's delivery conjunct. The fairness statement's consumption
    conjunct SURVIVES, which is what makes this starvation rather than global
    stutter. It is deliberately NOT claimed as a pin for the security statement:
    a parked router never writes the live channel again, so that channel never
    overflows, [ExExHandle::dropped] stays 0 and no obligation is ever incurred -
    [marker_owed] is unreachable under this mutation, as
    {!no_obligation_under_a_parked_router} asserts, so the security statement
    would flip by vacuity rather than by refutation. No sibling repairs it: there
    is no
    per-ExEx delivery task or timeout in the manager, the reverse
    [report_finished_height] path is also a [try_send] (context.rs:106-115), and
    [notify_exex]'s guard fires only when NO ExEx is registered
    (consensus_bus.rs:582-591). *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Exex_fanout_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Exex_fanout_model.Checker.make (Exex_fanout_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Exex_fanout_statements.name name))
    Exex_fanout_statements.all

(** The verdict of a proof attempt, distinguishing an honest refutation from a
    flip the mutation bought by making the antecedent unreachable. *)
let verdict_of result =
  Result.fold
    ~ok:(fun _ -> "proved")
    ~error:(fun e ->
      match e with
      | Exex_fanout_model.Checker.Refuted _ -> "refuted"
      | Exex_fanout_model.Checker.Vacuous_antecedent -> "vacuous")
    result

(** The negative half of a pin: the statement refutes under the mutation, and
    refutes because a counterexample RUN exists - not because the mutation made
    the antecedent unreachable. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check string)
            (name ^ " flips to refuted under the mutation")
            "refuted"
            (verdict_of (Exex_fanout_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Exex_fanout_model.Pristine (fun sys ->
          Alcotest.(check string) (name ^ " proves on pristine") "proved"
            (verdict_of (Exex_fanout_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The load-bearingness of {!Exex_fanout_model.No_canon_gap_marker}, asserted
    on the mutant itself: every state in which a payload slips past an owed
    marker has a canonical baseline, and such a state exists. The deleted block
    (manager.rs:345-353) is unreachable code at [last_canon_tip = None] -
    [canon_gap]'s [_ => None] arm (manager.rs:449-452) and the crate's test
    "First commit: no baseline -> no gap" (manager.rs:528-534) - so a refutation
    that could only happen there would be evidence about a transition on which
    pristine and mutated Rust emit identical bytes. This test forbids exactly
    that. *)
let silent_hole_needs_a_baseline () =
  with_mut Exex_fanout_model.No_canon_gap_marker (fun sys ->
      Alcotest.(check bool)
        "mutant: G (silent_hole -> canon_baseline), and EF silent_hole" true
        (Exex_fanout_model.Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 (f Exex_fanout_model.Silent_hole,
                  f Exex_fanout_model.Canon_baseline)))
        && Exex_fanout_model.Checker.satisfiable sys
             (Formula.And
                ( f Exex_fanout_model.Silent_hole,
                  f Exex_fanout_model.Canon_baseline ))))

(** Why the security statement is NOT pinned to
    {!Exex_fanout_model.Blocking_send}: with the router parked on the stalled
    sibling the live ExEx's channel is never written again, so it never
    overflows, [ExExHandle::dropped] stays 0 (manager.rs:87-97 is never reached)
    and no marker obligation is ever incurred. [marker_owed] is unreachable, so
    that statement would flip by [Vacuous_antecedent]. Asserted here so the
    absent pin is a checked fact rather than an omission. *)
let no_obligation_under_a_parked_router () =
  with_mut Exex_fanout_model.Blocking_send (fun sys ->
      Alcotest.(check bool) "parked router: ~EF marker_owed, but EF sib_full"
        true
        (Bool.not
           (Exex_fanout_model.Checker.satisfiable sys
              (f Exex_fanout_model.Marker_owed))
        && Exex_fanout_model.Checker.satisfiable sys
             (f Exex_fanout_model.Sib_chan_full)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "exex_fanout_mutation"
    [
      ( "dropped canon-gap marker lets a payload past an owed marker",
        pin Exex_fanout_model.No_canon_gap_marker
          "payload-never-delivered-while-a-gap-marker-is-owed" );
      ( "dropped Lagged pre-send lets a payload past an owed marker",
        pin Exex_fanout_model.No_lagged_presend
          "payload-never-delivered-while-a-gap-marker-is-owed" );
      ( "dropped Lagged pre-send never surfaces the downstream drop",
        pin Exex_fanout_model.No_lagged_presend
          "lagged-marker-is-delivered-and-known-but-its-cause-is-opaque" );
      ( "dropped canon-gap marker strands a post-baseline obligation",
        pin Exex_fanout_model.No_canon_gap_marker
          "lagged-marker-is-delivered-and-known-but-its-cause-is-opaque" );
      ( "blocking send lets the stalled sibling starve the live ExEx",
        pin Exex_fanout_model.Blocking_send
          "stalled-sibling-exex-cannot-starve-the-live-exex" );
      ( "the pins rest on real gates",
        [
          Alcotest.test_case "silent-hole-needs-a-baseline" `Quick
            silent_hole_needs_a_baseline;
          Alcotest.test_case "no-obligation-under-a-parked-router" `Quick
            no_obligation_under_a_parked_router;
        ] );
    ]
