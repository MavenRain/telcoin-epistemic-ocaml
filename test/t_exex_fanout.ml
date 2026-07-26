(** The EXEX_FANOUT family (three statements) proves on the pristine
    {!Exex_fanout_model} through [prove_nonvacuous] (so each antecedent is also
    checked reachable), the reachable graph stays in its justified band, the two
    invariants the delivery gates enforce hold - no payload ever lands while a
    marker is owed, and a marker head always implies a real loss - and the
    epistemic layer is genuinely partial-information: the one positive knowledge
    operand is contingent, its view class is provably not a singleton, and both
    ignorance conjuncts have a concrete colliding pair of reachable worlds. *)

open Telcoin_epistemic
open Exex_fanout_model

(** Build the pristine system or fail the test on an impossible [Empty_init]. *)
let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Checker.Empty_init -> Alcotest.fail "make: empty init")
    (make ())

(** Render a proof error for the assertion message. *)
let error_to_string = function
  | Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Checker.Vacuous_antecedent -> "vacuous antecedent"

(** One proof case: the statement proves on the pristine model. *)
let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Exex_fanout_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Exex_fanout_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Exex_fanout_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: phase (3) x sibling channel (2) x live channel (3) x
   canonical baseline (2) x the five booleans (2^5) = 1152. The pristine
   reachable set is exactly 25, pruned by [hole] false everywhere,
   [owed] -> [dropped] at every end-of-step state, [dropped] -> [down] ->
   [loss], and [sib] / [tip] being absorbing at [Sib_full] / [Tip_some]. The
   three mutants reach 37, 53 and 21. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 50))

(* The gate's own contract: the state both delivery gates forbid - a payload
   enqueue that SUCCEEDS while a loss is still un-signalled - is unreachable on
   the pristine model. This is S1's sanity claim; [No_canon_gap_marker] and
   [No_lagged_presend] each make it reachable and flip the proof. *)
let silent_hole_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF silent_hole" false
        (Checker.satisfiable sys (f Silent_hole)))

(* Marker soundness, the invariant that makes S2's positive [K] honest rather
   than a modelling artefact: every reachable state whose channel head is a
   [Lagged] marker really has had a loss. The three emission sites are
   [canon_gap]'s discontinuity test (manager.rs:449-452), [deliver_broadcast]'s
   [BroadcastStreamRecvError::Lagged] arm (manager.rs:294-307) and the
   [dropped > 0] pre-send (manager.rs:64-65) - none of them fires without one. *)
let marker_head_implies_loss () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G (head_1(Lagged) -> loss_occurred)" true
        (Checker.valid sys
           (Formula.Ag (Formula.Implies (f V1_marker_head, f Loss_occurred)))))

(* Both non-vacuity antecedents are genuinely reachable, so neither statement is
   certified on the strength of a state that never occurs: [marker_owed] after a
   drop on the full capacity-1 channel (manager.rs:89-97), [sib_full] after the
   very first fan-out into the stalled sibling. *)
let antecedents_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF marker_owed /\\ EF sib_full" true
        (Checker.satisfiable sys (f Marker_owed)
        && Checker.satisfiable sys (f Sib_chan_full)))

(* R2, contingency half, for the family's single positive [K] operand
   [K_V1(loss_occurred)] in S2 conjunct (A): its complement is reachable, so the
   knowledge did not collapse into plain truth under the view partition. It
   fails at the initial state (channel empty, nothing lost yet) and at the
   first-payload state - V1's view there is shared with a later same-head state
   in which a loss HAS occurred. *)
let k_loss_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1(loss_occurred): knowledge is contingent"
        true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Loss_occurred)))))

(* R2, non-singleton-view-class half, for [K_V1(loss_occurred)]. At the
   operative state - channel head is a [Lagged] marker - pick the atom
   [down_drop], which is FALSE at the upstream-only world; if V1 cannot rule it
   out there, the view class holds another world. The two concrete members are
   W_up = (Ph_fan_b, Sib_full, Chan_lagged, dropped = false, owed = false,
   loss = true, down = FALSE), reached by one [In_cert_lag] fan-out from the
   initial state, and W_down = (Ph_fan_b, Sib_full, Chan_lagged, dropped = true,
   owed = true, loss = true, down = TRUE), reached by [In_payload],
   [In_payload], poll, [In_payload]. Same [View_live Chan_lagged], opposite
   [down_drop]: the class has at least two members, so the [K] is not trivially
   true. *)
let k_loss_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (head_1(Lagged) /\\ ~K_v1(~down_drop)): class has >= 2 members" true
        (Checker.satisfiable sys
           (Formula.And
              ( f V1_marker_head,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Down_drop))) ))))

(* R3 for S2 conjunct (B), first half: on a delivered marker V1 cannot conclude
   the loss was a drop on its own channel. The colliding pair is W_up (down
   FALSE) against W_down (down TRUE) named above; [Lagged] carries only [missed]
   and no cause tag (notification.rs:141-144), so both project to the same
   [View_live Chan_lagged]. *)
let ignorance_of_downstream_cause () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (head_1(Lagged) /\\ ~K_v1(down_drop))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f V1_marker_head,
                Formula.Not (Formula.K (Validator.V1, f Down_drop)) ))))

(* R3 for S2 conjunct (B), second half: nor can V1 RULE OUT that the loss was a
   drop on its own channel. Same colliding pair, read the other way. *)
let ignorance_of_upstream_cause () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (head_1(Lagged) /\\ ~K_v1(~down_drop))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f V1_marker_head,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Down_drop))) ))))

(* The colliding pair itself, asserted explicitly rather than only through the
   [K] operator: BOTH a marker-head world with a downstream drop and a
   marker-head world without one are reachable. Without this pair the two
   ignorance conjuncts above would be satisfiable for the wrong reason. *)
let both_marker_causes_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (head_1(Lagged) /\\ down_drop) and EF (head_1(Lagged) /\\ ~down_drop)"
        true
        (Checker.satisfiable sys (Formula.And (f V1_marker_head, f Down_drop))
        && Checker.satisfiable sys
             (Formula.And (f V1_marker_head, Formula.Not (f Down_drop)))))

(* S2 conjunct (A) has real work to do: an owed marker is reachable at a state
   where the live ExEx's channel is EMPTY, so the [AF] is not discharged at the
   antecedent state itself but only after the [dropped > 0] pre-send lands the
   marker on the following fan (manager.rs:64-74). *)
let owed_at_empty_channel_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (empty_1 /\\ marker_owed)" true
        (Checker.satisfiable sys
           (Formula.And (f V1_chan_empty, f Marker_owed))))

(* The state on which the [canon_gap] gate is genuinely load-bearing: a
   canonical baseline exists ([last_canon_tip = Some(_)], manager.rs:126-129)
   AND the live ExEx's channel is empty with no obligation outstanding, so a
   canonical skip arriving here is detectable, is detected, and its marker has
   room to land ahead of the payload. It is reachable on the one-fan branch of
   the scheduler ([In_canon_commit], poll), which is precisely the branch the
   earlier revision of this model lacked. *)
let baseline_idle_state_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (canon_baseline /\\ empty_1 /\\ ~marker_owed)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Canon_baseline,
                Formula.And (f V1_chan_empty, Formula.Not (f Marker_owed)) ))))

(* The admitted hole, asserted rather than hidden: a REAL loss with no
   obligation to signal it is reachable on the pristine model. That is the
   pre-baseline canonical skip - [canon_gap] takes its [_ => None] arm when
   [last_canon_tip] is [None] (manager.rs:449-452), pinned by the crate's own
   unit test at manager.rs:528-534 - and it is why S1 is scoped to signalable
   gaps. Without this the safety statement would be stronger than the manager
   it describes. *)
let unsignalable_loss_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (loss_occurred /\\ ~marker_owed /\\ ~down_drop)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Loss_occurred,
                Formula.And
                  (Formula.Not (f Marker_owed), Formula.Not (f Down_drop)) ))))

(* The same input, the two baselines, checked directly on the transition
   function so the contrast is sharp rather than merely satisfiable. At the
   initial state ([last_canon_tip = None], manager.rs:152) a canonical skip
   yields a payload head, a real [loss], NO obligation and NO marker - the
   manager cannot see it. At the reachable state that differs only by a
   delivered canonical commit (reached by [In_canon_commit] then a poll), the
   very same skip yields a [Lagged] head with the obligation still outstanding
   for the payload that dropped behind it (manager.rs:345-354). Deleting
   manager.rs:345-353 changes the second and provably not the first, which is
   what makes {!Exex_fanout_model.No_canon_gap_marker} a real gate deletion. *)
let canon_gap_needs_a_baseline () =
  let no_baseline = fan Pristine In_commit_gap initial in
  let with_baseline =
    fan Pristine In_commit_gap { initial with tip = Tip_some; sib = Sib_full }
  in
  Alcotest.(check bool)
    "pre-baseline skip: payload head, loss, no obligation, no marker" true
    (Int.equal 0 (chan_compare no_baseline.chan Chan_payload)
    && no_baseline.loss
    && Bool.not no_baseline.owed
    && Bool.not no_baseline.hole);
  Alcotest.(check bool)
    "post-baseline skip: marker head first, obligation still live" true
    (Int.equal 0 (chan_compare with_baseline.chan Chan_lagged)
    && with_baseline.loss && with_baseline.owed
    && Bool.not with_baseline.hole)

(* The post-baseline state used above is not hand-waved: it is exactly the
   successor reached from the initial state by one [In_canon_commit] fan and one
   consumer poll, on the scheduler's one-fan branch. *)
let baseline_idle_state_is_a_successor () =
  let after_commit = fan Pristine In_canon_commit initial in
  let idle = { after_commit with chan = Chan_empty } in
  Alcotest.(check bool) "In_canon_commit then poll reaches the idle baseline"
    true
    (Int.equal 0
       (state_compare idle
          { initial with tip = Tip_some; sib = Sib_full; phase = Ph_fan_a }))

let () =
  Alcotest.run "exex_fanout"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Exex_fanout_statements.name `Quick
              (prove_one st))
          Exex_fanout_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "silent-hole-unreachable" `Quick
            silent_hole_unreachable;
          Alcotest.test_case "marker-head-implies-loss" `Quick
            marker_head_implies_loss;
          Alcotest.test_case "antecedents-reachable" `Quick
            antecedents_reachable;
          Alcotest.test_case "canon-gap-needs-a-baseline" `Quick
            canon_gap_needs_a_baseline;
          Alcotest.test_case "baseline-idle-state-is-a-successor" `Quick
            baseline_idle_state_is_a_successor;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-loss-contingent" `Quick k_loss_contingent;
          Alcotest.test_case "k-loss-class-not-singleton" `Quick
            k_loss_class_not_singleton;
          Alcotest.test_case "ignorance-of-downstream-cause" `Quick
            ignorance_of_downstream_cause;
          Alcotest.test_case "ignorance-of-upstream-cause" `Quick
            ignorance_of_upstream_cause;
          Alcotest.test_case "both-marker-causes-reachable" `Quick
            both_marker_causes_reachable;
          Alcotest.test_case "owed-at-empty-channel-reachable" `Quick
            owed_at_empty_channel_reachable;
          Alcotest.test_case "baseline-idle-state-reachable" `Quick
            baseline_idle_state_reachable;
          Alcotest.test_case "unsignalable-loss-reachable" `Quick
            unsignalable_loss_reachable;
        ] );
    ]
