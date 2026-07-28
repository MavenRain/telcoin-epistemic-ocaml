(** The engine_queue family proves on the pristine {!Engine_queue_model} through
    [prove_nonvacuous] (so every antecedent is checked reachable too), the
    reachable graph stays in its justified band, the three structural invariants
    the slot gates enforce are genuinely unreachable rather than merely
    unasserted, and the epistemic layer is real partial information:

    - the [sanity] group additionally pins the FAITHFULNESS of the two liveness
      conjuncts. The model carries the fatal-error path out of the release arm
      (engine/lib.rs:264 -> node/src/engine/inner.rs:75-87), and the two
      "unscoped" cases assert that the UNQUALIFIED forms - [AG(|queued| >= MAX ->
      AF |queued| < MAX)] and [AG(queued(o_B) -> AF executed(o_B))] - are FALSE
      here. That is the evidence that S2 conjunct (C) and S3 conjunct (A) are
      scoped because the code needs them scoped, and not manufactured by a model
      that omitted the one path on which the backlog never drains;
    - the [contingency] group discharges R3 for both ignorance conjuncts with
      concrete reachable pairs, and bounds them honestly: V0's blindness is
      scoped to the PEER's occupancy - it knows its own backlog perfectly, and
      that is asserted here too - and V1's blindness survives being handed V0's
      published execution tip. *)

open Telcoin_epistemic
open Engine_queue_model

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
        (st.Engine_queue_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Engine_queue_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Engine_queue_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** A [satisfiable] case with its own label. *)
let sat_case label want formula () =
  with_sys (fun sys ->
      Alcotest.(check bool) label want (Checker.satisfiable sys formula))

(** A [valid] case with its own label. *)
let valid_case label want formula () =
  with_sys (fun sys ->
      Alcotest.(check bool) label want (Checker.valid sys formula))

(** Crude product bound: 4 upstream suffixes x 8 backlog contents x 5 slot
    values x 4 tips x 4 heads x 3 grant counts x 2 x 2 x 2 = far more than the
    graph. The pristine reachable set is 41: the pipeline is a strictly
    consuming one (each step lowers 3|upstream| + 2|queued| + |in flight|), the
    two-task slot shape is unreachable without a mutation, [tip] and [head] are
    determined by what has completed, and the absorbing stopped state adds one
    twin per in-flight configuration. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 60))

(** The exclusivity gate (engine/lib.rs:227, with [pending_task] a single
    [Option] at :52-54): no reachable state holds two execution tasks. This is
    the invariant {!Engine_queue_model.No_slot_exclusion} deletes. *)
let no_concurrent_tasks () =
  sat_case "two in-flight tasks is unreachable" false (f Two_tasks_in_flight) ()

(** The chaining consequence of exclusivity: no reachable state has a task
    building on anything other than the highest committed block. *)
let no_stale_parent () =
  sat_case "an in-flight task on a superseded parent is unreachable" false
    (Formula.Not (f Parent_is_committed_head))
    ()

(** The bound gate (engine/lib.rs:245 with [MAX_QUEUED_OUTPUTS] at :38): the
    backlog never exceeds the bound. This is the invariant
    {!Engine_queue_model.No_queue_bound} deletes. *)
let no_backlog_overflow () =
  sat_case "a backlog past the bound is unreachable" false (f Queue_over_bound) ()

(** The grant-by-removal gate ([pop_front] at engine/lib.rs:124): no output is
    handed the slot twice. This is the invariant
    {!Engine_queue_model.Reexecute_head} deletes. *)
let no_second_grant () =
  sat_case "a second grant of the same output is unreachable" false
    (f Oa_granted_twice) ()

(** The saturated regime the whole family is about is genuinely reachable: the
    backlog sits at the bound while the [to_engine] channel still holds an
    output the engine is refusing to take. *)
let saturated_with_backpressure_reachable () =
  sat_case "gate closed with an undelivered output upstream is reachable" true
    (Formula.And (f Queue_gate_closed, f Upstream_undelivered))
    ()

(** The fatal-error path out of the release arm is really in the model
    (engine/lib.rs:264, node/src/engine/inner.rs:75-87), not merely described in
    a comment. *)
let engine_stop_reachable () =
  sat_case "an execution error ending the engine is reachable" true
    (f Engine_stopped) ()

(** R5 evidence, half one: the UNSCOPED gate-reopens claim is FALSE here. If the
    model had omitted the fatal-error path this would pass, and S2 conjunct (C)
    would be a manufactured liveness property rather than a scoped one. *)
let unscoped_reopen_is_false () =
  valid_case "AG(gate_closed -> AF ~gate_closed) is NOT valid: the engine can die"
    false
    (Formula.Ag
       (Formula.Implies
          (f Queue_gate_closed, Formula.Af (Formula.Not (f Queue_gate_closed)))))
    ()

(** R5 evidence, half two: the UNSCOPED no-starvation claim is FALSE here, for
    the same reason. S3 conjunct (A) carries its [engine_stopped] disjunct
    because the code needs it, not to make a proof go through. *)
let unscoped_no_starvation_is_false () =
  valid_case "AG(queued(o_B) -> AF executed(o_B)) is NOT valid: the engine can die"
    false
    (Formula.Ag (Formula.Implies (f Ob_queued, Formula.Af (f Ob_resolved))))
    ()

(** The empty non-epoch-closing output really does leave the tip alone
    (payload_builder.rs:84-97), so "every completion advances the chain" is not
    quietly assumed: [o_B] can resolve with the committed head still where it
    was when it was granted. *)
let empty_output_resolves_without_a_block () =
  sat_case "o_B resolved while the chain head is still 1 is reachable" true
    (Formula.conj [ f Ob_resolved; Formula.Not (f Ob_queued) ])
    ()

(** R3 for S2 conjunct (D): at a state where V0's backlog is at the bound and
    the peer really IS saturated too, V0 does not know it. This can only hold
    because a reachable state with the identical [View_engine] and a healthy peer
    exists - the concrete witness pair. *)
let saturation_not_known () =
  sat_case
    "gate_closed /\\ peer_at_bound /\\ ~K_V0(peer_at_bound): the healthy twin is \
     reachable"
    true
    (Formula.conj
       [
         f Queue_gate_closed;
         f Peer_saturated;
         Formula.Not (Formula.K (Validator.V0, f Peer_saturated));
       ])
    ()

(** R3 for S2 conjunct (E), the other direction: at a saturated state where the
    peer is in fact healthy, V0 cannot conclude that either. The two cases
    together are the pair R3 asks for, and they rule out the degenerate reading
    in which V0 simply happens to be right. *)
let health_not_known () =
  sat_case
    "gate_closed /\\ ~peer_at_bound /\\ ~K_V0(~peer_at_bound): the saturated twin \
     is reachable"
    true
    (Formula.conj
       [
         f Queue_gate_closed;
         Formula.Not (f Peer_saturated);
         Formula.Not
           (Formula.K (Validator.V0, Formula.Not (f Peer_saturated)));
       ])
    ()

(** The ignorance of S2 is SCOPED, not blanket: V0 knows its own backlog is at
    the bound perfectly well - [queued.len()] is its own field
    (engine/lib.rs:51) - and only the peer's occupancy is hidden. A model in
    which V0 knew nothing would make (D) and (E) cheap. *)
let own_saturation_is_known () =
  valid_case "AG(gate_closed -> K_V0(gate_closed)): the blindness is peer-only"
    true
    (Formula.Ag
       (Formula.Implies
          (f Queue_gate_closed, Formula.K (Validator.V0, f Queue_gate_closed))))
    ()

(** R3 for S3 conjunct (C): at a state where V0's slot is occupied, the peer V1
    cannot tell - even though V1's view here carries V0's last PUBLISHED
    execution tip (tn-reth/lib.rs:962-973 -> node.rs:1305-1322). The witness is a
    reachable idle state at the same published tip and the same peer occupancy. *)
let slot_occupancy_not_known () =
  sat_case "executing /\\ ~K_V1(executing): an idle twin at the same tip exists"
    true
    (Formula.And
       (f Executing, Formula.Not (Formula.K (Validator.V1, f Executing))))
    ()

(** The same blindness in the other direction: at an idle state V1 cannot
    conclude the slot is free either, so V1's class genuinely straddles the
    distinction rather than merely failing to confirm one side of it. *)
let idleness_not_known () =
  sat_case "~executing /\\ ~K_V1(~executing): a busy twin at the same tip exists"
    true
    (Formula.And
       ( Formula.Not (f Executing),
         Formula.Not (Formula.K (Validator.V1, Formula.Not (f Executing))) ))
    ()

(** The defence of the view asymmetry behind S2 conjuncts (D) and (E). V0's view
    carries no peer component at all, and a skeptic may ask whether the two
    ignorance claims would survive giving V0 the peer's PUBLISHED execution tip -
    the symmetric counterpart of what V1 gets here. They would, and this case is
    the reason inside the model: V1 does hold V0's published tip, and it still
    cannot tell whether V0's backlog is at the bound. A published tip is not a
    function of backlog depth - the same tip is reachable with the gate open and
    with it shut - so enriching V0's view that way could refine the class without
    ever creating knowledge of the peer's occupancy. *)
let published_tip_hides_backlog_depth () =
  sat_case
    "gate_closed /\\ ~K_V1(gate_closed): a published tip does not reveal backlog \
     depth"
    true
    (Formula.And
       ( f Queue_gate_closed,
         Formula.Not (Formula.K (Validator.V1, f Queue_gate_closed)) ))
    ()

let () =
  Alcotest.run "engine_queue"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Engine_queue_statements.name `Quick
              (prove_one st))
          Engine_queue_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "slot-exclusive" `Quick no_concurrent_tasks;
          Alcotest.test_case "no-stale-parent" `Quick no_stale_parent;
          Alcotest.test_case "backlog-bounded" `Quick no_backlog_overflow;
          Alcotest.test_case "grant-is-one-shot" `Quick no_second_grant;
          Alcotest.test_case "saturated-regime-reachable" `Quick
            saturated_with_backpressure_reachable;
          Alcotest.test_case "engine-stop-reachable" `Quick
            engine_stop_reachable;
          Alcotest.test_case "unscoped-reopen-is-false" `Quick
            unscoped_reopen_is_false;
          Alcotest.test_case "unscoped-no-starvation-is-false" `Quick
            unscoped_no_starvation_is_false;
          Alcotest.test_case "empty-output-keeps-the-tip" `Quick
            empty_output_resolves_without_a_block;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "peer-saturation-not-known" `Quick
            saturation_not_known;
          Alcotest.test_case "peer-health-not-known" `Quick health_not_known;
          Alcotest.test_case "own-saturation-is-known" `Quick
            own_saturation_is_known;
          Alcotest.test_case "slot-occupancy-not-known" `Quick
            slot_occupancy_not_known;
          Alcotest.test_case "slot-idleness-not-known" `Quick idleness_not_known;
          Alcotest.test_case "published-tip-hides-backlog-depth" `Quick
            published_tip_hides_backlog_depth;
        ] );
    ]
