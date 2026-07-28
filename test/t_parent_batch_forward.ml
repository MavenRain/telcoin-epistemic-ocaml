(** The parent-batch-forward family proves on the pristine
    {!Parent_batch_forward_model}, the reachable graph is the expected small
    pipeline, the gate invariants of the drain and of the quorum forward hold,
    and the epistemic layer is genuinely partial-information rather than
    collapsed:

    - the positive conjunct [K_V0(quorum_of_distinct_origins)] is contingent
      (a reachable state where the proposer does NOT know it) and its operand
      is not rigid (a reachable state where it is false);
    - V0's view class at the operative state is NOT a singleton, witnessed by
      the proposer failing to know that the straggler was not accepted;
    - both ignorance pairs are reachable on both sides - the certificate
      manager with a batch in flight cannot tell whether the proposer holds
      it, and the proposer holding the quorum trio cannot tell a slow fourth
      validator from a silent one;
    - the late origin's certificate can reach the header AND a header without
      it is also reachable, so S3's [EF] conjunct is a real admissibility
      claim rather than something the model forces;
    - the ungated future-round quorum batch is present and load-bearing: the
      strong persistence reading S3 used to assert is refuted on the pristine
      model, and the refuting witness is the future-round batch rather than
      the cert-validator notice. *)

open Telcoin_epistemic
open Parent_batch_forward_model

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
        (st.Parent_batch_forward_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Parent_batch_forward_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Parent_batch_forward_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The positive-K operand of S2, reused across the contingency probes. *)
let knows_quorum = Formula.K (Validator.V0, f Quorum_of_distinct_origins)

(** The operative state of S2's positive K: the proposer holds round-[r]
    parents and is still at round [r]. *)
let operative =
  Formula.And (f Proposer_holds_parents, f Proposer_at_round_r)

(** The reachable set is the round-[r] pipeline - three early acceptances, the
    quorum crossing with its emission, the straggler's acceptance with the
    second emission, the two FIFO deliveries, the proposal - taken over the
    in-sync run and the run in which the cert-validator's future-round notice
    jumps the proposer past [r], plus the ungated future-round quorum batch of
    {!Parent_batch_forward_model.step_future_batch}. Exactly 42 states
    pristine (32 before that batch was modelled). Product bound 4 early x 2
    latched x 2 straggler x 3 first x 3 second x 2 x 2 x 2 x 2 holds x 4 phase
    x 3 hdr x 3 notice is far larger; the pipeline's coupling is what keeps it
    small, so the band is asserted directly. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 50))

(** The drain of certificates.rs:98 forbids the state it is there to forbid:
    no reachable state has a certificate twice in [last_parents]. *)
let no_duplicate_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF duplicate_in_last_parents is unreachable" false
        (Checker.satisfiable sys (f Duplicate_in_last_parents)))

(** The quorum gate of certificates.rs:92 forbids its state too: the proposer
    never holds round-[r] parents without the aggregator having latched. *)
let parents_imply_latched () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (proposer_holds_parents /\\ ~aggregator_latched) is unreachable"
        false
        (Checker.satisfiable sys
           (Formula.And
              (f Proposer_holds_parents, Formula.Not (f Aggregator_latched)))))

(** The collection window always closes: every run either proposes a header
    for [r+1] or is jumped past [r] by the cert-validator's notice, so no
    path livelocks inside the round. *)
let collection_window_closes () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF ~proposer_can_still_collect" true
        (Checker.valid sys
           (Formula.Af (Formula.Not (f Proposer_can_still_collect)))))

(** S2's positive K does not collapse: there is a reachable state where the
    proposer does NOT know a quorum of distinct origins was accepted. *)
let k_quorum_not_collapsed () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v0(quorum_of_distinct_origins)" true
        (Checker.satisfiable sys (Formula.Not knows_quorum)))

(** S2's positive-K operand is not rigid: it is false at some reachable
    state, so the knowledge is about a contingent fact. *)
let k_quorum_operand_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~quorum_of_distinct_origins" true
        (Checker.satisfiable sys (Formula.Not (f Quorum_of_distinct_origins))))

(** R2 non-singleton evidence for S2's positive K. At an operative state the
    proposer does NOT know that the straggler was not accepted, which is only
    possible if some OTHER reachable state shares V0's view there and has the
    straggler accepted. A singleton view class would make this false. *)
let proposer_view_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (holds_parents /\\ at_round_r /\\ ~K_v0(~straggler_accepted))" true
        (Checker.satisfiable sys
           (Formula.And
              ( operative,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Straggler_accepted)))
              ))))

(** S3's ignorance witness, straggler-accepted side: a reachable state where
    the aggregator HAS accepted the late origin and the proposer cannot know
    it. *)
let straggler_ignorance_true_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (straggler_accepted /\\ ~K_v0(straggler_accepted))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Straggler_accepted,
                Formula.Not (Formula.K (Validator.V0, f Straggler_accepted)) ))))

(** S3's ignorance witness, straggler-absent side: a reachable state where the
    aggregator has NOT accepted the late origin and the proposer cannot know
    that either. Together with the previous case this is the concrete
    view-sharing pair R3 demands. *)
let straggler_ignorance_false_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (~straggler_accepted /\\ ~K_v0(~straggler_accepted))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.Not (f Straggler_accepted),
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Straggler_accepted)))
              ))))

(** S1's ignorance witness, proposer-holding side: the proposer has taken the
    batch and the certificate-manager task cannot know it. *)
let manager_ignorance_holding_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (holds_parents /\\ ~K_v1(holds_parents))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Proposer_holds_parents,
                Formula.Not
                  (Formula.K (Validator.V1, f Proposer_holds_parents)) ))))

(** S1's ignorance witness, proposer-empty side: the batch is out but not yet
    taken and the certificate manager cannot know that either - which is the
    literal justification of the never-reset weight at certificates.rs:94-97. *)
let manager_ignorance_empty_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (~holds_parents /\\ ~K_v1(~holds_parents))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.Not (f Proposer_holds_parents),
                Formula.Not
                  (Formula.K
                     (Validator.V1, Formula.Not (f Proposer_holds_parents))) ))))

(** S3's [EF] conjunct is a real admissibility claim: the late origin's
    certificate does reach a proposed header on some continuation. *)
let late_origin_reaches_header () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF header_carries_straggler" true
        (Checker.satisfiable sys (f Header_carries_straggler)))

(** ... and it is not forced: a header proposed WITHOUT the late origin is
    also reachable, because [should_create_header] (proposer.rs:755-757) can
    fire on the max-delay timeout before the second batch is delivered. That
    is exactly why S3 states [EF] and not [AF]. *)
let late_origin_can_be_missed () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (header_proposed /\\ ~header_carries_straggler)" true
        (Checker.satisfiable sys
           (Formula.And
              (f Header_proposed, Formula.Not (f Header_carries_straggler)))))

(** The strong persistence reading S3 used to assert -
    [AG((holds_straggler /\ ~header_proposed /\ ~catchup_notice_pending) ->
    A[holds_straggler W (header_proposed /\ header_carries_straggler)])] - is
    REFUTED on the pristine model, and the witness carries
    [~catchup_notice_pending], so it is the future-round quorum batch of
    {!Parent_batch_forward_model.step_future_batch} that breaks it and not the
    cert-validator notice. This case is the guard against the weakening in S3
    conjunct (2) silently rotting back into the unearned claim: if the
    ungated [Greater] assign of proposer.rs:404-407 ever falls out of the
    model again, this test goes red. *)
let strong_persistence_is_false () =
  with_sys (fun sys ->
      let in_header =
        Formula.And (f Header_proposed, f Header_carries_straggler)
      in
      Alcotest.(check bool)
        "EF (holds_straggler /\\ ~header_proposed /\\ ~notice /\\ E[~in_header \
         U (~holds_straggler /\\ ~in_header)])"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Proposer_holds_straggler;
                Formula.Not (f Header_proposed);
                Formula.Not (f Catchup_notice_pending);
                Formula.Eu
                  ( Formula.Not in_header,
                    Formula.And
                      ( Formula.Not (f Proposer_holds_straggler),
                        Formula.Not in_header ) );
              ])))

(** The future-round batch leaves [last_parents] NON-empty, which is why
    [Proposer_holds_parents] must be true there: proposer.rs:407 assigns that
    round's parents, and [enough_parents] (:751) does not look at rounds. A
    model that cleared the vector instead would hand S2's liveness conjunct a
    starvation it does not have. *)
let future_parents_are_parents () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (holds_future_round_parents /\\ holds_parents)" true
        (Checker.satisfiable sys
           (Formula.And
              (f Proposer_holds_future_round_parents, f Proposer_holds_parents))))

(** ... and it always closes the round-[r] collection window: once the
    [Greater] arm has taken a future round, every later round-[r] batch hits
    [Ordering::Less] (proposer.rs:427-436). *)
let future_parents_close_the_window () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "AG (holds_future_round_parents -> ~proposer_can_still_collect)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 ( f Proposer_holds_future_round_parents,
                   Formula.Not (f Proposer_can_still_collect) )))))

let () =
  Alcotest.run "parent_batch_forward"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Parent_batch_forward_statements.name `Quick
              (prove_one st))
          Parent_batch_forward_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "no-duplicate-reachable" `Quick
            no_duplicate_reachable;
          Alcotest.test_case "parents-imply-latched" `Quick
            parents_imply_latched;
          Alcotest.test_case "collection-window-closes" `Quick
            collection_window_closes;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-quorum-not-collapsed" `Quick
            k_quorum_not_collapsed;
          Alcotest.test_case "k-quorum-operand-contingent" `Quick
            k_quorum_operand_contingent;
          Alcotest.test_case "proposer-view-class-not-singleton" `Quick
            proposer_view_class_not_singleton;
          Alcotest.test_case "straggler-ignorance-true-side" `Quick
            straggler_ignorance_true_side;
          Alcotest.test_case "straggler-ignorance-false-side" `Quick
            straggler_ignorance_false_side;
          Alcotest.test_case "manager-ignorance-holding-side" `Quick
            manager_ignorance_holding_side;
          Alcotest.test_case "manager-ignorance-empty-side" `Quick
            manager_ignorance_empty_side;
          Alcotest.test_case "late-origin-reaches-header" `Quick
            late_origin_reaches_header;
          Alcotest.test_case "late-origin-can-be-missed" `Quick
            late_origin_can_be_missed;
        ] );
      ( "future-round-jump",
        [
          Alcotest.test_case "strong-persistence-is-false" `Quick
            strong_persistence_is_false;
          Alcotest.test_case "future-parents-are-parents" `Quick
            future_parents_are_parents;
          Alcotest.test_case "future-parents-close-the-window" `Quick
            future_parents_close_the_window;
        ] );
    ]
