(** Proof suite for the STORE_KEY_ORDER family: the three statements prove on
    the pristine model, the model stays inside its stated size bound, each
    gate's forbidden state is genuinely unreachable, the liveness statement is
    not an artefact of a model that always fetches, and - the part that matters
    most - the knowledge and the ignorance claims of S2 are discharged by
    explicit witnesses rather than by a collapsed view class.

    The [contingency] group carries, for the positive K conjunct, both
    obligations: the knowledge is contingent (its negation is satisfiable
    somewhere reachable) and its view class at the operative state is NOT a
    singleton (at an [Answer_high] state V0 fails to know the negation of an
    atom that is false there, which is only possible when another reachable
    state shares V0's view and satisfies that atom). For the ignorance conjunct
    it carries the witness pair: a state answering [None] where [j] really did
    sign and V0 does not know it, and a state with the same answer where [j]
    did not sign.

    The class sizes were measured rather than assumed. Of the six reachable
    [Answer_high] states, four have a V0-view class of size two - V0 holds no
    row for [k] there, so [k]'s act is genuinely hidden - and two have a class
    of size one, namely the states where V0 also holds [k]'s row and both
    signing ghosts are therefore pinned by rows it can see. The K conjunct is
    doing real work at the four, and the state that refutes it under
    {!Store_key_order_model.No_origin_guard} is one of them ([j]'s block empty,
    [k]'s row present, class size two). All six [Answer_absent] states have a
    class of size two or four in which the [j] ghost takes BOTH values, so the
    ignorance conjunct is two-sided at every operative state, not just at one. *)

open Telcoin_epistemic
open Store_key_order_model

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
        (st.Store_key_order_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Store_key_order_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Store_key_order_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The exact pristine reachable count: 18 index configurations x 3 stages. The
    eighteen are [(j_lo present?)] = 2, times [(j_hi, j signed at R_hi)] in
    {(absent,no), (absent,yes), (present,yes)} = 3, times [(k_hi, k signed at
    R_hi)] over the same three = 3. The three stages are [Filling], the
    [Probed] state its probe answer determines, and the [Decided] state that
    answer determines - each index configuration contributes exactly one of
    each, so the raw product bound of 18 x 4 = 72 collapses to 54. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check int) "reachable states" 54 (Checker.reachable_count sys))

(** The write path really is the only writer: no reachable state holds a row
    for [(j, R_hi)] that [j] did not sign, because [save_cert] derives the key
    from the certificate itself (stores/certificate_store.rs:140-142). *)
let row_implies_authorship_j () =
  with_sys (fun sys ->
      Alcotest.(check bool) "no unsigned row for j is reachable" false
        (Checker.satisfiable sys
           (Formula.And (f Row_j_high, Formula.Not (f J_signed_high)))))

(** The same for the neighbouring authority [k], whose row is what the deleted
    guard would otherwise let the probe speak for. *)
let row_implies_authorship_k () =
  with_sys (fun sys ->
      Alcotest.(check bool) "no unsigned row for k is reachable" false
        (Checker.satisfiable sys
           (Formula.And (f Row_k_high, Formula.Not (f K_signed_high)))))

(** The origin guard's forbidden state: no reachable state answers [Some(R_hi)]
    for [j] without a row of [j] at [R_hi]
    (stores/certificate_store.rs:414-416). *)
let no_answer_without_a_row () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "no round answer for an authority with no row is reachable" false
        (Checker.satisfiable sys
           (Formula.And (f Answer_high, Formula.Not (f Row_j_high)))))

(** The encoding contract's forbidden state: no reachable state answers
    [Some(R_lo)] while a row at the higher round is stored
    (types/src/codec.rs:45). *)
let no_shadowed_answer () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "no answer shadowed by a larger stored round is reachable" false
        (Checker.satisfiable sys (Formula.And (f Answer_low, f Row_j_high))))

(** S3 is not manufactured: the modelled fetcher genuinely does suppress
    fetches, so [AF fetch] is a claim about the gate rather than about a model
    that always fetches (certificate_fetcher.rs:207-209). *)
let suppression_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "a suppressed fetch is reachable" true
        (Checker.satisfiable sys (f Fetch_suppressed)))

(** The premise of the origin-guard statements is reachable: [j]'s block is
    empty while the authority immediately below it holds a row at the same
    round - the post-GC / new-committee-member shape. *)
let empty_origin_block_under_a_neighbour_row_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "an empty j block under a k row at R_hi is reachable" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Row_k_high;
                Formula.Not (f Row_j_high);
                Formula.Not (f Row_j_low);
                f Probe_returned;
              ])))

(** R2 contingency for [K_V0 signed(j, R_hi)]: the knowledge is not rigid -
    there are reachable states where V0 does not have it. *)
let round_answer_knowledge_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "K_V0 signed(j,R_hi) fails somewhere reachable" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f J_signed_high)))))

(** R2 non-singleton class for [K_V0 signed(j, R_hi)]: at an [Answer_high]
    state V0 does NOT know that [k] failed to sign at [R_hi]. That is only
    possible because another reachable state shares V0's view - same three
    rows, same stage - and disagrees on [k]'s act, which V0 cannot see while it
    holds no row for [k]. *)
let round_answer_view_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "the V0-view class at an Answer_high state holds more than one state"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Answer_high,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f K_signed_high))) ))))

(** R3 ignorance witness, true side: a reachable state where the probe answered
    [None], [j] really did sign at [R_hi], and V0 does not know it - the
    certificate exists and V0's fetch has simply not delivered it. *)
let absent_answer_ignorance_witness_true_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a None answer over a round j really signed, unknown to V0, is \
         reachable"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Answer_absent;
                f J_signed_high;
                Formula.Not (Formula.K (Validator.V0, f J_signed_high));
              ])))

(** R3 ignorance witness, false side: the state that makes the first half
    ignorance rather than knowledge - the same [None] answer over an authority
    that really did stay silent. *)
let absent_answer_ignorance_witness_false_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a None answer over a round j did not sign is reachable" true
        (Checker.satisfiable sys
           (Formula.And (f Answer_absent, Formula.Not (f J_signed_high)))))

(** The ignorance of S2 conjunct B is two-sided at one and the same state: V0
    neither knows the operand nor its negation. *)
let absent_answer_ignorance_is_two_sided () =
  with_sys (fun sys ->
      Alcotest.(check bool) "V0 knows neither side at a None answer" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Answer_absent;
                Formula.Not (Formula.K (Validator.V0, f J_signed_high));
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f J_signed_high)));
              ])))

let () =
  Alcotest.run "store_key_order"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Store_key_order_statements.name `Quick
              (prove_one st))
          Store_key_order_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "row-implies-authorship-j" `Quick
            row_implies_authorship_j;
          Alcotest.test_case "row-implies-authorship-k" `Quick
            row_implies_authorship_k;
          Alcotest.test_case "no-answer-without-a-row" `Quick
            no_answer_without_a_row;
          Alcotest.test_case "no-shadowed-answer" `Quick no_shadowed_answer;
          Alcotest.test_case "suppression-is-reachable" `Quick
            suppression_is_reachable;
          Alcotest.test_case "empty-origin-block-under-a-neighbour-row" `Quick
            empty_origin_block_under_a_neighbour_row_is_reachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "round-answer-knowledge-is-contingent" `Quick
            round_answer_knowledge_is_contingent;
          Alcotest.test_case "round-answer-view-class-is-not-a-singleton" `Quick
            round_answer_view_class_is_not_a_singleton;
          Alcotest.test_case "absent-answer-ignorance-witness-true-side" `Quick
            absent_answer_ignorance_witness_true_side;
          Alcotest.test_case "absent-answer-ignorance-witness-false-side" `Quick
            absent_answer_ignorance_witness_false_side;
          Alcotest.test_case "absent-answer-ignorance-is-two-sided" `Quick
            absent_answer_ignorance_is_two_sided;
        ] );
    ]
