(** Proof suite for the FETCH_VERIF_STATE family: the three statements prove on
    the pristine {!Fetch_verif_state_model}, the model really is as small as
    claimed, the invariants the verification plan enforces are unsatisfiable
    negatively, and - the point of the [contingency] group - the family's single
    positive K is neither collapsed nor propped up by a singleton view class.

    The [sanity] group pins the exact reachable count and the three states the
    pristine gates forbid. The [contingency] group discharges R2 and R3: the
    positive K of S1 is contingent (there are reachable states where V1 does NOT
    know the anchor's quorum is genuine), the operative view class provably
    contains at least two reachable worlds, and the ignorance conjunct of S1 has
    a real witness pair in both directions. *)

open Telcoin_epistemic
open Fetch_verif_state_model

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
        (st.Fetch_verif_state_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Fetch_verif_state_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Fetch_verif_state_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The pristine reachable set is the initial state plus one state per pipeline
    position per served response: 1 + 4 * (5 forgeries * 2 tag choices) = 41. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check int) "reachable states" 41 (Checker.reachable_count sys))

(** The state the periodic disjunct at cert_validator.rs:309-311 forbids: the
    round-50 anchor is never admitted on digest linkage alone. *)
let anchor_never_indirect () =
  with_sys (fun sys ->
      Alcotest.(check bool) "marked_indirectly(C50) is unreachable" false
        (Checker.satisfiable sys (f Anchor_marked_indirect)))

(** The state the chunk error propagation at cert_validator.rs:337-343 forbids:
    no member of the response is ever written once the anchor's aggregate check
    has failed. *)
let failed_anchor_stores_nothing () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "aggregate_check_failed(C50) /\\ stored(C49) is unreachable" false
        (Checker.satisfiable sys
           (Formula.And (f Anchor_check_failed, f Low_stored))))

(** The intra-chunk short-circuit at cert_validator.rs:356-361: when the anchor
    fails, the leaf's own aggregate is never put to the committee keys. *)
let failed_anchor_shields_the_leaf () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "aggregate_check_failed(C50) /\\ aggregate_examined(C52) is unreachable"
        false
        (Checker.satisfiable sys
           (Formula.And (f Anchor_check_failed, f Leaf_aggregate_examined))))

(** R2, part one - the positive K of S1 is CONTINGENT, not collapsed: there are
    reachable states (every state before the chunk has run) at which V1 does not
    know that C50's aggregate is genuine. *)
let anchor_knowledge_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "~K_V1(genuine_quorum(C50)) is satisfiable" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Anchor_quorum_genuine)))))

(** R2, part two - the operative view class is NOT a singleton. Take
    q = ~genuine_quorum(C51), which is false at the [Fg_none] operative state;
    [~K_V1(~q)] is [~K_V1(genuine_quorum(C51))], and it can only be satisfiable
    at an operative state if some OTHER reachable state shares V1's view there
    and satisfies q. A singleton class would make this false, which is exactly
    the point of the test. *)
let operative_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "batch_accepted /\\ ~K_V1(genuine_quorum(C51)) is satisfiable" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Batch_accepted,
                Formula.Not
                  (Formula.K (Validator.V1, f Link_quorum_genuine)) ))))

(** R3, the other half of S1's ignorance conjunct: V1 does not know the NEGATION
    either, so the class really does straddle both truth values of
    genuine_quorum(C51). *)
let link_ignorance_is_two_sided () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "batch_accepted /\\ ~K_V1(~genuine_quorum(C51)) is satisfiable" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Batch_accepted,
                Formula.Not
                  (Formula.K
                     (Validator.V1, Formula.Not (f Link_quorum_genuine))) ))))

(** The concrete disagreeing pair behind that ignorance: an accepted response in
    which C51's aggregate is genuine, and an accepted response in which it is
    forged. Both are reachable, so the ignorance is witnessed by real states and
    not by a quirk of the encoding. *)
let ignorance_witness_pair_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check (pair bool bool))
        "both (batch_accepted /\\ genuine_quorum(C51)) and its negation are \
         reachable"
        (true, true)
        ( Checker.satisfiable sys
            (Formula.And (f Batch_accepted, f Link_quorum_genuine)),
          Checker.satisfiable sys
            (Formula.And
               (f Batch_accepted, Formula.Not (f Link_quorum_genuine))) ))

(** The peer-tag branch is real: a response that arrives carrying a self-
    asserted [VerifiedDirectly] tag is still accepted after the ingress reset
    neutralises it, so S1's conjunct (D) is not vacuous. *)
let tagged_response_still_accepted () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "peer_claims_verified /\\ batch_accepted is satisfiable" true
        (Checker.satisfiable sys
           (Formula.And (f Peer_tagged, f Batch_accepted))))

let () =
  Alcotest.run "fetch_verif_state"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Fetch_verif_state_statements.name `Quick
              (prove_one st))
          Fetch_verif_state_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "anchor-never-indirect" `Quick
            anchor_never_indirect;
          Alcotest.test_case "failed-anchor-stores-nothing" `Quick
            failed_anchor_stores_nothing;
          Alcotest.test_case "failed-anchor-shields-the-leaf" `Quick
            failed_anchor_shields_the_leaf;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "anchor-knowledge-is-contingent" `Quick
            anchor_knowledge_is_contingent;
          Alcotest.test_case "operative-class-is-not-a-singleton" `Quick
            operative_class_is_not_a_singleton;
          Alcotest.test_case "link-ignorance-is-two-sided" `Quick
            link_ignorance_is_two_sided;
          Alcotest.test_case "ignorance-witness-pair-is-reachable" `Quick
            ignorance_witness_pair_is_reachable;
          Alcotest.test_case "tagged-response-still-accepted" `Quick
            tagged_response_still_accepted;
        ] );
    ]
