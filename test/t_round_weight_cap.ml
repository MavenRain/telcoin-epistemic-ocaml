(** The ROUND_WEIGHT_CAP family (S1 the per-identity voting-power cap, S2 what
    a round-quorum emission proves about remote certification rounds, S3 the
    silence of the equivocation drop) proves on the pristine
    {!Round_weight_cap_model} through [prove_nonvacuous] - so each antecedent
    is also checked reachable - the reachable graph stays in its justified
    band, the gates the family rests on really do forbid the states they are
    claimed to forbid, and the epistemic layer is genuinely partial
    information.

    R2 and R3 are discharged here explicitly. The family has exactly TWO
    positive knowledge conjuncts:
    [K_V0(certified(r) >= 2f+1)] in S2 conjunct (A) and
    [K_V0(equivocated(V3,r))] in S3 conjunct (B). Each gets a contingency test
    (the knowledge is reachable-false somewhere, so it did not collapse) and a
    non-singleton view-class test: at the operative state V0 cannot rule out
    that the peer primary has fired its own round-[r] aggregator, which is
    possible ONLY if a second reachable world shares V0's view. The two
    negative conjuncts - [~K_V0(emitted_1(r))] in S2 conjunct (B) and
    [~K_V1(equivocated(V3,r))] in S3 conjunct (C) - get their R3 ignorance
    witnesses in both directions.

    Measured on the 46-world pristine model: the V0-view class has 2 to 4
    members at each of the 16 emitting states and 2 to 3 members at each of the
    10 states where V0 holds the second header, and the V1-view class has 4 to
    14 members at each of the 18 states where the peer has fired - so no
    positive [K] here is standing on a singleton class anywhere, not merely at
    the one state the witness rows exhibit.

    The [sanity] group also pins the FAITHFULNESS side of the family: the
    downstream repair (handler.rs:725-728, :733-738) is modelled, it is
    reachable in the sense that a header really does get accepted, and it is
    NEVER tripped on the pristine model - [H_rejected] is unreachable here and
    becomes reachable only when a gate is deleted. *)

open Telcoin_epistemic
open Round_weight_cap_model

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
        (st.Round_weight_cap_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Round_weight_cap_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Round_weight_cap_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The operative state of both positive knowledge conjuncts' R2 tests: the
    local aggregator has fired for round [r]. *)
let emitted = f Emitted_round_quorum

(** The operative state of S3 conjunct (B): the node personally received the
    Byzantine origin's second round-[r] header. *)
let holds_second = Formula.And (f Duplicate_appended, f Origin_equivocated)

(* Loose product bound: 2 duplicate kinds x 2 certification levels x 4
   authorities_seen cardinalities (0..3) x 5 weights (0..4) x 2 emission
   latches x 2 duplicate deliveries x 2 peer statuses x 3 header verdicts =
   1920. The pristine reachable set is exactly 46: per frozen duplicate kind,
   5 states below the certification step (0..2 distinct origins, with the
   duplicate deliverable once at least one origin is counted) and 18 above it
   (0..3 distinct origins x the duplicate x the peer's own aggregator, plus
   the header verdict once the batch has been emitted), i.e. 23 per cone. The
   mutants are larger - 56 under the distinctness deletion, 78 under the
   threshold deletion - because both let the aggregator reach states the
   pristine gates forbid. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 1920))

(* S1 conjunct (A) as a direct unreachability claim: no identity ever moves
   the round toward its parent quorum by more than one unit. This is
   certificates.rs:82-85 standing in front of the accumulation at :87-89, with
   EQUAL_VOTING_POWER = 1 (committee.rs:25, :511-513) fixing the unit. *)
let cap_forbids_inflation () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (weight_0(r) > |authorities_seen_0(r)|)" false
        (Checker.satisfiable sys (f Weight_exceeds_origins)))

(* The state S2 and S3 rest on, asserted directly as unreachable: the round-r
   batch never goes to the proposer on fewer than 2f+1 DISTINCT origins.
   Deleting either gate makes this satisfiable. *)
let emission_needs_distinct_quorum () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (emitted_0(r) /\\ ~distinct_0(r) >= 2f+1)"
        false
        (Checker.satisfiable sys
           (Formula.And
              (emitted, Formula.Not (f Distinct_quorum_appended)))))

(* Faithfulness pin, the R5 half. The remote voters' re-derivation of parent
   distinctness and quorum stake (handler.rs:700, :725-728, :730, :733-738) IS
   in the model, but on the pristine model it never has anything to catch:
   [H_rejected] is unreachable. It becomes reachable the moment a gate is
   deleted, which is what makes it a modelled repair rather than a decoration. *)
let remote_repair_never_tripped_pristine () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF header_rejected_0(r+1)" false
        (Checker.satisfiable sys (f Header_rejected)))

(* ... and the other half: the repair path is genuinely exercised, i.e. a
   round-(r+1) header built on the emitted parent set really does get accepted,
   so S1 conjunct (C) is not true by the accepting branch being unreachable. *)
let header_acceptance_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF header_accepted_0(r+1)" true
        (Checker.satisfiable sys (f Header_accepted)))

(* S1 conjunct (B) as its own row: a duplicate certificate for an
   already-counted origin really does reach [append]. The re-fetch route
   (cert_validator.rs:235-243 -> :133, neither :246-268 nor :272-296 touching
   storage) needs no Byzantine behaviour at all. *)
let duplicate_reaches_append () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF duplicate_offered_0(r)" true
        (Checker.satisfiable sys (f Duplicate_appended)))

(* R2 contingency for S2 conjunct (A). The complement of
   [K_V0(certified(r) >= 2f+1)] is reachable, so the operand is not plain truth
   under the view partition and the knowledge did not collapse. Witness: every
   state before the certification step, and every state where V0 has appended
   fewer than 2f+1 distinct origins. *)
let k_remote_quorum_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v0(certified(r) >= 2f+1): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f Remote_quorum_certified)))))

(* R2 non-singleton view class for S2 conjunct (A). The probe atom
   q = emitted_1(r) is FALSE at the witnessing state and V0 still cannot
   conclude ~q there - possible ONLY if its view class holds a second reachable
   world in which the peer's own aggregator HAS fired. A singleton class would
   make this [false] and fail the row, which is exactly the point. *)
let k_remote_quorum_class_nonsingleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (emitted_0(r) /\\ ~K_v0(~emitted_1(r))): class is not a singleton"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( emitted,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Peer_reached_quorum)))
              ))))

(* R2 contingency for S3 conjunct (B): throughout the honest cone, where the
   duplicate is a re-delivered copy rather than a second header, V0 does not
   know that the origin equivocated. *)
let k_equivocation_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v0(equivocated(V3,r)): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f Origin_equivocated)))))

(* R2 non-singleton view class for S3 conjunct (B), at its own operative state
   (V0 is holding the second header). Same probe atom, same reasoning: V0's
   view class there contains at least one further reachable world, differing in
   the peer's aggregator status. *)
let k_equivocation_class_nonsingleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (holds second header /\\ ~K_v0(~emitted_1(r))): not a singleton"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( holds_second,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Peer_reached_quorum)))
              ))))

(* R3 ignorance witness for S2 conjunct (B), the "it is true and V0 does not
   know it" direction: a reachable emitting state at which the peer HAS fired
   and V0 cannot tell. *)
let ignorance_peer_quorum_true () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (emitted_0(r) /\\ emitted_1(r) /\\ ~K_v0(emitted_1(r)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( emitted,
                Formula.And
                  ( f Peer_reached_quorum,
                    Formula.Not
                      (Formula.K (Validator.V0, f Peer_reached_quorum)) ) ))))

(* R3 ignorance witness for S2 conjunct (B), the "it is false and V0 does not
   know that either" direction. Together the two rows exhibit the colliding
   pair: two reachable states with an identical V0 view disagreeing on
   emitted_1(r). *)
let ignorance_peer_quorum_false () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (emitted_0(r) /\\ ~emitted_1(r) /\\ ~K_v0(~emitted_1(r)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( emitted,
                Formula.And
                  ( Formula.Not (f Peer_reached_quorum),
                    Formula.Not
                      (Formula.K
                         (Validator.V0, Formula.Not (f Peer_reached_quorum))) )
              ))))

(* R3 ignorance witness for S3 conjunct (C), the equivocating direction: the
   peer has fired its own round-r aggregator, the origin DID equivocate, and
   the peer cannot tell - because the drop at certificates.rs:83-85 is a bare
   [return None] that puts nothing on the wire. *)
let ignorance_peer_equivocation_true () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (emitted_1(r) /\\ equivocated(V3,r) /\\ ~K_v1(equivocated(V3,r)))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Peer_reached_quorum,
                Formula.And
                  ( f Origin_equivocated,
                    Formula.Not
                      (Formula.K (Validator.V1, f Origin_equivocated)) ) ))))

(* R3 ignorance witness for S3 conjunct (C), the honest direction: nothing ever
   confirms to the peer that no equivocation happened either. *)
let ignorance_peer_equivocation_false () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (emitted_1(r) /\\ ~equivocated(V3,r) /\\ ~K_v1(~equivocated(V3,r)))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Peer_reached_quorum,
                Formula.And
                  ( Formula.Not (f Origin_equivocated),
                    Formula.Not
                      (Formula.K
                         (Validator.V1, Formula.Not (f Origin_equivocated))) )
              ))))

let () =
  Alcotest.run "round_weight_cap"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Round_weight_cap_statements.name `Quick
              (prove_one st))
          Round_weight_cap_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "cap-forbids-weight-inflation" `Quick
            cap_forbids_inflation;
          Alcotest.test_case "emission-needs-distinct-quorum" `Quick
            emission_needs_distinct_quorum;
          Alcotest.test_case "remote-repair-never-tripped-pristine" `Quick
            remote_repair_never_tripped_pristine;
          Alcotest.test_case "header-acceptance-reachable" `Quick
            header_acceptance_reachable;
          Alcotest.test_case "duplicate-reaches-append" `Quick
            duplicate_reaches_append;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-remote-quorum-contingent" `Quick
            k_remote_quorum_contingent;
          Alcotest.test_case "k-remote-quorum-class-nonsingleton" `Quick
            k_remote_quorum_class_nonsingleton;
          Alcotest.test_case "k-equivocation-contingent" `Quick
            k_equivocation_contingent;
          Alcotest.test_case "k-equivocation-class-nonsingleton" `Quick
            k_equivocation_class_nonsingleton;
          Alcotest.test_case "ignorance-peer-quorum-true" `Quick
            ignorance_peer_quorum_true;
          Alcotest.test_case "ignorance-peer-quorum-false" `Quick
            ignorance_peer_quorum_false;
          Alcotest.test_case "ignorance-peer-equivocation-true" `Quick
            ignorance_peer_equivocation_true;
          Alcotest.test_case "ignorance-peer-equivocation-false" `Quick
            ignorance_peer_equivocation_false;
        ] );
    ]
