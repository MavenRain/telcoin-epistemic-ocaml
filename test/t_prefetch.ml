(** The prefetch family (DESIGN CONSENSUS-EXT #6) proves on the pristine
    {!Prefetch_model}, the reachable graph is the expected tiny branching
    structure, and the epistemic layer is genuinely partial-information: the
    positive-K conjunct K_V1(exists other holder) does not collapse (there is
    a reachable ~K state), the card's false witness - a listener that
    received a FORGED digest with no holder anywhere and cannot know a holder
    exists (RUN A) - is reachable, its Cooperate collision partner with a
    REAL holder but the same view (RUN B) is reachable, and holder knowledge
    is attainable through the verified fetch (the Cooperate hold). *)

open Telcoin_epistemic
open Prefetch_model

(** Build the pristine system or fail the test on an impossible
    [Empty_init]. *)
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
        (st.Prefetch_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Prefetch_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Prefetch_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The card's positive-K operand, reused across the contingency probes. *)
let held_by_other = Formula.K (Validator.V1, f Held_by_other)

(** The reachable set is exactly the linear 3-phase run with one 2-way
    hidden branch at Gossip and a Deliver fan-out: initial, the two
    pre-fetch branch states, the Cooperate hold, and the Forge no-store
    terminal - 5 states pristine. Product bound 3 phases x 3 choices x 2
    recv x 2 stored = 36; 16 leaves slack. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 16))

(** Every path reaches the terminal phase (the liveness spine). *)
let terminal_reached () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF done" true
        (Checker.valid sys (Formula.Af (f At_done))))

(** The positive-K conjunct K_V1(exists other holder) does not collapse:
    there is a reachable state where V1 does NOT know a holder exists, so
    the operand is contingent under the view partition rather than rigidly
    true. *)
let k_not_collapsed () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(exists other holder): knowledge did not collapse" true
        (Checker.satisfiable sys (Formula.Not held_by_other)))

(** The card's false witness RUN A is reachable: V1 received a (forged)
    digest, holds nothing, no real holder exists, and V1 cannot know a
    holder exists - the operand-false side of the colliding pair. *)
let false_witness_run_a () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (recv /\\ ~holds /\\ ~held-by-other /\\ ~K_v1 held-by-other)" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Recv_digest;
                Formula.Not (f Holds);
                Formula.Not (f Held_by_other);
                Formula.Not held_by_other;
              ])))

(** The card's collision partner RUN B is reachable: the Cooperate pre-fetch
    state, view-identical to RUN A but with a REAL holder (operand true),
    where V1 still cannot know a holder exists - so the invariant's ~K is
    witnessed non-trivially. *)
let collision_partner_run_b () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (recv /\\ ~holds /\\ held-by-other /\\ ~K_v1 held-by-other)" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Recv_digest;
                Formula.Not (f Holds);
                f Held_by_other;
                Formula.Not held_by_other;
              ])))

(** Holder knowledge is attainable (the Cooperate verified fetch stores b
    and grounds K_V1(exists other holder)), so the ~K in the invariant is
    contingent, not vacuously true everywhere. *)
let knowledge_attainable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF K_v1(exists other holder)" true
        (Checker.satisfiable sys held_by_other))

let () =
  Alcotest.run "prefetch"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Prefetch_statements.name `Quick
              (prove_one st))
          Prefetch_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "terminal-reached" `Quick terminal_reached;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-not-collapsed" `Quick k_not_collapsed;
          Alcotest.test_case "false-witness-run-a" `Quick false_witness_run_a;
          Alcotest.test_case "collision-partner-run-b" `Quick
            collision_partner_run_b;
          Alcotest.test_case "knowledge-attainable" `Quick knowledge_attainable;
        ] );
    ]
