(** The PENDING_GC family proves on the pristine {!Pending_gc_model} through
    [prove_nonvacuous] (so every antecedent is also checked reachable), the
    reachable graph stays in its justified band, the three gates the family
    depends on genuinely forbid the states they claim to forbid, and the
    epistemic layer is genuinely partial-information.

    The contingency group is where R2 and R3 are discharged. The family has one
    POSITIVE knowledge conjunct, [K (V0, accepted_v(c))] in S3, which gets both
    a contingency test (the knowledge is not collapsed: it fails somewhere
    reachable) and TWO non-singleton-view-class tests (at a voted state the
    author still cannot rule out that the voter is past its horizon, nor learn
    whether the voter holds the grandparent - each is only possible if the
    class has another world). The family has two NEGATIVE knowledge conjuncts,
    [~K (V1, holds_w(d))] and [~K (V1, ~holds_w(d))] in S1, and each gets its
    ignorance witness naming the colliding pair - the all-honest world and the
    world in which the peer is [c]'s one faulty signer.

    TWO faithfulness guards sit in the sanity group rather than the contingency
    group. [pending-can-follow-a-missing-report] asserts the state that makes
    S3's [Ax] form NECESSARY is reachable, i.e. that the weaker-looking
    AG( missing_computed -> ~pending_v(c) ) really is FALSE and was not
    available to be stated instead. [one-computed-response-per-header] pins the
    scope S3 conjunct A is stated at: this model carries exactly ONE computed
    response per header, because a repeat request is served from the per-author
    vote cache (handler.rs:510-534), which replays an answer rather than
    computing one. If a later edit ever made an answered round emit a second
    response, that test fails and conjunct A must be restated. *)

open Telcoin_epistemic
open Pending_gc_model

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
        (st.Pending_gc_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Pending_gc_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Pending_gc_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 3 cert states x 3 dependency states x 2 horizons x 3
   vote rounds x 2 peer branches = 108. The pristine reachable set is exactly
   48: monotonicity collapses the certificate chain to 10 reachable
   (local_c, local_d, horizon) triples, [R_open] and [R_missing] pair with all
   10 while [R_voted] pairs with only the 4 that are reachable from an accepted
   state, giving 24 local configurations, doubled by the frozen peer bit. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 108))

(* The exact pristine reachable count, pinned so a silent transition-relation
   drift shows up as a failing test rather than as a quietly different model. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "exact pristine reachable count" 48
        (Checker.reachable_count sys))

(* S1 conjunct A's gate, stated as unreachability: no state accepts the
   certificate with the parent absent while the horizon is still BELOW the
   parent's round. This is exactly what the cert_manager.rs:108 round guard
   plus the cert_manager.rs:109-117 missing-parent branch enforce, and exactly
   what No_parent_check removes. *)
let causal_order_gate_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (accepted_v(c) /\\ ~stored_v(d) /\\ ~gc_past_v(d))" false
        (Checker.satisfiable sys
           (Formula.And
              ( f Cert_accepted,
                Formula.And
                  (Formula.Not (f Parent_stored), Formula.Not (f Horizon_past))
              ))))

(* S3 conjunct A's gate, stated as unreachability of the offending EDGE: from
   no state at which the voter has computed no response yet and the certificate
   is parked can a computed MissingParents naming it follow. The retain at
   pending_cert_manager.rs:171-173 is the sole filter that does this. Scoped to
   the COMPUTED response: a cached replay (handler.rs:519-534) is not modeled
   and is not claimed about. *)
let pending_never_named () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (unanswered_v(h) /\\ pending_v(c) /\\ EX missing_computed)" false
        (Checker.satisfiable sys
           (Formula.And
              ( f Vote_unanswered,
                Formula.And (f Cert_pending, Formula.Ex (f Missing_reported))
              ))))

(* Scope guard for S3 conjunct A: the model carries exactly ONE computed
   response per header, so the [Ax] in conjunct A really does quantify over the
   voter's computed answer and nothing else. Once an answer exists it is cached
   and replayed (handler.rs:510-534), never recomputed, so no second response
   event may follow. *)
let one_computed_response_per_header () =
  with_sys (fun sys ->
      let after_missing =
        Formula.And
          ( f Missing_reported,
            Formula.Ex (Formula.Or (f Vote_unanswered, f Vote_issued)) )
      in
      let after_vote =
        Formula.And
          ( f Vote_issued,
            Formula.Ex (Formula.Or (f Vote_unanswered, f Missing_reported)) )
      in
      Alcotest.(check bool)
        "no answered round emits a second computed response" false
        (Checker.satisfiable sys (Formula.Or (after_missing, after_vote))))

(* S3 conjunct B's gate, stated as unreachability: a vote is never issued
   without the certificate being in the voter's store. This is the blocking
   notify_read at handler.rs:693 and is exactly what No_parent_wait removes. *)
let vote_implies_accepted () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (vote_issued /\\ ~accepted_v(c))" false
        (Checker.satisfiable sys
           (Formula.And (f Vote_issued, Formula.Not (f Cert_accepted)))))

(* Faithfulness guard for S3's [Ax] form: the report is an INSTANT, and a
   certificate may legitimately become pending after the reply was emitted -
   the state (C_pending, D_absent, H_below, R_missing) is reachable by
   computing MissingParents while the certificate is still unknown and only
   then delivering it. So AG( missing_computed -> ~pending_v(c) ) is FALSE, and
   the [Ax] form was not a stylistic choice but the only true statement here.
   This is also the state the real voter replays verbatim on an empty-parents
   retry (handler.rs:519-534) - which is why conjunct A is scoped to the
   COMPUTED response rather than to every response the author receives. *)
let pending_can_follow_a_missing_report () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (missing_computed /\\ pending_v(c))" true
        (Checker.satisfiable sys
           (Formula.And (f Missing_reported, f Cert_pending))))

(* R3 ignorance witness for S1 conjunct B, first half. The operand is pinned
   TRUE at the witnessing state, so the [~K] cannot pass for the trivial reason
   that the operand is simply false there: at a state where the peer DOES hold
   the parent (it is one of [c]'s honest signers), V1 still cannot conclude it,
   because the certificate proves only that a QUORUM signed and with f = 1 this
   particular signer may be the faulty one. That forces a colliding world, and
   it is W2 below. Colliding pair, both reachable and identical under
   [View_local]:
   W1 = (C_accepted, D_absent, H_past, R_open, W_holds_parent) - all honest -
   W2 = (C_accepted, D_absent, H_past, R_open, W_without_parent) - the peer is
   the faulty signer. *)
let ignorance_peer_holds () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (accepted /\\ ~stored /\\ holds_w(d) /\\ ~K_v1 holds_w(d))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Cert_accepted, Formula.Not (f Parent_stored)),
                Formula.And
                  ( f Peer_holds_parent,
                    Formula.Not (Formula.K (Validator.V1, f Peer_holds_parent))
                  ) ))))

(* R3 ignorance witness for S1 conjunct B, second half, pinned the same way at
   W2: at a state where the peer does NOT hold the parent (it signed [c]
   faultily), V1 still cannot rule the possession out, which forces the
   colliding world W1. The same pair witnesses both halves, and that
   two-sidedness is what makes the fault branch genuinely unresolvable rather
   than a one-sided suspicion. *)
let ignorance_peer_lacks () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (accepted /\\ ~stored /\\ ~holds_w(d) /\\ ~K_v1 ~holds_w(d))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Cert_accepted, Formula.Not (f Parent_stored)),
                Formula.And
                  ( Formula.Not (f Peer_holds_parent),
                    Formula.Not
                      (Formula.K
                         (Validator.V1, Formula.Not (f Peer_holds_parent))) ) ))))

(* R2 contingency for the family's single positive knowledge conjunct,
   [K (V0, accepted_v(c))]: its complement is reachable, so the operand is NOT
   plain truth under V0's view partition. It fails at every [R_open] state,
   whose class contains the initial state where the certificate is unknown. *)
let k_author_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_a(accepted_v(c)): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f Cert_accepted)))))

(* R2 non-singleton view class for [K (V0, accepted_v(c))], first witness. Take
   q = gc_past_v(d) and pin it FALSE at the witnessing state, so the [~K] cannot
   pass for the trivial reason that the operand is false there: at a voted state
   where the voter is NOT past its horizon, the author still cannot rule the
   horizon out. That is only possible if V0's voted class holds a second world,
   and it does - the class holds all eight reachable voted states, among them
   A = (C_accepted, D_stored, H_below, R_voted, W_without_parent) (the witness)
   and B = (C_accepted, D_absent, H_past, R_voted, W_holds_parent). *)
let author_class_not_singleton_horizon () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (vote_issued /\\ ~gc_past_v(d) /\\ ~K_a(~gc_past_v(d)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Vote_issued,
                Formula.And
                  ( Formula.Not (f Horizon_past),
                    Formula.Not
                      (Formula.K (Validator.V0, Formula.Not (f Horizon_past)))
                  ) ))))

(* R2 non-singleton view class for [K (V0, accepted_v(c))], second witness,
   pinned the same way with q = stored_v(d) held TRUE at the witnessing world A:
   the author cannot conclude the voter holds the grandparent even where it
   does, because world B in the same class does not. The vote certifies
   possession of the parent it names and NOTHING deeper in the chain. *)
let author_class_not_singleton_stored () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (vote_issued /\\ stored_v(d) /\\ ~K_a(stored_v(d)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Vote_issued,
                Formula.And
                  ( f Parent_stored,
                    Formula.Not (Formula.K (Validator.V0, f Parent_stored)) ) ))))

(* S2's antecedent is genuinely reachable: [deliver_c] at
   (C_unknown, D_absent, H_below) parks the certificate. Without this the whole
   liveness backbone would be certified on a false antecedent. *)
let pending_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF pending_v(c)" true
        (Checker.satisfiable sys (f Cert_pending)))

(* Both of S2 conjunct B's release routes really are distinct successors of a
   parked state, not one rigged edge: the cascade lands on a stored parent, the
   GC release lands past the horizon with the parent still absent. *)
let both_release_routes_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (accepted /\\ stored) and EF (accepted /\\ ~stored /\\ gc_past)" true
        (Checker.satisfiable sys
           (Formula.And (f Cert_accepted, f Parent_stored))
        && Checker.satisfiable sys
             (Formula.And
                ( f Cert_accepted,
                  Formula.And (Formula.Not (f Parent_stored), f Horizon_past)
                ))))

let () =
  Alcotest.run "pending_gc"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Pending_gc_statements.name `Quick
              (prove_one st))
          Pending_gc_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "causal-order-gate-unreachable" `Quick
            causal_order_gate_unreachable;
          Alcotest.test_case "pending-never-named" `Quick pending_never_named;
          Alcotest.test_case "one-computed-response-per-header" `Quick
            one_computed_response_per_header;
          Alcotest.test_case "vote-implies-accepted" `Quick
            vote_implies_accepted;
          Alcotest.test_case "pending-can-follow-a-missing-report" `Quick
            pending_can_follow_a_missing_report;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "ignorance-peer-holds" `Quick ignorance_peer_holds;
          Alcotest.test_case "ignorance-peer-lacks" `Quick ignorance_peer_lacks;
          Alcotest.test_case "k-author-contingent" `Quick k_author_contingent;
          Alcotest.test_case "author-class-not-singleton-horizon" `Quick
            author_class_not_singleton_horizon;
          Alcotest.test_case "author-class-not-singleton-stored" `Quick
            author_class_not_singleton_stored;
          Alcotest.test_case "pending-reachable" `Quick pending_reachable;
          Alcotest.test_case "both-release-routes-reachable" `Quick
            both_release_routes_reachable;
        ] );
    ]
