(** The stall family (DESIGN CONSENSUS-EXT #14) proves on the pristine
    {!Stall_model} through [prove_nonvacuous] (so the antecedent is also
    checked reachable), the reachable graph stays in its justified band, and
    the epistemic layer is genuinely partial-information: the false
    witness - the totally starved victim at the end of the withheld
    [Deliver R1], where the R1 quorum EXISTS in peers' dags but the victim
    received nothing - collides in local view with an end-[Vote R1] state
    where no certificate has entered any dag, so [K_v2 cert_quorum(R1)] is
    contingent rather than collapsed. The pending-targets gate is exercised
    on both sides: the target-free starved branch reaches [Done] still
    starved (the Kick no-op, certificate_fetcher.rs:184), and the lagged
    branch's pending target is served by the timeout fetch. *)

open Telcoin_epistemic
open Stall_model

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
        (st.Stall_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Stall_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Stall_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The model is a deterministic single-branch tree: a 4-state pre-branch
    chain (Propose R1 -> Vote R1 -> Certify R1 -> Deliver R1), then the
    lone [Deliver R1] hidden choice splits into the [Deliver_all],
    [Starve_v2] and [Lag_v2] branches, each a linear 7-state run
    (Propose R2 -> Vote R2 -> Certify R2 -> Deliver R2 -> Commit_eval ->
    Timeout_fetch -> Done): 4 + 3 * 7 = 25 reachable states. Crude product
    bound 11 phase values x 4 delivery branches = 44 leaves slack without
    hiding blow-up. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 44))

(** Every path reaches the terminal phase - the commit-timeout micro-step
    is scheduled before [Done], so the strict AF form is well-founded. *)
let terminal_reached () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF done" true
        (Checker.valid sys (Formula.Af (f At_done))))

(** The single positive K conjunct of S14 is [K_v2 cert_quorum(R1)] (under
    the AF): assert its operand is NOT plain truth under the view partition,
    or the statement would be epistemically vacuous. It fails at the starved
    states and at every pre-certification state, so [~K] is satisfiable. *)
let k_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v2(cert-quorum-r1): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V2, f Cert_quorum_r1)))))

(** The false witness (operand-TRUE side): the totally starved victim - it
    holds NO R1 certificate and no pending target, yet the R1 quorum
    EXISTS in the union (peers' dags), and V2 cannot know it because its
    local view collides with a no-certificate state. This is the state
    that makes the ignorance clause's [~K] non-trivial. *)
let false_witness_starved () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (starved(v2) /\\ cert-quorum(r1) /\\ ~K_v2 cert-quorum(r1))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f V2_starved,
                Formula.And
                  ( f Cert_quorum_r1,
                    Formula.Not (Formula.K (Validator.V2, f Cert_quorum_r1)) )
              ))))

(** The collision partner (operand-FALSE side): an end-[Vote R1] state where
    no certificate has yet formed - the victim's dag is empty (starved) and
    [cert_quorum(R1)] is false. Its local view is bit-identical to the
    false witness above, which is exactly why V2's ignorance is grounded. *)
let no_cert_collision_partner () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (starved(v2) /\\ ~cert-quorum(r1))" true
        (Checker.satisfiable sys
           (Formula.And (f V2_starved, Formula.Not (f Cert_quorum_r1)))))

(** The negated operand does not collapse to falsehood: in the
    [Deliver_all] branch the delivered R1 quorum makes
    [K_v2 cert_quorum(R1)] hold (V2's own dag witnesses the union quorum),
    so the ignorance clause's [~K] is contingent, not trivially true
    everywhere. *)
let knowledge_attainable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF K_v2 cert-quorum(r1)" true
        (Checker.satisfiable sys (Formula.K (Validator.V2, f Cert_quorum_r1))))

(** The pending-targets gate, no-op side: the totally starved branch
    reaches [Done] still starved - the timeout Kick fetched nothing for a
    validator with an empty targets map (certificate_fetcher.rs:184).
    This pins the gate itself: the ungated model healed every branch and
    this formula was unsatisfiable there. *)
let starve_gate_noop () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (done /\\ starved(v2))" true
        (Checker.satisfiable sys (Formula.And (f At_done, f V2_starved))))

(** The pending-targets gate, service side: the lagged branch ends with
    the victim holding the fetched R1 quorum while still uncommitted -
    recovery came from the timeout fetch, not from a commit. *)
let lag_gate_served () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (done /\\ own-quorum(v2,r1) /\\ ~committed(v2))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f At_done,
                Formula.And (f V2_holds_r1_quorum, Formula.Not (f V2_committed))
              ))))

let () =
  Alcotest.run "stall"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Stall_statements.name `Quick (prove_one st))
          Stall_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "terminal-reached" `Quick terminal_reached;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-contingent" `Quick k_contingent;
          Alcotest.test_case "false-witness-starved" `Quick
            false_witness_starved;
          Alcotest.test_case "no-cert-collision-partner" `Quick
            no_cert_collision_partner;
          Alcotest.test_case "knowledge-attainable" `Quick knowledge_attainable;
        ] );
      ( "pending-targets gate",
        [
          Alcotest.test_case "starve-gate-noop" `Quick starve_gate_noop;
          Alcotest.test_case "lag-gate-served" `Quick lag_gate_served;
        ] );
    ]
