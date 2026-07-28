(** The RECORD_SERVE_POOL family (S1, S2, S3) proves on the pristine
    {!Record_serve_pool_model} through [prove_nonvacuous] (so each antecedent is
    also checked reachable), the reachable graph stays in its justified band,
    the two states the admission gate forbids - occupancy above the pool cap and
    any requester above the per-peer cap - are unreachable, and the epistemic
    layer is genuinely partial-information: the single positive knowledge
    operand is contingent AND its view class is provably not a singleton, and
    every ignorance conjunct has a reachable witness. *)

open Telcoin_epistemic
open Record_serve_pool_model

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
        (st.Record_serve_pool_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Record_serve_pool_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Record_serve_pool_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 10 canonical load tables (multisets of three counts in
   0..2) x 10 probe values (idle, shed x 3 selectors, serve x 3 selectors, done
   x 2 outcomes) = 100. The pristine reachable set is exactly 52: 9 idle tables
   (all multisets with total <= 5, i.e. all ten but (2,2,2)), 3 shed states (the
   probe is shed only from the one full table (1,2,2), once per selector), 24
   serve states (the 8 tables with total <= 4, once per selector) and 16 done
   states (those same 8 tables, once per outcome). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 100))

(* The exact pristine reachable count, pinned so a modelling drift that widens
   or narrows the graph cannot slip through as a still-green proof. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "exact pristine reachable count" 52
        (Checker.reachable_count sys))

(* The global semaphore's contract: occupancy never exceeds
   MAX_CONCURRENT_EPOCH_RECORD_REQUESTS = 5 (network/mod.rs:72-81, taken at
   :356). This is the state No_record_admission_gate makes reachable. *)
let over_cap_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (occupancy > 5)" false
        (Checker.satisfiable sys (f Pool_over_cap)))

(* The per-peer gate's contract: no requester ever holds more than
   MAX_PENDING_REQUESTS_PER_PEER = 2 concurrent serves (network/mod.rs:359).
   This is the state No_per_peer_record_cap makes reachable. *)
let per_peer_cap_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (some requester holds > 2)" false
        (Checker.satisfiable sys (f Requester_over_cap)))

(* S1's whole content as a reachability fact: a monopolised exhausted pool -
   occupancy 5 concentrated in fewer than three distinct requesters - does not
   exist in the pristine graph. *)
let monopolised_exhaustion_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (occupancy = 5 /\\ holders < 3)" false
        (Checker.satisfiable sys
           (Formula.And
              (f Pool_exhausted, Formula.Not (f Three_distinct_holders)))))

(* The only positive knowledge operand in the family is K_V1(admitted(P)) in S2
   conjunct D: assert its complement is reachable, so the knowledge is
   contingent and did not collapse into plain truth under the view partition.
   It fails at every idle and every shed state. *)
let k_admitted_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1(admitted(P)): knowledge did not collapse"
        true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Probe_admitted)))))

(* R2 non-singleton evidence for that same positive K. At a replied state pick
   an atom FALSE there - distinct_holders >= 3 - and assert V1 does not know its
   negation. That is only possible if another reachable state shares V1's view
   (Pv_replied out, which carries no component of the responder's slot table)
   and satisfies it, i.e. the view class is NOT a singleton: it contains every
   table the serve could have been admitted from. *)
let k_admitted_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (replied /\\ ~3holders /\\ ~K_v1(~3holders)): view class > 1" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Probe_replied,
                Formula.And
                  ( Formula.Not (f Three_distinct_holders),
                    Formula.Not
                      (Formula.K
                         (Validator.V1, Formula.Not (f Three_distinct_holders)))
                  ) ))))

(* S2 conjunct B's ignorance witness: the probe is shed - its response channel
   dropped at network/mod.rs:1612 - and cannot know it, because the shed state
   and the running-serve states share V1's view exactly. *)
let ignorance_witness_shed () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (shed(P) /\\ ~K_v1 shed(P))" true
        (Checker.satisfiable sys
           (Formula.And
              (f Probe_shed, Formula.Not (Formula.K (Validator.V1, f Probe_shed))))))

(* S2 conjunct C's ignorance witness, the dual: the probe IS being served and
   cannot know that either - the same view value covers the shed branch. *)
let ignorance_witness_serving () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (serving(P) /\\ ~K_v1 serving(P))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Probe_serving,
                Formula.Not (Formula.K (Validator.V1, f Probe_serving)) ))))

(* S3 conjunct D's ignorance witness, positive direction: the responder is
   serving an unaddressed request it is about to charge Medium and cannot
   confirm the requester is a griefer - the doc-conformant sibling state at the
   same slot table shares V0's view. *)
let ignorance_witness_deviant () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (serving_unaddressed /\\ ~K_v0 deviant_request)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Serve_unaddressed,
                Formula.Not (Formula.K (Validator.V0, f Serving_deviant)) ))))

(* S3 conjunct D's ignorance witness, negative direction: nor can the responder
   RULE OUT that it is scoring down a client written to the request type's own
   documented contract (network/message.rs:73-74). *)
let ignorance_witness_not_deviant () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (serving_unaddressed /\\ ~K_v0 ~deviant_request)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Serve_unaddressed,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Serving_deviant))) ))))

let () =
  Alcotest.run "record_serve_pool"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Record_serve_pool_statements.name `Quick
              (prove_one st))
          Record_serve_pool_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "over-cap-unreachable" `Quick over_cap_unreachable;
          Alcotest.test_case "per-peer-cap-unreachable" `Quick
            per_peer_cap_unreachable;
          Alcotest.test_case "monopolised-exhaustion-unreachable" `Quick
            monopolised_exhaustion_unreachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-admitted-contingent" `Quick k_admitted_contingent;
          Alcotest.test_case "k-admitted-class-not-singleton" `Quick
            k_admitted_class_not_singleton;
          Alcotest.test_case "ignorance-witness-shed" `Quick
            ignorance_witness_shed;
          Alcotest.test_case "ignorance-witness-serving" `Quick
            ignorance_witness_serving;
          Alcotest.test_case "ignorance-witness-deviant" `Quick
            ignorance_witness_deviant;
          Alcotest.test_case "ignorance-witness-not-deviant" `Quick
            ignorance_witness_not_deviant;
        ] );
    ]
