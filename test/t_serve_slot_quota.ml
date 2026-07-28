(** The SERVE_SLOT_QUOTA family (S1, S2, S3) proves on the pristine
    {!Serve_slot_quota_model} through [prove_nonvacuous] (so each antecedent is
    also checked reachable), the reachable graph stays in its justified band and
    at its exact pinned size, the two states the per-peer stream gates forbid -
    a peer above [MAX_PENDING_REQUESTS_PER_PEER] and a monopolised exhausted
    pool - are unreachable, and the epistemic layer is genuinely
    partial-information: the family's single positive knowledge operand is
    contingent AND its view class is provably not a singleton, and both
    ignorance conjuncts have reachable witnesses. *)

open Telcoin_epistemic
open Serve_slot_quota_model

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
        (st.Serve_slot_quota_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Serve_slot_quota_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Serve_slot_quota_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 5 flooder splits under the union cap ((0,0), (1,0),
   (2,0), (0,1), (1,1)) x 3 values of T's count x 3 values of Q's stream outcome
   x 2 values of Q's record outcome = 90 before the three-permit pool constraint
   is applied. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 90))

(* The exact pristine reachable count, pinned so a modelling drift that widens
   or narrows the graph cannot slip through as a still-green proof. It is 2 (Q's
   record outcome) x 26 stream configurations: 13 with Q's stream request
   unsent (flooder+third totals under the 3-permit pool), 4 with Q denied (only
   the exhausted configurations (1,2), (0+1,2), (2,1), (1+1,1) can deny) and 9
   with Q admitted (the configurations leaving room for Q's own permit). *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "exact pristine reachable count" 52
        (Checker.reachable_count sys))

(* The per-peer gates' contract: no peer's legacy entries plus sync streams ever
   exceed MAX_PENDING_REQUESTS_PER_PEER = 2 (network/mod.rs:102-105, enforced at
   :337 and :1667-1676). This is the state both stream mutations make
   reachable. *)
let per_peer_cap_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (some peer holds > 2 stream slots)" false
        (Checker.satisfiable sys (f Peer_over_stream_cap)))

(* S2 conjunct B's whole content as a reachability fact: an exhausted stream
   pool concentrated in a single other peer - the monopoly the cap exists to
   forbid - does not exist in the pristine graph. *)
let monopolised_exhaustion_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (pool full /\\ Q holds nothing /\\ fewer than two holders)"
        false
        (Checker.satisfiable sys
           (Formula.And
              ( f Stream_pool_full,
                Formula.And
                  ( Formula.Not (f Q_holds_stream_slot),
                    Formula.Not (f Two_stream_holders) ) ))))

(* The stream class really does refuse someone: without a reachable denial S3
   would be vacuous rather than proved. *)
let denial_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF denied_at_capacity(Q)" true
        (Checker.satisfiable sys (f Q_stream_denied)))

(* The only positive knowledge operand in the family is S3 conjunct A's
   K_V2(distinct_other_stream_holders >= 2): assert its complement is reachable,
   so the knowledge is contingent and did not collapse into plain truth under
   the view partition. It fails at every state in which Q has not yet been
   denied. *)
let k_denial_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v2(two other holders): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V2, f Two_stream_holders)))))

(* R2 non-singleton evidence for that same positive K. At a denied state pick an
   atom FALSE there - stream_inflight(P) = 2 - and assert V2 does not know its
   negation. That is only possible if another reachable state shares V2's view
   (View_honest (Qs_denied, _), which carries no component of the responder's
   counters) and satisfies it, i.e. the view class is NOT a singleton: it
   contains both ways three permits can be split between P and T. *)
let k_denial_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (denied /\\ ~at_cap(P) /\\ ~K_v2(~at_cap(P))): view class > 1" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Q_stream_denied,
                Formula.And
                  ( Formula.Not (f Flooder_at_cap),
                    Formula.Not
                      (Formula.K (Validator.V2, Formula.Not (f Flooder_at_cap)))
                  ) ))))

(* S3 conjunct B's ignorance witness: the denial reveals an aggregate, never a
   distribution, because the (1, 2) and (2, 1) splits of the exhausted pool are
   the same value of V2's view. *)
let ignorance_witness_distribution () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (denied(Q) /\\ ~K_v2 at_cap(P))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Q_stream_denied,
                Formula.Not (Formula.K (Validator.V2, f Flooder_at_cap)) ))))

(* S1 conjunct B's ignorance witness, in its pointed form: the stream pool IS
   exhausted, Q's epoch-record request has been answered out of the other
   budget, and Q cannot tell - the record admission never consults the stream
   semaphore (network/mod.rs:351-363). *)
let ignorance_witness_record_answer () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (record served /\\ no stream request /\\ pool full /\\ ~K_v2 full)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Q_record_served,
                Formula.And
                  ( f Q_stream_unsent,
                    Formula.And
                      ( f Stream_pool_full,
                        Formula.Not
                          (Formula.K (Validator.V2, f Stream_pool_full)) ) ) ))))

(* The dual direction of the same ignorance: a served record request does not
   let Q rule the exhaustion OUT either, so conjunct B is a genuine two-sided
   blindness and not an artefact of one witness. *)
let ignorance_witness_record_answer_dual () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (record served /\\ no stream request /\\ ~K_v2 ~full)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Q_record_served,
                Formula.And
                  ( f Q_stream_unsent,
                    Formula.Not
                      (Formula.K
                         (Validator.V2, Formula.Not (f Stream_pool_full))) ) ))))

let () =
  Alcotest.run "serve_slot_quota"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Serve_slot_quota_statements.name `Quick
              (prove_one st))
          Serve_slot_quota_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "per-peer-cap-unreachable" `Quick
            per_peer_cap_unreachable;
          Alcotest.test_case "monopolised-exhaustion-unreachable" `Quick
            monopolised_exhaustion_unreachable;
          Alcotest.test_case "denial-reachable" `Quick denial_reachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-denial-contingent" `Quick k_denial_contingent;
          Alcotest.test_case "k-denial-class-not-singleton" `Quick
            k_denial_class_not_singleton;
          Alcotest.test_case "ignorance-witness-distribution" `Quick
            ignorance_witness_distribution;
          Alcotest.test_case "ignorance-witness-record-answer" `Quick
            ignorance_witness_record_answer;
          Alcotest.test_case "ignorance-witness-record-answer-dual" `Quick
            ignorance_witness_record_answer_dual;
        ] );
    ]
