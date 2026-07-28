(** Proofs, sanity and contingency for the WORKER_STREAM_QUOTA family: the
    worker's shared batch-stream budget, the combined per-peer in-flight cap,
    the pending -> serving handoff and the sync path's read-nothing load shed
    ({!Worker_stream_quota_model}).

    - [proofs]: every statement certifies on the pristine model through
      [prove_nonvacuous], so none of them rides on an unreachable antecedent.
    - [sanity]: the reachable set is bounded as stated, and each invariant the
      gates enforce is checked in its refutation form - the forbidden state is
      [satisfiable = false] - while the states the statements are ABOUT are
      shown reachable, so nothing here is green by emptiness.
    - [contingency]: discharges R2 and R3 for every knowledge conjunct of S3.
      Each positive [K] is shown contingent (its negation is satisfiable) AND
      shown to have a non-singleton view class at its operative state, by
      asking whether the victim can fail to know something FALSE where it
      stands - only another reachable state sharing its view can make that
      true. Each ignorance conjunct gets the concrete witness pair. *)

open Telcoin_epistemic
open Worker_stream_quota_model

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
        (st.Worker_stream_quota_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Worker_stream_quota_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Worker_stream_quota_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** Assert that a formula holds at some reachable state. *)
let sat_case msg formula () =
  with_sys (fun sys ->
      Alcotest.(check bool) msg true (Checker.satisfiable sys formula))

(** Assert that a formula holds at NO reachable state. *)
let unsat_case msg formula () =
  with_sys (fun sys ->
      Alcotest.(check bool) msg false (Checker.satisfiable sys formula))

(** The reachable set is small, as R6 requires. The universe is the four
    counters with [pend + serv + ghost + sync <= pool_cap] (35 tuples) times
    the five {!att} constructors, i.e. 175; the pristine reachable count is
    exactly 45. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        ("pristine reachable count is 45, bounded by 48; got "
        ^ Int.to_string (Checker.reachable_count sys))
        true
        (Checker.reachable_count sys <= 48))

(** The victim's knowledge that the responder never decoded its request frame
    is CONTINGENT: at an admitted exchange the responder has read it
    (network/mod.rs:728-739), so the [K] fails there. *)
let read_knowledge_contingent =
  sat_case "K_V2(~read_request) fails somewhere reachable"
    (Formula.Not
       (Formula.K (Validator.V2, Formula.Not (f Resp_read_v2_request))))

(** The victim's knowledge that the pool is exhausted is CONTINGENT: at a
    lightly loaded responder it does not hold. *)
let pool_knowledge_contingent =
  sat_case "K_V2(pool_exhausted) fails somewhere reachable"
    (Formula.Not (Formula.K (Validator.V2, f Pool_exhausted)))

(** R2 for S3's first [K]: at a denied state where the flooder is serving
    NOTHING, the victim still does not know the flooder is serving nothing.
    That is only possible if another reachable state shares the victim's view
    and has the flooder serving - i.e. the view class is not a singleton. *)
let read_class_not_singleton =
  sat_case "S3a operative view class holds >= 2 reachable states"
    (Formula.conj
       [
         f V2_denied;
         Formula.Not (f V1_serving_any);
         Formula.Not (Formula.K (Validator.V2, Formula.Not (f V1_serving_any)));
       ])

(** R2 for S3's second [K]: the same probe at that [K]'s own operative states,
    the denials suffered while the victim is UNDER its per-peer cap. *)
let pool_class_not_singleton =
  sat_case "S3b operative view class holds >= 2 reachable states"
    (Formula.conj
       [
         f V2_denied;
         Formula.Not (f V2_at_own_cap);
         Formula.Not (f V1_serving_any);
         Formula.Not (Formula.K (Validator.V2, Formula.Not (f V1_serving_any)));
       ])

(** R3, witness one: the victim is at its own per-peer cap, is denied, and the
    global pool IS exhausted - the [try_admit_sync] refusal could have come
    from [semaphore.try_acquire_owned] (network/mod.rs:235). *)
let ignorance_witness_exhausted =
  sat_case "denied at own cap with the pool exhausted is reachable"
    (Formula.conj [ f V2_denied; f V2_at_own_cap; f Pool_exhausted ])

(** R3, witness two: same victim, same [Deny(AtCapacity)] frame, same
    [View_requester] value - but the pool is NOT exhausted and the refusal came
    from the per-peer branch (network/mod.rs:239-243). The pair is why the
    victim cannot tell the causes apart. *)
let ignorance_witness_not_exhausted =
  sat_case "denied at own cap with the pool NOT exhausted is reachable"
    (Formula.conj
       [ f V2_denied; f V2_at_own_cap; Formula.Not (f Pool_exhausted) ])

let () =
  Alcotest.run "worker_stream_quota"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Worker_stream_quota_statements.name `Quick
              (prove_one st))
          Worker_stream_quota_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "flooder-never-over-per-peer-cap" `Quick
            (unsat_case "no state has the flooder above MAX_PENDING_REQUESTS_PER_PEER"
               (f V1_over_peer_cap));
          Alcotest.test_case "victim-never-over-per-peer-cap" `Quick
            (unsat_case "no state has the victim above MAX_PENDING_REQUESTS_PER_PEER"
               (f V2_over_peer_cap));
          Alcotest.test_case "no-uncounted-serve" `Quick
            (unsat_case
               "the pending -> serving handoff never drops a peer's tally"
               (f V1_uncounted_serve));
          Alcotest.test_case "no-rearm-while-serving-at-cap" `Quick
            (unsat_case
               "a peer serving at the cap never also holds a pending slot"
               (Formula.And (f V1_serving_at_cap, f V1_pending_any)));
          Alcotest.test_case "idle-victim-never-denied" `Quick
            (unsat_case
               "a requester holding nothing is never shed by a two-peer pool"
               (Formula.And (f V2_denied, f V2_idle_at_r)));
          Alcotest.test_case "pool-exhaustion-reachable" `Quick
            (sat_case "the responder's pool does fill up" (f Pool_exhausted));
          Alcotest.test_case "shed-reachable" `Quick
            (sat_case "the sync shed arm is reachable" (f V2_denied));
          Alcotest.test_case "serve-reachable" `Quick
            (sat_case "the sync serve arm is reachable" (f V2_served));
          Alcotest.test_case "stream-open-reachable" `Quick
            (sat_case "the admission decision point is reachable"
               (f V2_attempt_open));
        ] );
      ( "contingency",
        [
          Alcotest.test_case "read-knowledge-contingent" `Quick
            read_knowledge_contingent;
          Alcotest.test_case "read-class-not-singleton" `Quick
            read_class_not_singleton;
          Alcotest.test_case "pool-knowledge-contingent" `Quick
            pool_knowledge_contingent;
          Alcotest.test_case "pool-class-not-singleton" `Quick
            pool_class_not_singleton;
          Alcotest.test_case "ignorance-witness-exhausted" `Quick
            ignorance_witness_exhausted;
          Alcotest.test_case "ignorance-witness-not-exhausted" `Quick
            ignorance_witness_not_exhausted;
        ] );
    ]
