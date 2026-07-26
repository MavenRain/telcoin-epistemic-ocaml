(** The DISCOVERY family (kad GET fold, inbound-PUT freshness gate,
    peer-exchange identity boundary) proves on the pristine
    {!Discovery_model} through [prove_nonvacuous] (so every antecedent is also
    checked reachable), the reachable graph stays in its justified band, the
    four states the gates forbid are unreachable, and the epistemic layer is
    genuinely partial-information.

    The family has EXACTLY ONE positive knowledge conjunct - [knows_newer],
    AG( query_got_r1 -> K_V0(newer_record_exists) ) in the query statement - so
    R2 is discharged twice for it here: a contingency test (the knowledge did
    not collapse into plain truth) and a NON-SINGLETON VIEW CLASS probe (at the
    operative state V0's class provably holds a second world). Every [~K]
    conjunct in the family gets its own ignorance witness (R3), each naming the
    concrete colliding pair of reachable states in a comment.

    Two faithfulness guards (R5) assert that a modelled branch which could have
    made a statement true by omission is LIVE: [px_repair_path_is_live] for the
    px statement, and [stale_put_regresses_cache_when_store_absent] for the
    inbound-PUT statement - the latter is the branch in which
    [is_newer_record]'s "not found -> true" arm (consensus.rs:1968-1971) lets a
    relayed OLDER record regress [known_peers(A)], which is exactly why that
    statement's non-regression conjunct is guarded by [kad_store_fresh]. *)

open Telcoin_epistemic
open Discovery_model

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
        (st.Discovery_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Discovery_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Discovery_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 3 worlds x 3 cache values x 32 episode shapes
   (query 2x3x2 = 12, put 3x2x2 = 12, px 2x2x2 = 8) = 288. The pristine
   reachable set is exactly 35 - 16 query states (4 in the no-newer-record
   world, 6 in each of the two newer-record worlds), 10 inbound-PUT states (each
   newer-record world with each of the two local-store states, plus the stale
   and invalid successors), 9 px states - because the episodes are a disjoint
   union rather than a product and each is acyclic. Only [No_query_max_fold]
   grows it, to 39. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 288))

(* The strict-max fold (consensus.rs:1993-1999) forbids "a response carrying the
   newer record arrived, yet KadQuery.result still tracks the older one".
   [No_query_max_fold] makes exactly this state reachable. *)
let received_newer_never_tracks_older () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (query_got_r1 /\\ query_result=r0)" false
        (Checker.satisfiable sys
           (Formula.And (f Query_got_r1, f Query_result_r0))))

(* The [is_newer_record] gate (consensus.rs:1916) forbids "a stale relayed
   record was processed WHILE THE LOCAL KAD STORE STILL HELD A RECORD FOR A'S
   KEY, and the cached endpoint is no longer the newer one".
   [No_put_freshness_gate] makes exactly this state reachable. The store guard
   is load-bearing: see [stale_put_regresses_cache_when_store_absent] below for
   the branch in which the very same conditional lets the regression through. *)
let stale_put_with_fresh_store_never_regresses_cache () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (put_stale_processed /\\ kad_store_fresh /\\ ~known_peers(A)=r1)"
        false
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Put_stale_processed, f Kad_store_fresh),
                Formula.Not (f Cache_r1) ))))

(* Faithfulness guard (R5) for [no_regression_while_store_fresh]: the branch the
   guard carves out is LIVE in the pristine model, so the conjunct is scoped
   rather than true by omission. [is_newer_record] reads the local kad record
   store (consensus.rs:1955-1957) and returns TRUE when the key is absent
   (:1968-1971), and neither the GET route (consensus.rs:1744-1755, :2015-2024)
   nor the startup restore (consensus.rs:438-439 -> manager.rs:771-774) ever
   writes that store - so a [known_peers(A)=r1] learned either way sits next to
   an empty store, the relayed OLDER record is stored (:1917-1922) and cached
   through the not-source-gated committee branch (manager.rs:820-821, :868), and
   [known_peers(A)] regresses to r0 on the PRISTINE model. *)
let stale_put_regresses_cache_when_store_absent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (put_stale_processed /\\ ~kad_store_fresh /\\ ~known_peers(A)=r1)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Put_stale_processed, Formula.Not (f Kad_store_fresh)),
                Formula.Not (f Cache_r1) ))))

(* The deliberate no-penalty carve-out (consensus.rs:1932-1937) forbids "a Fatal
   was assessed against a source that did not deviate" on this route.
   [Penalize_stale_record] makes exactly this state reachable, in the honest
   restarted-replicator world. *)
let no_penalty_without_deviation () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (put_source_penalized /\\ ~source_deviated)"
        false
        (Checker.satisfiable sys
           (Formula.And (f Put_source_penalized, Formula.Not (f Source_deviated)))))

(* Non-vacuity guard for [attribution_sound]: its antecedent must actually be
   reachable, or "a Fatal implies the source deviated" would hold for free. It
   is - the invalid-record branch (consensus.rs:1938-1944) fires at
   {N_replayer; C_r1; Ep_put{P_invalid; penalized=true}}. That state's V0-view
   class IS a singleton (only the deviating world can produce a
   signature-invalid record), which is precisely why the attributability
   contrast is carried NON-epistemically by [attribution_sound] rather than by a
   collapsed K_V0(source_deviated) there. *)
let fatal_penalty_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF put_source_penalized" true
        (Checker.satisfiable sys (f Put_source_penalized)))

(* The BLS-key discard in [process_peer_exchange] (manager.rs:624) forbids "a
   bls<->peer_id binding exists without any signature-validated record from that
   endpoint". [Px_binds_identity] makes exactly this state reachable. *)
let no_identity_without_signed_record () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (px_identity_bound /\\ ~signed_record_seen)"
        false
        (Checker.satisfiable sys
           (Formula.And (f Px_identity_bound, Formula.Not (f Signed_record_seen)))))

(* R2, part 1 - the family's ONLY positive knowledge conjunct,
   K_V0(newer_record_exists) in [knows_newer], is CONTINGENT: its complement is
   reachable, so the operand is not plain truth under the view partition. The
   witness is any of the four reachable no-newer-record query states, e.g.
   {N_current; C_none; Ep_query{false; Q_none; Q_open}}, whose V0-view class
   also holds the [N_lagging] and [N_replayer] worlds. *)
let k_newer_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v0(newer_record_exists): knowledge did not collapse"
        true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f Newer_record_exists)))))

(* R2, part 2 - the NON-SINGLETON VIEW CLASS probe for that same positive K.
   At the operative state w1 = {N_lagging; C_none; Ep_query{got_r1=true;
   res=Q_r1; phase=Q_open}} the atom [source_deviated] is FALSE, yet V0 cannot
   rule it out - which is only possible if V0's view class at w1 holds a second
   reachable world. It does: w2 = the byte-identical observable state with
   nature = [N_replayer]. Both satisfy [newer_record_exists], which is why
   [knows_newer] still holds there; they disagree on [source_deviated], which is
   what this probe detects. So K_V0(newer_record_exists) is NOT trivially true
   on a singleton class. *)
let k_newer_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (query_got_r1 /\\ ~source_deviated /\\ ~K_v0(~source_deviated))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Query_got_r1,
                Formula.And
                  ( Formula.Not (f Source_deviated),
                    Formula.Not
                      (Formula.K (Validator.V0, Formula.Not (f Source_deviated)))
                  ) ))))

(* R3 for [currency_unknown]'s first ~K. Ignorance pair, both reachable, sharing
   V0's view (cache = C_r0, ep = Ep_query{false; Q_r0; Q_closed}): u1 =
   {N_current; ...} - the adopted record IS A's current one - and u2 =
   {N_lagging; ...} - A published a newer record and only stale responders
   answered. So having adopted r0, V0 cannot RULE OUT that a newer record
   exists. *)
let ignorance_currency_cannot_exclude_newer () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (closed /\\ result=r0 /\\ ~got_r1 /\\ ~K_v0(~newer_record_exists))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.conj
                  [
                    f Query_closed;
                    f Query_result_r0;
                    Formula.Not (f Query_got_r1);
                  ],
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Newer_record_exists)))
              ))))

(* R3 for [currency_unknown]'s second ~K - the same u1/u2 pair read the other
   way: V0 cannot CONFIRM that a newer record exists either, because u1 (the
   no-newer-record world) is in the class. Together the two tests are the
   "neither confirm nor rule out" content of the statement. *)
let ignorance_currency_cannot_confirm_newer () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (closed /\\ result=r0 /\\ ~got_r1 /\\ ~K_v0(newer_record_exists))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.conj
                  [
                    f Query_closed;
                    f Query_result_r0;
                    Formula.Not (f Query_got_r1);
                  ],
                Formula.Not (Formula.K (Validator.V0, f Newer_record_exists)) ))))

(* R3 for [replay_unattributable]'s first ~K. Ignorance pair, both reachable,
   byte-identical V0 view (cache = C_r1, ep = Ep_put{P_stale; St_fresh;
   penalized=false}; the [St_absent] half at cache = C_r0 is a second such
   pair):
   b1 = {N_lagging; ...} - S is an honest node that restarted from a persisted
   store holding only r0, or is running kad's periodic replication of a record
   it did not publish (kad.rs:339-379) - and b2 = {N_replayer; ...} - S holds r1
   and replays r0 to keep V0 on the old endpoint. At b2 the source really DID
   deviate, yet V0 cannot know it. *)
let ignorance_replay_cannot_confirm_deviation () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (put_stale_processed /\\ source_deviated /\\ ~K_v0(source_deviated))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Put_stale_processed,
                Formula.And
                  ( f Source_deviated,
                    Formula.Not (Formula.K (Validator.V0, f Source_deviated)) )
              ))))

(* R3 for [replay_unattributable]'s second ~K - the same b1/b2 pair read the
   other way: at b1 the source is honest, yet V0 cannot rule out deviation
   either. This is why the code's restraint (no penalty on the stale branch)
   cannot be replaced by detection. *)
let ignorance_replay_cannot_exclude_deviation () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (put_stale_processed /\\ ~source_deviated /\\ ~K_v0(~source_deviated))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Put_stale_processed,
                Formula.And
                  ( Formula.Not (f Source_deviated),
                    Formula.Not
                      (Formula.K (Validator.V0, Formula.Not (f Source_deviated)))
                  ) ))))

(* R3 for [sybil_unknown]'s first ~K. Ignorance triple sharing V0's view
   (cache = C_none, ep = Ep_px{hinted=true; signed_seen=false; bound=false}):
   c1 = {N_current} and c2 = {N_lagging} - the sender is honest and listed
   genuine connected peers from its own store ([peers_for_exchange] ->
   [AllPeers::peer_exchange], manager.rs:655-657) - and c3 = {N_replayer} - the
   sender listed endpoints it controls. All three reachable, so V0 cannot
   confirm the endpoints are sybils. *)
let ignorance_sybil_cannot_confirm_deviation () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (px_hints_ingested /\\ ~K_v0(source_deviated))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Px_hints_ingested,
                Formula.Not (Formula.K (Validator.V0, f Source_deviated)) ))))

(* R3 for [sybil_unknown]'s second ~K - the same c1/c2/c3 triple read the other
   way: V0 cannot rule the sybils out either, because c3 shares the view. *)
let ignorance_sybil_cannot_exclude_deviation () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (px_hints_ingested /\\ ~K_v0(~source_deviated))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Px_hints_ingested,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Source_deviated))) ))))

(* R3 for [binding_is_not_distinctness]'s ~K. The same three-world class
   survives to the POST-confirmation state ep = Ep_px{true; true; true}: even
   after the hinted endpoint dialed, connected and pushed its own signed record,
   V0 still cannot rule out that it is a sybil the sender controls - a sybil
   owns its own keys, so key ownership is orthogonal to distinctness. *)
let ignorance_binding_is_not_distinctness () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (px_hints_ingested /\\ px_identity_bound /\\ ~K_v0(~source_deviated))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Px_hints_ingested,
                Formula.And
                  ( f Px_identity_bound,
                    Formula.Not
                      (Formula.K (Validator.V0, Formula.Not (f Source_deviated)))
                  ) ))))

(* Faithfulness guard (R5) for the px statement: the modelled REPAIR path is
   live, so [identity_needs_signature] is not true merely because the model
   omits the way a px-hinted endpoint acquires an identity. A binding IS
   reachable - just only ever together with a signature-validated record from
   that endpoint. *)
let px_repair_path_is_live () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (px_identity_bound /\\ signed_record_seen)" true
        (Checker.satisfiable sys
           (Formula.And (f Px_identity_bound, f Signed_record_seen))))

let () =
  Alcotest.run "discovery"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Discovery_statements.name `Quick
              (prove_one st))
          Discovery_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "received-newer-never-tracks-older" `Quick
            received_newer_never_tracks_older;
          Alcotest.test_case "stale-put-with-fresh-store-never-regresses-cache"
            `Quick stale_put_with_fresh_store_never_regresses_cache;
          Alcotest.test_case "no-penalty-without-deviation" `Quick
            no_penalty_without_deviation;
          Alcotest.test_case "fatal-penalty-is-reachable" `Quick
            fatal_penalty_is_reachable;
          Alcotest.test_case "no-identity-without-signed-record" `Quick
            no_identity_without_signed_record;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-newer-contingent" `Quick k_newer_contingent;
          Alcotest.test_case "k-newer-class-not-singleton" `Quick
            k_newer_class_not_singleton;
          Alcotest.test_case "ignorance-currency-cannot-exclude-newer" `Quick
            ignorance_currency_cannot_exclude_newer;
          Alcotest.test_case "ignorance-currency-cannot-confirm-newer" `Quick
            ignorance_currency_cannot_confirm_newer;
          Alcotest.test_case "ignorance-replay-cannot-confirm-deviation" `Quick
            ignorance_replay_cannot_confirm_deviation;
          Alcotest.test_case "ignorance-replay-cannot-exclude-deviation" `Quick
            ignorance_replay_cannot_exclude_deviation;
          Alcotest.test_case "ignorance-sybil-cannot-confirm-deviation" `Quick
            ignorance_sybil_cannot_confirm_deviation;
          Alcotest.test_case "ignorance-sybil-cannot-exclude-deviation" `Quick
            ignorance_sybil_cannot_exclude_deviation;
          Alcotest.test_case "ignorance-binding-is-not-distinctness" `Quick
            ignorance_binding_is_not_distinctness;
          Alcotest.test_case "stale-put-regresses-cache-when-store-absent"
            `Quick stale_put_regresses_cache_when_store_absent;
          Alcotest.test_case "px-repair-path-is-live" `Quick
            px_repair_path_is_live;
        ] );
    ]
