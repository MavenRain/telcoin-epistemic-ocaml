(** The BACKEND_ENV_SPLIT family (S1, S2, S3) proves on the pristine
    {!Backend_env_split_model} through [prove_nonvacuous] (so every antecedent is
    also checked reachable), the reachable graph stays in its justified band, the
    invariants the modelled gates enforce are genuinely unreachable-when-
    forbidden, and the epistemic layer is partial-information rather than
    collapsed.

    The contingency group is where R2 and R3 are discharged. The family has
    exactly ONE positive knowledge conjunct - [K_V1(index_cleared_durable)] in S2
    conjunct D - so it carries both required R2 tests (operand contingency and a
    non-singleton view class), and one R3 ignorance witness per [~K] conjunct
    (S1-C, S1-D, S2-E).

    The group also carries four HONESTY tests that the contract does not demand
    but the family's own claims do. [positive_k_is_actually_realised] proves the
    operative state of S2-D exists at all, so the positive K is a live inference
    and not an empty implication. [co_tenancy_window_is_reachable] proves that a
    Cache-hint logical txn really can be open while the epoch commit is queued -
    the exact state the merge mutation turns into a deferral, so S1-A is about a
    reachable configuration rather than an impossible one.
    [split_tears_in_both_directions] proves the cross-environment tear is
    reachable with the CACHE side durable and the epoch side not, which is what
    makes the split's independence a symmetric fact rather than an ordering.
    [ungrouped_route_reaches_durability] proves the boundary's own route gets
    both epoch tables to disk on some path, so S2 conjunct C's tear is one
    interleaving among several rather than the only outcome. *)

open Telcoin_epistemic
open Backend_env_split_model

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
        (st.Backend_env_split_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Backend_env_split_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Backend_env_split_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: route (3) x ep_stage (5) x ca_stage (5) x six booleans
   x cache_tbl (2) = 4800. The pristine reachable set is exactly 34: one
   route-unchosen initial world, plus the grouped track's 9 live pipeline states
   and 5 post-restart shapes, plus the ungrouped track's 10 live states and 9
   post-restart shapes. The mutants stay in the same band: 32 states under
   Merge_cache_into_epoch_env (the deferral collapses the interleavings that made
   the tear) and 44 under No_redb_table_recreate (the deleted handle and the
   boundary scan fault add states). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 4800))

(* The same-hint grouping invariant (db_run:238-242 applies every Clear into the
   one open physical txn, end_txn:161-164 commits it once): on the grouped route
   no reachable state has the Certificates clear on disk without the round-index
   clear. This is the state the ungrouped route makes reachable, and it is what
   S2 conjunct A asserts as a crash property. *)
let grouped_epoch_clears_never_tear () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (grouped_txn /\\ certs_cleared_durable /\\ \
         ~index_cleared_durable)"
        false
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Route_is_grouped;
                f Certs_cleared_durable;
                Formula.Not (f Index_cleared_durable);
              ])))

(* The redb clear recreates the table inside the same write transaction
   (redb/database.rs:58-63), so the deleted-handle state is unreachable on the
   pristine model. No_redb_table_recreate is exactly what makes it reachable. *)
let cleared_table_handle_always_survives () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF cache_table_absent" false
        (Checker.satisfiable sys (f Cache_table_absent)))

(* And therefore the boundary scan of a Cache-hint table
   (close_epoch.rs:57-63 -> layered_db.rs:423-428 -> redb/database.rs:155-160)
   never reaches its `expect("Missing table, DB not configured/opened
   correctly")`. This is S3 conjunct B stated as a reachability claim. *)
let boundary_scan_never_faults () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF scan_faulted" false
        (Checker.satisfiable sys (f Scan_faulted)))

(* R2, operand contingency for S2 conjunct D. K_V1(index_cleared_durable) is not
   collapsed: there are reachable states at which the certificate-store client
   does NOT know the round index reached disk - every pre-commit state, and every
   ungrouped post-restart state where the first clear committed and the second
   did not (db_run:243-245 runs each as its own backend transaction). *)
let k_v1_index_durability_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1(index_cleared_durable)" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Index_cleared_durable)))))

(* R2, non-singleton view class for S2 conjunct D. At an operative state -
   restarted, grouped route, a certificate read answering empty - pick
   cache_cleared_durable, which is FALSE there on the torn branch, and assert
   that V1 does not know its negation. That can only hold if another reachable
   state shares V1's view and satisfies cache_cleared_durable, i.e. the class is
   not a singleton. It is not: V1's view is (route, certificate read, restarted)
   and carries nothing of the cache environment, so the class spans both sides of
   the cross-environment tear. *)
let s2d_view_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (restarted /\\ grouped_txn /\\ certs_read_empty /\\ \
         ~K_v1(~cache_cleared_durable))"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Restarted;
                f Route_is_grouped;
                f Certs_read_empty;
                Formula.Not
                  (Formula.K
                     (Validator.V1, Formula.Not (f Cache_cleared_durable)));
              ])))

(* R3 ignorance witness for S1 conjunct C. Colliding pair: the grouped state
   with the epoch CommitTxn queued and the Cache-hint clear still staged, versus
   the same pipeline before the cache clear was staged. Both are reachable and
   both project to View_cert_client (Route_grouped, true, false), because the
   only instrument that reports another layer's open_txn_count is
   CompositeDatabase::stats (composite_db.rs:47-54, layered_db.rs:139-147,
   :250-255) and its only callers are that aggregator and the storage crate's own
   unit tests. *)
let cert_client_blind_to_cache_txn () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (epoch_commit_queued /\\ ~K_v1(cache_txn_open))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Epoch_commit_queued,
                Formula.Not (Formula.K (Validator.V1, f Cache_txn_open)) ))))

(* R3 ignorance witness for S1 conjunct D. Colliding pair: the two post-restart
   states with cache_cleared_durable true and certs_cleared_durable false or
   true. Both project to View_cache_client (route, true, true): the cache
   environment is not full-memory (composite_db.rs:35) so the batch-cache client
   does see its OWN clear reach disk (layered_db.rs:383-389, :412-418), and it
   still sees nothing of the epoch environment, which is a different physical
   transaction committed by a different thread. *)
let cache_client_blind_to_epoch_env () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (restarted /\\ cache_cleared_durable /\\ \
         ~K_v2(certs_cleared_durable))"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Restarted;
                f Cache_cleared_durable;
                Formula.Not
                  (Formula.K (Validator.V2, f Certs_cleared_durable));
              ])))

(* R3 ignorance witness for S2 conjunct E. The same colliding pair read from the
   epoch side: two post-restart states agreeing on (route, certificate read,
   restarted) and disagreeing on cache_cleared_durable, which exist because
   CompositeDbTxMut::commit is three sequential sends to three independent
   threads (composite_db.rs:250-261 over layered_db.rs:118-134) and not a
   two-phase commit. *)
let cert_client_blind_to_cache_durability () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (restarted /\\ certs_read_empty /\\ ~K_v1(cache_cleared_durable))"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Restarted;
                f Certs_read_empty;
                Formula.Not
                  (Formula.K (Validator.V1, f Cache_cleared_durable));
              ])))

(* Honesty test for S2 conjunct D. The positive K is realised somewhere: there
   is a reachable post-restart grouped state where the certificate read answers
   empty and V1 therefore DOES know the round index reached disk. Without this
   the conjunct would be an implication with an empty antecedent and would prove
   for the wrong reason. *)
let positive_k_is_actually_realised () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (restarted /\\ grouped_txn /\\ certs_read_empty /\\ \
         K_v1(index_cleared_durable))"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Restarted;
                f Route_is_grouped;
                f Certs_read_empty;
                Formula.K (Validator.V1, f Index_cleared_durable);
              ])))

(* Honesty test for S1 conjunct A. The co-tenancy window is real: a Cache-hint
   logical txn can be open at the very moment the epoch environment's CommitTxn
   is queued. On the split that costs nothing, because the counts are per
   environment (db_run's own `txn` local, layered_db.rs:179); it is precisely
   this state that Merge_cache_into_epoch_env turns into end_txn's deferral
   branch (:170-172). If it were unreachable the conjunct would be vacuous where
   it matters. *)
let co_tenancy_window_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (epoch_commit_queued /\\ cache_txn_open)" true
        (Checker.satisfiable sys
           (Formula.And (f Epoch_commit_queued, f Cache_txn_open))))

(* Honesty test for S2 conjunct B. The cross-environment tear is symmetric: the
   CACHE commit can land while the epoch commit has not. Three independent
   threads mean neither commit order is guaranteed, so stating only the
   epoch-first direction would understate the hole. *)
let split_tears_in_both_directions () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (restarted /\\ grouped_txn /\\ boundary_ran /\\ \
         cache_cleared_durable /\\ ~certs_cleared_durable)"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Restarted;
                f Route_is_grouped;
                f Boundary_ran;
                f Cache_cleared_durable;
                Formula.Not (f Certs_cleared_durable);
              ])))

(* Honesty test for S2 conjunct C. The ungrouped route is not a doomed route:
   there are interleavings in which both Epoch-hint clears reach disk before the
   crash. The tear is one outcome among several, which is what makes it an EF
   claim rather than an AG one. *)
let ungrouped_route_reaches_durability () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (ungrouped_calls /\\ certs_cleared_durable /\\ \
         index_cleared_durable)"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Route_is_ungrouped;
                f Certs_cleared_durable;
                f Index_cleared_durable;
              ])))

let () =
  Alcotest.run "backend_env_split"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Backend_env_split_statements.name `Quick
              (prove_one st))
          Backend_env_split_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "grouped-epoch-clears-never-tear" `Quick
            grouped_epoch_clears_never_tear;
          Alcotest.test_case "cleared-table-handle-always-survives" `Quick
            cleared_table_handle_always_survives;
          Alcotest.test_case "boundary-scan-never-faults" `Quick
            boundary_scan_never_faults;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "s2d-operand-contingent" `Quick
            k_v1_index_durability_is_contingent;
          Alcotest.test_case "s2d-view-class-not-singleton" `Quick
            s2d_view_class_is_not_a_singleton;
          Alcotest.test_case "s1c-ignorance-witness" `Quick
            cert_client_blind_to_cache_txn;
          Alcotest.test_case "s1d-ignorance-witness" `Quick
            cache_client_blind_to_epoch_env;
          Alcotest.test_case "s2e-ignorance-witness" `Quick
            cert_client_blind_to_cache_durability;
          Alcotest.test_case "s2d-positive-k-realised" `Quick
            positive_k_is_actually_realised;
          Alcotest.test_case "s1a-co-tenancy-window-reachable" `Quick
            co_tenancy_window_is_reachable;
          Alcotest.test_case "s2b-tear-is-symmetric" `Quick
            split_tears_in_both_directions;
          Alcotest.test_case "s2c-ungrouped-route-can-succeed" `Quick
            ungrouped_route_reaches_durability;
        ] );
    ]
