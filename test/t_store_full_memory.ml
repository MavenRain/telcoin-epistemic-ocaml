(** The STORE_FULL_MEMORY family (S1, S2, S3) proves on the pristine
    {!Store_full_memory_model} through [prove_nonvacuous] (so each antecedent is
    also checked reachable), the reachable graph stays in its justified band, the
    three invariants the modelled gates enforce are genuinely unreachable-when-
    forbidden, and the epistemic layer is partial-information rather than
    collapsed.

    The contingency group is where R2 and R3 are discharged. The family has
    exactly ONE positive knowledge conjunct - [K_V1(durable(c))] in S1 conjunct B
    - so it carries both required R2 tests (operand contingency and a
    non-singleton view class), and one R3 ignorance witness per [~K] conjunct
    (S1-C, S2-B, S3-B).

    The group also carries three HONESTY tests that the contract does not demand
    but the family's own claims do. [restart_scope_of_s2b_is_load_bearing] proves
    that at a post-restart index hit V1 genuinely DOES know durability, so the
    [~restarted] scope on S2 conjunct B is a live distinction and not a
    convenience. [crash_escape_of_s3a_is_reachable] proves the crash-loss branch
    S3 conjunct A carries as an escape is actually reachable, so the escape is
    honest rather than a decoration - and [queue_window_is_reachable] proves the
    mem-only window both S2 and S3 turn on exists in the model at all. *)

open Telcoin_epistemic
open Store_full_memory_model

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
        (st.Store_full_memory_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Store_full_memory_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Store_full_memory_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: ten independent booleans = 1024. The pristine reachable
   set is exactly 27, the product of an epoch track of 3 pre-restart shapes plus
   2 post-restart shapes with a cache track of 5 pre-restart plus 6 post-restart
   shapes: 3 x 5 + 2 x 6 = 27. The mutants stay in the same band: 27, 27 and 30
   states for No_open_preload, No_full_memory_mode_test and
   No_mem_chain_in_iter respectively. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 1024))

(* The no-eviction invariant (layered_db.rs:311): with mem_db == None the epoch
   DB's writer thread has no eviction channel at all - the retention push
   (:217-219), the post-commit drain (:165-169) and the direct-write clear
   (:224-226) are all dead - and open_table's preload (:347-356) restores the
   disk image at every restart. So the mem layer is a superset of the physical
   layer at every reachable state, i.e. a record on disk that the mem-only
   surface cannot see is UNREACHABLE pristine. This is the state
   No_full_memory_mode_test and No_open_preload each make reachable, from
   opposite ends. *)
let full_memory_mem_is_a_superset () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (durable(c) /\\ ~index_visible(c))" false
        (Checker.satisfiable sys
           (Formula.And (f Durable_c, Formula.Not (f Index_visible_c)))))

(* The boundary clear is total (close_epoch.rs:63 -> layered_db.rs:405-410):
   clear_table wipes the mem layer at once and queues the physical clear, so no
   reachable state has the scan already done and the batch still in a layer.
   This is what makes the loss S3 forbids PERMANENT rather than transient. *)
let boundary_clear_is_total () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (boundary_done /\\ cached(b))" false
        (Checker.satisfiable sys
           (Formula.And (f Boundary_done, f Batch_cached))))

(* S3 conjunct A stated as a reachability claim: absent a crash, no sealed batch
   ever survives the epoch boundary without its transactions coming back
   (close_epoch.rs:57-92 over the chained iterator, layered_db.rs:427).
   No_mem_chain_in_iter is exactly what makes this satisfiable. *)
let no_silent_orphan_loss () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (sealed(b) /\\ boundary_done /\\ ~pool_restored /\\ ~restarted)"
        false
        (Checker.satisfiable sys
           (Formula.And
              ( f Batch_sealed,
                Formula.And
                  ( f Boundary_done,
                    Formula.And
                      ( Formula.Not (f Pool_restored),
                        Formula.Not (f Restarted) ) ) ))))

(* R2, operand contingency for S1 conjunct B. K_V1(durable(c)) is not collapsed:
   there are reachable states at which the primary's certificate-store reader
   does NOT know its own record is on physical disk - every pre-restart state
   whose write is still queued on the background thread
   (layered_db.rs:391-396). *)
let k_v1_durability_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1(durable(c))" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Durable_c)))))

(* R2, non-singleton view class for S1 conjunct B. At an operative state -
   restarted with an index hit - pick batch_durable(b), which is FALSE there when
   the batch's own physical write never happened, and assert that V1 does not
   know its negation. That can only hold if another reachable state shares V1's
   view and satisfies batch_durable(b), i.e. the class is not a singleton. It is
   not: V1's view is (index answer, point answer, restarted) and carries nothing
   of the cache DB, so the class at each of the six operative states has six
   members. *)
let s1b_view_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (restarted /\\ index_visible(c) /\\ ~K_v1(~batch_durable(b)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Restarted,
                Formula.And
                  ( f Index_visible_c,
                    Formula.Not
                      (Formula.K (Validator.V1, Formula.Not (f Batch_durable)))
                  ) ))))

(* R3 ignorance witness for S1 conjunct C. Colliding pair: the state right after
   the epoch insert (c in the mem layer, physical write still queued, durable(c)
   false) and the state after the writer thread applies it (c in both layers,
   durable(c) true). Both are reachable and both project to View_peer true,
   because a peer's only route to a certificate enumerates rounds with
   next_round_number (cert_collector.rs:124 -> certificate_store.rs:429 ->
   skip_to, mem-only) and then reads the value (cert_collector.rs:137) - the
   response carries certificate bytes and nothing about which layer produced
   them. So a peer holding c cannot tell whether the serving node's copy would
   survive that node's next restart. *)
let peer_blind_to_serving_node_durability () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (index_visible(c) /\\ ~K_v2(durable(c)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Index_visible_c,
                Formula.Not (Formula.K (Validator.V2, f Durable_c)) ))))

(* R3 ignorance witness for S2 conjunct B. The same colliding pair, read by the
   node's OWN certificate-store reader: both states project to
   View_cert_reader (true, true, false) because get is mem-first and reports no
   provenance (layered_db.rs:383-389), commit's doc comment warns the write "may
   not be committed on-disk yet" (:118-124), persist/sync_persist answer with a
   bare oneshot (:463-495, :247-249) and stats()'s retained_inserts is
   structurally 0 in this mode (:217-219). *)
let node_blind_to_own_epoch_durability () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (point_visible(c) /\\ ~restarted /\\ ~K_v1(durable(c)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Point_visible_c,
                Formula.And
                  ( Formula.Not (f Restarted),
                    Formula.Not (Formula.K (Validator.V1, f Durable_c)) ) ))))

(* R3 ignorance witness for S3 conjunct B. Colliding pair: the state right after
   the worker caches b (mem layer only, physical write queued) and the state
   after the writer thread flushes it (physical layer only, mirror evicted by
   clear_insert_mem, layered_db.rs:165-169 / :224-226 / :538-541). Both are
   reachable and both project to View_cache_reader (true, false, false, _),
   because iter yields bare key/value pairs with no layer provenance
   (:420-429). That ignorance is precisely why the chain at :427 must exist. *)
let epoch_manager_blind_to_cache_layer () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (cached(b) /\\ ~boundary_done /\\ ~K_v3(batch_durable(b)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Batch_cached,
                Formula.And
                  ( Formula.Not (f Boundary_done),
                    Formula.Not (Formula.K (Validator.V3, f Batch_durable)) ) ))))

(* Honesty test for S2 conjunct B's [~restarted] scope. After a restart the epoch
   mem layer is EXACTLY the disk image (open_table's preload over the fresh empty
   BTreeMap MemDatabase::open_table installs, layered_db.rs:347-356 with
   mem_db.rs:124-127), so a post-restart index hit certifies physical residency
   and V1 genuinely DOES know durable(c) there. The scope is therefore a live
   distinction; this is also S1 conjunct B stated as a reachability claim. *)
let restart_scope_of_s2b_is_load_bearing () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (restarted /\\ index_visible(c) /\\ K_v1(durable(c)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Restarted,
                Formula.And
                  (f Index_visible_c, Formula.K (Validator.V1, f Durable_c)) ))))

(* Honesty test for S3 conjunct A's crash escape. The writer thread and its mpsc
   queue die with the process (layered_db.rs:308-313) and the cache DB gets no
   startup preload (the seed at :350-354 is guarded by self.full_memory, and the
   cache DB is opened with false at composite_db.rs:35), so a restart really does
   destroy an unflushed cache write - close_epoch.rs:38-41 says as much. If this
   were unreachable the escape would be a free pass and the weak-until would be
   weaker than it looks. *)
let crash_escape_of_s3a_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (sealed(b) /\\ restarted /\\ ~cached(b) /\\ ~pool_restored)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Batch_sealed,
                Formula.And
                  ( f Restarted,
                    Formula.And
                      ( Formula.Not (f Batch_cached),
                        Formula.Not (f Pool_restored) ) ) ))))

(* The mem-only window both S2 and S3 turn on is a real state of the model:
   Database::insert writes the mem layer and only QUEUES the physical write
   (layered_db.rs:391-396), so there is a reachable state in which the record
   exists in memory and nowhere else. *)
let queue_window_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (epoch_write_queued(c) /\\ ~durable(c))" true
        (Checker.satisfiable sys
           (Formula.And (f Epoch_write_queued, Formula.Not (f Durable_c)))))

let () =
  Alcotest.run "store_full_memory"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Store_full_memory_statements.name `Quick
              (prove_one st))
          Store_full_memory_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "full-memory-mem-is-a-superset" `Quick
            full_memory_mem_is_a_superset;
          Alcotest.test_case "boundary-clear-is-total" `Quick
            boundary_clear_is_total;
          Alcotest.test_case "no-silent-orphan-loss" `Quick
            no_silent_orphan_loss;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "s1b-operand-contingent" `Quick
            k_v1_durability_is_contingent;
          Alcotest.test_case "s1b-view-class-not-singleton" `Quick
            s1b_view_class_is_not_a_singleton;
          Alcotest.test_case "s1c-peer-ignorance-witness" `Quick
            peer_blind_to_serving_node_durability;
          Alcotest.test_case "s2b-node-ignorance-witness" `Quick
            node_blind_to_own_epoch_durability;
          Alcotest.test_case "s3b-cache-ignorance-witness" `Quick
            epoch_manager_blind_to_cache_layer;
          Alcotest.test_case "s2b-restart-scope-load-bearing" `Quick
            restart_scope_of_s2b_is_load_bearing;
          Alcotest.test_case "s3a-crash-escape-reachable" `Quick
            crash_escape_of_s3a_is_reachable;
          Alcotest.test_case "queue-window-reachable" `Quick
            queue_window_is_reachable;
        ] );
    ]
