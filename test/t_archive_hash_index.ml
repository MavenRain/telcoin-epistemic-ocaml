(** Proof suite for the ARCHIVE_HASH_INDEX family: the three statements prove
    on the pristine model, the model's own invariants hold, and every
    ignorance conjunct is discharged by an explicit witness pair rather than
    by a view class that happens to be a singleton.

    The [contingency] group is where R2/R3 are settled. The family asserts NO
    positive [K] - see the reading guide at the head of
    {!Archive_hash_index_statements} - so there is no non-singleton class
    obligation to discharge for a positive knowledge claim. What there is
    instead is two ignorance conjuncts over the same hidden fact
    ({!Archive_hash_index_model.Chain_corrupt}), and both are pinned in their
    strong form: at a pending walk on a chain that REALLY IS corrupt, the
    agent still does not know it, which is only possible when another
    reachable state sharing that agent's view carries a sound chain. *)

open Telcoin_epistemic
open Archive_hash_index_model

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
        (st.Archive_hash_index_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Archive_hash_index_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Archive_hash_index_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** Assert that a formula is satisfiable somewhere in the reachable set. *)
let sat_case label phi () =
  with_sys (fun sys ->
      Alcotest.(check bool) label true (Checker.satisfiable sys phi))

(** Assert that a formula is satisfiable NOWHERE in the reachable set. *)
let unsat_case label phi () =
  with_sys (fun sys ->
      Alcotest.(check bool) label false (Checker.satisfiable sys phi))

(** The raw component product is [appends] 3 x [buckets] 3 x [hot] 3 x
    clean-cache words of length <= 2 over two slots 7 x [walk] 4 = 756, but
    the pack's life is sequential (append-open, then sealed) and the phases
    pin most of those components, so the pristine reachable set is exactly 40:
    5 append-open states ([A0,B2,plain], [A1,B3,plain], [A1,B3,spilled],
    [A2,B4,plain], [A2,B4,spilled] - the cache is untouched and no walk is
    running while the pack is append-open), 3 sealed-but-idle states (empty
    cache, chain in each of its three shapes), 14 pending states (2 chained
    shapes x 7 cache words) and 18 answered states (3 chain shapes x the 6
    non-empty cache words, an answer having just admitted a slot). The
    mutants: 40 under [No_growth_gate], 80 under [No_cache_eviction_loop] (the
    cache word reaches three slots), 40 under [No_chain_decrease_guard]. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check int) "reachable states" 40 (Checker.reachable_count sys))

(** The eviction loop really is a cap: no reachable state holds more clean
    cache slots than [CACHED_BUCKETS] (index.rs:428-432). The model's cache is
    a list, so this is a checked property and not a type-level one - the same
    list reaches three slots once the loop is deleted. *)
let cap_is_enforced =
  unsat_case "no reachable state exceeds the clean-cache cap"
    (f Cache_over_cap)

(** The rotation is in index order: no reachable state has split bucket 1
    without having split bucket 0 first, because [split_bucket = buckets -
    modulus/2] (index.rs:549) yields 0 before 1. *)
let rotation_is_in_index_order =
  unsat_case "no reachable state splits the cold bucket first"
    (Formula.And (f Cold_bucket_split, Formula.Not (f Hot_bucket_split)))

(** A pending walk always has a chain to walk: the model only parks a lookup
    when bucket 0's head carries a non-zero overflow pointer, which is the
    only way [next_bucket_element] enters [reset_next_overflow]
    (bucket_iter.rs:151-152, :162-164). *)
let pending_implies_a_chain =
  unsat_case "no reachable pending walk is on an unchained bucket"
    (Formula.And (f Lookup_pending, Formula.Not (f Hot_overflowed)))

(** Growth is contingent, so S1's [Af] is a claim and not a tautology of the
    atom: the cold bucket is unsplit somewhere in the reachable set. *)
let growth_is_contingent =
  sat_case "the cold bucket is unsplit somewhere"
    (Formula.Not (f Cold_bucket_split))

(** The corrupt chain shape S3 defends against is reachable, so the guard is
    not guarding an empty branch in this model. *)
let corruption_is_reachable =
  sat_case "a self-linked overflow record is reachable" (f Chain_corrupt)

(** Both halves of the ignorance witness pair exist: a pending walk on a
    corrupt chain, and a pending walk on a sound one. *)
let pending_on_a_corrupt_chain =
  sat_case "a walk is pending on a corrupt chain"
    (Formula.And (f Lookup_pending, f Chain_corrupt))

(** The other half of the same pair. *)
let pending_on_a_sound_chain =
  sat_case "a walk is pending on a sound chain"
    (Formula.And (f Lookup_pending, Formula.Not (f Chain_corrupt)))

(** R3, strong form, for the [~K_V1] conjunct of S3: at a pending walk whose
    chain really is corrupt the parked worker still does not know it. This is
    satisfiable only because another reachable state shares V1's view
    ([Req_pending]) and carries a sound chain, so V1's class at the operative
    state is not a singleton. *)
let worker_ignorance_witness =
  sat_case "the parked worker does not know the chain it waits on is corrupt"
    (Formula.And
       ( f Lookup_pending,
         Formula.And
           ( f Chain_corrupt,
             Formula.Not (Formula.K (Validator.V1, f Chain_corrupt)) ) ))

(** R3, strong form, for the [~K_V2] conjunct of S3. V2's view carries the
    append count, the bucket count, whether bucket 0's head buffer has a
    non-zero overflow pointer, the whole clean-cache word and the walk, and it
    STILL cannot separate the corrupt chain from the sound one, because the
    chained record's own link is on disk (bucket_iter.rs:106-113). *)
let index_thread_ignorance_witness =
  sat_case "the index thread does not know the chain it walks is corrupt"
    (Formula.And
       ( f Lookup_pending,
         Formula.And
           ( f Chain_corrupt,
             Formula.Not (Formula.K (Validator.V2, f Chain_corrupt)) ) ))

(** The ignorance is total, not merely generic: nowhere in the reachable set
    does the index thread know the chain is corrupt. *)
let index_thread_never_knows =
  unsat_case "no reachable state has the index thread knowing of corruption"
    (Formula.K (Validator.V2, f Chain_corrupt))

(** S2's monopolisation conjunct is not vacuous: a full queue every slot of
    which names the hot bucket is reachable, which is only possible because
    [add_bucket_to_cache] admits duplicates (index.rs:422-435). *)
let monopolisation_is_reachable =
  sat_case "a full clean-cache queue naming only the hot bucket is reachable"
    (Formula.And (f Cache_at_cap, f Cache_all_hot))

(** ... and the cold bucket really does get a slot first, so the
    monopolisation conjunct's outer [Ef] has something to start from. *)
let cold_residency_is_reachable =
  sat_case "the cold bucket is resident somewhere" (f Cold_resident)

let () =
  Alcotest.run "archive_hash_index"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Archive_hash_index_statements.name `Quick
              (prove_one st))
          Archive_hash_index_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "cache-cap-enforced" `Quick cap_is_enforced;
          Alcotest.test_case "rotation-in-index-order" `Quick
            rotation_is_in_index_order;
          Alcotest.test_case "pending-implies-a-chain" `Quick
            pending_implies_a_chain;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "growth-is-contingent" `Quick growth_is_contingent;
          Alcotest.test_case "corruption-is-reachable" `Quick
            corruption_is_reachable;
          Alcotest.test_case "pending-on-a-corrupt-chain" `Quick
            pending_on_a_corrupt_chain;
          Alcotest.test_case "pending-on-a-sound-chain" `Quick
            pending_on_a_sound_chain;
          Alcotest.test_case "worker-ignorance-witness" `Quick
            worker_ignorance_witness;
          Alcotest.test_case "index-thread-ignorance-witness" `Quick
            index_thread_ignorance_witness;
          Alcotest.test_case "index-thread-never-knows" `Quick
            index_thread_never_knows;
          Alcotest.test_case "monopolisation-is-reachable" `Quick
            monopolisation_is_reachable;
          Alcotest.test_case "cold-residency-is-reachable" `Quick
            cold_residency_is_reachable;
        ] );
    ]
