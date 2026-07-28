(** Confirm-by-mutation pins for the ARCHIVE_HASH_INDEX family. Each gate
    deletion is asserted per STATEMENT, so a pin cannot pass because some
    other statement in the family happened to flip.

    - [No_growth_gate] deletes the growth condition of [expand_buckets]
      (index.rs:441). [split_one_bucket] (index.rs:546) has exactly one
      caller, [expand_buckets] (:442), and [inc_buckets] (:456-459) has
      exactly one caller, [split_one_bucket] (:550), so no sibling path
      re-establishes the rotation.
    - [No_cache_eviction_loop] deletes the eviction loop of
      [add_bucket_to_cache] (index.rs:428-432). Nothing else removes an entry
      from the CLEAN cache: [remove_bucket_cache] (:471-478) and
      [remove_bucket] (:482-504) hand a buffer to a writer and
      [save_to_bucket] returns it to the DIRTY map (:601-609),
      [save_bucket_cache] drains that dirty map (:512) and re-inserts through
      this same function (:520-522), and [Drop] (:723-758) flushes without
      evicting.
    - [No_chain_decrease_guard] deletes the strict-decrease test of
      [reset_next_overflow] (bucket_iter.rs:123-126). [next_bucket_element]
      (bucket_iter.rs:142-169) has no visit counter and no depth cap, the
      per-record [check_crc] (:114-117) passes on an individually valid
      self-linked record, [read_exact(...).ok()?] (:113) repairs only a link
      past the end of the odx, the caller has no [tokio::time::timeout]
      (consensus_pack.rs:595-600), and [run_pack_loop] is one blocking thread
      (:132-193) so nothing concurrent can clear the chain.

    The [sibling-survives] group is the other half of R4 and the reason this
    family models the overflow chain at all: with the growth gate deleted the
    spill path (index.rs:667-685) keeps appends landing and lookups answering,
    so S3 must - and does - keep proving under [No_growth_gate]. A mutation
    that took S3 down with it would mean the model had smuggled the rotation
    into the lookup path. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Archive_hash_index_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Archive_hash_index_model.Checker.make
       (Archive_hash_index_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Archive_hash_index_statements.name name))
    Archive_hash_index_statements.all

(** Does the named statement prove under [mut]. *)
let proves_under mut name k =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          k
            (Result.fold ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Archive_hash_index_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " flips to refuted under the mutation")
        false proved)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  proves_under Archive_hash_index_model.Pristine name (fun proved ->
      Alcotest.(check bool) (name ^ " proves on the pristine model") true proved)

(** A statement that must SURVIVE a mutation aimed at a different gate. *)
let survives_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " still proves under a mutation of a different gate")
        true proved)

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** Short case labels; the statement names are long. *)
let s1 = "split-rotation-reaches-the-cold-bucket-independent-of-occupancy"

(** Short case label for the clean-cache statement. *)
let s2 =
  "bucket-cache-residency-is-capped-yet-one-hot-bucket-evicts-the-cold-one"

(** Short case label for the overflow-walk statement. *)
let s3 =
  "overflow-chain-decrease-guard-answers-a-corrupt-chain-instead-of-wedging"

let () =
  Alcotest.run "archive_hash_index_mutation"
    [
      ("growth-gate", pin Archive_hash_index_model.No_growth_gate s1);
      ( "cache-eviction-loop",
        pin Archive_hash_index_model.No_cache_eviction_loop s2 );
      ( "chain-decrease-guard",
        pin Archive_hash_index_model.No_chain_decrease_guard s3 );
      ( "sibling-survives",
        [
          Alcotest.test_case "overflow-spill-keeps-lookups-answering" `Quick
            (survives_under Archive_hash_index_model.No_growth_gate s3);
          Alcotest.test_case "growth-gate-does-not-touch-the-cache" `Quick
            (survives_under Archive_hash_index_model.No_growth_gate s2);
          Alcotest.test_case "cache-loop-does-not-touch-the-rotation" `Quick
            (survives_under Archive_hash_index_model.No_cache_eviction_loop s1);
          Alcotest.test_case "cache-loop-does-not-touch-the-walk" `Quick
            (survives_under Archive_hash_index_model.No_cache_eviction_loop s3);
          Alcotest.test_case "decrease-guard-does-not-touch-the-rotation" `Quick
            (survives_under Archive_hash_index_model.No_chain_decrease_guard s1);
          Alcotest.test_case "decrease-guard-does-not-touch-the-cache" `Quick
            (survives_under Archive_hash_index_model.No_chain_decrease_guard s2);
        ] );
    ]
