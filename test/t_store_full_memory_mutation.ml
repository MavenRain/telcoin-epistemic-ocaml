(** Confirm-by-mutation pins for the STORE_FULL_MEMORY family: each statement
    proves on the pristine model and REFUTES under the gate deletion it names, so
    the gate is load-bearing and the proof is not an artefact of the encoding.

    - {!Store_full_memory_model.No_open_preload} deletes the startup seed
      [if self.full_memory { for (k, v) in self.db.iter::<T>() { .. } }]
      (layered_db.rs:350-354), so a reopened node has an EMPTY epoch mem layer.
      It pins S1 through conjunct A: a certificate on physical disk becomes
      invisible to [contains]/[after_round]/[next_round_number]. The sibling
      repair is real, partial and MODELLED - [get] still falls through to the
      physical layer in both modes (:383-389), so [point_visible(c)] stays true
      under the mutation and S1 survives it only by being about the index
      surface. Nothing else re-seeds the mem layer (mem_db.rs:124-127, :92-111)
      and no read repopulates it (:30-38, :383-389). The same deletion refutes S2
      from the other end, and that cross pin is asserted below.
    - {!Store_full_memory_model.No_full_memory_mode_test} deletes the mode test
      at layered_db.rs:311, re-enabling [clear_insert_mem] for the epoch DB
      (:165-169, :224-226, :538-541). It pins S2: the applied write leaves
      [durable(c)] without [index_visible(c)]. No mem-only reader has a durable
      fall-back to repair it (:375-381, :412-461) and nothing re-inserts on a
      read miss. It leaves S1 standing, because the startup preload it does not
      touch still restores the disk image at every restart - which is exactly the
      separation the two statements are drawing.
    - {!Store_full_memory_model.No_mem_chain_in_iter} deletes
      [.chain(self.mem_db.iter::<T>())] at layered_db.rs:427. It pins S3: from
      the sealed-but-unflushed state the epoch-boundary scan returns nothing, the
      [clear_table] at close_epoch.rs:63 wipes both layers, and the batch's
      transactions are in no pool and no committed batch. The flush ordering IS
      the sibling path and the model has it - if the writer thread applies the
      insert first, [db.iter()] alone still finds the batch - which is why the
      statement quantifies over both orderings. The two other readers of
      [OurNodeBatchesCache] do not repair it: run_epoch.rs:543 is a point remove
      on the happy path, and [NodeBatchesCache] is cleared at close_epoch.rs:270
      with no re-injection. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Store_full_memory_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Store_full_memory_model.Checker.make
       (Store_full_memory_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Store_full_memory_statements.name name))
    Store_full_memory_statements.all

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " flips to refuted under the mutation")
            false
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Store_full_memory_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Store_full_memory_model.Pristine (fun sys ->
          Alcotest.(check bool)
            (name ^ " proves on the pristine model")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Store_full_memory_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** A statement that must SURVIVE a mutation: the evidence that the two epoch-DB
    gates are separate gates and not one gate counted twice. *)
let survives mut name =
  Alcotest.test_case (name ^ ":survives") `Quick (pristine_proves name)
  :: [
       Alcotest.test_case (name ^ ":still-proves-under-mutation") `Quick
         (fun () ->
           match find name with
           | [] -> Alcotest.fail ("unknown statement: " ^ name)
           | st :: _ ->
               with_mut mut (fun sys ->
                   Alcotest.(check bool)
                     (name ^ " still proves under the other gate's deletion")
                     true
                     (Result.fold
                        ~ok:(fun _ -> true)
                        ~error:(fun _ -> false)
                        (Store_full_memory_statements.prove sys st))));
     ]

let () =
  Alcotest.run "store_full_memory_mutation"
    [
      ( "open_table full-memory preload (layered_db.rs:350-354)",
        pin Store_full_memory_model.No_open_preload
          "restart-preload-is-the-only-recovery-of-round-indexed-visibility"
        @ [
            Alcotest.test_case
              "full-memory-layer-is-never-evicted-so-index-and-point-reads-agree:also-flips"
              `Quick
              (refuted_under Store_full_memory_model.No_open_preload
                 "full-memory-layer-is-never-evicted-so-index-and-point-reads-agree");
          ] );
      ( "writer-thread mem handle mode test (layered_db.rs:311)",
        pin Store_full_memory_model.No_full_memory_mode_test
          "full-memory-layer-is-never-evicted-so-index-and-point-reads-agree"
        @ survives Store_full_memory_model.No_full_memory_mode_test
            "restart-preload-is-the-only-recovery-of-round-indexed-visibility"
      );
      ( "layered iter mem chain (layered_db.rs:427)",
        pin Store_full_memory_model.No_mem_chain_in_iter
          "cache-iteration-chains-the-unflushed-layer-so-orphan-batches-are-never-lost"
      );
    ]
