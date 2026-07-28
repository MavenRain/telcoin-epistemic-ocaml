(** Confirm-by-mutation pins for the STORE_NOTIFY_VISIBILITY family: each
    statement proves on the pristine model and REFUTES under the gate deletion
    it names, so the gate is load-bearing and the proof is not an artefact of
    the encoding.

    - {!Store_notify_visibility_model.No_post_registration_reread} deletes the
      re-read block [if let Ok(Some(cert)) = self.read(id) {
      NOTIFY_SUBSCRIBERS.notify(&id, &cert); return Ok(cert); }]
      (certificate_store.rs:255-263), so [register_one] (:253) is followed
      straight by [receiver.await] (:266). It pins S1 through conjunct C: a
      handler that registers after the write is parked on a oneshot that the
      already-fired notify will never fire again. The duplicate-write sibling is
      REAL and MODELLED - [accept_verified_certificates] calls [write_all] with
      no already-stored filter (cert_manager.rs:189-196, reached from :124 and
      :237) and [handler.rs:267] re-writes gossiped certificates while catching
      up, so a second [save_cert] notifies again (certificate_store.rs:144) -
      and the [sibling_repair_is_live_under_the_reread_deletion] test below
      proves it really can still rescue the parked handler in the mutant. The
      pin holds anyway because re-delivery is a BRANCH, not an obligation: on
      the single-delivery branch nothing wakes the handler, there is no timeout
      at the production caller (header_validator.rs:56-63 awaits the
      [FuturesOrdered] bare; only tests use [timeout]), and [Registration] never
      re-arms (notify_read.rs:109-125, :127-135). The same deletion also
      refutes S2, because it makes the both-parked state reachable AFTER the
      write, where no notify is coming - that cross pin is asserted below rather
      than hidden. It leaves S3 standing, and that survival is asserted too.
    - {!Store_notify_visibility_model.No_notify_fanout} deletes the fan-out loop
      [for registration in registrations { registration.send(value.clone()).ok();
      }] (notify_read.rs:38-40) and sends to a single registration. It pins S2:
      one handler resolves and the other is stranded. The stranding is
      PERMANENT because [remove(key)] at :33 already took the whole list out of
      the sharded map, so neither a duplicate [save_cert] (:144) nor another
      handler's re-read notify (:259) can reach it - both re-enter [notify] and
      take the empty-key early return (:34-36). The
      [stranded_registration_is_terminal] test below asserts exactly that in the
      mutant. It leaves S1 and S3 standing, and both survivals are asserted.
    - {!Store_notify_visibility_model.No_mem_write_on_insert} deletes the
      mem-layer write [self.mem_db.insert::<T>(key, value)?;] from
      [LayeredDbTxMut::insert] (layered_db.rs:98) and from its byte-identical
      sibling in [LayeredDatabase::insert] (:392). It pins S3: [save_cert] has
      run and fired its notify (certificate_store.rs:144, before [txn.commit()]
      at :183/:206) while both layers still answer [None]. No third read source
      repairs it - [get] (:383-389), [contains_key] (:375-381), [is_empty]
      (:412-418) and [iter] (:423-429) read exactly the two layers with no retry
      and no re-fetch, [MemDatabase::get] returns [None] silently
      (mem_db.rs:145-147 via :12-21), the writer thread's [insert_txn]
      (:210-219) writes into an uncommitted physical txn, and [open_table]'s
      preload (:347-356) runs once at process start. It refutes S1 and S2 as
      collateral, because a re-read that misses cannot resolve anything; those
      cross effects are asserted below. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Store_notify_visibility_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Store_notify_visibility_model.Checker.make
       (Store_notify_visibility_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0
        (String.compare st.Store_notify_visibility_statements.name name))
    Store_notify_visibility_statements.all

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
               (Store_notify_visibility_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Store_notify_visibility_model.Pristine (fun sys ->
          Alcotest.(check bool)
            (name ^ " proves on the pristine model")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Store_notify_visibility_statements.prove sys st)))

(** A statement that must SURVIVE a mutation: the evidence that the three gates
    are separate gates and not one gate counted three times. *)
let still_proves_under mut name () =
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
               (Store_notify_visibility_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* R4 evidence for the re-read deletion. The duplicate-write sibling is not
   merely mentioned in the doc comment - it is a live transition of the MUTATED
   model, and it really can still resolve a handler that the deleted re-read
   left parked. The pin is therefore not an artefact of a model that omitted the
   repair path: it holds because re-delivery is a branch (T5) rather than an
   obligation, and the single-delivery branch (T6) reaches a terminal with the
   handler still parked. *)
let sibling_repair_is_live_under_the_reread_deletion () =
  with_mut Store_notify_visibility_model.No_post_registration_reread
    (fun sys ->
      Alcotest.(check bool)
        "EF (written(d) /\\ registered_1(d) /\\ EF resolved_1(d)): a duplicate \
         write can still rescue the parked handler"
        true
        (Store_notify_visibility_model.Checker.satisfiable sys
           (Formula.And
              ( f Store_notify_visibility_model.Cert_written,
                Formula.And
                  ( f Store_notify_visibility_model.W1_reg,
                    Formula.Ef (f Store_notify_visibility_model.W1_done) ) ))))

(* R4 evidence for the fan-out deletion, the other way round. Once [remove(key)]
   (notify_read.rs:33) has taken a registration out of the map and the mutated
   notify has dropped its sender, NOTHING reaches it: no later write, no other
   handler's re-read notify. The stranded state is terminal in the mutant, so
   the starvation the pin reports is permanent rather than transient. *)
let stranded_registration_is_terminal () =
  with_mut Store_notify_visibility_model.No_notify_fanout (fun sys ->
      Alcotest.(check bool)
        "not EF (starved_2(d) /\\ EF resolved_2(d)): a dropped sender is \
         unreachable by any later notify"
        false
        (Store_notify_visibility_model.Checker.satisfiable sys
           (Formula.And
              ( f Store_notify_visibility_model.W2_lost,
                Formula.Ef (f Store_notify_visibility_model.W2_done) ))))

(* And the starvation the fan-out deletion creates is reachable at all - without
   this the pin above would be vacuous. *)
let starvation_is_reachable_under_the_fanout_deletion () =
  with_mut Store_notify_visibility_model.No_notify_fanout (fun sys ->
      Alcotest.(check bool) "EF starved_2(d)" true
        (Store_notify_visibility_model.Checker.satisfiable sys
           (f Store_notify_visibility_model.W2_lost)))

(* The visibility hole the mem-write deletion creates is reachable, i.e. the
   mutation really does what its doc comment says: save_cert has run - and has
   already fired its notify - while CertificateStore::read(d) still answers
   None. *)
let visibility_hole_is_reachable_under_the_mem_deletion () =
  with_mut Store_notify_visibility_model.No_mem_write_on_insert (fun sys ->
      Alcotest.(check bool) "EF (written(d) /\\ ~store_visible(d))" true
        (Store_notify_visibility_model.Checker.satisfiable sys
           (Formula.And
              ( f Store_notify_visibility_model.Cert_written,
                Formula.Not (f Store_notify_visibility_model.Store_visible) ))))

let () =
  Alcotest.run "store_notify_visibility_mutation"
    [
      ( "post-registration re-read (certificate_store.rs:255-263)",
        pin Store_notify_visibility_model.No_post_registration_reread
          "post-registration-reread-resolves-a-parent-wait-that-began-too-late"
        @ [
            Alcotest.test_case
              "one-write-wakes-every-registered-parent-waiter:also-flips" `Quick
              (refuted_under
                 Store_notify_visibility_model.No_post_registration_reread
                 "one-write-wakes-every-registered-parent-waiter");
            Alcotest.test_case
              "certificate-is-store-visible-from-the-instant-its-write-notifies:survives"
              `Quick
              (still_proves_under
                 Store_notify_visibility_model.No_post_registration_reread
                 "certificate-is-store-visible-from-the-instant-its-write-notifies");
            Alcotest.test_case "duplicate-write-sibling-is-live-in-the-mutant"
              `Quick sibling_repair_is_live_under_the_reread_deletion;
          ] );
      ( "notify fan-out (notify_read.rs:38-40)",
        pin Store_notify_visibility_model.No_notify_fanout
          "one-write-wakes-every-registered-parent-waiter"
        @ [
            Alcotest.test_case
              "post-registration-reread-resolves-a-parent-wait-that-began-too-late:survives"
              `Quick
              (still_proves_under Store_notify_visibility_model.No_notify_fanout
                 "post-registration-reread-resolves-a-parent-wait-that-began-too-late");
            Alcotest.test_case
              "certificate-is-store-visible-from-the-instant-its-write-notifies:survives"
              `Quick
              (still_proves_under Store_notify_visibility_model.No_notify_fanout
                 "certificate-is-store-visible-from-the-instant-its-write-notifies");
            Alcotest.test_case "starvation-is-reachable" `Quick
              starvation_is_reachable_under_the_fanout_deletion;
            Alcotest.test_case "stranded-registration-is-terminal" `Quick
              stranded_registration_is_terminal;
          ] );
      ( "mem-first insert (layered_db.rs:98, sibling :392)",
        pin Store_notify_visibility_model.No_mem_write_on_insert
          "certificate-is-store-visible-from-the-instant-its-write-notifies"
        @ [
            Alcotest.test_case
              "post-registration-reread-resolves-a-parent-wait-that-began-too-late:also-flips"
              `Quick
              (refuted_under Store_notify_visibility_model.No_mem_write_on_insert
                 "post-registration-reread-resolves-a-parent-wait-that-began-too-late");
            Alcotest.test_case
              "one-write-wakes-every-registered-parent-waiter:also-flips" `Quick
              (refuted_under Store_notify_visibility_model.No_mem_write_on_insert
                 "one-write-wakes-every-registered-parent-waiter");
            Alcotest.test_case "visibility-hole-is-reachable" `Quick
              visibility_hole_is_reachable_under_the_mem_deletion;
          ] );
    ]
