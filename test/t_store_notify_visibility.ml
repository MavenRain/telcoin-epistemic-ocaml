(** The STORE_NOTIFY_VISIBILITY family (S1, S2, S3) proves on the pristine
    {!Store_notify_visibility_model} through [prove_nonvacuous] (so each
    antecedent is also checked reachable), the reachable graph stays in its
    justified band, the three invariants the modelled gates enforce really are
    unreachable-when-forbidden, and the epistemic layer is partial-information
    rather than collapsed.

    The contingency group is where R2 and R3 are discharged. The family has
    exactly ONE positive knowledge conjunct - [K_V1(possessed(d))] in S1
    conjunct B - so it carries both required R2 tests (operand contingency and a
    non-singleton view class) plus a witness that the operative state is
    reachable at all, and one R3 ignorance witness per [~K] conjunct (S1-A,
    S2-B, S3-B).

    The group also carries three windows the statements turn on, asserted as
    reachability claims so that no statement is quietly true because its
    interesting case does not exist: the LATE-REGISTRATION window that S1 is
    entirely about ([save_cert] has run while the handler is still between
    entering [notify_read] and calling [register_one]), the BOTH-PARKED state
    that S2 is about, and the PRE-COMMIT window that S3 is about (the store
    answers while the background thread's physical commit has not returned). *)

open Telcoin_epistemic
open Store_notify_visibility_model

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
        (st.Store_notify_visibility_statements.name ^ " ["
        ^ Statements.bucket_to_string
            st.Store_notify_visibility_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Store_notify_visibility_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: two branch/history booleans (possessed, delivery_closed)
   times three store booleans (written, mem, durable) times two handler
   lifecycles of five states each = 2*2*2*2*2*5*5 = 800. The pristine reachable
   set is exactly 36: nine states on the fabricated-parent branch (neither
   handler can get past W_reg because no write ever happens, 3 x 3), plus nine
   pre-write states on the honest branch (3 x 3 again), plus eighteen post-write
   states (two values of the physical-commit bit times the nine combinations of
   {idle, want, done} for the two handlers - W_reg is unreachable after a write
   pristine, which is exactly what S1 and S2 say). The mutants stay in a sane
   band: 74, 38 and 74 states for No_post_registration_reread, No_notify_fanout
   and No_mem_write_on_insert respectively. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 800))

(* S3 conjunct A stated as a reachability claim (certificate_store.rs:144 fires
   before txn.commit() at :183/:206; layered_db.rs:98 writes the mem layer
   first and :383-389 reads it first): no reachable state has save_cert done for
   d and CertificateStore::read(d) still answering None. This is the invariant
   No_mem_write_on_insert makes reachable. *)
let no_visibility_hole () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (written(d) /\\ ~store_visible(d))" false
        (Checker.satisfiable sys
           (Formula.And (f Cert_written, Formula.Not (f Store_visible)))))

(* The re-read (certificate_store.rs:255-263) and the fan-out
   (notify_read.rs:38-40) together mean no handler is ever left parked once the
   certificate is written: one registered before the write is fired at by the
   notify, one registering after it is resolved by its own re-read. This is the
   state BOTH No_post_registration_reread and No_mem_write_on_insert make
   reachable, from opposite ends - the first by deleting the re-read, the second
   by making the re-read miss. *)
let no_parked_handler_survives_a_write () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (written(d) /\\ (registered_1(d) \\/ registered_2(d)))" false
        (Checker.satisfiable sys
           (Formula.And (f Cert_written, Formula.Or (f W1_reg, f W2_reg)))))

(* The fan-out invariant (notify_read.rs:31-42): because notify removes the
   whole registration list and then fires every sender, no registration is ever
   taken out of the map and dropped unsent. W_lost is therefore unreachable on
   the pristine model - it is exactly what No_notify_fanout creates, and on the
   real code it is not even a quiet loss (Registration::poll's expect at :123
   panics on the dropped sender). *)
let no_starved_handler () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF starved_2(d)" false
        (Checker.satisfiable sys (f W2_lost)))

(* The fabricated-parent branch is genuinely write-free: save_cert only runs on
   a certificate some validator actually delivered, so a digest a Byzantine
   header author invented is never written anywhere. If this failed, the
   ignorance conjuncts would be witnessed by states that are not really the
   fabricated case. *)
let fabricated_branch_is_write_free () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (~possessed(d) /\\ written(d))" false
        (Checker.satisfiable sys
           (Formula.And (Formula.Not (f Possessed), f Cert_written))))

(* R2, operand contingency for S1 conjunct B. K_V1(possessed(d)) is not
   collapsed: there are reachable states at which the waiting handler does NOT
   know any honest validator holds the parent certificate - every state of the
   fabricated-parent branch, and every pre-write state of the honest one. *)
let k_v1_possession_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1(possessed(d))" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Possessed)))))

(* R2, operative-state reachability for S1 conjunct B: the knowledge really is
   asserted somewhere, i.e. resolved_1(d) is reachable and V1 does know
   possession there. Without this the conjunct would be vacuously true. *)
let s1b_operative_state_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (resolved_1(d) /\\ K_v1(possessed(d)))" true
        (Checker.satisfiable sys
           (Formula.And (f W1_done, Formula.K (Validator.V1, f Possessed)))))

(* R2, non-singleton view class for S1 conjunct B. At an operative state - V1's
   notify_read has returned - pick durable(d), which is FALSE at the state
   reached the instant the notify fires (the physical commit is still queued),
   and assert that V1 does not know its negation. That can only hold if another
   reachable state shares V1's view and satisfies durable(d), i.e. the class is
   not a singleton. It is not: V1's view is (its own call state, the store's
   answer) and carries nothing of the physical commit or of the other handler,
   so the class at a resolved state spans both values of the commit bit and all
   three reachable states of the other handler. *)
let s1b_view_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (resolved_1(d) /\\ ~K_v1(~durable(d)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f W1_done,
                Formula.Not (Formula.K (Validator.V1, Formula.Not (f Durable)))
              ))))

(* R3 ignorance witness for S1 conjunct A. Colliding pair: an honest-branch
   state in which V1's handler has entered notify_read for d and the store still
   answers None, and the fabricated-branch state of the same shape. Both are
   reachable and both project to View_v1 (W_want, false), because a header
   carries parent DIGESTS and no certificate (header_validator.rs:56-63) and
   V1's only other observation is its own store. So a validator parked on a
   parent digest cannot tell a real parent from one its peer invented. *)
let waiting_handler_blind_to_peer_possession () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (waiting_1(d) /\\ ~store_visible(d) /\\ ~K_v1(possessed(d)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f W1_want,
                Formula.And
                  ( Formula.Not (f Store_visible),
                    Formula.Not (Formula.K (Validator.V1, f Possessed)) ) ))))

(* R3 ignorance witness for S2 conjunct B. Colliding pair: two states in which
   V1's handler is parked on its oneshot, differing only in whether the other
   handler has registered as well. Both project to View_v1 (W_reg, false),
   because registrations live in a private map behind one of 255 shard mutexes
   (notify_read.rs:19, :26, :64-74), the bare num_pending counter (:76-78) is
   read by no consensus path, and save_cert discards even the remaining count
   that notify returns (certificate_store.rs:144). *)
let parked_handler_blind_to_the_other_registration () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (registered_1(d) /\\ ~K_v1(registered_2(d)))"
        true
        (Checker.satisfiable sys
           (Formula.And
              (f W1_reg, Formula.Not (Formula.K (Validator.V1, f W2_reg))))))

(* Both halves of that witness pair are reachable in their own right: two
   handlers parked on the same digest at once (the normal case - process_vote_
   request spawns one task per inbound vote request, network/mod.rs:1517-1530,
   and headers of one round name overlapping parents) and one parked alone. *)
let both_handlers_parked_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (registered_1(d) /\\ registered_2(d))" true
        (Checker.satisfiable sys (Formula.And (f W1_reg, f W2_reg))))

(* The other half. *)
let one_handler_parked_alone_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (registered_1(d) /\\ ~registered_2(d))" true
        (Checker.satisfiable sys
           (Formula.And (f W1_reg, Formula.Not (f W2_reg)))))

(* R3 ignorance witness for S3 conjunct B. Colliding pair: the state the instant
   save_cert's notify fires (mem layer holds d, the physical txn is still
   queued) and the state after the background thread's current_txn.commit()
   returns (layered_db.rs:162). Both are reachable and both project to
   View_v2 (_, true), because get is mem-first and reports no provenance
   (:383-389), commit's doc comment warns the data "may not be committed on-disk
   yet" (:118-124), persist/sync_persist answer with a bare oneshot (:247-249,
   :463-495) and LayeredDatabase::stats (:317-333) is called by no consensus
   path. *)
let reader_blind_to_physical_commit () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (store_visible(d) /\\ ~K_v2(durable(d)))" true
        (Checker.satisfiable sys
           (Formula.And
              (f Store_visible, Formula.Not (Formula.K (Validator.V2, f Durable))))))

(* The LATE-REGISTRATION window S1 is entirely about: save_cert has already run
   (and already fired its one notify at certificate_store.rs:144) while V1's
   handler is still between entering notify_read_parent_certificates
   (header_validator.rs:56-63) and reaching register_one
   (certificate_store.rs:253). If this were unreachable, the re-read at
   :255-263 would have nothing to close and S1 would be an empty claim. *)
let late_registration_window_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (written(d) /\\ waiting_1(d))" true
        (Checker.satisfiable sys (Formula.And (f Cert_written, f W1_want))))

(* The PRE-COMMIT window S3 is about: the store answers Some while the
   background thread's physical commit has not returned. That window is what
   makes the notify-before-commit ordering (certificate_store.rs:144 vs :183)
   safe rather than reckless, and it is what conjunct B's ignorance is about. *)
let pre_commit_window_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (store_visible(d) /\\ ~durable(d))" true
        (Checker.satisfiable sys
           (Formula.And (f Store_visible, Formula.Not (f Durable)))))

let () =
  Alcotest.run "store_notify_visibility"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Store_notify_visibility_statements.name `Quick
              (prove_one st))
          Store_notify_visibility_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "no-visibility-hole" `Quick no_visibility_hole;
          Alcotest.test_case "no-parked-handler-survives-a-write" `Quick
            no_parked_handler_survives_a_write;
          Alcotest.test_case "no-starved-handler" `Quick no_starved_handler;
          Alcotest.test_case "fabricated-branch-is-write-free" `Quick
            fabricated_branch_is_write_free;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "s1b-operand-contingent" `Quick
            k_v1_possession_is_contingent;
          Alcotest.test_case "s1b-operative-state-reachable" `Quick
            s1b_operative_state_is_reachable;
          Alcotest.test_case "s1b-view-class-not-singleton" `Quick
            s1b_view_class_is_not_a_singleton;
          Alcotest.test_case "s1a-possession-ignorance-witness" `Quick
            waiting_handler_blind_to_peer_possession;
          Alcotest.test_case "s2b-registration-ignorance-witness" `Quick
            parked_handler_blind_to_the_other_registration;
          Alcotest.test_case "s2b-witness-both-parked" `Quick
            both_handlers_parked_is_reachable;
          Alcotest.test_case "s2b-witness-one-parked" `Quick
            one_handler_parked_alone_is_reachable;
          Alcotest.test_case "s3b-durability-ignorance-witness" `Quick
            reader_blind_to_physical_commit;
          Alcotest.test_case "late-registration-window-reachable" `Quick
            late_registration_window_is_reachable;
          Alcotest.test_case "pre-commit-window-reachable" `Quick
            pre_commit_window_is_reachable;
        ] );
    ]
