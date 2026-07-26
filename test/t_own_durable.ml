(** The OWN_DURABLE family (S1, S2, S3) proves on the pristine
    {!Own_durable_model} through [prove_nonvacuous] (so each antecedent is also
    checked reachable), the reachable graph stays in its justified band, the
    three invariants the modelled gates enforce are genuinely unreachable-when-
    forbidden, and the epistemic layer is partial-information rather than
    collapsed.

    The contingency group is where R2 and R3 are discharged. The family has
    exactly ONE positive knowledge conjunct - [K_V2(own_cert_stored)] in S3
    conjunct A - so it carries both required R2 tests (operand contingency and a
    non-singleton view class), and one R3 ignorance witness per [~K] conjunct
    (S1-B, S2-B, and the two halves of S3-B).

    The group also carries two HONESTY tests that are not required by the
    contract but are required by the family's own claims. S1's [Af] is scoped to
    the crash-free tail, and [s1_unscoped_persist_is_false] proves the UNSCOPED
    form really is refuted in this model - so the [restarted] conjunct in S1's
    antecedent is load-bearing rather than a convenience. S3 conjunct B is
    scoped to the SILENT re-release route, and [revote_reveals_restart] proves
    that at a re-certifying state V2 genuinely DOES know the restart - so the
    [~revote_requested] conjunct is load-bearing too. *)

open Telcoin_epistemic
open Own_durable_model

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
        (st.Own_durable_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Own_durable_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Own_durable_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 3 mem values x 3 disk values x 2^6 boolean components =
   288. The pristine reachable set is exactly 22, hand-enumerated as: the five
   pre-restart states s0=(none,none,F,F,F,F,F,F), A=(c1,none,T,F,F,F,T,F),
   B=(c1,c1,F,F,F,F,T,F), C=(c1,none,T,T,F,F,T,F), D=(c1,c1,F,T,F,F,T,F); the
   five restart images R0=(none,none,F,F,F,T,F,F), R1=(none,none,F,F,F,T,T,F),
   R2=(c1,c1,F,F,F,T,T,F), R3=(none,none,F,T,F,T,T,F), R4=(c1,c1,F,T,F,T,T,F);
   the four same-aggregate re-certify states P1=(c1,none,T,F,F,T,T,T),
   P2=(c1,none,T,T,F,T,T,T), S1'=(c1,c1,F,F,F,T,T,T), S2'=(c1,c1,F,T,F,T,T,T);
   and the eight different-aggregate re-certify states Q1..Q8 over mem=c2. The
   mutants stay in the same band: 20, 28 and 24 states respectively. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 288))

(* The store-before-release gate (certifier.rs:443-446): the insert-failure arm
   returns Err strictly before process_own_certificate (:448) and
   publish_certificate (:454), so a certificate on the gossip topic that was
   never persisted is UNREACHABLE pristine. This is the state
   No_store_before_publish makes reachable, which is exactly how it refutes S3
   conjunct A. *)
let published_implies_stored () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (published(C1) /\\ ~own_cert_stored)" false
        (Checker.satisfiable sys
           (Formula.And (f Pub_c1, Formula.Not (f Own_cert_stored)))))

(* The re-certify gate (certifier.rs:418-430): once the record is on physical
   disk a restart reloads it into the full-memory mem layer
   (layered_db.rs:347-356), the lookup hits, and the certifier re-publishes the
   STORED certificate instead of re-running vote collection - so no second,
   differently-signed aggregate for the same header digest is ever reachable
   from a durable state. This is S2 conjunct A stated as a reachability claim,
   and No_proposed_cert_guard is what makes it satisfiable. *)
let durable_record_never_equivocates () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (disk=C1 /\\ EF published(C2))" false
        (Checker.satisfiable sys
           (Formula.And (f Disk_c1, Formula.Ef (f Pub_c2)))))

(* A second aggregate over the same header digest can only ever arise AFTER a
   restart: within one process the proposal lock (certifier.rs:411-416) plus the
   re-certify guard exclude it, and the model gives no in-process route to
   mem=C2 at all. *)
let no_in_process_equivocation () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (mem=C2 /\\ ~restarted)" false
        (Checker.satisfiable sys
           (Formula.And (f Mem_c2, Formula.Not (f Restarted)))))

(* R3 ignorance witness for S1 conjunct B. Colliding pair: world B = (mem C1,
   disk C1, no pend, nothing published, not restarted, stored) and world A =
   (mem C1, disk NONE, write still queued, nothing published, not restarted,
   stored). Both are reachable - A right after the store step, B after the store
   step then the background persist - and V1's view at both is
   View_v1 (Cell_c1, false, false, false, false), identical. They disagree on
   disk=C1, so the AUTHOR of the write cannot tell whether its own write is
   durable. *)
let author_blind_to_own_durability () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (disk=C1 /\\ ~restarted /\\ ~K_v1 disk=C1)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Disk_c1,
                Formula.And
                  ( Formula.Not (f Restarted),
                    Formula.Not (Formula.K (Validator.V1, f Disk_c1)) ) ))))

(* R3 ignorance witness for S2 conjunct B. Colliding pair: world D = (mem C1,
   disk C1, no pend, published C1, not restarted) and world C = (mem C1, disk
   NONE, write still queued, published C1, not restarted). Both reachable; V2's
   view at both is View_v2 (true, false, false); they disagree on disk=C1. A
   gossip peer holding C1 therefore cannot see the durability precondition its
   own equivocation guarantee rests on. *)
let peer_blind_to_durability () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (published(C1) /\\ ~published(C2) /\\ ~K_v2 disk=C1)" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Pub_c1, Formula.Not (f Pub_c2)),
                Formula.Not (Formula.K (Validator.V2, f Disk_c1)) ))))

(* R2, half one, for the family's ONE positive K (S3 conjunct A,
   K_V2(own_cert_stored)): the operand is contingent, not rigid. Witnessed at
   the initial state, whose V2 class (published nothing) also contains the
   post-restart world R0 - the run in which V1 crashed before ever persisting -
   so own_cert_stored is genuinely false somewhere reachable. *)
let stored_operand_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v2(own_cert_stored): knowledge not collapsed"
        true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V2, f Own_cert_stored)))))

(* R2, half two, for the same positive K: the operative view class is NOT a
   singleton. Operative state C = (mem C1, disk NONE, write queued, published
   C1, not restarted, stored), at which the probe atom q = disk=C1 is FALSE. If
   C's V2-class were a singleton, K_V2(~q) would hold there; the test asserts it
   does NOT, which is only possible because another world shares C's view. The
   two concrete worlds are C (disk = none, write still queued) and D (disk = C1,
   write persisted) - the class View_v2 (true, false, false) has four members:
   C, D, R3, R4. *)
let stored_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (published(C1) /\\ ~published(C2) /\\ ~disk=C1 /\\ ~K_v2 ~disk=C1)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Pub_c1, Formula.Not (f Pub_c2)),
                Formula.And
                  ( Formula.Not (f Disk_c1),
                    Formula.Not
                      (Formula.K (Validator.V2, Formula.Not (f Disk_c1))) ) ))))

(* R3 ignorance witness for S3 conjunct B, first half. Colliding pair: world C
   (restarted = false, the first release) and world R3 = (mem none, disk none,
   published C1, restarted, stored, NOT yet re-certified) - the post-restart
   world in which the write was lost and the re-proposal has not yet reached the
   peers. Both share View_v2 (true, false, false), so V2 cannot tell a first
   publication from a post-restart re-publication: on the guard's route the
   certifier re-publishes the SAME stored certificate bytes (certifier.rs:426)
   and the proposer re-sends the SAME stored header (proposer.rs:563-586). The
   ~revote_requested conjunct is what confines the claim to that silent route.
*)
let cannot_know_restarted () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (published(C1) /\\ ~published(C2) /\\ ~revote /\\ ~K_v2 restarted)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.conj
                  [
                    f Pub_c1;
                    Formula.Not (f Pub_c2);
                    Formula.Not (f Revote_requested);
                  ],
                Formula.Not (Formula.K (Validator.V2, f Restarted)) ))))

(* R3 ignorance witness for S3 conjunct B, second half - the same colliding pair
   read the other way: V2 equally cannot rule the restart OUT, because R3 shares
   C's view and has restarted = true. *)
let cannot_know_not_restarted () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (published(C1) /\\ ~published(C2) /\\ ~revote /\\ ~K_v2 ~restarted)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.conj
                  [
                    f Pub_c1;
                    Formula.Not (f Pub_c2);
                    Formula.Not (f Revote_requested);
                  ],
                Formula.Not
                  (Formula.K (Validator.V2, Formula.Not (f Restarted))) ))))

(* The ~revote_requested restriction in S3 conjunct B is LOAD-BEARING, and this
   is the test that watches it be load-bearing rather than assuming it. Drop the
   restriction and the conjunct is false: at a re-certifying state the peer DOES
   know V1 restarted. Grounding for the model's V2-visible re-vote component:
   when the ProposedCertificates lookup misses, spawn_header_proposal falls
   through to propose_header (certifier.rs:431-440), which spawns a fresh
   request_vote to every other primary (:286-312), and the receiving handler
   recognises the repeat for a header it already voted on (handler.rs:494-506);
   an in-process re-entry could not have produced it, because at a published
   state the insert at certifier.rs:443 already succeeded and the full-memory
   epoch DB answers mem-first (composite_db.rs:33, layered_db.rs:383-389), so
   the guard would have hit and re-published instead. *)
let revote_reveals_restart () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (published(C1) /\\ ~published(C2) /\\ revote /\\ K_v2 restarted)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.conj
                  [ f Pub_c1; Formula.Not (f Pub_c2); f Revote_requested ],
                Formula.K (Validator.V2, f Restarted) ))))

(* HONESTY witness that S1's liveness half is genuinely scoped rather than
   asserted where it is false. The unscoped card claim - a queued own-store
   write ALWAYS reaches disk - is REFUTED in this very model: at the pre-restart
   state A the path A -> R1 -> Q1 -> Q3 -> Q7 crashes before the background
   thread runs, loses the queued insert (layered_db.rs:306-315 spawns the writer
   inside the process), re-certifies to a different aggregate and terminates
   with disk = C2. This is why S1 carries [restarted] in its antecedent and
   claims inevitability only on the crash-free tail. *)
let s1_unscoped_persist_is_false () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (mem=C1 /\\ commit_pending /\\ ~restarted /\\ ~AF disk=C1)" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Mem_c1, f Commit_pending),
                Formula.And
                  ( Formula.Not (f Restarted),
                    Formula.Not (Formula.Af (f Disk_c1)) ) ))))

(* Contingency of S2 conjunct A: the equivocation it forbids is a REAL
   restriction, not a tautology of the model. published(C2) is reachable
   pristine - on the crash-before-persist branch, where the guard's lookup comes
   back empty on restart (certifier.rs:418-420 misses because
   layered_db.rs:347-356 reloaded nothing), vote collection re-runs, and the
   aggregation loop's arrival-order quorum break (certifier.rs:318-322) yields a
   different aggregate under the same header digest. *)
let equivocation_reachable_without_durability () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF published(C2)" true
        (Checker.satisfiable sys (f Pub_c2)))

let () =
  Alcotest.run "own_durable"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Own_durable_statements.name `Quick
              (prove_one st))
          Own_durable_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "published-implies-stored" `Quick
            published_implies_stored;
          Alcotest.test_case "durable-record-never-equivocates" `Quick
            durable_record_never_equivocates;
          Alcotest.test_case "no-in-process-equivocation" `Quick
            no_in_process_equivocation;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "author-blind-to-own-durability" `Quick
            author_blind_to_own_durability;
          Alcotest.test_case "peer-blind-to-durability" `Quick
            peer_blind_to_durability;
          Alcotest.test_case "stored-operand-contingent" `Quick
            stored_operand_contingent;
          Alcotest.test_case "stored-class-not-singleton" `Quick
            stored_class_not_singleton;
          Alcotest.test_case "cannot-know-restarted" `Quick
            cannot_know_restarted;
          Alcotest.test_case "cannot-know-not-restarted" `Quick
            cannot_know_not_restarted;
          Alcotest.test_case "revote-reveals-restart" `Quick
            revote_reveals_restart;
          Alcotest.test_case "s1-unscoped-persist-is-false" `Quick
            s1_unscoped_persist_is_false;
          Alcotest.test_case "equivocation-reachable-without-durability" `Quick
            equivocation_reachable_without_durability;
        ] );
    ]
