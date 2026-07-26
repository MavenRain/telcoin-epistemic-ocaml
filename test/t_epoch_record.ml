(** The EPOCH_RECORD family (S1, S2, S3) proves on the pristine
    {!Epoch_record_model} through [prove_nonvacuous] (so each antecedent is
    also checked reachable), the reachable graph stays in its justified band,
    the gate invariants hold (a stored certificate always has a real
    super-quorum behind it; the collector's cursor never passes an epoch NO
    record of which was certified), and the epistemic layer is genuinely
    partial-information: both positive knowledge operands are contingent, the
    classes that make them true are provably NOT singletons, and the ignorance
    window has a concrete colliding-pair witness.

    Two tests exist specifically to keep the family honest about the two
    branches the model was enriched with:

    - [tally-quorum-window-knows] shows that inside [Sg_tally_quorum] - the
      [reached_quorum]-but-unpersisted window of epoch_votes.rs:103-104 - V1
      DOES know the super-quorum endorsement while its DB is still certless.
      That is exactly why S2(A) and S3(A) carry the [~tally_quorum_held]
      guard: without it they would be false of the real system.
    - [divergent-cursor-advance-reachable] shows that the cursor CAN pass
      epoch 1 while V1's own record stays certless (the [E_alt] branch:
      certificate filed under the fetched record's digest,
      epoch_records.rs:601, :611-614, read back under the stored record's
      digest, :374-375). That is why S2 no longer claims
      "cursor>1 -> store_has_cert(1)". *)

open Telcoin_epistemic
open Epoch_record_model

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
        (st.Epoch_record_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Epoch_record_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Epoch_record_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 6 endorsement values x 2 store values x 7 stages x 2
   Byzantine-budget values = 168. The pristine reachable set is exactly 42,
   broken down by stage as Sg_close 1, Sg_tally 5, Sg_tally_quorum 2,
   Sg_boot 7, Sg_scan0 7, Sg_scan1 14, Sg_scan2 6. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 168))

(* The exact pristine reachable count, pinned so a modelling drift that widens
   or narrows the graph is caught rather than silently absorbed. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "exact pristine reachable count" 42
        (Checker.reachable_count sys))

(* The quorum gate's contract (S1 conjunct A as a reachability claim): a state
   holding a certificate for epoch 1 WITHOUT a real super-quorum behind it is
   unreachable pristine. This is exactly what [auth_iter < super_quorum]
   (crates/types/src/primary/epoch.rs:84-88) forbids, and exactly what
   No_quorum_count makes reachable. *)
let cert_implies_quorum () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (store_has_cert /\\ ~quorum_endorsed)" false
        (Checker.satisfiable sys
           (Formula.And (f Store_cert, Formula.Not (f Quorum_endorsed)))))

(* The collector's cursor contract (S2 conjunct B as a reachability claim): the
   cursor never sits above epoch 1 unless SOME epoch-1 record really was
   super-quorum certified. This is the [Some((rec, Some(_)))] conjunct at
   crates/state-sync/src/epoch.rs:61, the fetch-side [verify_with_cert] at :102
   and the break at :147-149 - and exactly what Cert_conjunct_dropped removes.
   Note what is NOT claimed: the cursor may pass epoch 1 while V1's OWN record
   is certless, see [divergent-cursor-advance-reachable]. *)
let cursor_never_passes_uncertified_epoch () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (cursor>1 /\\ ~quorum_certified(some))"
        false
        (Checker.satisfiable sys
           (Formula.And
              (f Collector_past_epoch, Formula.Not (f Some_record_certified)))))

(* S2 conjunct (D) as a reachability claim: the cursor never passes epoch 1
   leaving V1's own record certless UNLESS V1's record is the one that missed
   the quorum. Grounded in the digest keying of the certificate write
   (epoch_records.rs:601, :611-614) versus the read (:374-375) plus quorum
   intersection at n = 4, f = 1. *)
let certless_completion_means_divergence () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (cursor>1 /\\ ~store_has_cert /\\ quorum_endorsed)" false
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And
                  (f Collector_past_epoch, Formula.Not (f Store_cert)),
                f Quorum_endorsed ))))

(* R2 contingency for the positive knowledge operand of S1(B) and S3(B):
   K_V1(quorum_endorsed) is NOT collapsed - it fails somewhere reachable.
   Witness: the initial state (E_pending, St_rec, Sg_close, B_avail), where the
   operand is plain false. *)
let k_quorum_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1(quorum_endorsed): knowledge is contingent"
        true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Quorum_endorsed)))))

(* R2 contingency for the positive knowledge operand of S2(C):
   K_V1(quorum_certified(some epoch-1 record)) is NOT collapsed either.
   Witness: (E_solo, St_rec, Sg_scan1, B_avail), which shares V1's view with
   (E_quorum3, St_rec, Sg_scan1, B_avail) and (E_alt, St_rec, Sg_scan1,
   B_avail) - the existential is open there. *)
let k_some_record_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(quorum_certified(some)): knowledge is contingent" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Some_record_certified)))))

(* R2 non-singleton view class for S1(B)'s positive K. At the operative state
   w3 = (E_quorum3, St_cert, Sg_scan2, B_avail) the atom [Byz_endorsed] is
   FALSE, yet V1 cannot rule it out - because the V1-view class
   View_v1 (Sg_scan2, St_cert, B_avail) also contains the reachable world
   w4 = (E_quorum4, St_cert, Sg_scan2, B_avail). Two worlds, agreeing on
   [Quorum_endorsed] (so the K of S1(B) really does hold) and disagreeing on
   [Byz_endorsed] (so the class is provably not a singleton). Grounded in the
   aggregator's early break at quorum, epoch_votes.rs:103-110. *)
let cert_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (store_has_cert /\\ ~byz_endorsed /\\ ~K_v1(~byz_endorsed))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Store_cert, Formula.Not (f Byz_endorsed)),
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Byz_endorsed))) ))))

(* R2 non-singleton view class for S2(C)'s positive K, at the cursor-past-epoch
   states specifically. Same two worlds as above -
   (E_quorum3, St_cert, Sg_scan2, B_avail) and
   (E_quorum4, St_cert, Sg_scan2, B_avail) - now selected by the
   [Collector_past_epoch] atom, so the class carrying S2(C)'s knowledge (and
   S3(B)'s [Af] target) is independently shown to hold two reachable worlds.
   This is where S2(C)'s non-degenerate content lives; on the divergent
   [E_alt] branch its class is a singleton, as the statement doc says. *)
let cursor_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (cursor>1 /\\ ~byz_endorsed /\\ ~K_v1(~byz_endorsed))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Collector_past_epoch, Formula.Not (f Byz_endorsed)),
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Byz_endorsed))) ))))

(* R3 ignorance witness for S2(A) and S3(A): the SETTLED certless window, i.e.
   outside V1's own tally-quorum window. The colliding pair is
   u = (E_solo, St_rec, Sg_scan1, B_avail) and
   v = (E_quorum3, St_rec, Sg_scan1, B_avail) - both reachable, both projecting
   to View_v1 (Sg_scan1, St_rec, B_avail), disagreeing on [quorum_endorsed]
   (the divergent world (E_alt, St_rec, Sg_scan1, B_avail) is in the same
   class). So at v a super-quorum really did endorse and V1 still cannot know
   it. The same pair also exists at (Sg_tally, B_avail), (Sg_boot, B_avail),
   (Sg_scan0, B_avail) and (Sg_scan1, B_spent). *)
let ignorance_witness_certless_gap () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (~store_has_cert /\\ ~tally_quorum_held /\\ quorum_endorsed /\\ \
         ~K_v1(quorum_endorsed))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And
                  ( Formula.And
                      (Formula.Not (f Store_cert), Formula.Not (f Tally_quorum_held)),
                    f Quorum_endorsed ),
                Formula.Not (Formula.K (Validator.V1, f Quorum_endorsed)) ))))

(* The guard in S2(A) and S3(A) is load-bearing, not decoration: inside the
   [reached_quorum]-but-unpersisted window (epoch_votes.rs:103-104, the save is
   at :159) V1's DB is certless AND V1 knows the super-quorum endorsement,
   because every counted vote cleared the handler's BLS verify
   (handler.rs:452-461). Witness: (E_quorum3, St_rec, Sg_tally_quorum, B_avail)
   and (E_quorum4, St_rec, Sg_tally_quorum, B_avail) are the whole class, and
   both endorse. Dropping the guard would therefore make both conjuncts FALSE
   of this model, as they are of the real system. *)
let tally_quorum_window_knows () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (tally_quorum_held /\\ ~store_has_cert /\\ K_v1(quorum_endorsed))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Tally_quorum_held, Formula.Not (f Store_cert)),
                Formula.K (Validator.V1, f Quorum_endorsed) ))))

(* The divergent branch is reachable, which is why S2 claims only "some record
   was certified" at cursor>1: at (E_alt, St_rec, Sg_scan2, B_avail) the
   committee certified R1' <> R1, the fetched pair verified
   (state-sync/src/epoch.rs:100-103), the cursor advanced (:115), and yet
   [get_epoch_by_number(1)] still answers (R1, None) because the certificate
   was filed under [digest(R1')] (epoch_records.rs:601, :611-614) and is read
   back under [digest(R1)] (:374-375). *)
let divergent_cursor_advance_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (cursor>1 /\\ ~store_has_cert /\\ quorum_certified(some) /\\ \
         ~quorum_endorsed)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And
                  (f Collector_past_epoch, Formula.Not (f Store_cert)),
                Formula.And
                  (f Some_record_certified, Formula.Not (f Quorum_endorsed)) ))))

(* The Byzantine sub-quorum offer is reachable AND defeated pristine: the
   adversary spends its one answer (byz_cert_delivered) on a branch where no
   super-quorum exists, and V1's DB still holds no certificate afterwards -
   [verify_with_cert] refused it at epoch.rs:84 and the collector logged and
   retried (epoch.rs:129-136). This is the [Ef] conjunct deliberately kept OUT
   of S1's formula (it would make S1 spuriously refuted by the two mutations
   that make the offer unreachable), discharged here instead. *)
let byz_offer_reachable_and_defeated () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (byz_cert_delivered /\\ ~quorum_endorsed /\\ ~store_has_cert)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Byz_cert_delivered,
                Formula.And
                  (Formula.Not (f Quorum_endorsed), Formula.Not (f Store_cert))
              ))))

let () =
  Alcotest.run "epoch_record"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Epoch_record_statements.name `Quick
              (prove_one st))
          Epoch_record_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "cert-implies-quorum" `Quick cert_implies_quorum;
          Alcotest.test_case "cursor-never-passes-uncertified-epoch" `Quick
            cursor_never_passes_uncertified_epoch;
          Alcotest.test_case "certless-completion-means-divergence" `Quick
            certless_completion_means_divergence;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-quorum-contingent" `Quick k_quorum_contingent;
          Alcotest.test_case "k-some-record-contingent" `Quick
            k_some_record_contingent;
          Alcotest.test_case "cert-class-not-singleton" `Quick
            cert_class_not_singleton;
          Alcotest.test_case "cursor-class-not-singleton" `Quick
            cursor_class_not_singleton;
          Alcotest.test_case "ignorance-witness-certless-gap" `Quick
            ignorance_witness_certless_gap;
          Alcotest.test_case "tally-quorum-window-knows" `Quick
            tally_quorum_window_knows;
          Alcotest.test_case "divergent-cursor-advance-reachable" `Quick
            divergent_cursor_advance_reachable;
          Alcotest.test_case "byz-offer-reachable-and-defeated" `Quick
            byz_offer_reachable_and_defeated;
        ] );
    ]
