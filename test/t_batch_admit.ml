(** The three BATCH-ADMIT statements prove on the pristine model through
    [prove_nonvacuous] (so each antecedent is also checked reachable), the
    reachable graph stays in its justified band, the two content gates really
    do make their forbidden states unreachable, and the epistemic layer is
    genuinely partial-information:

    - the refusing worker's knowledge of the committee-wide gated verdict is
      contingent (it fails somewhere reachable) and its operative view class is
      NOT a singleton - the same view class contains a reachable state in which
      the peer holds the batch and one in which it does not;
    - the unvalidated route that would make a naive reading of the blob gate
      false is present and reachable: a blob-carrying batch and an
      over-ceiling batch each reach an honest worker's cache through the
      digest-only prefetch, while neither is ever admitted through the
      content-gated path;
    - each ignorance conjunct has a concrete witness pair - the peer's refusal
      versus its silence, and the peer's early stamp versus its late one. *)

open Telcoin_epistemic
open Batch_admit_model

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
        (st.Batch_admit_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Batch_admit_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Batch_admit_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** One [satisfiable] assertion on the pristine system. *)
let sat label expected formula () =
  with_sys (fun sys ->
      Alcotest.(check bool) label expected (Checker.satisfiable sys formula))

(* Justified bound: three content classes branch at the root; within one class
   the gate-side worker's report leg takes at most two reachable values (a
   class either passes every check or fails one, never both), the fetch-side
   worker has at most seven configurations (an empty cache slot, or a held copy
   from one of three routes with one of two stamps), and the store-key binding
   is determined by whether any copy has been stored. 3 x 2 x 7 = 42. The
   actual pristine reachable set is 36 states (36 under No_gas_ceiling, 36
   under No_blob_reject, 34 under Digest_covers_received_at, which loses the
   two relay states). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in the justified band: " ^ Int.to_string n)
        true
        (Int.compare n 42 <= 0 && Int.compare n 0 > 0))

(** The trigger of S1: an over-ceiling batch whose report leg to the gate-side
    worker has resolved. *)
let operative = Formula.And (f Content_over_ceiling, f Reported_1)

(** The operand of S1's positive [K]: nobody admitted the batch through the
    content-gated path. *)
let no_gated_admission =
  Formula.And (Formula.Not (f Gated_admit_1), Formula.Not (f Gated_admit_2))

(** Some worker admitted the batch through the content-gated path. *)
let some_gated_admission = Formula.Or (f Gated_admit_1, f Gated_admit_2)

let () =
  Alcotest.run "batch_admit"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Batch_admit_statements.name `Quick
              (prove_one st))
          Batch_admit_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "no-gated-admission-of-a-blob-batch" `Quick
            (sat
               "EF (gated-admit /\\ carries-blob) - the validator.rs:198-206 \
                gate"
               false
               (Formula.And (some_gated_admission, f Content_carries_blob)));
          Alcotest.test_case "no-gated-admission-over-the-ceiling" `Quick
            (sat
               "EF (gated-admit /\\ over-ceiling) - the validator.rs:177-182 \
                gate"
               false
               (Formula.And (some_gated_admission, f Content_over_ceiling)));
          Alcotest.test_case "every-stored-copy-content-addresses" `Quick
            (sat "EF ~(key = digest(stored)) - the sealed_batch.rs:86 skip"
               false
               (Formula.Not (f Key_matches_digest)));
          Alcotest.test_case "the-unvalidated-route-really-stores-a-blob" `Quick
            (sat
               "EF (holds_v2 /\\ carries-blob) - handler.rs:181-208 has no \
                validator call"
               true
               (Formula.And (f Holds_2, f Content_carries_blob)));
          Alcotest.test_case "the-unvalidated-route-really-stores-over-ceiling"
            `Quick
            (sat "EF (holds_v2 /\\ over-ceiling) - the same bypass" true
               (Formula.And (f Holds_2, f Content_over_ceiling)));
          Alcotest.test_case "a-refusing-worker-can-still-end-up-holding-it"
            `Quick
            (sat
               "EF (refused_v2 /\\ holds_v2) - handler.rs:167-170 only checks \
                the cache"
               true
               (Formula.And (f Refused_2, f Holds_2)));
          Alcotest.test_case "relay-out-of-a-stamped-copy-is-reachable" `Quick
            (sat "EF relay-held_v2" true (f Relay_held_2));
        ] );
      ( "contingency",
        [
          (* S1's positive K: contingent, not collapsed. *)
          Alcotest.test_case "s1-k-is-contingent" `Quick
            (sat "EF ~K_V1 (no gated admission anywhere)" true
               (Formula.Not (Formula.K (Validator.V1, no_gated_admission))));
          (* S1's positive K: the operative V1-view class is NOT a singleton.
             [holds_v2] is false at an operative state, and V1 still does not
             know it is false, which is only possible if another reachable
             state shares V1's view and satisfies it. *)
          Alcotest.test_case "s1-k-operative-class-is-not-a-singleton" `Quick
            (sat
               "EF (over-ceiling /\\ reported_v1 /\\ ~K_V1 (~holds_v2))" true
               (Formula.And
                  ( operative,
                    Formula.Not
                      (Formula.K (Validator.V1, Formula.Not (f Holds_2))) )));
          Alcotest.test_case "s1-k-operative-state-with-holds_v2-false" `Quick
            (sat "EF (over-ceiling /\\ reported_v1 /\\ ~holds_v2)" true
               (Formula.And (operative, Formula.Not (f Holds_2))));
          (* S1's ignorance witness pair: same V1 view, opposite [holds_v2]. *)
          Alcotest.test_case "s1-ignorance-witness-peer-holds" `Quick
            (sat "EF (over-ceiling /\\ refused_v1 /\\ holds_v2)" true
               (Formula.And
                  (Formula.And (f Content_over_ceiling, f Refused_1), f Holds_2)));
          Alcotest.test_case "s1-ignorance-witness-peer-empty" `Quick
            (sat "EF (over-ceiling /\\ refused_v1 /\\ ~holds_v2)" true
               (Formula.And
                  ( Formula.And (f Content_over_ceiling, f Refused_1),
                    Formula.Not (f Holds_2) )));
          (* S2's ignorance witness pair: same V2 view, opposite
             [refused_v1]. *)
          Alcotest.test_case "s2-ignorance-witness-peer-refused" `Quick
            (sat "EF (holds_v2 /\\ carries-blob /\\ refused_v1)" true
               (Formula.And
                  ( Formula.And (f Holds_2, f Content_carries_blob),
                    f Refused_1 )));
          Alcotest.test_case "s2-ignorance-witness-peer-never-asked" `Quick
            (sat "EF (holds_v2 /\\ carries-blob /\\ ~reported_v1)" true
               (Formula.And
                  ( Formula.And (f Holds_2, f Content_carries_blob),
                    Formula.Not (f Reported_1) )));
          Alcotest.test_case "s2-ignorance-holds" `Quick
            (sat "EF (holds_v2 /\\ carries-blob /\\ ~K_V2 (refused_v1))" true
               (Formula.And
                  ( Formula.And (f Holds_2, f Content_carries_blob),
                    Formula.Not (Formula.K (Validator.V2, f Refused_1)) )));
          (* S3's ignorance witness pair: same V1 view, opposite stamp. *)
          Alcotest.test_case "s3-ignorance-witness-late-stamp" `Quick
            (sat "EF (gated-admit_v1 /\\ holds_v2 /\\ received-at_v2 = late)"
               true
               (Formula.And
                  (Formula.And (f Gated_admit_1, f Holds_2), f Tick2_late)));
          Alcotest.test_case "s3-ignorance-witness-early-stamp" `Quick
            (sat "EF (gated-admit_v1 /\\ holds_v2 /\\ received-at_v2 = early)"
               true
               (Formula.And
                  ( Formula.And (f Gated_admit_1, f Holds_2),
                    Formula.Not (f Tick2_late) )));
          Alcotest.test_case "s3-ignorance-both-directions" `Quick
            (sat
               "EF (gated-admit_v1 /\\ holds_v2 /\\ ~K_V1 (late) /\\ ~K_V1 \
                (~late))"
               true
               (Formula.And
                  ( Formula.And (f Gated_admit_1, f Holds_2),
                    Formula.And
                      ( Formula.Not (Formula.K (Validator.V1, f Tick2_late)),
                        Formula.Not
                          (Formula.K
                             (Validator.V1, Formula.Not (f Tick2_late))) ) )));
        ] );
    ]
