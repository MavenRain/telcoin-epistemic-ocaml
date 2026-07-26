(** The VERIF_PROV family (S1 storage weak-until, S2 known-but-anonymous quorum,
    S3 failed-dependent quarantine) proves on the pristine {!Verif_prov_model}
    through [prove_nonvacuous] (so each antecedent is also checked reachable),
    the reachable graph stays in its justified band, the gates the family rests
    on really do forbid the states they are claimed to forbid, and the epistemic
    layer is genuinely partial-information.

    R2 and R3 are discharged here explicitly. The family has exactly ONE positive
    knowledge conjunct - [K_V1(endorsed_by_quorum(C))] in S2 conjunct (A) - which
    gets both a contingency test ([k-c-endorsed-contingent]: the knowledge is
    reachable-false somewhere, so it did not collapse) and a non-singleton
    view-class test ([k-class-nonsingleton] plus its dual): at an operative state
    V1 can rule out neither "the third signer was V3" nor its negation, which is
    only possible if its view class holds at least two reachable worlds. Those
    same two rows are the R3 ignorance witnesses for S2 conjunct (B), and
    [ignorance-at-mark-time] is the R3 witness for S3 conjunct (B). *)

open Telcoin_epistemic
open Verif_prov_model

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
        (st.Verif_prov_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Verif_prov_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Verif_prov_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The operative state of S2: the pre-stamped parent has been stored. *)
let operative = Formula.And (f Stored_c, f Marked_indirect_c)

(* Loose product bound: 5 pipeline steps x 4 chunk dispositions x 3 store
   contents x 2 dep_genuine x 2 peer_claim x 3 endorsements = 720. The pristine
   reachable set is exactly 41: the single Ingress state plus the ten
   peer-chosen batch configurations allowed by the vote-path premise (4 with
   dep_genuine = true, where the premise forces c_endorse in {Q_v2, Q_v3}, and 6
   with dep_genuine = false) times the four remaining pipeline steps, each
   configuration's cone being a deterministic chain. All three mutants are also
   exactly 41 - the mutations reroute edges, they do not add configurations. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 720))

(* The vote-path premise, observed end to end: nothing that reaches V1's
   certificate store pristine is a certificate whose header no quorum signed.
   This is the whole point of the chunk-abort discipline plus the leaf direct
   verification; every mutation makes it satisfiable. *)
let stored_implies_endorsed () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (stored(C) /\\ ~endorsed_by_quorum(C))" false
        (Checker.satisfiable sys
           (Formula.And (f Stored_c, Formula.Not (f C_endorsed)))))

(* The state S1 conjunct (A) forbids, asserted directly as unreachable: C in the
   store while the dependent's aggregate signature has not been verified. This
   is exactly what the `?` at cert_validator.rs:260 and the leaf-verification
   disjunct at :308 jointly enforce. *)
let no_storage_without_dependent_crypto () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (stored(C) /\\ ~dep_aggregate_verified(D))" false
        (Checker.satisfiable sys
           (Formula.And (f Stored_c, Formula.Not (f Dep_crypto_verified)))))

(* The state S3 conjunct (A) forbids: a failed direct verification coexisting
   with anything from that response in the store. cert_manager's is_verified gate
   stops the leaf D but NOT the pre-stamped parent C (VerifiedIndirectly
   satisfies is_verified, certificate.rs:356-364), so the collection-wide abort
   is the only thing making this unreachable. *)
let failed_check_stores_nothing () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (dep_aggregate_failed(D) /\\ (stored(C) \\/ stored(D)))" false
        (Checker.satisfiable sys
           (Formula.And
              (f Dep_crypto_failed, Formula.Or (f Stored_c, f Stored_d)))))

(* R2 contingency for the family's ONLY positive knowledge conjunct,
   K_V1(endorsed_by_quorum(C)) in S2 conjunct (A): its complement is reachable,
   so the operand is not plain truth under the view partition and the knowledge
   did not collapse. Witness: any Classified state, whose V1-view class holds all
   five configurations sharing its peer_claim - including a No_quorum world. *)
let k_c_endorsed_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(endorsed_by_quorum(C)): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Marked_indirect_c,
                Formula.Not (Formula.K (Validator.V1, f C_endorsed)) ))))

(* R2 non-singleton view class for S2 conjunct (A), and simultaneously the R3
   ignorance witness for the second half of S2 conjunct (B). The atom q =
   signed_by(V3,C) is pinned FALSE at the witnessing state and V1 still cannot
   conclude ~q there - which is possible ONLY if its view class holds a second
   reachable world where q is true, so the class is provably not a singleton.
   Pinning ~q in the formula matters: without it the row is satisfiable by a
   state where q merely happens to hold, which proves nothing about the class
   size. The two worlds are w_a = (Settled, Ck_pass_real, St_cd, dep_genuine =
   true, c_endorse = Q_v2 = {V0,V1,V2}) and w_b = the same with c_endorse = Q_v3
   = {V0,V1,V3}: they agree on everything V1 sees (step, chunk outcome, store,
   peer tag) and disagree on signed_by(V3,C). *)
let k_class_nonsingleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (stored(C) /\\ marked(C) /\\ ~signed_by(V3,C) /\\ \
         ~K_v1(~signed_by(V3,C)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( operative,
                Formula.And
                  ( Formula.Not (f C_signed_by_v3),
                    Formula.Not
                      (Formula.K (Validator.V1, Formula.Not (f C_signed_by_v3)))
                  ) ))))

(* The dual half, pinned the other way: at a state where the third signer really
   WAS V3, V1 still cannot conclude it. Same colliding pair w_a / w_b read in
   reverse, so the class is provably non-singleton from both sides and both
   ignorance conjuncts of S2 (B) have a genuine R3 witness. *)
let k_class_nonsingleton_dual () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (stored(C) /\\ marked(C) /\\ signed_by(V3,C) /\\ \
         ~K_v1(signed_by(V3,C)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( operative,
                Formula.And
                  ( f C_signed_by_v3,
                    Formula.Not (Formula.K (Validator.V1, f C_signed_by_v3)) )
              ))))

(* R3 ignorance witness for S3 conjunct (B): while C carries the
   VerifiedIndirectly stamp but is not yet stored, V1 does not know the parent
   was endorsed - the stamp is a pure tag rewrite, not evidence. The operand is
   pinned TRUE at the witnessing state, so ~K there forces a second class member
   where it is false: the colliding pair at (Classified, Obs_no_verification,
   St_empty, peer_claim = false) is u_a = (dep_genuine = true, c_endorse = Q_v2),
   where endorsed_by_quorum(C) holds, and u_b = (dep_genuine = false, c_endorse =
   No_quorum), where it does not; V1's view is identical in both. *)
let ignorance_at_mark_time () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (marked(C) /\\ ~stored(C) /\\ endorsed_by_quorum(C) /\\ \
         ~K_v1(endorsed_by_quorum(C)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Marked_indirect_c,
                Formula.And
                  ( Formula.Not (f Stored_c),
                    Formula.And
                      ( f C_endorsed,
                        Formula.Not (Formula.K (Validator.V1, f C_endorsed)) )
                  ) ))))

(* S1 conjunct (B) as a standalone witness: the mark-before-evidence window is
   real, not modelled away. classify stamps C VerifiedIndirectly at
   cert_validator.rs:293 while :260's chunk verification has not yet run, so
   S1's storage weak-until is not vacuously true by absence of the window. *)
let mark_precedes_evidence () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (marked(C) /\\ ~dep_aggregate_verified(D))" true
        (Checker.satisfiable sys
           (Formula.And
              (f Marked_indirect_c, Formula.Not (f Dep_crypto_verified)))))

(* S3's antecedent really can fire on a forged batch: a response whose dependent
   fails verification and whose parent no quorum ever endorsed is reachable, so
   the quarantine conjunct is quantifying over a live case. *)
let forged_batch_rejected () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (dep_aggregate_failed(D) /\\ ~endorsed_by_quorum(C))" true
        (Checker.satisfiable sys
           (Formula.And (f Dep_crypto_failed, Formula.Not (f C_endorsed)))))

(* S1 conjunct (C) as a standalone witness: the ingress tag reset NEUTRALISES a
   peer-asserted verified tag, it does not reject the response.
   aggregated_signature keeps the signature bytes for every tag but Genesis
   (certificate.rs:329-337), so honest traffic that arrives tagged is still
   stored - S1 (A) is not achieved by discarding tagged responses. *)
let tagged_traffic_still_stored () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (peer_claims_verified /\\ stored(C))" true
        (Checker.satisfiable sys
           (Formula.And (f Peer_claims_verified, f Stored_c))))

let () =
  Alcotest.run "verif_prov"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Verif_prov_statements.name `Quick
              (prove_one st))
          Verif_prov_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "stored-implies-endorsed" `Quick
            stored_implies_endorsed;
          Alcotest.test_case "no-storage-without-dependent-crypto" `Quick
            no_storage_without_dependent_crypto;
          Alcotest.test_case "failed-check-stores-nothing" `Quick
            failed_check_stores_nothing;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-c-endorsed-contingent" `Quick
            k_c_endorsed_contingent;
          Alcotest.test_case "k-class-nonsingleton" `Quick k_class_nonsingleton;
          Alcotest.test_case "k-class-nonsingleton-dual" `Quick
            k_class_nonsingleton_dual;
          Alcotest.test_case "ignorance-at-mark-time" `Quick
            ignorance_at_mark_time;
          Alcotest.test_case "mark-precedes-evidence" `Quick
            mark_precedes_evidence;
          Alcotest.test_case "forged-batch-rejected" `Quick
            forged_batch_rejected;
          Alcotest.test_case "tagged-traffic-still-stored" `Quick
            tagged_traffic_still_stored;
        ] );
    ]
