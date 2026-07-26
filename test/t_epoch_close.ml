(** The EPOCH_CLOSE family proves on the pristine {!Epoch_close_model} through
    [prove_nonvacuous] (so each antecedent is also checked reachable), the
    reachable graph stays in its justified band, the three gate invariants the
    family rests on hold (the pre-dial's zero-peer wait is unreachable, no
    stored certificate lacks a super-quorum, and a diverged member never ends
    the boundary certified), and the epistemic layer is genuinely partial
    information: both positive knowledge conjuncts are contingent AND sit in
    non-singleton view classes, and both ignorance conjuncts have concrete
    colliding pairs.

    Two of the contingency cases carry the repair of a confirmed faithfulness
    defect: [certless-open-reachable] and
    [unrelativised-opened-knowledge-fails] assert that an epoch pack really is
    opened with an uncertified record (run_epoch.rs:451-463, :518), so S3's
    acquired-record knowledge conjunct must be - and is - relativised to
    [holds_foreign_record]. They fail loudly if the model ever stops carrying
    that branch. *)

open Telcoin_epistemic
open Epoch_close_model

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
        (st.Epoch_close_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Epoch_close_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Epoch_close_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: the two scenario cones are disjoint and each stage
   admits only a handful of (store, tally, cand, peers) combinations, so a
   generous band is 96. The pristine reachable set is exactly 51: 1 root + 28
   branch-A states (2 byz x (8 for truth = Tr_own, 6 for truth = Tr_far)) + 8
   branch-A opened states (one per settled state: [run_epochs] loops into
   epoch e and [open_epoch_pack] finds the record present, run_epoch.rs:219,
   :451-463, :518) + 14 branch-B states (4 entry openings, then 2 each of
   wait / wait-with-sound / wait-with-lone / halt / open). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 96))

(* The pre-dial's contract (run_epoch.rs:487-503): a node that reaches the
   missing-record wait ALWAYS has peers, because the zero-peer entry line
   dials the whole committee before blocking. This is the state
   No_committee_predial makes reachable, and its unreachability is what makes
   S3's EF-opened conjunct true. *)
let zero_peer_wait_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (waiting /\\ ~peers_connected)" false
        (Checker.satisfiable sys
           (Formula.And (f Waiting, Formula.Not (f Peers_connected)))))

(* The super-quorum count's contract (epoch.rs:84-88): every certificate that
   reaches the store carries at least 2n/3+1 genuine committee signatures on
   the record it is attached to. This is the state No_cert_quorum_count makes
   reachable, and its unreachability is the non-epistemic shadow of S1 c1. *)
let stored_cert_always_quorum_backed () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (holds_cert /\\ ~quorum_backs_stored)" false
        (Checker.satisfiable sys
           (Formula.And (f Holds_cert, Formula.Not (f Quorum_backs_stored)))))

(* The certificate index's content-addressing (written under the FETCHED
   record's digest at epoch_records.rs:601, :612-614; read back by the STORED
   record's digest at :374-375): a member whose execution diverged and that
   never reached quorum on its own digest ends the boundary with NO certificate
   attached, because the fetched cert is filed under the PEER's digest. This is
   the state No_cert_digest_binding makes reachable. *)
let diverged_member_never_certified () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (settled /\\ tally_short /\\ committee_chose_other /\\ holds_cert)"
        false
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Settled; f Tally_short; f Committee_chose_other; f Holds_cert;
              ])))

(* R2 contingency, S1 c1: [K_V1(quorum_backs_stored)] is not collapsed - at a
   settled state with an uncertified own record the operand is false, so the
   knowledge fails there. The gate, not structure, is what makes it hold at the
   certified states. *)
let k_quorum_contingent_branch_a () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (settled /\\ ~K_v1(quorum_backs_stored))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Settled,
                Formula.Not
                  (Formula.K (Validator.V1, f Quorum_backs_stored)) ))))

(* R2 contingency, S3 c4: same operand on the acquisition branch - while V1 is
   still blocked in the wait nothing is stored, so the knowledge fails. *)
let k_quorum_contingent_branch_b () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (waiting /\\ ~K_v1(quorum_backs_stored))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Waiting,
                Formula.Not
                  (Formula.K (Validator.V1, f Quorum_backs_stored)) ))))

(* R2 non-singleton view class for S3 c4. [byz_fourth_vote] is FALSE at the
   operative state, yet V1 cannot rule it out - which is only possible if the
   class has another world. The two concrete worlds are
   (Sg_open, St_far_cert, Tl_pending, Cd_none, Pr_some, Tr_far, Bz_silent,
   Hd_quorum) and its twin with byz = Bz_signed: the fourth committee member
   cast a vote for the endorsed record that never reached V1 before the
   collector timed out (epoch_votes.rs:130-140). *)
let opened_view_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (opened /\\ ~K_v1(~byz_fourth_vote)): class has >= 2 worlds" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Opened,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Byz_fourth_vote)))
              ))))

(* R2 non-singleton view class for S1 c1 at its branch-A operative state. The
   two concrete worlds are (Sg_settled, St_own_cert, Tl_quorum, Cd_none,
   Pr_some, Tr_own, Bz_silent, Hd_quorum) and its byz = Bz_signed twin: V1
   reached quorum on three signatures and never learned whether the fourth
   member also voted. *)
let settled_cert_view_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (settled /\\ holds_cert /\\ ~K_v1(~byz_fourth_vote)): class has >= 2 worlds"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Settled;
                f Holds_cert;
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Byz_fourth_vote)));
              ])))

(* The relativisation of S3 c4 is load-bearing, half one: an epoch pack really
   is opened with an UNCERTIFIED record. [open_epoch_pack]'s found-record
   branch (run_epoch.rs:451-463) imposes no certificate requirement before
   [consensus_chain.new_epoch] at :518, and a committee member's own record is
   written certless by [save_record] (close_epoch.rs:238-249) and can stay
   certless when quorum fails and all five recovery fetches fail
   (epoch_votes.rs:188-231, :225-231). *)
let certless_open_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (opened /\\ ~holds_cert)" true
        (Checker.satisfiable sys
           (Formula.And (f Opened, Formula.Not (f Holds_cert)))))

(* The relativisation of S3 c4 is load-bearing, half two: the UNrelativised
   AG( opened -> K_v1(quorum_backs_stored) ) is false on the pristine model,
   because at the certless open above the operand itself fails. This is the
   confirmed faithfulness defect the relativisation repairs; if this ever
   starts failing, the model has stopped modelling the found-record branch. *)
let unrelativised_opened_knowledge_fails () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (opened /\\ ~K_v1(quorum_backs_stored))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Opened,
                Formula.Not (Formula.K (Validator.V1, f Quorum_backs_stored))
              ))))

(* R3 ignorance witness for S1 c2. The colliding pair is
   (Sg_recover, St_own, Tl_short, Cd_sound, Pr_some) and
   (Sg_recover, St_own, Tl_short, Cd_lone, Pr_some): identical V1 view (the
   candidate is projected as the bare "a response is in hand" bit, because
   request_epoch_cert returns unvalidated peer bytes, network/mod.rs:809-829),
   disagreeing on candidate_sound. *)
let ignorance_candidate_flavour () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (response_in_hand /\\ ~K_v1(sound) /\\ ~K_v1(~sound))" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Response_in_hand;
                Formula.Not (Formula.K (Validator.V1, f Candidate_sound));
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Candidate_sound)));
              ])))

(* R3 ignorance witness for S2 c3. The colliding pair, both reachable and
   sharing V1's entire view (Sg_settled, St_own, Tl_short, no response,
   Pr_some): truth = Tr_own (the committee DID endorse V1's record, V1 simply
   never saw enough votes and all five recovery fetches failed) and
   truth = Tr_far (V1's execution diverged and the idempotent save left it
   uncertified). *)
let ignorance_own_divergence () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (settled /\\ tally_short /\\ ~K_v1(other) /\\ ~K_v1(~other))" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Settled;
                f Tally_short;
                Formula.Not
                  (Formula.K (Validator.V1, f Committee_chose_other));
                Formula.Not
                  (Formula.K
                     (Validator.V1, Formula.Not (f Committee_chose_other)));
              ])))

let () =
  Alcotest.run "epoch_close"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Epoch_close_statements.name `Quick
              (prove_one st))
          Epoch_close_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "zero-peer-wait-unreachable" `Quick
            zero_peer_wait_unreachable;
          Alcotest.test_case "stored-cert-always-quorum-backed" `Quick
            stored_cert_always_quorum_backed;
          Alcotest.test_case "diverged-member-never-certified" `Quick
            diverged_member_never_certified;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-quorum-contingent-branch-a" `Quick
            k_quorum_contingent_branch_a;
          Alcotest.test_case "k-quorum-contingent-branch-b" `Quick
            k_quorum_contingent_branch_b;
          Alcotest.test_case "opened-view-class-not-singleton" `Quick
            opened_view_class_not_singleton;
          Alcotest.test_case "settled-cert-view-class-not-singleton" `Quick
            settled_cert_view_class_not_singleton;
          Alcotest.test_case "certless-open-reachable" `Quick
            certless_open_reachable;
          Alcotest.test_case "unrelativised-opened-knowledge-fails" `Quick
            unrelativised_opened_knowledge_fails;
          Alcotest.test_case "ignorance-candidate-flavour" `Quick
            ignorance_candidate_flavour;
          Alcotest.test_case "ignorance-own-divergence" `Quick
            ignorance_own_divergence;
        ] );
    ]
