(** The EPOCH_REWARD family (S1 blockless credit, S2 crash-rebuild partition,
    S3 batch-less boundary seal) proves on the pristine {!Epoch_reward_model}
    through [prove_nonvacuous] (so each antecedent is also checked reachable),
    the reachable graph stays in its justified band, the invariants the guards
    enforce hold, and the epistemic layer is genuinely partial-information: all
    three positive knowledge operands are contingent AND sit in non-singleton
    view classes, and every ignorance conjunct has a reachable colliding pair.

    The [peer-vote-reachable] and [vote-implies-both-sealed] sanity cases are
    load-bearing for S3: they show the modelled seal acknowledgement (the epoch
    record vote, epoch_votes.rs:59-73 into :88-111) actually fires, so scoping
    S3's ignorance conjunct to the pre-vote window is a real restriction rather
    than a vacuous guard over a branch the model hardwired away. *)

open Telcoin_epistemic
open Epoch_reward_model

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
        (st.Epoch_reward_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Epoch_reward_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Epoch_reward_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: per node 4 phases x 3^3 ledgers x 2 sealed flags, two
   nodes, the peer's crash flag and V1's vote flag - a product far larger than
   anything the transition relation can reach. The pristine reachable set is
   exactly 22: V1's phase determines its whole node state (4 values), the peer
   has 5 configurations (its 4 never-crashed states plus the single
   (P3,(1,1,1),sealed) state every crash point rebuilds to), 4 x 5 = 20, plus the
   2 states where V1 has additionally matched the peer's epoch vote (only
   reachable with V1 at P3 sealed and the peer in one of its 2 sealed
   configurations). Kept as a band so the test states an honest bound rather than
   a fitted constant. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 64))

(* The watermark guard's contract (consensus_pack.rs:1287-1289): no reachable
   state has the peer crediting one committed round twice. This is exactly the
   state {!No_catchup_watermark} makes reachable. *)
let no_double_credit_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (v2 credited a round twice)" false
        (Checker.satisfiable sys (f V2_double_credit)))

(* The credit at payload_builder.rs:30 sits above the skip, so a sealed ledger
   always includes the blockless round: the skipped output is never the round
   that gets lost. *)
let sealed_includes_blockless () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G (sealed_1 -> credited_blockless)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies (f V1_sealed, f V1_credited_blockless)))))

(* S1's antecedent is a real state, not a modelling artifact: V1 has consumed
   the batch-less non-closing output yet its executed-block watermark has not
   moved (recent_blocks.rs:36-60 pushes no block for a skipped round). *)
let credited_yet_blockless_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (consumed_blockless /\\ watermark_zero)" true
        (Checker.satisfiable sys
           (Formula.And (f V1_consumed_blockless, f V1_watermark_zero))))

(* R2 contingency, S1 conjunct B: the positive knowledge
   K_V1(sealed_2 -> credit_blockless_agrees) did NOT collapse into plain truth.
   It fails at v1 = (P0, (0,0,0), unsealed), whose view class contains the
   sealed peer holding (1,1,1): there the operand's antecedent is true and its
   consequent false. *)
let k_credit_agreement_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(sealed_2 -> credit_blockless_agrees)" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 ( Validator.V1,
                   Formula.Implies (f V2_sealed, f Credit_blockless_agrees) )))))

(* R2 non-singleton view class, S1 conjunct B. At the operative state
   v1 = (P1, (One,Zero,Zero), unsealed) - where V1_credited_blockless holds -
   V1 cannot rule out that the peer restarted, which is only possible if the
   class holds a second world. The two concrete worlds are
   w1 = (that v1, v2 = (P0,(Zero,Zero,Zero),unsealed), v2_restarted = false) and
   w2 = (that v1, v2 = (P3,(One,One,One),sealed), v2_restarted = true). *)
let k_credit_agreement_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (credited_blockless /\\ ~K_v1(~restarted_2))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f V1_credited_blockless,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f V2_restarted))) ))))

(* R2 contingency, S2 conjunct C: the positive knowledge
   K_V1(sealed_2 -> ledgers_equal) is contingent - it fails at
   v1 = (P1, (One,Zero,Zero), unsealed), whose class contains the sealed peer
   holding (One,One,One). V1 earns this knowledge only by sealing itself. *)
let k_ledger_agreement_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1(sealed_2 -> ledgers_equal)" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 (Validator.V1, Formula.Implies (f V2_sealed, f Ledgers_equal))))))

(* R2 non-singleton view class, S2 conjunct C. At the operative state
   v1 = (P3, (One,One,One), sealed) the class contains the never-crashed peer
   w1 = (that v1, v2 = (P3,(One,One,One),sealed), v2_restarted = false) and the
   crashed-and-rebuilt peer w2 = (that v1, v2 = (P3,(One,One,One),sealed),
   v2_restarted = true) - byte-identical ledgers, distinct worlds. *)
let k_ledger_agreement_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (sealed_1 /\\ ~K_v1(~restarted_2))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f V1_sealed,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f V2_restarted))) ))))

(* R3 ignorance witness, S2 conjunct C first half: a sealed V1 cannot conclude
   the peer crashed. Colliding pair: w1 and w2 above, same V1 view, disagreeing
   on restarted_2 - the crash leaves no wire trace at all (node.rs:189-268 and
   start_epoch.rs:71-107 are startup-local recovery). *)
let ignorance_peer_crashed () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (sealed_1 /\\ ~K_v1(restarted_2))" true
        (Checker.satisfiable sys
           (Formula.And
              (f V1_sealed, Formula.Not (Formula.K (Validator.V1, f V2_restarted))))))

(* R3 ignorance witness, S3 conjunct C: BEFORE the peer's epoch vote arrives,
   sealing is a purely local execution act, so a sealed V1 cannot know the peer
   has sealed. Colliding pair: (v1 = (P3,(One,One,One),sealed,no peer vote),
   v2 = (P3,(One,One,One),sealed)) and the same v1 with
   v2 = (P0,(Zero,Zero,Zero),unsealed). *)
let ignorance_peer_sealed_before_vote () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (sealed_1 /\\ ~saw_peer_vote /\\ ~K_v1(sealed_2))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f V1_sealed, Formula.Not (f V1_saw_peer_vote)),
                Formula.Not (Formula.K (Validator.V1, f V2_sealed)) ))))

(* The acknowledgement is REACHABLE, so S3 conjunct C's added [~saw_peer_vote]
   guard is a genuine scoping and not a vacuous weakening: the peer's epoch vote
   really does arrive in this model (epoch_votes.rs:59-73 into :88-111). Without
   this test the fix to the confirmed D7 finding would be indistinguishable from
   hardwiring the branch away again. *)
let peer_vote_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF saw_peer_vote" true
        (Checker.satisfiable sys (f V1_saw_peer_vote)))

(* Model sanity for the vote step's two preconditions: a matched epoch vote
   exists only once BOTH nodes have executed the closing block - the peer signs
   only after its own write_epoch_record (close_epoch.rs:231-248 into
   epoch_votes.rs:59-73) and V1 matches only against its OWN record's digest
   (epoch_votes.rs:88-96). *)
let vote_implies_both_sealed () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G (saw_peer_vote -> sealed_1 /\\ sealed_2)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 (f V1_saw_peer_vote, Formula.And (f V1_sealed, f V2_sealed))))))

(* R2 contingency, S3 conjunct D: the positive knowledge K_V1(sealed_2) is not
   rigid - it FAILS at every sealed state before the vote arrives, which is
   exactly what conjunct C asserts. *)
let k_peer_sealed_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1(sealed_2)" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f V2_sealed)))))

(* R2 non-singleton view class, S3 conjunct D. At the operative state
   v1 = (P3, (One,One,One), sealed, peer vote matched) the class still holds two
   worlds - the never-crashed peer and the crashed-and-rebuilt one - because the
   vote commits to [final_state] and [final_consensus] (close_epoch.rs:238-245),
   never to how the signer's in-memory accumulator was assembled. *)
let k_peer_sealed_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (saw_peer_vote /\\ ~K_v1(~restarted_2))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f V1_saw_peer_vote,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f V2_restarted))) ))))

let () =
  Alcotest.run "epoch_reward"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Epoch_reward_statements.name `Quick
              (prove_one st))
          Epoch_reward_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "no-double-credit-reachable" `Quick
            no_double_credit_reachable;
          Alcotest.test_case "sealed-includes-blockless" `Quick
            sealed_includes_blockless;
          Alcotest.test_case "credited-yet-blockless-reachable" `Quick
            credited_yet_blockless_reachable;
          Alcotest.test_case "peer-vote-reachable" `Quick peer_vote_reachable;
          Alcotest.test_case "vote-implies-both-sealed" `Quick
            vote_implies_both_sealed;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-credit-agreement-contingent" `Quick
            k_credit_agreement_contingent;
          Alcotest.test_case "k-credit-agreement-class-not-singleton" `Quick
            k_credit_agreement_class_not_singleton;
          Alcotest.test_case "k-ledger-agreement-contingent" `Quick
            k_ledger_agreement_contingent;
          Alcotest.test_case "k-ledger-agreement-class-not-singleton" `Quick
            k_ledger_agreement_class_not_singleton;
          Alcotest.test_case "ignorance-peer-crashed" `Quick
            ignorance_peer_crashed;
          Alcotest.test_case "ignorance-peer-sealed-before-vote" `Quick
            ignorance_peer_sealed_before_vote;
          Alcotest.test_case "k-peer-sealed-contingent" `Quick
            k_peer_sealed_contingent;
          Alcotest.test_case "k-peer-sealed-class-not-singleton" `Quick
            k_peer_sealed_class_not_singleton;
        ] );
    ]
