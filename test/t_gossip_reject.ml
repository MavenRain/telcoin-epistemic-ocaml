(** The GOSSIP_REJECT family (S1 knowably-guilty relayer, S2 unjudgeable
    forwarder, S3 ignorance-absorbing committee exemption) proves on the
    pristine {!Gossip_reject_model} through [prove_nonvacuous] (so every
    antecedent is also checked reachable), the reachable graph stays in its
    justified band, the four attribution invariants the reject path enforces
    hold, and the epistemic layer is genuinely partial-information: the one
    positive knowledge operand is contingent AND its view class is provably not
    a singleton, and every ignorance conjunct has a reachable colliding pair. *)

open Telcoin_epistemic
open Gossip_reject_model

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
        (st.Gossip_reject_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Gossip_reject_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Gossip_reject_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 4 pipeline stages x 2 payload classes x 4 author
   standings x 2 hidden relayer maps = 64 (the three derived fields rdev,
   charge and arep are functions of those, so they multiply nothing). The
   pristine reachable set is exactly 49 = 1 + 3 * 16: the single Quiet root
   plus the 16 deliveries carried through Inbound, Settled and Rotated. All
   three mutants are 49 too - every mutation relabels, none branches. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 64))

(* S1 conjunct (C): RejectReason::TooLarge maps only to FatalRelayer or Skip
   (consensus.rs:2092-2093), so an oversized delivery NEVER charges the author.
   The No_receive_size_gate mutation makes this state reachable. *)
let oversized_never_charges_author () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (oversized /\\ charged(A))" false
        (Checker.satisfiable sys
           (Formula.And (f Payload_over, f Charged_author))))

(* S2 conjunct (A): RejectReason::UnauthorizedAuthor maps only to FatalAuthor
   or Skip (consensus.rs:2094-2095), so an in-bounds reject NEVER charges the
   forwarder. The No_reject_attribution_split mutation makes this reachable. *)
let in_bounds_denied_never_charges_relayer () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (~oversized /\\ unauthorized_author /\\ charged(R))" false
        (Checker.satisfiable sys
           (Formula.conj
              [
                Formula.Not (f Payload_over); f Authz_denied; f Charged_relayer;
              ])))

(* S1 conjunct (A) at the state level: because the size bound is a compile-time
   constant every honest node applies (config/network.rs:98-112), an oversized
   delivery is ALWAYS relayer misbehavior pristine. This is what turns the
   visible evidence into knowledge; No_receive_size_gate breaks it. *)
let oversized_implies_relayer_deviation () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (oversized /\\ ~deviated(R))" false
        (Checker.satisfiable sys
           (Formula.And (f Payload_over, Formula.Not (f Relayer_deviated)))))

(* S3 conjunct (A): the TrustBasis exemption (peer.rs:218-233) means a peer in
   a tracked committee slot is never banned by the charge, even though the
   modelled sibling repair (the Rotated apply_committee_membership unban) is
   live. No_committee_exemption makes this state reachable at Settled. *)
let committee_author_never_banned () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (committee(A) /\\ banned(A))" false
        (Checker.satisfiable sys
           (Formula.And (f Author_in_committee, f Author_banned))))

(* S3 conjunct (A) is not vacuous: a ban really is reachable in this model. The
   Auth_rogue scenario sits in no tracked slot and is not allowlisted, so its
   Charge_author lands on the score model and reaches Rep_banned at Settled. *)
let author_ban_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF banned(A)" true
        (Checker.satisfiable sys (f Author_banned)))

(* S3's antecedent is reachable: the stale-but-tracked committee authors are
   charged (consensus.rs:2094 -> :1075-1088) while sitting in a slot. *)
let charged_committee_author_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (charged(A) /\\ committee(A))" true
        (Checker.satisfiable sys
           Gossip_reject_statements.charged_committee_author))

(* R2 part 1, for the family's ONE positive K (S1 conjunct A,
   K_V0(deviated(R))): the knowledge is contingent, not collapsed. It fails at
   the Quiet root and at every reachable (Within, Map_permits) state, where the
   relayer did not deviate at all. *)
let k_relayer_deviation_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v0(deviated(R)): knowledge did not collapse"
        true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f Relayer_deviated)))))

(* R2, the other half of "not collapsed": the K operand is not RIGID either.
   deviated(R) is genuinely false at a delivered message - every reachable
   (Within, Map_permits) state has rdev = Dev_none, an honest forwarder of an
   in-bounds message its own publisher map authorizes. So K_V0(deviated(R)) on
   the oversized branch is a real inference from the compile-time bound, not a
   restatement of something true everywhere. *)
let relayer_deviation_not_rigid () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (inbound /\\ ~deviated(R))" true
        (Checker.satisfiable sys
           (Formula.And (f Msg_inbound, Formula.Not (f Relayer_deviated)))))

(* R2 part 2, for the same positive K: the operative view class is NOT a
   singleton. Take q = relayer_map_forbids(A), which is FALSE at the operative
   world w1 = (Inbound, Oversized, Auth_current, Map_permits, rdev=Dev_relay,
   Charge_none, Rep_trusted); V0 nevertheless cannot rule q out, because the
   reachable world w2 = the same tuple with Map_forbids has an identical
   View_v0 (rmap is not in the view and feeds neither charge nor arep). So the
   class holds at least w1 and w2, and K_V0(deviated(R)) is real knowledge over
   a genuinely uncertain class rather than a singleton artefact. *)
let oversized_view_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ((inbound /\\ oversized) /\\ ~K_v0(~relayer_map_forbids(A)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Gossip_reject_statements.oversized_receipt,
                Formula.Not
                  (Formula.K
                     (Validator.V0, Formula.Not (f Relayer_map_forbids))) ))))

(* R3 for S1 conjunct (B), positive half: at an oversized receipt V0 cannot
   CONFIRM that the relayer's own publisher map forbids this author. Colliding
   pair: (Inbound, Oversized, Auth_current, Map_forbids) and its Map_permits
   sibling - identical View_v0, disagreeing on relayer_map_forbids(A). *)
let ignorance_relayer_map_confirm () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ((inbound /\\ oversized) /\\ ~K_v0(relayer_map_forbids(A)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Gossip_reject_statements.oversized_receipt,
                Formula.Not
                  (Formula.K (Validator.V0, f Relayer_map_forbids)) ))))

(* R3 for S2 conjunct (B), conviction half: on an in-bounds unauthorized-author
   reject V0 cannot convict the forwarder. Colliding pair: wA = (Settled,
   Within, Auth_stale_honest, Map_permits, rdev=Dev_none, Charge_author,
   Rep_trusted), the honest epoch-skewed forwarder, and wB = the same tuple
   with Map_forbids and rdev=Dev_relay, the Byzantine amplifier. Identical
   View_v0 = (Settled, Within, Cls_denied_committee, Charge_author,
   Rep_trusted); they disagree on deviated(R). *)
let ignorance_forwarder_convict () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (denied-in-bounds /\\ ~K_v0(deviated(R)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Gossip_reject_statements.denied_in_bounds_receipt,
                Formula.Not (Formula.K (Validator.V0, f Relayer_deviated)) ))))

(* R3 for S2 conjunct (B), exoneration half: nor can V0 exonerate the
   forwarder. Same wA / wB pair, read the other way round. *)
let ignorance_forwarder_exonerate () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (denied-in-bounds /\\ ~K_v0(~deviated(R)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Gossip_reject_statements.denied_in_bounds_receipt,
                Formula.Not
                  (Formula.K
                     (Validator.V0, Formula.Not (f Relayer_deviated))) ))))

(* R3 for S3 conjunct (B), conviction half: V0 charges a tracked committee
   author without being able to convict it of deliberate deviation. Colliding
   pair: wC = (Settled, Within, Auth_stale_honest, Map_permits, Charge_author,
   Rep_trusted) and wD = the same tuple with Auth_stale_byz. Both reachable,
   identical View_v0 (the author_class merge is the whole point), disagreeing
   on deviates(A). *)
let ignorance_author_intent_convict () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ((charged(A) /\\ committee(A)) /\\ ~K_v0(deviates(A)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Gossip_reject_statements.charged_committee_author,
                Formula.Not (Formula.K (Validator.V0, f Author_deviates)) ))))

(* R3 for S3 conjunct (B), exoneration half: nor can V0 exonerate it - which is
   exactly why the exemption at peer.rs:218-233 has to absorb the charge. Same
   wC / wD pair. *)
let ignorance_author_intent_exonerate () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ((charged(A) /\\ committee(A)) /\\ ~K_v0(~deviates(A)))" true
        (Checker.satisfiable sys
           (Formula.And
              ( Gossip_reject_statements.charged_committee_author,
                Formula.Not
                  (Formula.K
                     (Validator.V0, Formula.Not (f Author_deviates))) ))))

let () =
  Alcotest.run "gossip_reject"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Gossip_reject_statements.name `Quick
              (prove_one st))
          Gossip_reject_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "oversized-never-charges-author" `Quick
            oversized_never_charges_author;
          Alcotest.test_case "in-bounds-denied-never-charges-relayer" `Quick
            in_bounds_denied_never_charges_relayer;
          Alcotest.test_case "oversized-implies-relayer-deviation" `Quick
            oversized_implies_relayer_deviation;
          Alcotest.test_case "committee-author-never-banned" `Quick
            committee_author_never_banned;
          Alcotest.test_case "author-ban-reachable" `Quick author_ban_reachable;
          Alcotest.test_case "charged-committee-author-reachable" `Quick
            charged_committee_author_reachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-relayer-deviation-contingent" `Quick
            k_relayer_deviation_contingent;
          Alcotest.test_case "relayer-deviation-not-rigid" `Quick
            relayer_deviation_not_rigid;
          Alcotest.test_case "oversized-view-class-not-singleton" `Quick
            oversized_view_class_not_singleton;
          Alcotest.test_case "ignorance-relayer-map-confirm" `Quick
            ignorance_relayer_map_confirm;
          Alcotest.test_case "ignorance-forwarder-convict" `Quick
            ignorance_forwarder_convict;
          Alcotest.test_case "ignorance-forwarder-exonerate" `Quick
            ignorance_forwarder_exonerate;
          Alcotest.test_case "ignorance-author-intent-convict" `Quick
            ignorance_author_intent_convict;
          Alcotest.test_case "ignorance-author-intent-exonerate" `Quick
            ignorance_author_intent_exonerate;
        ] );
    ]
