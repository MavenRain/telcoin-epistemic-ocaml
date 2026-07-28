(** The FEE_ROUTING_SINK family (S1, S2, S3) proves on the pristine
    {!Fee_routing_sink_model} through [prove_nonvacuous] (so every antecedent is
    also checked reachable), the reachable graph stays in its justified band,
    each invariant the modelled gates enforce is unreachable-by-construction
    rather than merely unasserted, and the epistemic layer is genuinely
    partial-information: both positive knowledge operands are contingent AND
    their view classes are proved non-singleton, and every ignorance conjunct
    has a reachable witness pair in both directions.

    The contingency group is where R2 and R3 are discharged. The two positive
    [K]s of S3 rest on view classes that stay non-singleton for a reason taken
    straight from the source: at a matching execution tip the class still holds
    both an unset peer parameter and an explicit governance one, because
    crates/tn-reth/src/lib.rs:201 and :209 both funnel through
    [unwrap_or(GOVERNANCE_SAFE_ADDRESS)]; at a mismatching tip it still holds
    both non-governance addresses, because the comparison reveals divergence and
    not an address. *)

open Telcoin_epistemic
open Fee_routing_sink_model

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
        (st.Fee_routing_sink_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Fee_routing_sink_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Fee_routing_sink_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The family's single knowledge agent. *)
let obs = observer

(** Assert a formula is satisfiable somewhere in the pristine reachable set. *)
let sat_case msg fml () =
  with_sys (fun sys ->
      Alcotest.(check bool) msg true (Checker.satisfiable sys fml))

(** Assert a formula is reachable NOWHERE in the pristine reachable set. *)
let unsat_case msg fml () =
  with_sys (fun sys ->
      Alcotest.(check bool) msg false (Checker.satisfiable sys fml))

(* Loose product bound over the eight state fields: 4 own slots x 5 peer slots
   x 5 stages x 3 gas profiles x 3 producer legs x 4 sink legs x 3 payees x 3
   tip observations = 32400. The pristine reachable set is exactly 38, because
   the observing node's slot only ever takes [Own_unresolved] and
   [Own_locked Gov] (the [Alt] values are reachable only under
   [Mutable_fee_sink]), the pipeline cannot leave [Booting] until both slots are
   locked, and gas profile, producer leg, sink leg and payee are all functions
   of the stage the pipeline reached: 2 own x 5 peer = 10 booting, then 4
   resolved peer values each at Proposed, Certified and Aborted = 12, then
   4 x 2 gas profiles = 8 settled with no comparison and 8 more once the single
   tip comparison has been made. 10 + 12 + 8 + 8 = 38. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 120))

(* The exact pristine count, pinned so a silent change to the transition
   relation cannot pass unnoticed. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 38
        (Checker.reachable_count sys))

let () =
  Alcotest.run "fee_routing_sink"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Fee_routing_sink_statements.name `Quick
              (prove_one st))
          Fee_routing_sink_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          (* The gate at handler.rs:156: no reachable state credits the base-fee
             leg to the block producer. *)
          Alcotest.test_case "producer-never-takes-the-basefee" `Quick
            (unsat_case "EF basefee_in_credit(beneficiary)"
               (f Producer_took_basefee));
          (* The gate at subscriber.rs:524: the batch's self-declared payee is
             on no value path at all. *)
          Alcotest.test_case "declared-payee-never-bound" `Quick
            (unsat_case "EF beneficiary(b)=batch.beneficiary"
               (f Payee_is_declared));
          (* handler.rs:121/:127-130/:157-160/:165-168 are the only credits, so
             a settled block's legs sum to exactly the charge. *)
          Alcotest.test_case "settled-block-conserves-the-charge" `Quick
            (unsat_case "EF (settled(b) /\\ credits<>charge)"
               (Formula.And (f Settled_block, Formula.Not (f Fees_conserved))));
          (* subscriber.rs:422-434 has no fallback payee: an unknown author
             aborts the output rather than falling through to the batch field. *)
          Alcotest.test_case "unknown-author-never-settles" `Quick
            (unsat_case "EF (unknown_author(b) /\\ EF settled(b))"
               (Formula.And (f Lookup_failed, Formula.Ef (f Settled_block))));
          (* lib.rs:207-210: the second [OnceLock::set] is discarded. *)
          Alcotest.test_case "locked-sink-never-changes" `Quick
            (unsat_case
               "EF (sink(V0)=governance_safe /\\ EF sink(V0)<>governance_safe)"
               (Formula.And
                  ( f Sink_locked_gov,
                    Formula.Ef (Formula.Not (f Sink_locked_gov)) )));
          (* The execution-tip comparison of handler.rs:639-650 is sound in both
             directions on this family's frame. *)
          Alcotest.test_case "tip-match-implies-agreement" `Quick
            (unsat_case "EF (peer_exec_tip=own /\\ sink(V0)<>sink(peer))"
               (Formula.And (f Tip_match, Formula.Not (f Sinks_agree))));
          Alcotest.test_case "tip-mismatch-implies-divergence" `Quick
            (unsat_case "EF (peer_exec_tip<>own /\\ sink(V0)=sink(peer))"
               (Formula.And (f Tip_mismatch, f Sinks_agree)));
          (* The antecedents and the guarded conjuncts are not formalities: the
             abort branch, the penalty leg and both comparison outcomes are all
             genuinely reachable. *)
          Alcotest.test_case "unknown-author-branch-reachable" `Quick
            (sat_case "EF unknown_author(b)" (f Lookup_failed));
          Alcotest.test_case "penalty-leg-reachable" `Quick
            (sat_case "EF (settled(b) /\\ penalty_in_credit(fee_sink))"
               (Formula.And (f Settled_block, f Penalty_at_sink)));
          Alcotest.test_case "both-tip-outcomes-reachable" `Quick
            (sat_case "EF peer_exec_tip=own /\\ EF peer_exec_tip<>own"
               (Formula.And
                  (Formula.Ef (f Tip_match), Formula.Ef (f Tip_mismatch))));
        ] );
      ( "contingency",
        [
          (* R2, first half, for both positive Ks of S3: the knowledge is
             contingent, not collapsed to plain truth. *)
          Alcotest.test_case "agreement-knowledge-is-contingent" `Quick
            (sat_case "EF ~K_V0(sink(V0)=sink(peer))"
               (Formula.Not (Formula.K (obs, f Sinks_agree))));
          Alcotest.test_case "divergence-knowledge-is-contingent" `Quick
            (sat_case "EF ~K_V0(sink(V0)<>sink(peer))"
               (Formula.Not (Formula.K (obs, Formula.Not (f Sinks_agree)))));
          (* R2, second half: the view class at the operative state of
             [Tip_match -> K_V0(agree)] is NOT a singleton. At a matching tip
             with an unset peer parameter, V0 still does not know the parameter
             is unset - only a second reachable state sharing V0's entire view
             and carrying [Some(GOVERNANCE_SAFE_ADDRESS)] makes that possible
             (lib.rs:201, lib.rs:209). *)
          Alcotest.test_case "match-class-is-not-a-singleton" `Quick
            (sat_case
               "EF (peer_exec_tip=own /\\ ~peer_param=Some(addr) /\\ \
                ~K_V0(~peer_param=Some(addr)))"
               (Formula.conj
                  [
                    f Tip_match;
                    Formula.Not (f Peer_sink_explicit);
                    Formula.Not
                      (Formula.K (obs, Formula.Not (f Peer_sink_explicit)));
                  ]));
          (* R2, second half, for [Tip_mismatch -> K_V0(~agree)]: at a
             mismatching tip with the peer on [Alt2], V0 still does not know the
             peer is not on [Alt1]. *)
          Alcotest.test_case "mismatch-class-is-not-a-singleton" `Quick
            (sat_case
               "EF (peer_exec_tip<>own /\\ sink(peer)<>alt1 /\\ \
                ~K_V0(sink(peer)<>alt1))"
               (Formula.conj
                  [
                    f Tip_mismatch;
                    Formula.Not (f Peer_sink_is_alt1);
                    Formula.Not
                      (Formula.K (obs, Formula.Not (f Peer_sink_is_alt1)));
                  ]));
          (* R3 for S3 conjunct B, both directions: after settling a block but
             before comparing any peer execution tip, the two states that agree
             and disagree on the sink share V0's whole view. *)
          Alcotest.test_case "ignorance-sinks-agree" `Quick
            (sat_case
               "EF (settled(b) /\\ no_peer_tip_compared /\\ \
                sink(V0)=sink(peer) /\\ ~K_V0(sink(V0)=sink(peer)))"
               (Formula.conj
                  [
                    f Settled_block;
                    f Tip_unchecked;
                    f Sinks_agree;
                    Formula.Not (Formula.K (obs, f Sinks_agree));
                  ]));
          Alcotest.test_case "ignorance-sinks-diverge" `Quick
            (sat_case
               "EF (settled(b) /\\ no_peer_tip_compared /\\ \
                sink(V0)<>sink(peer) /\\ ~K_V0(sink(V0)<>sink(peer)))"
               (Formula.conj
                  [
                    f Settled_block;
                    f Tip_unchecked;
                    Formula.Not (f Sinks_agree);
                    Formula.Not
                      (Formula.K (obs, Formula.Not (f Sinks_agree)));
                  ]));
          (* R3 for S3 conjunct D, both directions: a matching tip never reveals
             whether the peer set the parameter or inherited the default. *)
          Alcotest.test_case "ignorance-peer-param-explicit" `Quick
            (sat_case
               "EF (peer_exec_tip=own /\\ peer_param=Some(addr) /\\ \
                ~K_V0(peer_param=Some(addr)))"
               (Formula.conj
                  [
                    f Tip_match;
                    f Peer_sink_explicit;
                    Formula.Not (Formula.K (obs, f Peer_sink_explicit));
                  ]));
          Alcotest.test_case "ignorance-peer-param-defaulted" `Quick
            (sat_case
               "EF (peer_exec_tip=own /\\ ~peer_param=Some(addr) /\\ \
                ~K_V0(~peer_param=Some(addr)))"
               (Formula.conj
                  [
                    f Tip_match;
                    Formula.Not (f Peer_sink_explicit);
                    Formula.Not
                      (Formula.K (obs, Formula.Not (f Peer_sink_explicit)));
                  ]));
          (* R3 for S3 conjunct E's ignorance half, both directions: a
             mismatching tip never narrows the peer's address. *)
          Alcotest.test_case "ignorance-peer-sink-alt1" `Quick
            (sat_case
               "EF (peer_exec_tip<>own /\\ sink(peer)=alt1 /\\ \
                ~K_V0(sink(peer)=alt1))"
               (Formula.conj
                  [
                    f Tip_mismatch;
                    f Peer_sink_is_alt1;
                    Formula.Not (Formula.K (obs, f Peer_sink_is_alt1));
                  ]));
          Alcotest.test_case "ignorance-peer-sink-alt2" `Quick
            (sat_case
               "EF (peer_exec_tip<>own /\\ sink(peer)<>alt1 /\\ \
                ~K_V0(sink(peer)<>alt1))"
               (Formula.conj
                  [
                    f Tip_mismatch;
                    Formula.Not (f Peer_sink_is_alt1);
                    Formula.Not
                      (Formula.K (obs, Formula.Not (f Peer_sink_is_alt1)));
                  ]));
        ] );
    ]
