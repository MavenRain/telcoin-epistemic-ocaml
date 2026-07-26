(** The EXEX_LIFE family (S1 output window, S2 committee gate, S3 isolated ExEx
    spawn policy) proves on the pristine {!Exex_life_model} through
    [prove_nonvacuous] (so each antecedent is also checked reachable), the
    reachable graph stays in its justified band, the three states the gates
    forbid are unreachable, and the epistemic layer is genuinely
    partial-information: the family's single positive K is contingent and sits in
    a demonstrably non-singleton view class, every ~K has a concrete reachable
    colliding pair, and V2 is not a blank-view agent.

    Post-review addition: two cases pin the epoch-record branch of
    [get_committee] (handler.rs:215-223, storage/src/epoch_records.rs:354-367),
    the branch whose absence made S1's original conjunct C false of the Rust.
    [epoch-record-branch-reachable] asserts the branch's three witness states,
    and [s1-c-verified-cert-leaks-the-lead] asserts the knowledge leak it
    creates - the very leak conjunct C now guards against with
    [~exex_cert_signal]. Delete that branch from the model again and both cases
    fail. *)

open Telcoin_epistemic
open Exex_life_model

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
        (st.Exex_life_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Exex_life_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Exex_life_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 2 epochs x 3 network epochs x 2 output levels x 7
   certificate fates x 3 ExEx outcomes = 252. The pristine reachable set is
   exactly 52 = 26 x 2: seven reachable (ep, net, out) triples carrying
   Cert_none at all 7, Cert_unknown_forged at all 7, Cert_unknown_genuine at the
   3 with net = Net_e2, Cert_verified_genuine at those same 3 and
   Cert_invalid_forged at 6 (the 4 with ep = Ep_e1, plus (Ep_e, Net_e1, Out_e)
   and (Ep_e, Net_e2, Out_e) reached through get_committee's epoch-record
   branch); the x2 is the free [exex] factor over {Exex_live,
   Exex_dead_isolated}, free because [node_up] holds for both. Cert_leaked_*
   need No_committee_gate and Exex_dead_fatal needs Spawn_exex_critical, so
   neither is reachable here. The count rose from 46 to 52 when the epoch-record
   branch of [get_committee] was added to the model (see
   [epoch-record-branch-reachable]); it stays inside the family's ~50-state
   budget. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 252))

(* The epoch window's contract (subscriber.rs:143-147, state-sync/src/lib.rs
   :324-327 and :231-233): the ExEx is never handed epoch-(E+1) output while its
   host is still configured at epoch E. No_epoch_window makes this reachable and
   flips S1 conjunct A. *)
let output_never_outruns_host_epoch () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (exex_output(E+1) /\\ ~host_epoch=E+1)" false
        (Checker.satisfiable sys
           (Formula.And (f Exex_output_e1, Formula.Not (f Host_epoch_e1)))))

(* The committee gate's contract (handler.rs:251, else arm :280-286): an
   unevaluable certificate never produces a CertificateAccepted notification.
   No_committee_gate makes this reachable and flips S2 conjunct A. *)
let unverifiable_cert_never_signalled () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (cert_unverifiable /\\ exex_cert_signal)"
        false
        (Checker.satisfiable sys
           (Formula.And (f Cert_unverifiable, f Exex_cert_signal))))

(* The spawn policy's contract (node.rs:953-957, manager/exex.rs:15-36,
   task_manager.rs:459-461): with exex_critical = false the host never halts on
   an ExEx failure. Spawn_exex_critical makes Host_halted reachable and flips S3.
*)
let host_never_halts () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF host_halted" false
        (Checker.satisfiable sys (f Host_halted)))

(* R2 contingency for the family's ONLY positive K (S1 conjunct B): the
   knowledge K_V1(net_reached(E+1)) did not collapse into plain truth under the
   view partition - it fails at the initial state (Ep_e, Net_e, Out_e, Cert_none,
   Exex_live), whose V1-view class contains net = Net_e worlds. *)
let k_v1_net_e1_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_v1(net_reached(E+1))" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Net_reached_e1)))))

(* R2 non-singleton view class for S1 conjunct B. At the operative state
   w1 = (Ep_e1, Net_e1, Out_e1, Cert_none, Exex_live) the atom net_reached(E+2)
   is FALSE, yet V1 cannot rule it out - which is only possible because the
   class View_v1 (Ep_e1, Out_e1, Tr_none, Exex_live) also contains
   w2 = (Ep_e1, Net_e2, Out_e1, Cert_none, Exex_live). So the class where
   K_V1(net_reached(E+1)) is asserted has at least two reachable members. *)
let s1_b_class_non_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (exex_output(E+1) /\\ ~net_reached(E+2) /\\ ~K_v1 ~net_reached(E+2))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Exex_output_e1,
                Formula.And
                  ( Formula.Not (f Net_reached_e2),
                    Formula.Not
                      (Formula.K (Validator.V1, Formula.Not (f Net_reached_e2)))
                  ) ))))

(* R3 ignorance witness for S1 conjunct C, in its GUARDED form: while the host
   is still at epoch E and no epoch-(E+2) certificate has verified, the network
   has already reached E+2 and V1 cannot know it. Colliding pair:
   w3 = (Ep_e, Net_e2, Out_e, Cert_none, Exex_live) and
   w4 = (Ep_e, Net_e, Out_e, Cert_none, Exex_live) share
   View_v1 (Ep_e, Out_e, Tr_none, Exex_live). The warn-and-drop variant of the
   same collision is w5 = (Ep_e, Net_e2, Out_e, Cert_unknown_genuine, Exex_live)
   against w6 = (Ep_e, Net_e, Out_e, Cert_unknown_forged, Exex_live), both
   View_v1 (Ep_e, Out_e, Tr_dropped, Exex_live); and the record-evaluated
   variant is w9 = (Ep_e, Net_e2, Out_e, Cert_invalid_forged, Exex_live) against
   w10 = (Ep_e, Net_e1, Out_e, Cert_invalid_forged, Exex_live), both
   View_v1 (Ep_e, Out_e, Tr_invalid, Exex_live). *)
let s1_c_two_epoch_lead_hidden () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (net_reached(E+2) /\\ ~host_epoch=E+1 /\\ ~exex_cert_signal /\\ ~K_v1 \
         net_reached(E+2))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Net_reached_e2,
                Formula.And
                  ( Formula.Not (f Host_epoch_e1),
                    Formula.And
                      ( Formula.Not (f Exex_cert_signal),
                        Formula.Not (Formula.K (Validator.V1, f Net_reached_e2))
                      ) ) ))))

(* The reason conjunct C carries the ~exex_cert_signal guard, asserted as a
   reachable fact rather than left as prose: [get_committee]'s third source, the
   epoch-record fallback record_by_epoch(E+1).next_committee
   (handler.rs:215-223, storage/src/epoch_records.rs:354-367), answers for epoch
   E+2 with NO epoch advance, because the node-scoped record collector
   deliberately fetches past the node's own epoch (node.rs:888-895,
   state-sync/src/epoch.rs:46-150). So an epoch-(E+2) certificate really can
   verify while the host is still configured at epoch E - and since a lone
   forger cannot produce that trace, the class
   View_v1 (Ep_e, Out_e, Tr_verified, Exex_live) is genuine-only and V1 DOES
   then know net_reached(E+2). An unguarded conjunct C would be refuted exactly
   here; this test fails the moment that branch is removed from the model
   again. *)
let s1_c_verified_cert_leaks_the_lead () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (net_reached(E+2) /\\ ~host_epoch=E+1 /\\ exex_cert_signal /\\ K_v1 \
         net_reached(E+2))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Net_reached_e2,
                Formula.And
                  ( Formula.Not (f Host_epoch_e1),
                    Formula.And
                      ( f Exex_cert_signal,
                        Formula.K (Validator.V1, f Net_reached_e2) ) ) ))))

(* The epoch-record branch, asserted state by state (the atom vocabulary cannot
   tell Cert_none from Cert_invalid_forged, so this one checks membership in the
   reachable set directly). All three worlds have [ep = Ep_e], i.e. NO epoch
   advance has happened:
     w9  = (Ep_e, Net_e2, Out_e, Cert_invalid_forged,   Exex_live) - a forgery
           checked against the record-derived key set and rejected;
     w10 = (Ep_e, Net_e1, Out_e, Cert_invalid_forged,   Exex_live) - the same
           rejection with the network NOT yet committing in E+2, which is what
           keeps the Tr_invalid class non-leaking and conjunct C true;
     w11 = (Ep_e, Net_e2, Out_e, Cert_verified_genuine, Exex_live) - the leak
           that forces conjunct C's guard.
   w9 and w10 must also share V1's view, or the Tr_invalid collision this rests
   on would not exist. *)
let epoch_record_branch_reachable () =
  with_sys (fun sys ->
      let reach = Checker.sat sys Formula.Top in
      let w9 =
        { ep = Ep_e; net = Net_e2; out = Out_e; cert = Cert_invalid_forged;
          exex = Exex_live }
      in
      let w10 =
        { ep = Ep_e; net = Net_e1; out = Out_e; cert = Cert_invalid_forged;
          exex = Exex_live }
      in
      let w11 =
        { ep = Ep_e; net = Net_e2; out = Out_e; cert = Cert_verified_genuine;
          exex = Exex_live }
      in
      Alcotest.(check bool)
        "get_committee's epoch-record branch is modeled: forgery rejected and \
         genuine cert verified at ep = E, and the two rejections collide in \
         V1's view"
        true
        (Checker.State_set.mem w9 reach
        && Checker.State_set.mem w10 reach
        && Checker.State_set.mem w11 reach
        && Int.equal 0
             (view_compare (view Validator.V1 w9) (view Validator.V1 w10))))

(* R3 ignorance witness for S2 conjunct B (cannot confirm). Colliding pair:
   w5 = (Ep_e, Net_e2, Out_e, Cert_unknown_genuine, Exex_live) - the real
   epoch-(E+2) committee certified a header - and w6 = (Ep_e, Net_e, Out_e,
   Cert_unknown_forged, Exex_live) - Byzantine V0 alone fabricated one. Both
   project to View_v1 (Ep_e, Out_e, Tr_dropped, Exex_live), the byte-identical
   warn-and-drop trace of handler.rs:280-286. *)
let s2_b_cannot_confirm () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (cert_unverifiable /\\ ~K_v1 cert_quorum_genuine)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Cert_unverifiable,
                Formula.Not (Formula.K (Validator.V1, f Cert_quorum_genuine)) ))))

(* R3 ignorance witness for S2 conjunct C (cannot rule out): the same w5/w6
   collision, taken from the forged side - at w6 the class still contains the
   genuine world w5, so V1 cannot conclude ~cert_quorum_genuine either. *)
let s2_c_cannot_rule_out () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (cert_unverifiable /\\ ~K_v1 ~cert_quorum_genuine)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Cert_unverifiable,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Cert_quorum_genuine)))
              ))))

(* R3 ignorance witness for S3 conjunct B. Colliding pair:
   w7 = (Ep_e, Net_e, Out_e, Cert_none, Exex_dead_isolated) - V1 registered an
   ExEx that panicked, contained and logged - and w8 = (Ep_e, Net_e, Out_e,
   Cert_none, Exex_live) - V1's ExEx is healthy. Both project to
   View_v2 (Net_e, Responding), because the reverse channel is dropped unread
   (node.rs:964-974) and the context carries no network handle
   (context.rs:26-39). *)
let s3_b_internode_opacity () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (exex_task_stopped /\\ ~K_v2 exex_task_stopped)"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Exex_task_stopped,
                Formula.Not (Formula.K (Validator.V2, f Exex_task_stopped)) ))))

(* V2 is not a blank-view agent: its view ([net], liveness) is genuinely
   informative about the network - at a net = Net_e2 state V2 knows
   net_reached(E+2) - and genuinely partial - at a net = Net_e state it does
   not. Both halves must be satisfiable, otherwise the K_V2 of S3 would be
   riding on a degenerate view. *)
let v2_view_is_informative_but_partial () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF K_v2(net_reached(E+2)) and EF ~K_v2(net_reached(E+2))" true
        (Checker.satisfiable sys (Formula.K (Validator.V2, f Net_reached_e2))
        && Checker.satisfiable sys
             (Formula.Not (Formula.K (Validator.V2, f Net_reached_e2)))))

(* Plain reachability of the three operative atoms, so none of the conjuncts is
   proved on an empty stage: the ExEx really is handed epoch-(E+1) output, a
   CertificateAccepted signal really is emitted (for a verified certificate),
   and a genuine epoch-(E+2) quorum certificate really does exist on some
   reachable branch. *)
let operative_atoms_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF exex_output(E+1), EF exex_cert_signal, EF genuine"
        true
        (Checker.satisfiable sys (f Exex_output_e1)
        && Checker.satisfiable sys (f Exex_cert_signal)
        && Checker.satisfiable sys (f Cert_quorum_genuine)))

let () =
  Alcotest.run "exex_life"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Exex_life_statements.name `Quick (prove_one st))
          Exex_life_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "output-never-outruns-host-epoch" `Quick
            output_never_outruns_host_epoch;
          Alcotest.test_case "unverifiable-cert-never-signalled" `Quick
            unverifiable_cert_never_signalled;
          Alcotest.test_case "host-never-halts" `Quick host_never_halts;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-v1-net-e1-contingent" `Quick
            k_v1_net_e1_contingent;
          Alcotest.test_case "s1-b-class-non-singleton" `Quick
            s1_b_class_non_singleton;
          Alcotest.test_case "s1-c-two-epoch-lead-hidden" `Quick
            s1_c_two_epoch_lead_hidden;
          Alcotest.test_case "s1-c-verified-cert-leaks-the-lead" `Quick
            s1_c_verified_cert_leaks_the_lead;
          Alcotest.test_case "epoch-record-branch-reachable" `Quick
            epoch_record_branch_reachable;
          Alcotest.test_case "s2-b-cannot-confirm" `Quick s2_b_cannot_confirm;
          Alcotest.test_case "s2-c-cannot-rule-out" `Quick s2_c_cannot_rule_out;
          Alcotest.test_case "s3-b-internode-opacity" `Quick
            s3_b_internode_opacity;
          Alcotest.test_case "v2-view-informative-but-partial" `Quick
            v2_view_is_informative_but_partial;
          Alcotest.test_case "operative-atoms-reachable" `Quick
            operative_atoms_reachable;
        ] );
    ]
