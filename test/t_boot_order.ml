(** The three BOOT-ORDER statements prove on the pristine model through
    [prove_nonvacuous] (so each antecedent is also checked reachable), the
    reachable graph stays in its justified band, the three gates the family is
    about really do make their forbidden states unreachable, and the epistemic
    layer is genuinely partial-information:

    - the peer's knowledge that the node bound its listener is contingent (it
      fails somewhere reachable) and its operative view class is not a
      singleton;
    - the sibling path that would make a naive version of that knowledge false
      is present and reachable: the booting node can hold an outbound
      connection to the peer while its own listener is unbound, and at that
      view the peer does NOT know the node is bound;
    - the booting node's ignorance of the replay-and-close startup shape has a
      concrete witness pair - both startup shapes reach a pre-replay state
      with an identical [V0] view and opposite [close-on-replay]. *)

open Telcoin_epistemic
open Boot_order_model

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
        (st.Boot_order_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Boot_order_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Boot_order_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Justified bound: the boot is a sequential 9-phase chain, every other
   component is written exactly once by a named step of that chain (so it is
   phase-determined given the startup shape), and the only free dimensions are
   the two startup shapes and the two monotone peer-link booleans:
   9 x 2 x 2 x 2 = 72. The actual pristine reachable set is 38 states (34
   under Initial_only_network_gate, 40 under Rebind_on_replay). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in the justified band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 72))

(** One [satisfiable] assertion on the pristine model. *)
let sat_is label expected formula () =
  with_sys (fun sys ->
      Alcotest.(check bool) label expected (Checker.satisfiable sys formula))

(* S1's gate: no startup component reads the marker while it still lags the
   persisted canonical tip (node.rs:864 ahead of :869). *)
let no_read_before_heal =
  sat_is "EF (restore-ran /\\ ~marker-at-tip) is unreachable" false
    (Formula.And (f Restore_ran, Formula.Not (f Marker_healed_to_tip)))

(* S1's consequence: the rebuild is never short on the pristine path. *)
let no_short_rebuild =
  sat_is "EF (restore-ran /\\ ~totals-complete) is unreachable" false
    (Formula.And (f Restore_ran, Formula.Not (f Totals_complete)))

(* S2's gate: the replay never derives a watermark from an unseeded window
   (node.rs:906 ahead of run_epoch.rs:220). *)
let no_replay_before_prime =
  sat_is "EF (replay-ran /\\ ~recent-blocks-seeded) is unreachable" false
    (Formula.And (f Replay_ran, Formula.Not (f Recent_blocks_seeded)))

(* S2's consequence: the engine is never handed an output it already
   executed. *)
let no_double_execution =
  sat_is "EF double-executed is unreachable" false (f Double_executed)

(* S3's gate: the one-time per-process setup never binds a second listener
   (run_epoch.rs:255 with the flag set at :269). *)
let no_second_bind =
  sat_is "EF (listener-bound /\\ ~bound-exactly-once) is unreachable" false
    (Formula.And (f Listener_bound, Formula.Not (f Bound_exactly_once)))

(* R2, part 1, for S3's positive K: the knowledge is contingent, not
   collapsed - somewhere reachable the peer does not know the node bound. *)
let k_contingent =
  sat_is "EF ~K_v1(listener-bound): knowledge did not collapse" true
    (Formula.Not (Formula.K (Validator.V1, f Listener_bound)))

(* R2, part 2, for S3's positive K: the operative view class is NOT a
   singleton. At a state where the peer has dialed in, the epoch loop is not
   yet live; asserting that the peer does not know it is not live forces a
   second reachable state in the same [V1] view class (same connection facts,
   further along the boot). *)
let k_class_not_singleton =
  sat_is "EF (peer-dialed-in /\\ ~K_v1(~epoch-running)): class is not a singleton"
    true
    (Formula.And
       ( f Peer_dialed_in,
         Formula.Not (Formula.K (Validator.V1, Formula.Not (f Epoch_running)))
       ))

(* R5 evidence: the sibling path is in the model and reachable - the booting
   node's swarms run from node.rs:877, so it can hold an outbound connection
   to the peer with no listener bound at all. *)
let sibling_link_without_bind =
  sat_is "EF (peer-linked /\\ ~listener-bound): connected but undialable" true
    (Formula.And (f Peer_linked, Formula.Not (f Listener_bound)))

(* ...and the sibling path does NOT ground the knowledge: at the peer's
   linked-but-not-dialed-in view, both truth values of [listener-bound] are
   reachable, so the peer is ignorant even where the node happens to be
   bound. This is why S3's K conjunct is keyed on the peer's own inbound dial
   rather than on connectivity. *)
let sibling_does_not_ground_knowledge =
  sat_is
    "EF (peer-linked /\\ listener-bound /\\ ~K_v1(listener-bound)): a link is \
     not knowledge"
    true
    (Formula.conj
       [
         f Peer_linked;
         f Listener_bound;
         Formula.Not (Formula.K (Validator.V1, f Listener_bound));
       ])

(* R3 witness pair for S3's ignorance conjunct, side A: a pre-replay state on
   the boundary startup shape, where this iteration WILL replay-and-close. *)
let ignorance_witness_close =
  sat_is "EF (~replay-ran /\\ close-on-replay)" true
    (Formula.And (Formula.Not (f Replay_ran), f Close_on_replay))

(* R3 witness pair, side B: a pre-replay state on the crash-window startup
   shape, where it will not. *)
let ignorance_witness_no_close =
  sat_is "EF (~replay-ran /\\ ~close-on-replay)" true
    (Formula.And (Formula.Not (f Replay_ran), Formula.Not (f Close_on_replay)))

(* ...and the pair really does share the booting node's view: at a pre-replay
   state the node cannot rule the replay-and-close shape out, which is only
   possible if a state with the opposite shape carries the same [V0] view. *)
let ignorance_pair_shares_the_view =
  sat_is
    "EF (~replay-ran /\\ ~K_v0(~close-on-replay)): the shapes are \
     indistinguishable at gate time"
    true
    (Formula.And
       ( Formula.Not (f Replay_ran),
         Formula.Not
           (Formula.K (Validator.V0, Formula.Not (f Close_on_replay))) ))

let () =
  Alcotest.run "boot_order"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Boot_order_statements.name `Quick
              (prove_one st))
          Boot_order_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "no-marker-read-before-heal" `Quick
            no_read_before_heal;
          Alcotest.test_case "no-short-rebuild" `Quick no_short_rebuild;
          Alcotest.test_case "no-replay-before-prime" `Quick
            no_replay_before_prime;
          Alcotest.test_case "no-double-execution" `Quick no_double_execution;
          Alcotest.test_case "no-second-bind" `Quick no_second_bind;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-contingent" `Quick k_contingent;
          Alcotest.test_case "k-class-not-singleton" `Quick
            k_class_not_singleton;
          Alcotest.test_case "sibling-link-without-bind" `Quick
            sibling_link_without_bind;
          Alcotest.test_case "sibling-does-not-ground-knowledge" `Quick
            sibling_does_not_ground_knowledge;
          Alcotest.test_case "ignorance-witness-close" `Quick
            ignorance_witness_close;
          Alcotest.test_case "ignorance-witness-no-close" `Quick
            ignorance_witness_no_close;
          Alcotest.test_case "ignorance-pair-shares-the-view" `Quick
            ignorance_pair_shares_the_view;
        ] );
    ]
