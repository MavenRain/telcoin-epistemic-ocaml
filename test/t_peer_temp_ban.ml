(** The PEER_TEMP_BAN family proves on the pristine {!Peer_temp_ban_model}
    through [prove_nonvacuous] (so every antecedent is also checked reachable),
    the reachable graph stays in its justified band, and the two invariants the
    cache's own lines enforce are unreachable-by-negation: no plain peer is ever
    out of the cache before its duration ran, and an aged-out entry only ever
    exists inside an unserviced heartbeat window.

    The "contingency" group is where the epistemic obligations are discharged.
    For the family's one positive knowledge conjunct, [K (V1, duration_elapsed
    \\/ forgiven)]: it is contingent (its negation is reachable), and the V1-view
    class at an admitted state is NOT a singleton, witnessed twice - by a state
    of that class in which the other peer P2 is still excluded (a fact P1 cannot
    see at all) and by one in which the forgive path fired. For the ignorance
    conjunct [~K (V0, ~stamp_expired)]: the witness pair - a still-running
    exclusion and an aged-out one sharing the gate's membership view - is
    asserted reachable. The forgive path itself is asserted reachable too, so
    the [~forgiven] hypothesis every statement carries is load-bearing rather
    than decorative. *)

open Telcoin_epistemic
open Peer_temp_ban_model

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
        (st.Peer_temp_ban_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Peer_temp_ban_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Peer_temp_ban_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** Conjunction shorthand for the witness formulas. *)
let both a b = Formula.And (a, b)

(* Loose product bound: 4 entry values for P1 x 3 ghost ages x 2 offence
   budgets x 4 entry values for P2 x 2 heartbeat flags = 192, plus the absorbing
   forgiven sink. The pristine reachable set is exactly 26: under [Pristine] the
   ghost equals P1's stamp age at every state (that equality is the refresh
   branch's content), an aged-out entry survives only inside an unserviced
   heartbeat window, and P1 leaves the cache only with the full duration
   elapsed. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check int)
        "pristine reachable count, against a loose product bound of 193" 26
        (Checker.reachable_count sys))

(* The expiry guard's contract as an unreachability: a plain (non-forgiven) peer
   is never out of the cache before a full duration has elapsed since its last
   insertion. This is the state No_expiry_guard and No_reinsert_refresh both
   make reachable. *)
let never_released_early () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (~contains(P1) /\\ ~duration_elapsed(P1) /\\ ~forgiven(P1))"
        false
        (Checker.satisfiable sys
           (both
              (Formula.Not (f Cached_1))
              (both
                 (Formula.Not (f Duration_elapsed_1))
                 (Formula.Not (f Forgiven_1))))))

(* The drain call's contract as an unreachability: an aged-out entry exists only
   inside a heartbeat interval that has not yet been serviced. This is the state
   No_heartbeat_drain makes reachable, and it is the exact width of the
   documented late-release window (manager.rs:78-81). *)
let expired_only_inside_the_window () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (stamp_expired(P1) /\\ ~heartbeat_due)" false
        (Checker.satisfiable sys
           (both (f Stamp_expired_1) (Formula.Not (f Heartbeat_due)))))

(* S1(B)'s knowledge is contingent, not collapsed: there are reachable states
   at which P1 does NOT know its duration ran (every state where it is still
   cached with a fresh stamp). *)
let k_admission_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(duration_elapsed(P1) \\/ forgiven(P1))" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 (Validator.V1, Formula.Or (f Duration_elapsed_1, f Forgiven_1))))))

(* R2, first witness: at an admitted state P1 does not know that the OTHER peer
   is out of the cache, which is only possible if another reachable state shares
   P1's view and has P2 still excluded. The V1-view class at the operative state
   is therefore not a singleton, and the knowledge claim of S1(B) is not true by
   partition-triviality. *)
let admitted_class_not_singleton_other_peer () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (~contains(P1) /\\ ~K_v1(~contains(P2)))" true
        (Checker.satisfiable sys
           (both
              (Formula.Not (f Cached_1))
              (Formula.Not
                 (Formula.K (Validator.V1, Formula.Not (f Cached_2)))))))

(* R2, second witness: at an admitted state P1 also cannot rule out that it was
   released by the forgive path rather than by expiry - the sink shares its
   view. This is the same non-singleton fact read off the disjunct that keeps
   S1(B) honest about the repair path. *)
let admitted_class_not_singleton_forgive () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (~contains(P1) /\\ ~K_v1(~forgiven(P1)))" true
        (Checker.satisfiable sys
           (both
              (Formula.Not (f Cached_1))
              (Formula.Not
                 (Formula.K (Validator.V1, Formula.Not (f Forgiven_1)))))))

(* R3 for S2(B): the ignorance witness itself - a state where the gate is
   refusing a still-running exclusion and cannot know that is what it is doing.
   *)
let gate_ignorance_witness () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (contains(P1) /\\ ~stamp_expired(P1) /\\ ~K_v0(~stamp_expired(P1)))"
        true
        (Checker.satisfiable sys
           (both (f Cached_1)
              (both
                 (Formula.Not (f Stamp_expired_1))
                 (Formula.Not
                    (Formula.K (Validator.V0, Formula.Not (f Stamp_expired_1))))))))

(* R3 for S2(B), the other half of the pair: the aged-out-but-still-refused
   state that shares the gate's membership view really is reachable. Without it
   the ignorance above would have no witness. *)
let gate_ignorance_sibling () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (contains(P1) /\\ stamp_expired(P1))" true
        (Checker.satisfiable sys (both (f Cached_1) (f Stamp_expired_1))))

(* The modelled repair path is live: the committee/trusted forgive routes really
   do release P1 with its timer unrun, so the [~forgiven(P1)] hypothesis carried
   by every statement of this family excludes a real behaviour rather than an
   empty one. *)
let forgive_path_releases_early () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (~contains(P1) /\\ ~duration_elapsed(P1) /\\ forgiven(P1))" true
        (Checker.satisfiable sys
           (both
              (Formula.Not (f Cached_1))
              (both (Formula.Not (f Duration_elapsed_1)) (f Forgiven_1)))))

(* S3's antecedent is operative: the two-entry queue in which P1's last
   insertion is strictly more recent than P2's is reachable, which is what makes
   the release-order conjunct about a real configuration. *)
let queue_order_configuration_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF younger(P1,P2)" true
        (Checker.satisfiable sys (f Younger_1)))

let () =
  Alcotest.run "peer_temp_ban"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Peer_temp_ban_statements.name `Quick
              (prove_one st))
          Peer_temp_ban_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "never-released-early" `Quick never_released_early;
          Alcotest.test_case "expired-only-inside-the-window" `Quick
            expired_only_inside_the_window;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-admission-contingent" `Quick
            k_admission_contingent;
          Alcotest.test_case "admitted-class-not-singleton-other-peer" `Quick
            admitted_class_not_singleton_other_peer;
          Alcotest.test_case "admitted-class-not-singleton-forgive" `Quick
            admitted_class_not_singleton_forgive;
          Alcotest.test_case "gate-ignorance-witness" `Quick
            gate_ignorance_witness;
          Alcotest.test_case "gate-ignorance-sibling" `Quick
            gate_ignorance_sibling;
          Alcotest.test_case "forgive-path-releases-early" `Quick
            forgive_path_releases_early;
          Alcotest.test_case "queue-order-configuration-reachable" `Quick
            queue_order_configuration_reachable;
        ] );
    ]
