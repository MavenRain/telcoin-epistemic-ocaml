(** The topos gate for the vote_cache_retry family: {!Vote_cache_retry_model}
    runs on [Denote.Make], so it owes the three obligations of {!Topos_gate} on
    its own reachable graph, under the pristine model and under every mutation
    that pins one of its statements.

    - the frame classification: this family's reachability relation is a
      PREORDER and not a poset, because two of its transitions genuinely undo
      earlier ones - the hint reset of certifier.rs:191-195 takes
      [missing_parents] back to [None], and the re-propose of
      proposer.rs:802-822 revives a vote task that an [RPCError] had killed. A
      preorder is still a thin category, so presheaf restriction stays
      path-independent; the negative pin below asserts the classification rather
      than assuming it;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Vote_cache_retry_model.State) (Vote_cache_retry_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Vote_cache_retry_model.Pristine;
    Vote_cache_retry_model.No_empty_parent_reissue;
    Vote_cache_retry_model.No_one_epoch_ahead_arm;
    Vote_cache_retry_model.Single_shared_vote_lock;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Vote_cache_retry_model.Pristine -> "pristine"
  | Vote_cache_retry_model.No_empty_parent_reissue -> "no-empty-parent-reissue"
  | Vote_cache_retry_model.No_one_epoch_ahead_arm -> "no-one-epoch-ahead-arm"
  | Vote_cache_retry_model.Single_shared_vote_lock -> "single-shared-vote-lock"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Vote_cache_retry_statements.formula
      @ Topos_gate.subformulas st.Vote_cache_retry_statements.antecedent)
    Vote_cache_retry_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Validator.V0 ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list matches {!Vote_cache_retry_model.spec_of} exactly: the single
    initial state. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Vote_cache_retry_model.initial ]
       ~next:(Vote_cache_retry_model.next_with mut)
       ~view:Vote_cache_retry_model.view ~label:Vote_cache_retry_model.label
       ~formulas)

(** The frame really is the preorder case, so t_topos_frames.ml is pinning a
    live distinction and not a stale one: the hint reset (certifier.rs:191-195)
    and the re-propose (proposer.rs:802-822) both return the system to a state
    it had already left, so reachability is not antisymmetric. *)
let frame_is_a_preorder () =
  with_verdict Vote_cache_retry_model.Pristine (fun v ->
      Alcotest.(check bool) "reachability is a preorder, not a poset" false
        v.G.poset)

(** The topos denotation agrees with the original checker, world by world. *)
let reduction_holds mut () =
  with_verdict mut (fun v ->
      Alcotest.(check (option int))
        ("is_true o grade = System.sat over "
        ^ Int.to_string v.G.checked
        ^ " formulas x "
        ^ Int.to_string v.G.worlds
        ^ " worlds")
        None v.G.mismatch)

(** Deleting the classical bridge changes a verdict here, so the reduction gate
    above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Vote_cache_retry_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "vote_cache_retry-topos"
    [
      ("frame", [ Alcotest.test_case "preorder-not-poset" `Quick frame_is_a_preorder ]);
      ( "reduction",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (reduction_holds m))
          muts );
      ("reflection", [ Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous ]);
    ]
