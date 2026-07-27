(** The topos gate for the exex_fanout family: {!Exex_fanout_model} runs on
    [Denote.Make], so it owes the reduction and reflection obligations of
    {!Topos_gate} on its own reachable graph, under the pristine model and
    under every mutation that pins one of its statements.

    This family has NO poset case. Its reachability relation is a preorder,
    not a poset - it models a mechanism that undoes itself, so two distinct
    states are mutually reachable - and that classification is pinned once
    for all 27 models in test/t_topos_frames.ml rather than repeated here.
    A preorder is still a thin category, so the presheaf topos over it is
    intact; what the gate below establishes is the thing that actually
    matters, that the denotation computes what {!System} computes at every
    reachable world.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}). *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G = Topos_gate.Make (Exex_fanout_model.State) (Exex_fanout_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Exex_fanout_model.Pristine;
    Exex_fanout_model.No_canon_gap_marker;
    Exex_fanout_model.No_lagged_presend;
    Exex_fanout_model.Blocking_send;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Exex_fanout_model.Pristine -> "pristine"
  | Exex_fanout_model.No_canon_gap_marker -> "no-canon-gap-marker"
  | Exex_fanout_model.No_lagged_presend -> "no-lagged-presend"
  | Exex_fanout_model.Blocking_send -> "blocking-send"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Exex_fanout_statements.formula
      @ Topos_gate.subformulas st.Exex_fanout_statements.antecedent)
    Exex_fanout_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Validator.V0 ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:[ Exex_fanout_model.initial ] ~next:(Exex_fanout_model.next_with mut)
       ~view:Exex_fanout_model.view ~label:Exex_fanout_model.label ~formulas)

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

(** The frame really is the preorder case, so t_topos_frames.ml is pinning a
    live distinction and not a stale one. *)
let frame_is_a_preorder () =
  with_verdict
    Exex_fanout_model.Pristine
    (fun v ->
      Alcotest.(check bool) "reachability is a preorder, not a poset" false
        v.G.poset)

(** Deleting the classical bridge changes a verdict here, so the reduction
    gate above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Exex_fanout_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "exex_fanout-topos"
    [
      ( "reduction",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (reduction_holds m))
          muts );
      ( "frame",
        [ Alcotest.test_case "preorder-not-poset" `Quick frame_is_a_preorder ] );
      ( "reflection",
        [ Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous ] );
    ]
