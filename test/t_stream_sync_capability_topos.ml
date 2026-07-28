(** The topos gate for the stream_sync_capability family:
    {!Stream_sync_capability_model} runs on [Denote.Make], so it owes the
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    This family has NO poset case. Its reachability relation is a preorder, not
    a poset: the epoch boundary (start_epoch.rs:547-550) toggles the epoch
    counter and clears the map, returning the model to a state it has already
    occupied, so two distinct states are mutually reachable. That
    classification is pinned once for all models in test/t_topos_frames.ml
    rather than repeated here, and the negative case below keeps that pin live.
    A preorder is still a thin category, so the presheaf topos over it is
    intact; what the gate establishes is the thing that actually matters, that
    the denotation computes what {!System} computes at every reachable world.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make
    (Stream_sync_capability_model.State)
    (Stream_sync_capability_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Stream_sync_capability_model.Pristine;
    Stream_sync_capability_model.No_io_classification_split;
    Stream_sync_capability_model.No_partial_probe_guard;
    Stream_sync_capability_model.No_epoch_clear;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Stream_sync_capability_model.Pristine -> "pristine"
  | Stream_sync_capability_model.No_io_classification_split ->
      "no-io-classification-split"
  | Stream_sync_capability_model.No_partial_probe_guard ->
      "no-partial-probe-guard"
  | Stream_sync_capability_model.No_epoch_clear -> "no-epoch-clear"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Stream_sync_capability_statements.formula
      @ Topos_gate.subformulas st.Stream_sync_capability_statements.antecedent)
    Stream_sync_capability_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Validator.V0 ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list is {!Stream_sync_capability_model.inits}, exactly what
    [spec_of] passes. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:Stream_sync_capability_model.inits
       ~next:(Stream_sync_capability_model.next_with mut)
       ~view:Stream_sync_capability_model.view
       ~label:Stream_sync_capability_model.label ~formulas)

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
  with_verdict Stream_sync_capability_model.Pristine (fun v ->
      Alcotest.(check bool) "reachability is a preorder, not a poset" false
        v.G.poset)

(** Deleting the classical bridge changes a verdict here, so the reduction gate
    above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Stream_sync_capability_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "stream_sync_capability-topos"
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
