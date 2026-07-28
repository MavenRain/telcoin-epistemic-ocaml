(** The topos gate for the TEL_DISPATCH_SURFACE family:
    {!Tel_dispatch_surface_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies. Every transition here
      strictly advances the phase - [Choose -> Dispatched -> Settled] - and no
      transition ever returns to an earlier phase, so no state is ever returned
      to. (The revert rollback in {!Tel_dispatch_surface_model.settled_of} undoes
      a storage write but does so while advancing the phase, so it does not
      create a cycle.)
    - [is_true (grade phi s) = System.sat phi] at every reachable world for every
      subformula of every statement plus a spanning constructor battery, this
      family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Tel_dispatch_surface_model.State)
    (Tel_dispatch_surface_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Tel_dispatch_surface_model.Pristine;
    Tel_dispatch_surface_model.No_short_calldata_guard;
    Tel_dispatch_surface_model.Open_selector_fallthrough;
    Tel_dispatch_surface_model.Frame_scoped_storage;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Tel_dispatch_surface_model.Pristine -> "pristine"
  | Tel_dispatch_surface_model.No_short_calldata_guard -> "no-short-calldata-guard"
  | Tel_dispatch_surface_model.Open_selector_fallthrough ->
      "open-selector-fallthrough"
  | Tel_dispatch_surface_model.Frame_scoped_storage -> "frame-scoped-storage"

(** Three contingent atoms of this family, named rather than derived: the burn
    that settled, the produced block, and the dispatcher's rejection. Both truth
    values of each are reachable on the pristine model. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Tel_dispatch_surface_model.Burn_took_effect;
      Tel_dispatch_surface_model.Block_produced;
      Tel_dispatch_surface_model.Dispatch_errored;
    ]

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Tel_dispatch_surface_statements.formula
      @ Topos_gate.subformulas st.Tel_dispatch_surface_statements.antecedent)
    Tel_dispatch_surface_statements.all

(** The checked set: the statements plus the spanning battery over this family's
    three knowledge agents - the dispatcher frame V1, the on-chain supply reader
    V2 (the one that carries the family's positive [K]) and the event-stream
    consumer V3. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V2
      ~group:[ Validator.V1; Validator.V2; Validator.V3 ]

(** Run the gate under one mutation, mirroring
    {!Tel_dispatch_surface_model.spec_of} exactly: the single initial state. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Tel_dispatch_surface_model.initial ]
       ~next:(Tel_dispatch_surface_model.next_with mut)
       ~view:Tel_dispatch_surface_model.view
       ~label:Tel_dispatch_surface_model.label ~formulas)

(** Obligation 1: [W] is a genuine finite poset - reflexive, transitive and
    antisymmetric. *)
let poset_certified mut () =
  with_verdict mut (fun v ->
      Alcotest.(check bool)
        ("W is a finite poset over " ^ Int.to_string v.G.worlds ^ " worlds")
        true v.G.poset)

(** Obligation 2: the topos denotation agrees with the original checker, world
    by world. *)
let reduction_holds mut () =
  with_verdict mut (fun v ->
      Alcotest.(check (option int))
        ("is_true o grade = System.sat over "
        ^ Int.to_string v.G.checked
        ^ " formulas x "
        ^ Int.to_string v.G.worlds
        ^ " worlds")
        None v.G.mismatch)

(** Obligation 3: deleting the classical bridge changes a verdict here, so the
    reduction gate above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Tel_dispatch_surface_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "tel-dispatch-surface-topos"
    [
      ( "poset",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (poset_certified m))
          muts );
      ( "reduction",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (reduction_holds m))
          muts );
      ( "reflection",
        [ Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous ] );
    ]
