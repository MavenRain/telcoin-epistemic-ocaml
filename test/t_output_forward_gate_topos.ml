(** The topos gate for the OUTPUT_FORWARD_GATE family:
    {!Output_forward_gate_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies. Every transition here
      strictly advances a monotone quantity - the commit position, the number of
      forwards, the length of the execution order, or one of the one-shot flags
      ([rebroadcast], [skipped], [status], the two violation flags) - so no
      state is ever returned to;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for every
      subformula of every statement plus a spanning constructor battery, this
      family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Output_forward_gate_model.State)
    (Output_forward_gate_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Output_forward_gate_model.Pristine;
    Output_forward_gate_model.No_stale_arm;
    Output_forward_gate_model.No_gap_arm;
    Output_forward_gate_model.Queue_pop_back;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Output_forward_gate_model.Pristine -> "pristine"
  | Output_forward_gate_model.No_stale_arm -> "no-stale-arm"
  | Output_forward_gate_model.No_gap_arm -> "no-gap-arm"
  | Output_forward_gate_model.Queue_pop_back -> "queue-pop-back"

(** Three contingent atoms of this family, named rather than derived: the
    forwarder's stale skip, the engine's execution of output 1, and the epoch
    halt. Both truth values of each are reachable on the pristine model. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Output_forward_gate_model.Stale_skipped;
      Output_forward_gate_model.Executed_1;
      Output_forward_gate_model.Epoch_errored;
    ]

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Output_forward_gate_statements.formula
      @ Topos_gate.subformulas st.Output_forward_gate_statements.antecedent)
    Output_forward_gate_statements.all

(** The checked set: the statements plus the spanning battery over this
    family's two knowledge agents, the forwarder V1 and the engine V2. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V1
      ~group:[ Validator.V1; Validator.V2 ]

(** Run the gate under one mutation, mirroring
    {!Output_forward_gate_model.spec_of} exactly: both hidden-ring initial
    states. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:
         [
           Output_forward_gate_model.initial;
           Output_forward_gate_model.initial_rebroadcast_buffered;
         ]
       ~next:(Output_forward_gate_model.next_with mut)
       ~view:Output_forward_gate_model.view
       ~label:Output_forward_gate_model.label ~formulas)

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
  with_verdict Output_forward_gate_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "output-forward-gate-topos"
    [
      ( "poset",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (poset_certified m))
          muts );
      ( "reduction",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (reduction_holds m))
          muts );
      ("reflection", [ Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous ]);
    ]
