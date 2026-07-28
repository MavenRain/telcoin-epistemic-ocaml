(** The topos gate for the pack_replay family: {!Pack_replay_model} runs on
    [Denote.Make], so it owes the three obligations of {!Topos_gate} on its own
    reachable graph, under the pristine model and under every mutation that pins
    one of its statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies. Every transition of
      this family strictly advances one of (pack tip, signed tip, received tip,
      execution tip, phase) or flips the epoch flag false-to-true, so nothing
      undoes itself and reachability is antisymmetric - and this is asserted, not
      assumed;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for every
      subformula of every statement plus a spanning constructor battery, this
      family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. The battery agent is the
    observing peer {!Pack_replay_model.observer}, whose view is a strict
    projection of the state, so the battery's [K] shapes are evaluated over
    genuinely non-singleton classes rather than collapsing to plain truth. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G = Topos_gate.Make (Pack_replay_model.State) (Pack_replay_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Pack_replay_model.Pristine;
    Pack_replay_model.No_save_before_publish;
    Pack_replay_model.No_replay_scan;
    Pack_replay_model.No_boundary_recompute;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Pack_replay_model.Pristine -> "pristine"
  | Pack_replay_model.No_save_before_publish -> "no-save-before-publish"
  | Pack_replay_model.No_replay_scan -> "no-replay-scan"
  | Pack_replay_model.No_boundary_recompute -> "no-boundary-recompute"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Pack_replay_statements.formula
      @ Topos_gate.subformulas st.Pack_replay_statements.antecedent)
    Pack_replay_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Pack_replay_model.observer ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list matches {!Pack_replay_model.spec_of} exactly: the single initial
    state. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Pack_replay_model.initial ]
       ~next:(Pack_replay_model.next_with mut) ~view:Pack_replay_model.view
       ~label:Pack_replay_model.label ~formulas)

(** [W] is a genuine finite poset: reflexive, transitive and antisymmetric. *)
let poset_certified mut () =
  with_verdict mut (fun v ->
      Alcotest.(check bool)
        ("W is a finite poset over " ^ Int.to_string v.G.worlds ^ " worlds")
        true v.G.poset)

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
  with_verdict Pack_replay_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "pack_replay-topos"
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
