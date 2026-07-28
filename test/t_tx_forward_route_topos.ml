(** The topos gate for the tx_forward_route family:
    {!Tx_forward_route_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset. One forward pass only ever moves forward:
      every transition either steps the chain position of the current
      transaction or advances the [for tx] cursor (forward.rs:139), and the
      lexicographic pair (cursor, chain position) strictly increases at each
      step, so no state is ever returned to and reachability is antisymmetric.
      That holds under all four gate deletions too, because none of them adds a
      backward move: they change which slot a position addresses, whether the
      budget stops the chain, or how one answer is classified. This is asserted
      here, not assumed;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}), which takes the three smallest atoms: [delivered
    (tx1)], [holds(owner,tx1)] and [holds(other,tx1)]. All three are contingent,
    and the last two are invisible to the battery agent, so the battery's [K]
    shapes are evaluated over genuinely non-singleton classes rather than
    collapsing to plain truth. The battery agent is
    {!Tx_forward_route_model.observer}, the family's forwarding agent. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Tx_forward_route_model.State) (Tx_forward_route_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Tx_forward_route_model.Pristine;
    Tx_forward_route_model.Round_robin_owner;
    Tx_forward_route_model.No_forward_budget;
    Tx_forward_route_model.No_transient_fallthrough;
    Tx_forward_route_model.Timeout_counts_as_delivered;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Tx_forward_route_model.Pristine -> "pristine"
  | Tx_forward_route_model.Round_robin_owner -> "round-robin-owner"
  | Tx_forward_route_model.No_forward_budget -> "no-forward-budget"
  | Tx_forward_route_model.No_transient_fallthrough ->
      "no-transient-fallthrough"
  | Tx_forward_route_model.Timeout_counts_as_delivered ->
      "timeout-counts-as-delivered"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Tx_forward_route_statements.formula
      @ Topos_gate.subformulas st.Tx_forward_route_statements.antecedent)
    Tx_forward_route_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Tx_forward_route_model.observer ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list is {!Tx_forward_route_model.inits} itself, which is exactly what
    {!Tx_forward_route_model.spec_of} passes: the eight endpoint
    configurations. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:Tx_forward_route_model.inits
       ~next:(Tx_forward_route_model.next_with mut)
       ~view:Tx_forward_route_model.view ~label:Tx_forward_route_model.label
       ~formulas)

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
  with_verdict Tx_forward_route_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "tx_forward_route-topos"
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
