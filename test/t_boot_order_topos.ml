(** The topos gate for the BOOT-ORDER family: {!Boot_order_model} runs on
    [Denote.Make], so it owes the three obligations of {!Topos_gate} on its own
    reachable graph, under the pristine model and under every mutation that
    pins one of its statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies (this family's boot
      chain is monotone: no phase, cell or connection ever reverts);
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are named rather than derived: the three atoms below are the
    contingent ones this family's epistemics turn on (both truth values are
    reachable for each), with the peer's knowledge operand first so the
    battery's [K]/[Everyone]/[Common] shapes land on the agent that has a real
    partition. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G = Topos_gate.Make (Boot_order_model.State) (Boot_order_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Boot_order_model.Pristine;
    Boot_order_model.No_marker_heal;
    Boot_order_model.No_recent_blocks_prime;
    Boot_order_model.Initial_only_network_gate;
    Boot_order_model.Rebind_on_replay;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Boot_order_model.Pristine -> "pristine"
  | Boot_order_model.No_marker_heal -> "no-marker-heal"
  | Boot_order_model.No_recent_blocks_prime -> "no-recent-blocks-prime"
  | Boot_order_model.Initial_only_network_gate -> "initial-only-network-gate"
  | Boot_order_model.Rebind_on_replay -> "rebind-on-replay"

(** The family's knowledge agents: the booting node [V0] and its peer [V1];
    [V2]..[V9] carry the constant blank view. *)
let agents = [ Validator.V0; Validator.V1 ]

(** Three contingent atoms: the peer-facing bind fact the family's positive K
    is about, the peer's own dial outcome, and the hidden startup shape the
    booting node is ignorant of. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Boot_order_model.Listener_bound;
      Boot_order_model.Peer_dialed_in;
      Boot_order_model.Close_on_replay;
    ]

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Boot_order_statements.formula
      @ Topos_gate.subformulas st.Boot_order_statements.antecedent)
    Boot_order_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V1 ~group:agents

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list matches [spec_of] exactly: both startup shapes. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:Boot_order_model.inits
       ~next:(Boot_order_model.next_with mut) ~view:Boot_order_model.view
       ~label:Boot_order_model.label ~formulas)

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

(** Deleting the classical bridge changes a verdict here, so the reduction
    gate above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Boot_order_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "boot_order-topos"
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
