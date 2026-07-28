(** The topos gate for the close_block_syscall family:
    {!Close_block_syscall_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies. Every transition of
      this family strictly advances the block's execution phase and both
      terminals ([Ph_sealed], [Ph_halted]) have no successors, so nothing undoes
      itself and reachability is antisymmetric - and this is asserted, not
      assumed;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for every
      subformula of every statement plus a spanning constructor battery, this
      family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. The battery agent is the
    replay node {!Close_block_syscall_model.replay_observer}, whose view is a
    strict projection of the state - nothing at all before the block seals, the
    header marker afterwards - so the battery's [K] shapes are evaluated over
    genuinely non-singleton classes rather than collapsing to plain truth. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Close_block_syscall_model.State)
    (Close_block_syscall_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Close_block_syscall_model.Pristine;
    Close_block_syscall_model.No_close_marker_gate;
    Close_block_syscall_model.No_env_restore;
    Close_block_syscall_model.Nonzero_basefee_for_syscall;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Close_block_syscall_model.Pristine -> "pristine"
  | Close_block_syscall_model.No_close_marker_gate -> "no-close-marker-gate"
  | Close_block_syscall_model.No_env_restore -> "no-env-restore"
  | Close_block_syscall_model.Nonzero_basefee_for_syscall ->
      "nonzero-basefee-for-syscall"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Close_block_syscall_statements.formula
      @ Topos_gate.subformulas st.Close_block_syscall_statements.antecedent)
    Close_block_syscall_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Close_block_syscall_model.replay_observer ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list matches {!Close_block_syscall_model.spec_of} exactly: the eight
    initial worlds of {!Close_block_syscall_model.inits}. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:Close_block_syscall_model.inits
       ~next:(Close_block_syscall_model.next_with mut)
       ~view:Close_block_syscall_model.view
       ~label:Close_block_syscall_model.label ~formulas)

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
  with_verdict Close_block_syscall_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "close_block_syscall-topos"
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
