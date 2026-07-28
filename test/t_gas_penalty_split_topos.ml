(** The topos gate for the gas_penalty_split family:
    {!Gas_penalty_split_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the
    pristine model and under every mutation that pins one of its
    statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies. This family
      models a strictly one-way pipeline - a batch is proposed, admitted,
      then settled by the handler, and nothing undoes a settlement - so
      reachability is antisymmetric and the poset case applies;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor
      battery, this family's instance of the DESIGN sec.6 gate 2
      differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Gas_penalty_split_model.State) (Gas_penalty_split_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Gas_penalty_split_model.Pristine;
    Gas_penalty_split_model.No_small_limit_exemption;
    Gas_penalty_split_model.Refund_aware_penalty;
    Gas_penalty_split_model.Burn_the_penalty;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Gas_penalty_split_model.Pristine -> "pristine"
  | Gas_penalty_split_model.No_small_limit_exemption ->
      "no-small-limit-exemption"
  | Gas_penalty_split_model.Refund_aware_penalty -> "refund-aware-penalty"
  | Gas_penalty_split_model.Burn_the_penalty -> "burn-the-penalty"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Gas_penalty_split_statements.formula
      @ Topos_gate.subformulas st.Gas_penalty_split_statements.antecedent)
    Gas_penalty_split_statements.all

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
    (G.run
       ~init:[ Gas_penalty_split_model.initial ]
       ~next:(Gas_penalty_split_model.next_with mut)
       ~view:Gas_penalty_split_model.view ~label:Gas_penalty_split_model.label
       ~formulas)

(** [W] is a genuine finite poset: reflexive, transitive and
    antisymmetric. *)
let poset_certified mut () =
  with_verdict mut (fun v ->
      Alcotest.(check bool)
        ("W is a finite poset over " ^ Int.to_string v.G.worlds ^ " worlds")
        true v.G.poset)

(** The topos denotation agrees with the original checker, world by
    world. *)
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
  with_verdict Gas_penalty_split_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "gas_penalty_split-topos"
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
