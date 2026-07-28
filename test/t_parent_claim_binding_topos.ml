(** The topos gate for the PARENT_CLAIM_BINDING family:
    {!Parent_claim_binding_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the
    pristine model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies. Every transition of
      this family strictly advances a phase index inside one scenario
      component, so reachability is acyclic and antisymmetry holds;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are named explicitly rather than taken from
    {!Topos_gate.seeds}: the three chosen atoms are the family's
    FUTURE-CLOSED contingent ones ([exists(d)] is a constant of the hidden
    world, [stored(j,d)] and [timeout(j,h_b)] are absorbing), which keeps the
    battery's bare [Implies] and [Not (Ag (Not _))] shapes off the
    non-persistent atoms ([bound=a], [blocked], [offered]) whose graded and
    Boolean readings the battery is not intended to probe. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Parent_claim_binding_model.State)
    (Parent_claim_binding_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Parent_claim_binding_model.Pristine;
    Parent_claim_binding_model.No_requester_binding;
    Parent_claim_binding_model.No_vacant_claim;
    Parent_claim_binding_model.No_author_parent_filter;
    Parent_claim_binding_model.No_evaluation_deadline;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Parent_claim_binding_model.Pristine -> "pristine"
  | Parent_claim_binding_model.No_requester_binding -> "no-requester-binding"
  | Parent_claim_binding_model.No_vacant_claim -> "no-vacant-claim"
  | Parent_claim_binding_model.No_author_parent_filter ->
      "no-author-parent-filter"
  | Parent_claim_binding_model.No_evaluation_deadline ->
      "no-evaluation-deadline"

(** The three future-closed contingent atoms of this family. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Parent_claim_binding_model.D_exists;
      Parent_claim_binding_model.Stored;
      Parent_claim_binding_model.Hb_timedout;
    ]

(** [V1] (the voter [j]) is this family's only knowledge agent; [V2] (the
    proposer [a]) has a real but never-[K]'d view. The battery's group is the
    two of them. *)
let knowers = [ Validator.V1; Validator.V2 ]

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Parent_claim_binding_statements.formula
      @ Topos_gate.subformulas st.Parent_claim_binding_statements.antecedent)
    Parent_claim_binding_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V1 ~group:knowers

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list is {!Parent_claim_binding_model.inits}, exactly as [spec_of]
    passes it. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:Parent_claim_binding_model.inits
       ~next:(Parent_claim_binding_model.next_with mut)
       ~view:Parent_claim_binding_model.view
       ~label:Parent_claim_binding_model.label ~formulas)

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
  with_verdict Parent_claim_binding_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "parent_claim_binding-topos"
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
