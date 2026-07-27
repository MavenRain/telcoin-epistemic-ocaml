(** The topos gate for the own_durable family: {!Own_durable_model} runs on
    [Denote.Make], so it owes the three obligations of {!Topos_gate} on its
    own reachable graph, under the pristine model and under every mutation
    that pins one of its statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor
      battery, this family's instance of the DESIGN sec.6 gate 2
      differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G = Topos_gate.Make (Own_durable_model.State) (Own_durable_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Own_durable_model.Pristine;
    Own_durable_model.No_disk_write;
    Own_durable_model.No_proposed_cert_guard;
    Own_durable_model.No_store_before_publish;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Own_durable_model.Pristine -> "pristine"
  | Own_durable_model.No_disk_write -> "no-disk-write"
  | Own_durable_model.No_proposed_cert_guard -> "no-proposed-cert-guard"
  | Own_durable_model.No_store_before_publish -> "no-store-before-publish"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Own_durable_statements.formula
      @ Topos_gate.subformulas st.Own_durable_statements.antecedent)
    Own_durable_statements.all

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
    (G.run ~init:[ Own_durable_model.initial ] ~next:(Own_durable_model.next_with mut)
       ~view:Own_durable_model.view ~label:Own_durable_model.label ~formulas)

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
  with_verdict Own_durable_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "own_durable-topos"
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
