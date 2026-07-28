(** The topos gate for the batch_admit family: {!Batch_admit_model} runs on
    [Denote.Make], so it owes the three obligations of {!Topos_gate} on its own
    reachable graph, under the pristine model and under every mutation that
    pins one of its statements.

    - [W] is a genuine finite poset: every transition of this family resolves a
      report leg that was unresolved or fills a cache slot that was empty, and
      nothing ever un-resolves or un-stores, so reachability is antisymmetric
      as well as reflexive and transitive;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G = Topos_gate.Make (Batch_admit_model.State) (Batch_admit_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Batch_admit_model.Pristine;
    Batch_admit_model.No_gas_ceiling;
    Batch_admit_model.No_blob_reject;
    Batch_admit_model.Digest_covers_received_at;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Batch_admit_model.Pristine -> "pristine"
  | Batch_admit_model.No_gas_ceiling -> "no-gas-ceiling"
  | Batch_admit_model.No_blob_reject -> "no-blob-reject"
  | Batch_admit_model.Digest_covers_received_at -> "digest-covers-received-at"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Batch_admit_statements.formula
      @ Topos_gate.subformulas st.Batch_admit_statements.antecedent)
    Batch_admit_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Validator.V0 ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list matches {!Batch_admit_model.spec_of} exactly. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:Batch_admit_model.inits
       ~next:(Batch_admit_model.next_with mut) ~view:Batch_admit_model.view
       ~label:Batch_admit_model.label ~formulas)

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
  with_verdict Batch_admit_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "batch_admit-topos"
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
