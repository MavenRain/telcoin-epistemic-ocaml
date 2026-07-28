(** The topos gate for the archive_hash_index family:
    {!Archive_hash_index_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the
    pristine model and under every mutation that pins one of its statements.

    - [W] is classified by [Frame.certify_functorial]: this family's
      transition relation genuinely undoes itself - a sealed pack answers
      lookups forever and the clean-cache word cycles among its slot
      configurations, e.g. admitting the cold bucket into the word [b1; b1]
      evicts the front and pushes it straight back - so reachability here is a
      PREORDER, not a poset, and the negative pin below is the live
      classification. A preorder is still a thin category, so parallel
      [W]-arrows remain unique and presheaf restriction is still
      path-independent.
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Archive_hash_index_model.State) (Archive_hash_index_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Archive_hash_index_model.Pristine;
    Archive_hash_index_model.No_growth_gate;
    Archive_hash_index_model.No_cache_eviction_loop;
    Archive_hash_index_model.No_chain_decrease_guard;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Archive_hash_index_model.Pristine -> "pristine"
  | Archive_hash_index_model.No_growth_gate -> "no-growth-gate"
  | Archive_hash_index_model.No_cache_eviction_loop -> "no-cache-eviction-loop"
  | Archive_hash_index_model.No_chain_decrease_guard -> "no-chain-decrease-guard"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Archive_hash_index_statements.formula
      @ Topos_gate.subformulas st.Archive_hash_index_statements.antecedent)
    Archive_hash_index_statements.all

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
       ~init:[ Archive_hash_index_model.initial ]
       ~next:(Archive_hash_index_model.next_with mut)
       ~view:Archive_hash_index_model.view ~label:Archive_hash_index_model.label
       ~formulas)

(** The frame really is the preorder case, so t_topos_frames.ml is pinning a
    live distinction and not a stale one. *)
let frame_is_a_preorder () =
  with_verdict Archive_hash_index_model.Pristine (fun v ->
      Alcotest.(check bool) "reachability is a preorder, not a poset" false
        v.G.poset)

(** The topos denotation agrees with the original checker, world by world. *)
let reduction_holds mut () =
  with_verdict mut (fun v ->
      Alcotest.(check (option int))
        ("is_true o grade = System.sat over " ^ Int.to_string v.G.checked
       ^ " formulas x " ^ Int.to_string v.G.worlds ^ " worlds")
        None v.G.mismatch)

(** Deleting the classical bridge changes a verdict here, so the reduction
    gate above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Archive_hash_index_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "archive_hash_index-topos"
    [
      ("frame", [ Alcotest.test_case "preorder-not-poset" `Quick frame_is_a_preorder ]);
      ( "reduction",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (reduction_holds m))
          muts );
      ("reflection", [ Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous ]);
    ]
