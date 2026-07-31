(** The topos gate for the epoch_sync family: {!Epoch_sync_model} runs on
    [Denote.Make], so it owes the reduction and reflection obligations of
    {!Topos_gate} on its own reachable graph, under the pristine model and
    under every mutation that pins one of its statements.

    This family has NO poset case. Its reachability relation is a preorder,
    not a poset - it models a mechanism that undoes itself, so two distinct
    states are mutually reachable - and that classification is pinned once
    for all 69 models in test/t_topos_frames.ml, and re-pinned negatively
    below. A preorder is still a thin category, so the presheaf topos over
    it is intact; what the gate below establishes is the thing that actually
    matters, that the denotation computes what {!System} computes at every
    reachable world.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}). *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G = Topos_gate.Make (Epoch_sync_model.State) (Epoch_sync_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Epoch_sync_model.Pristine;
    Epoch_sync_model.No_parent_hash_check;
    Epoch_sync_model.No_cert_quorum_check;
    Epoch_sync_model.Committee_targeted_fetch;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Epoch_sync_model.Pristine -> "pristine"
  | Epoch_sync_model.No_parent_hash_check -> "no-parent-hash-check"
  | Epoch_sync_model.No_cert_quorum_check -> "no-cert-quorum-check"
  | Epoch_sync_model.Committee_targeted_fetch -> "committee-targeted-fetch"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Epoch_sync_statements.formula
      @ Topos_gate.subformulas st.Epoch_sync_statements.antecedent)
    Epoch_sync_statements.all

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
    (G.run ~init:[ Epoch_sync_model.initial ] ~next:(Epoch_sync_model.next_with mut)
       ~view:Epoch_sync_model.view ~label:Epoch_sync_model.label ~formulas)

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

(** The frame really is the preorder case, so t_topos_frames.ml is pinning a
    live distinction and not a stale one. *)
let frame_is_a_preorder () =
  with_verdict
    Epoch_sync_model.Pristine
    (fun v ->
      Alcotest.(check bool) "reachability is a preorder, not a poset" false
        v.G.poset)

(** Deleting the classical bridge changes a verdict here, so the reduction
    gate above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Epoch_sync_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "epoch_sync-topos"
    [
      ( "reduction",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (reduction_holds m))
          muts );
      ( "frame",
        [ Alcotest.test_case "preorder-not-poset" `Quick frame_is_a_preorder ] );
      ( "reflection",
        [ Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous ] );
    ]
