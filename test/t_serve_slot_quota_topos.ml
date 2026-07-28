(** The topos gate for the serve_slot_quota family:
    {!Serve_slot_quota_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies. That is not an
      accident of this family: every modelled step is an ADMISSION and each one
      strictly advances a component (a peer's in-flight count, Q's stream
      outcome, Q's record outcome), so the reachability relation is acyclic and
      antisymmetry holds. The release routes that would make it a preorder - the
      permit dropped when a served stream finishes and the 15s sweep evicting
      entries older than 30s ([cleanup_stale_pending_requests],
      network/mod.rs:1451-1456) - are deliberately out of this family's scope
      and are the subject of the stream_slot_tenure family;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Serve_slot_quota_model.State) (Serve_slot_quota_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Serve_slot_quota_model.Pristine;
    Serve_slot_quota_model.No_cross_path_count;
    Serve_slot_quota_model.No_per_peer_stream_cap;
    Serve_slot_quota_model.Shared_permit_pool;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Serve_slot_quota_model.Pristine -> "pristine"
  | Serve_slot_quota_model.No_cross_path_count -> "no-cross-path-count"
  | Serve_slot_quota_model.No_per_peer_stream_cap -> "no-per-peer-stream-cap"
  | Serve_slot_quota_model.Shared_permit_pool -> "shared-permit-pool"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Serve_slot_quota_statements.formula
      @ Topos_gate.subformulas st.Serve_slot_quota_statements.antecedent)
    Serve_slot_quota_statements.all

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
       ~init:[ Serve_slot_quota_model.initial ]
       ~next:(Serve_slot_quota_model.next_with mut)
       ~view:Serve_slot_quota_model.view ~label:Serve_slot_quota_model.label
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
  with_verdict Serve_slot_quota_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "serve_slot_quota-topos"
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
