(** The topos gate for the record_serve_pool family:
    {!Record_serve_pool_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - the frame classification of [W] (see the "frame" group below);
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Record_serve_pool_model.State) (Record_serve_pool_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Record_serve_pool_model.Pristine;
    Record_serve_pool_model.No_per_peer_record_cap;
    Record_serve_pool_model.No_record_admission_gate;
    Record_serve_pool_model.No_unaddressed_request_reject;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Record_serve_pool_model.Pristine -> "pristine"
  | Record_serve_pool_model.No_per_peer_record_cap -> "no-per-peer-record-cap"
  | Record_serve_pool_model.No_record_admission_gate ->
      "no-record-admission-gate"
  | Record_serve_pool_model.No_unaddressed_request_reject ->
      "no-unaddressed-request-reject"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Record_serve_pool_statements.formula
      @ Topos_gate.subformulas st.Record_serve_pool_statements.antecedent)
    Record_serve_pool_statements.all

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
       ~init:[ Record_serve_pool_model.initial ]
       ~next:(Record_serve_pool_model.next_with mut)
       ~view:Record_serve_pool_model.view ~label:Record_serve_pool_model.label
       ~formulas)

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

(** The frame really is the preorder case - the flooding requesters' slots are
    admitted AND released ([PeerSlotPermit]'s [Drop], network/mod.rs:305-315),
    so the idle region of the graph genuinely undoes itself and two distinct
    states are mutually reachable - so t_topos_frames.ml is pinning a live
    distinction and not a stale one. *)
let frame_is_a_preorder () =
  with_verdict Record_serve_pool_model.Pristine (fun v ->
      Alcotest.(check bool) "reachability is a preorder, not a poset" false
        v.G.poset)

(** Deleting the classical bridge changes a verdict here, so the reduction gate
    above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Record_serve_pool_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "record_serve_pool-topos"
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
