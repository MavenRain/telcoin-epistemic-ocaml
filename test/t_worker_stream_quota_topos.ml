(** The topos gate for the worker_stream_quota family:
    {!Worker_stream_quota_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [W] is a genuine finite PREORDER, not a poset: the mechanism undoes
      itself everywhere (a pending request is expired or served, a serve
      finishes and releases its permit, a sync exchange is admitted, cleared
      and released), so reachability has cycles and is not antisymmetric. That
      is the documented four-of-twenty-seven case, and a preorder is still a
      thin category, so presheaf restriction is still path-independent. The
      classification is pinned negatively below, exactly as
      test/t_admission_topos.ml does, so t_topos_frames.ml is pinning a live
      distinction.
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Worker_stream_quota_model.State)
    (Worker_stream_quota_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Worker_stream_quota_model.Pristine;
    Worker_stream_quota_model.No_legacy_per_peer_cap;
    Worker_stream_quota_model.No_serving_guard;
    Worker_stream_quota_model.No_pre_read_sync_shed;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Worker_stream_quota_model.Pristine -> "pristine"
  | Worker_stream_quota_model.No_legacy_per_peer_cap -> "no-legacy-per-peer-cap"
  | Worker_stream_quota_model.No_serving_guard -> "no-serving-guard"
  | Worker_stream_quota_model.No_pre_read_sync_shed -> "no-pre-read-sync-shed"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Worker_stream_quota_statements.formula
      @ Topos_gate.subformulas st.Worker_stream_quota_statements.antecedent)
    Worker_stream_quota_statements.all

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
       ~init:[ Worker_stream_quota_model.initial ]
       ~next:(Worker_stream_quota_model.next_with mut)
       ~view:Worker_stream_quota_model.view
       ~label:Worker_stream_quota_model.label ~formulas)

(** The frame really is the preorder case, so t_topos_frames.ml is pinning a
    live distinction and not a stale one. *)
let frame_is_a_preorder () =
  with_verdict Worker_stream_quota_model.Pristine (fun v ->
      Alcotest.(check bool) "reachability is a preorder, not a poset" false
        v.G.poset)

(** The topos denotation agrees with the original checker, world by world. *)
let reduction_holds mut () =
  with_verdict mut (fun v ->
      Alcotest.(check (option int))
        ("is_true o grade = System.sat over " ^ Int.to_string v.G.checked
       ^ " formulas x " ^ Int.to_string v.G.worlds ^ " worlds")
        None v.G.mismatch)

(** Deleting the classical bridge changes a verdict here, so the reduction gate
    above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Worker_stream_quota_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "worker_stream_quota-topos"
    [
      ("frame", [ Alcotest.test_case "preorder-not-poset" `Quick frame_is_a_preorder ]);
      ( "reduction",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (reduction_holds m))
          muts );
      ("reflection", [ Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous ]);
    ]
