(** The topos gate for the stream_slot_tenure family:
    {!Stream_slot_tenure_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - the frame classification: reachability here is a PREORDER, not a poset -
      the modeled mechanism undoes itself by design (an admission is evicted and
      re-granted, the responder's select! loop returns to its first peer slice
      every interval), so states are genuinely revisited. A preorder is still a
      thin category, so parallel [W]-arrows are still unique and presheaf
      restriction is still path-independent; the negative pin below is the live
      half of the distinction test/t_topos_frames.ml maintains in both
      directions;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Stream_slot_tenure_model.State)
    (Stream_slot_tenure_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Stream_slot_tenure_model.Pristine;
    Stream_slot_tenure_model.No_stale_prune;
    Stream_slot_tenure_model.Rearm_created_at;
    Stream_slot_tenure_model.Non_consuming_open;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Stream_slot_tenure_model.Pristine -> "pristine"
  | Stream_slot_tenure_model.No_stale_prune -> "no-stale-prune"
  | Stream_slot_tenure_model.Rearm_created_at -> "rearm-created-at"
  | Stream_slot_tenure_model.Non_consuming_open -> "non-consuming-open"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Stream_slot_tenure_statements.formula
      @ Topos_gate.subformulas st.Stream_slot_tenure_statements.antecedent)
    Stream_slot_tenure_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Validator.V0 ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list matches [spec_of] exactly: both frozen requester dispositions. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:
         [
           Stream_slot_tenure_model.initial;
           Stream_slot_tenure_model.initial_requester_silent;
         ]
       ~next:(Stream_slot_tenure_model.next_with mut)
       ~view:Stream_slot_tenure_model.view ~label:Stream_slot_tenure_model.label
       ~formulas)

(** The frame really is the preorder case - RUN, not assumed: the [poset] group
    of section 5.5 was tried first and reported [false] at all four mutations
    (39 pristine worlds), because this mechanism undoes itself by construction.
    So t_topos_frames.ml is pinning a live distinction here and not a stale
    one. *)
let frame_is_a_preorder () =
  with_verdict Stream_slot_tenure_model.Pristine (fun v ->
      Alcotest.(check bool) "reachability is a preorder, not a poset" false
        v.G.poset)

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
  with_verdict Stream_slot_tenure_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "stream_slot_tenure-topos"
    [
      ( "frame",
        [ Alcotest.test_case "preorder-not-poset" `Quick frame_is_a_preorder ]
      );
      ( "reduction",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (reduction_holds m))
          muts );
      ( "reflection",
        [ Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous ] );
    ]
