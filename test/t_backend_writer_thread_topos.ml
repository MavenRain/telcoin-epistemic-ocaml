(** The topos gate for the backend_writer_thread family:
    {!Backend_writer_thread_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset: every component of the state is monotone -
      each logical transaction runs [idle -> open -> committed | dropped] and
      never restarts, the modelled key runs
      [unwritten -> pending -> on_disk | discarded], and the writer thread runs
      [running -> exited] and is terminal there - so no state is ever returned
      to and {!Frame.certify_functorial} gets antisymmetry. The overlap counter
      does go up and down, but only as a function of the monotone lifecycles,
      so it never closes a cycle;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make
    (Backend_writer_thread_model.State)
    (Backend_writer_thread_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Backend_writer_thread_model.Pristine;
    Backend_writer_thread_model.No_end_txn_on_drop;
    Backend_writer_thread_model.No_shutdown_break;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Backend_writer_thread_model.Pristine -> "pristine"
  | Backend_writer_thread_model.No_end_txn_on_drop -> "no-end-txn-on-drop"
  | Backend_writer_thread_model.No_shutdown_break -> "no-shutdown-break"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Backend_writer_thread_statements.formula
      @ Topos_gate.subformulas st.Backend_writer_thread_statements.antecedent)
    Backend_writer_thread_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Validator.V0 ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list matches [spec_of] exactly: the single quiescent start state. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Backend_writer_thread_model.initial ]
       ~next:(Backend_writer_thread_model.next_with mut)
       ~view:Backend_writer_thread_model.view
       ~label:Backend_writer_thread_model.label ~formulas)

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
  with_verdict Backend_writer_thread_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "backend_writer_thread-topos"
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
