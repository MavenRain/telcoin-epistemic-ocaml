(** The topos gate for the ARCHIVE-EPOCH-IMPORT family:
    {!Archive_epoch_import_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies. This family's graph
      is monotone by construction: the importer only ever moves forward through
      [stream_import], the buffer only fills, the FIFO entry is only ever
      evicted and the reader only ever arrives and resolves, so no state is
      ever returned to;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are named rather than derived: the three atoms below are the
    contingent ones the family's epistemics turn on (both truth values are
    reachable for each on the pristine model), with the peer's possession past
    the epoch boundary first so the battery's [K]/[Everyone]/[Common] shapes
    land on the fact that actually partitions [V0] from [V1]. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Archive_epoch_import_model.State)
    (Archive_epoch_import_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Archive_epoch_import_model.Pristine;
    Archive_epoch_import_model.No_final_header_link;
    Archive_epoch_import_model.No_already_held_shortcircuit;
    Archive_epoch_import_model.No_batch_count_cap;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Archive_epoch_import_model.Pristine -> "pristine"
  | Archive_epoch_import_model.No_final_header_link -> "no-final-header-link"
  | Archive_epoch_import_model.No_already_held_shortcircuit ->
      "no-already-held-shortcircuit"
  | Archive_epoch_import_model.No_batch_count_cap -> "no-batch-count-cap"

(** The family's knowledge agents: the importing node [V0] and the serving peer
    [V1]; [V2]..[V9] carry the constant blank view. *)
let agents = [ Validator.V0; Validator.V1 ]

(** Three contingent atoms: the hidden possession S1's ignorance conjunct is
    about, the publish event both of S1's conjuncts are guarded by, and the
    install window S2 is about. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Archive_epoch_import_model.Peer_holds_beyond_epoch;
      Archive_epoch_import_model.Published;
      Archive_epoch_import_model.Epoch_dir_absent;
    ]

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Archive_epoch_import_statements.formula
      @ Topos_gate.subformulas st.Archive_epoch_import_statements.antecedent)
    Archive_epoch_import_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V0 ~group:agents

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list is [Archive_epoch_import_model.inits], exactly what [spec_of]
    passes. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:Archive_epoch_import_model.inits
       ~next:(Archive_epoch_import_model.next_with mut)
       ~view:Archive_epoch_import_model.view
       ~label:Archive_epoch_import_model.label ~formulas)

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
  with_verdict Archive_epoch_import_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "archive_epoch_import-topos"
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
