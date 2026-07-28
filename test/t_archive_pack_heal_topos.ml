(** The topos gate for the ARCHIVE-PACK-HEAL family:
    {!Archive_pack_heal_model} runs on [Denote.Make], so it owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset, so the presheaf topos over it is the
      construction lib/internal/DESIGN.md sec.1 specifies. This family's graph
      is monotone by construction: the data file only ever grows while the
      writer runs, the crash moves the pack into the at-rest phase and the
      reopen phases are terminal, so nothing ever returns to a state it left;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are named rather than derived: the three atoms below are the
    contingent ones this family's epistemics turn on (both truth values are
    reachable for each), with the peer's possession first so the battery's
    [K]/[Everyone]/[Common] shapes land on the agent that has a real
    partition. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Archive_pack_heal_model.State) (Archive_pack_heal_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Archive_pack_heal_model.Pristine;
    Archive_pack_heal_model.No_shrink_clamp;
    Archive_pack_heal_model.No_static_consistency_gate;
    Archive_pack_heal_model.No_write_failure_latch;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Archive_pack_heal_model.Pristine -> "pristine"
  | Archive_pack_heal_model.No_shrink_clamp -> "no-shrink-clamp"
  | Archive_pack_heal_model.No_static_consistency_gate ->
      "no-static-consistency-gate"
  | Archive_pack_heal_model.No_write_failure_latch -> "no-write-failure-latch"

(** The family's knowledge agents: the node that owns the pack [V0] and the
    remote holder [V1]; [V2]..[V9] carry the constant blank view. *)
let agents = [ Validator.V0; Validator.V1 ]

(** Three contingent atoms: the peer-possession fact S1's ignorance conjunct
    is about, the hidden latch S3's ignorance conjunct is about, and the
    repair outcome that gates the first of those. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Archive_pack_heal_model.Peer_holds_epoch_bytes;
      Archive_pack_heal_model.Pack_latched;
      Archive_pack_heal_model.Heal_dropped_output;
    ]

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Archive_pack_heal_statements.formula
      @ Topos_gate.subformulas st.Archive_pack_heal_statements.antecedent)
    Archive_pack_heal_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V0 ~group:agents

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list matches [spec_of] exactly: the single freshly created pack. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Archive_pack_heal_model.initial ]
       ~next:(Archive_pack_heal_model.next_with mut)
       ~view:Archive_pack_heal_model.view ~label:Archive_pack_heal_model.label
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

(** Deleting the classical bridge changes a verdict here, so the reduction
    gate above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Archive_pack_heal_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "archive_pack_heal-topos"
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
