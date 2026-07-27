(** The topos gate for the epoch_record family (S1, S2, S3):
    {!Epoch_record_model}'s checker is [Denote.Make], so the family owes the
    three obligations of {!Topos_gate} on its own reachable graph, under the
    pristine model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded
      for this family);
    - [is_true ∘ grade = System.sat] over every subformula of S1, S2 and S3
      plus the spanning constructor battery, at every reachable world: the
      family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

module G =
  Topos_gate.Make (Epoch_record_model.State) (Epoch_record_model.View)

(** Pristine plus all three statement pins: the gate must hold on the mutants
    too, since the mutation tests read verdicts off the mutated systems. *)
let muts =
  [
    Epoch_record_model.Pristine;
    Epoch_record_model.No_quorum_count;
    Epoch_record_model.Cert_conjunct_dropped;
    Epoch_record_model.Cursor_starts_at_latest;
  ]

(** Exhaustive naming of this family's mutation sum. *)
let mut_name = function
  | Epoch_record_model.Pristine -> "pristine"
  | Epoch_record_model.No_quorum_count -> "no-quorum-count"
  | Epoch_record_model.Cert_conjunct_dropped -> "cert-conjunct-dropped"
  | Epoch_record_model.Cursor_starts_at_latest -> "cursor-starts-at-latest"

(** V1 is the sole knowledge agent of this family: V0, V2 and V3 carry the
    constant blank view and never appear under K. *)
let agents = [ Validator.V1 ]

(** Three contingent atoms of this family: the hidden Byzantine endorsement
    fact, V1's own epoch-1 database local, and the terminal cursor phase. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Epoch_record_model.Byz_endorsed;
      Epoch_record_model.Store_cert;
      Epoch_record_model.Collector_past_epoch;
    ]

(** Every subformula of every statement, plus the spanning battery. *)
let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Epoch_record_statements.formula
      @ Topos_gate.subformulas st.Epoch_record_statements.antecedent)
    Epoch_record_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V1 ~group:agents

(** Run the gate on one mutant, mirroring [Epoch_record_model.spec_of]. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Epoch_record_model.initial ]
       ~next:(Epoch_record_model.next_with mut) ~view:Epoch_record_model.view
       ~label:Epoch_record_model.label ~formulas)

(** Obligation 1: the reachable order is a genuine finite poset. *)
let poset_certified mut () =
  with_verdict mut (fun v ->
      Alcotest.(check bool)
        ("W is a finite poset over " ^ Int.to_string v.G.worlds ^ " worlds")
        true v.G.poset)

(** Obligation 2: the denotation agrees with the exact checker everywhere. *)
let reduction_holds mut () =
  with_verdict mut (fun v ->
      Alcotest.(check (option int))
        ("is_true ∘ grade = System.sat over "
        ^ Int.to_string v.G.checked
        ^ " formulas × "
        ^ Int.to_string v.G.worlds
        ^ " worlds")
        None v.G.mismatch)

(** Obligation 3: the classical bridge is load-bearing on this family. *)
let reflection_non_vacuous () =
  with_verdict Epoch_record_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "epoch-record-topos"
    [
      ( "poset",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (poset_certified m))
          muts );
      ( "reduction",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (reduction_holds m))
          muts );
      ("reflection", [ Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous ]);
    ]
