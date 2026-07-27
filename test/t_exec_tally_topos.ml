(** The topos gate for the exec-tally family (DESIGN EXEC-TALLY S8):
    {!Exec_tally_model}'s checker is [Denote.Make], so the family owes the
    three obligations of {!Topos_gate} on its own reachable graph, under the
    pristine model and under every mutation that pins its statement.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded
      for this family);
    - [is_true ∘ grade = System.sat] over every subformula of S8 plus the
      spanning constructor battery, at every reachable world - the family's
      instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

module G = Topos_gate.Make (Exec_tally_model.State) (Exec_tally_model.View)

(** Pristine plus the single statement pin: the gate must hold on the mutant
    too, since the mutation tests read verdicts off the mutated system. *)
let muts = [ Exec_tally_model.Pristine; Exec_tally_model.Weak_sig_threshold ]

(** Exhaustive naming of this family's mutation enum. *)
let mut_name = function
  | Exec_tally_model.Pristine -> "pristine"
  | Exec_tally_model.Weak_sig_threshold -> "weak-sig-threshold"

(** The family's knowledge-agent group: V0, the non-executing state-sync
    observer, is the only agent (V1/V2/V3 carry the constant [Blind] view). *)
let observers = [ Validator.V0 ]

(** Three contingent atoms of this family: the hidden Byzantine
    fabricate-branch fact, the honest CVVs' save local, and the observer's
    terminal watch advance. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Exec_tally_model.In_tally Validator.V3;
      Exec_tally_model.Honest_saved;
      Exec_tally_model.Advance_o;
    ]

(** Every subformula of every statement, plus the spanning battery. *)
let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Exec_tally_statements.formula
      @ Topos_gate.subformulas st.Exec_tally_statements.antecedent)
    Exec_tally_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V0 ~group:observers

(** Run the gate on one mutation and hand the verdict to [k]. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Exec_tally_model.initial ]
       ~next:(Exec_tally_model.next_with mut)
       ~view:Exec_tally_model.view ~label:Exec_tally_model.label ~formulas)

(** Obligation 1: the reachable order is a genuine finite poset. *)
let poset_certified mut () =
  with_verdict mut (fun v ->
      Alcotest.(check bool)
        ("W is a finite poset over " ^ Int.to_string v.G.worlds ^ " worlds")
        true v.G.poset)

(** Obligation 2: the denotation reduces to the exact checker everywhere. *)
let reduction_holds mut () =
  with_verdict mut (fun v ->
      Alcotest.(check (option int))
        ("is_true ∘ grade = System.sat over "
        ^ Int.to_string v.G.checked
        ^ " formulas × "
        ^ Int.to_string v.G.worlds
        ^ " worlds")
        None v.G.mismatch)

(** Obligation 3: the classical bridge is not vacuous on this family. *)
let reflection_non_vacuous () =
  with_verdict Exec_tally_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

(** The three obligation groups, one case per mutation for the first two. *)
let () =
  Alcotest.run "exec_tally-topos"
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
