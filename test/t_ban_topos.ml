(** The topos gate for the ban family (DESIGN BAN #2, #5): {!Ban_model}'s
    checker is [Denote.Make], so the family owes the three obligations of
    {!Topos_gate} on its own reachable graph, under the pristine model and
    under every mutation that pins one of its statements.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded
      for this family);
    - [is_true ∘ grade = System.sat] over every subformula of S2 and S5 plus
      the spanning constructor battery, at every reachable world. This is the
      family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

module G = Topos_gate.Make (Ban_model.State) (Ban_model.View)

(** Pristine plus both statement pins: the gate must hold on the mutants too,
    since the mutation tests read verdicts off the mutated systems. *)
let muts = [ Ban_model.Pristine; Ban_model.Charge_relayer; Ban_model.No_exemption ]

let mut_name = function
  | Ban_model.Pristine -> "pristine"
  | Ban_model.Charge_relayer -> "charge-relayer"
  | Ban_model.No_exemption -> "no-exemption"

(** Three contingent atoms of this family: the hidden Byzantine branch fact,
    the victim's evidence local, and the terminal phase. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Ban_model.Byz_v3;
      Ban_model.Evidence Validator.V2;
      Ban_model.At_done;
    ]

let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Ban_statements.formula
      @ Topos_gate.subformulas st.Ban_statements.antecedent)
    Ban_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V2
      ~group:Ban_model.honest

let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:[ Ban_model.initial ] ~next:(Ban_model.next_with mut)
       ~view:Ban_model.view ~label:Ban_model.label ~formulas)

let poset_certified mut () =
  with_verdict mut (fun v ->
      Alcotest.(check bool)
        ("W is a finite poset over " ^ Int.to_string v.G.worlds ^ " worlds")
        true v.G.poset)

let reduction_holds mut () =
  with_verdict mut (fun v ->
      Alcotest.(check (option int))
        ("is_true ∘ grade = System.sat over "
        ^ Int.to_string v.G.checked
        ^ " formulas × "
        ^ Int.to_string v.G.worlds
        ^ " worlds")
        None v.G.mismatch)

let reflection_non_vacuous () =
  with_verdict Ban_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "ban-topos"
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
        [
          Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous;
        ] );
    ]
