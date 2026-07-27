(** The topos gate for the ahead-certificate catch-up family (DESIGN
    CONSENSUS-EXT #13): {!Catchup_model}'s checker is [Denote.Make], so the
    family owes the three obligations of {!Topos_gate} on its own reachable
    graph, under the pristine model and under the mutation that pins its
    statement.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded
      for this family);
    - [is_true ∘ grade = System.sat] over every subformula of S13 plus the
      spanning constructor battery, at every reachable world - the family's
      instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

module G = Topos_gate.Make (Catchup_model.State) (Catchup_model.View)

(** Pristine plus the single statement pin: the gate must hold on the mutant
    too, since the mutation test reads its verdict off the mutated system. *)
let muts = [ Catchup_model.Pristine; Catchup_model.Drop_catch_up ]

(** Exhaustive naming of this family's mutation enum. *)
let mut_name = function
  | Catchup_model.Pristine -> "pristine"
  | Catchup_model.Drop_catch_up -> "drop-catch-up"

(** Three contingent atoms of this family: the hidden lag-branch fact (the
    victim's own R1 certificate forms only on the [No_lag] branch), the
    victim's proposer-round local that the statement's antecedent reads, and
    the terminal phase. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Catchup_model.Cert_formed
        { Catchup_model.author = Validator.V2; round = Catchup_model.R1 };
      Catchup_model.Proposer_round_le (Validator.V2, Catchup_model.R0);
      Catchup_model.At_done;
    ]

(** Every subformula of every statement, plus the spanning battery seeded on
    the contingent atoms. The lag victim is this family's only knowledge
    agent (the family is pure temporal liveness, so its knowledge group is
    the singleton [victim]). *)
let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Catchup_statements.formula
      @ Topos_gate.subformulas st.Catchup_statements.antecedent)
    Catchup_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Catchup_model.victim
      ~group:[ Catchup_model.victim ]

(** Run the gate on one mutant, mirroring {!Catchup_model.spec_of} exactly. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:[ Catchup_model.initial ]
       ~next:(Catchup_model.next_with mut) ~view:Catchup_model.view
       ~label:Catchup_model.label ~formulas)

(** Obligation 1: the reachable order is a finite poset. *)
let poset_certified mut () =
  with_verdict mut (fun v ->
      Alcotest.(check bool)
        ("W is a finite poset over " ^ Int.to_string v.G.worlds ^ " worlds")
        true v.G.poset)

(** Obligation 2: the denotation reduces to the exact checker. *)
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
  with_verdict Catchup_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

(** The three alcotest groups: poset and reduction per mutation, reflection
    non-vacuity on the pristine model. *)
let () =
  Alcotest.run "catchup-topos"
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
