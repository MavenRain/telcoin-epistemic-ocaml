(** The topos gate for the pre-vote execution-tip family (DESIGN EXEC_TIP #1,
    #2, #3): {!Exec_tip_model}'s checker is [Denote.Make], so the family owes
    the three obligations of {!Topos_gate} on its own reachable graph, under the
    pristine model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded for
      this family);
    - [is_true ∘ grade = System.sat] over every subformula of S1, S2 and S3 plus
      the spanning constructor battery, at every reachable world - the family's
      instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

module G = Topos_gate.Make (Exec_tip_model.State) (Exec_tip_model.View)

(** Pristine plus both statement pins: the gate must hold on the mutants too,
    since the mutation tests read verdicts off the mutated systems. *)
let muts =
  [
    Exec_tip_model.Pristine;
    Exec_tip_model.No_execution_gate;
    Exec_tip_model.No_engine_spawn;
  ]

(** Exhaustive naming of this family's mutation enum. *)
let mut_name = function
  | Exec_tip_model.Pristine -> "pristine"
  | Exec_tip_model.No_execution_gate -> "no-execution-gate"
  | Exec_tip_model.No_engine_spawn -> "no-engine-spawn"

(** Three contingent atoms of this family: the hidden author branch fact (the
    K operand of S1 and S2), the first voter's own execution local, and the
    terminal broadcast certificate flag. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Exec_tip_model.Author_executed;
      Exec_tip_model.Executed_1;
      Exec_tip_model.Cert_formed;
    ]

(** Every subformula of every statement, plus the spanning battery seeded on
    the contingent atoms. V1 is the peer voter whose knowledge S1 and S3 read;
    the family's knowledge-agent group is [V1] together with the coarse
    observer V3 that carries S2's positive knowledge conjunct. *)
let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Exec_tip_statements.formula
      @ Topos_gate.subformulas st.Exec_tip_statements.antecedent)
    Exec_tip_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V1
      ~group:[ Validator.V1; Validator.V3 ]

(** Run the gate on one mutant, mirroring {!Exec_tip_model.spec_of} exactly:
    [initial] is already the list of the three hidden-branch initial states. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:Exec_tip_model.initial ~next:(Exec_tip_model.next_with mut)
       ~view:Exec_tip_model.view ~label:Exec_tip_model.label ~formulas)

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
  with_verdict Exec_tip_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

(** The three alcotest groups: poset and reduction per mutation, reflection
    non-vacuity on the pristine model. *)
let () =
  Alcotest.run "exec-tip-topos"
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
