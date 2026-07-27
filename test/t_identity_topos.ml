(** The topos gate for the identity family (DESIGN IDENTITY #9):
    {!Identity_model}'s checker is [Denote.Make], so the family owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins its statement.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded
      for this family);
    - [is_true ∘ grade = System.sat] over every subformula of S9 plus the
      spanning constructor battery, at every reachable world - the family's
      instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

module G = Topos_gate.Make (Identity_model.State) (Identity_model.View)

(** Pristine plus the statement pin: the gate must hold on the mutant too,
    since the mutation tests read verdicts off the mutated system. *)
let muts = [ Identity_model.Pristine; Identity_model.Drop_record_verify ]

(** The mutation names, matched exhaustively over the family's enum. *)
let mut_name = function
  | Identity_model.Pristine -> "pristine"
  | Identity_model.Drop_record_verify -> "drop-record-verify"

(** Three contingent atoms of this family: the hidden Byzantine signing act,
    an honest node's confirmed-identity local, and the startup-connect phase
    fact. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Identity_model.Signed_binding (Validator.V3, Identity_model.P3);
      Identity_model.Confirmed
        (Validator.V0, Identity_model.P1, Validator.V1);
      Identity_model.First_connect (Validator.V0, Validator.V1);
    ]

(** Every subformula of every statement of the family, plus the spanning
    constructor battery over the seed atoms. *)
let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Identity_statements.formula
      @ Topos_gate.subformulas st.Identity_statements.antecedent)
    Identity_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V0
      ~group:Identity_model.honest

(** Run the gate on one mutation and hand the verdict to [k]. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Identity_model.initial ]
       ~next:(Identity_model.next_with mut)
       ~view:Identity_model.view ~label:Identity_model.label ~formulas)

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

(** Obligation 3: the classical bridge is load-bearing on this family. *)
let reflection_non_vacuous () =
  with_verdict Identity_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "identity-topos"
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
