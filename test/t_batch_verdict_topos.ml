(** The topos gate for the batch_verdict family (DESIGN BATCH_VERDICT S1, S2,
    S3): {!Batch_verdict_model}'s checker is [Denote.Make], so the family owes
    the three obligations of {!Topos_gate} on its own reachable graph, under the
    pristine model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded
      for this family);
    - [is_true ∘ grade = System.sat] over every subformula of S1, S2 and S3 plus
      the spanning constructor battery, at every reachable world - the family's
      instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

module G =
  Topos_gate.Make (Batch_verdict_model.State) (Batch_verdict_model.View)

(** Pristine plus both gate deletions: the gate must hold on the mutants too,
    since the mutation tests read verdicts off the mutated systems. *)
let muts =
  [
    Batch_verdict_model.Pristine;
    Batch_verdict_model.No_peer_store_before_ack;
    Batch_verdict_model.No_recoverable_class;
  ]

let mut_name = function
  | Batch_verdict_model.Pristine -> "pristine"
  | Batch_verdict_model.No_peer_store_before_ack -> "no-peer-store-before-ack"
  | Batch_verdict_model.No_recoverable_class -> "no-recoverable-class"

(** V0, the batch author, is this family's only knowledge agent, so the group
    under [Everyone] / [Common] is the singleton author group. *)
let agents = [ Validator.V0 ]

(** Three contingent atoms of this family: the hidden peer-possession fact, the
    author's per-peer accept local, and the terminal anti-quorum verdict. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Batch_verdict_model.Holds_v1;
      Batch_verdict_model.Accepted_v1;
      Batch_verdict_model.Verdict_anti;
    ]

let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Batch_verdict_statements.formula
      @ Topos_gate.subformulas st.Batch_verdict_statements.antecedent)
    Batch_verdict_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V0 ~group:agents

let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Batch_verdict_model.initial ]
       ~next:(Batch_verdict_model.next_with mut) ~view:Batch_verdict_model.view
       ~label:Batch_verdict_model.label ~formulas)

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
  with_verdict Batch_verdict_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "batch_verdict-topos"
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
