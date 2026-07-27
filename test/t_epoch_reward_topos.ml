(** The topos gate for the epoch_reward family (S1 blockless credit, S2
    crash-rebuild partition, S3 batch-less boundary seal): {!Epoch_reward_model}'s
    checker is [Denote.Make], so the family owes the three obligations of
    {!Topos_gate} on its own reachable graph, under the pristine model and under
    every mutation that pins one of its statements.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded for
      this family);
    - [is_true ∘ grade = System.sat] over every subformula of S1, S2 and S3 plus
      the spanning constructor battery, at every reachable world - the family's
      instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

module G =
  Topos_gate.Make (Epoch_reward_model.State) (Epoch_reward_model.View)

(** Pristine plus all three statement pins: the gate must hold on the mutants
    too, since the mutation tests read verdicts off the mutated systems. *)
let muts =
  [
    Epoch_reward_model.Pristine;
    Epoch_reward_model.Credit_after_skip;
    Epoch_reward_model.No_catchup_watermark;
    Epoch_reward_model.Skip_batchless_close;
  ]

(** Exhaustive naming of this family's mutation enum. *)
let mut_name = function
  | Epoch_reward_model.Pristine -> "pristine"
  | Epoch_reward_model.Credit_after_skip -> "credit-after-skip"
  | Epoch_reward_model.No_catchup_watermark -> "no-catchup-watermark"
  | Epoch_reward_model.Skip_batchless_close -> "skip-batchless-close"

(** The family's knowledge agents: V1 is the reference node and the only agent
    the statements put under [K], V2 is the peer carrying the hidden crash
    branch. V0 and V3..V9 are idle non-agents with the constant blank view. *)
let agents = [ Validator.V1; Validator.V2 ]

(** Three contingent atoms of this family: the peer's hidden crash-and-rebuild
    branch fact, V1's own blockless-round credit local, and the terminal seal.
    All three are exercised as contingent by test/t_epoch_reward.ml. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Epoch_reward_model.V2_restarted;
      Epoch_reward_model.V1_credited_blockless;
      Epoch_reward_model.V1_sealed;
    ]

let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Epoch_reward_statements.formula
      @ Topos_gate.subformulas st.Epoch_reward_statements.antecedent)
    Epoch_reward_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V1 ~group:agents

let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Epoch_reward_model.initial ]
       ~next:(Epoch_reward_model.next_with mut) ~view:Epoch_reward_model.view
       ~label:Epoch_reward_model.label ~formulas)

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
  with_verdict Epoch_reward_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "epoch_reward-topos"
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
