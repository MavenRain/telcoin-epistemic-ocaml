(** The topos gate for the discovery family (DISCOVERY SA, SB, SC):
    {!Discovery_model}'s checker is [Denote.Make], so the family owes the three
    obligations of {!Topos_gate} on its own reachable graph, under the pristine
    model and under every mutation that pins one of its statements.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded
      for this family);
    - [is_true ∘ grade = System.sat] over every subformula of SA, SB and SC plus
      the spanning constructor battery, at every reachable world - the family's
      instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

(** This family's instance of the shared gate. *)
module G = Topos_gate.Make (Discovery_model.State) (Discovery_model.View)

(** Pristine plus all four statement pins: the gate must hold on the mutants
    too, since the mutation tests read verdicts off the mutated systems. *)
let muts =
  [
    Discovery_model.Pristine;
    Discovery_model.No_query_max_fold;
    Discovery_model.No_put_freshness_gate;
    Discovery_model.Penalize_stale_record;
    Discovery_model.Px_binds_identity;
  ]

(** Exhaustive naming of this family's mutation enum. *)
let mut_name = function
  | Discovery_model.Pristine -> "pristine"
  | Discovery_model.No_query_max_fold -> "no-query-max-fold"
  | Discovery_model.No_put_freshness_gate -> "no-put-freshness-gate"
  | Discovery_model.Penalize_stale_record -> "penalize-stale-record"
  | Discovery_model.Px_binds_identity -> "px-binds-identity"

(** Three contingent atoms of this family: the hidden publication fact, V0's own
    per-episode record that a signature-valid newer response arrived, and the
    terminal query phase. [Cache_r1] is deliberately NOT a seed: it is the one
    atom of this vocabulary that is not future-closed (the [St_absent] stale-PUT
    step regresses [known_peers(A)] from r1 to r0, SB's whole point), and a
    non-persistent seed would put the battery's bare [Implies] over a consequent
    that the graded reading and [System.sat] legitimately disagree on. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Discovery_model.Newer_record_exists;
      Discovery_model.Query_got_r1;
      Discovery_model.Query_closed;
    ]

(** V0 is this family's ONLY knowledge agent (A and S are phantom parties folded
    into [nature]; V1-V9 carry the constant blank [View_idle]), so the knowledge
    group is the singleton it generates. *)
let knowers = [ Validator.V0 ]

(** Every subformula of every statement of the family, plus the spanning
    constructor battery over the seed atoms. *)
let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Discovery_statements.formula
      @ Topos_gate.subformulas st.Discovery_statements.antecedent)
    Discovery_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V0 ~group:knowers

(** Run the gate on this family under one mutation and hand the verdict to [k];
    an empty init is a test failure rather than an exception. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:Discovery_model.initial
       ~next:(Discovery_model.next_with mut) ~view:Discovery_model.view
       ~label:Discovery_model.label ~formulas)

(** Obligation 1: this family's reachability order is a genuine finite poset. *)
let poset_certified mut () =
  with_verdict mut (fun v ->
      Alcotest.(check bool)
        ("W is a finite poset over " ^ Int.to_string v.G.worlds ^ " worlds")
        true v.G.poset)

(** Obligation 2: the differential against the {!System} oracle. *)
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
  with_verdict Discovery_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

(** The three obligation groups, one case per mutation on the first two. *)
let () =
  Alcotest.run "discovery-topos"
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
