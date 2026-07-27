(** The topos gate for the cert_envelope family (DESIGN CERT_ENVELOPE S1, S2,
    S3): {!Cert_envelope_model}'s checker is [Denote.Make], so the family owes
    the three obligations of {!Topos_gate} on its own reachable graph, under the
    pristine model and under every gate-deletion mutation that pins one of its
    statements.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded
      for this family);
    - [is_true ∘ grade = System.sat] over every subformula of S1, S2 and S3 plus
      the spanning constructor battery, at every reachable world - the family's
      instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

module G =
  Topos_gate.Make (Cert_envelope_model.State) (Cert_envelope_model.View)

(** Pristine plus all three statement pins: the gate must hold on the mutants
    too, since the mutation tests read verdicts off the mutated systems. *)
let muts =
  [
    Cert_envelope_model.Pristine;
    Cert_envelope_model.No_basefee_gate;
    Cert_envelope_model.No_recovery_gate;
    Cert_envelope_model.No_empty_batch_gate;
  ]

(** Exhaustive naming of this family's mutation sum. *)
let mut_name = function
  | Cert_envelope_model.Pristine -> "pristine"
  | Cert_envelope_model.No_basefee_gate -> "no-basefee-gate"
  | Cert_envelope_model.No_recovery_gate -> "no-recovery-gate"
  | Cert_envelope_model.No_empty_batch_gate -> "no-empty-batch-gate"

(** The family's knowledge-agent group: V1 the gated worker and V2 the ungated
    holder/executor. V0 and V3 carry the constant blank view and are not
    agents. *)
let agents = [ Validator.V1; Validator.V2 ]

(** Three contingent atoms of this family: the hidden Byzantine content choice,
    V1's own gated-ingress local, and V2's terminal execution phase. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Cert_envelope_model.Content_unrecoverable;
      Cert_envelope_model.V1_accepted;
      Cert_envelope_model.V2_executed;
    ]

(** Every subformula of every statement, plus the spanning battery. *)
let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Cert_envelope_statements.formula
      @ Topos_gate.subformulas st.Cert_envelope_statements.antecedent)
    Cert_envelope_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V1 ~group:agents

(** Run the gate on one mutation, mirroring [Cert_envelope_model.spec_of]. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Cert_envelope_model.initial ]
       ~next:(Cert_envelope_model.next_with mut)
       ~view:Cert_envelope_model.view ~label:Cert_envelope_model.label ~formulas)

(** [W] is reflexive, transitive and antisymmetric under this mutation. *)
let poset_certified mut () =
  with_verdict mut (fun v ->
      Alcotest.(check bool)
        ("W is a finite poset over " ^ Int.to_string v.G.worlds ^ " worlds")
        true v.G.poset)

(** The differential reduction gate against the exact {!System} oracle. *)
let reduction_holds mut () =
  with_verdict mut (fun v ->
      Alcotest.(check (option int))
        ("is_true ∘ grade = System.sat over "
        ^ Int.to_string v.G.checked
        ^ " formulas × "
        ^ Int.to_string v.G.worlds
        ^ " worlds")
        None v.G.mismatch)

(** Confirm-by-mutation for {!Reflect}: the classical bridge is not vacuous. *)
let reflection_non_vacuous () =
  with_verdict Cert_envelope_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "cert_envelope-topos"
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
