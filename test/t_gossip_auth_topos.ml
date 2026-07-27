(** The topos gate for the gossip-auth family (DESIGN GOSSIP-AUTH #1):
    {!Gossip_auth_model}'s checker is [Denote.Make], so the family owes the
    three obligations of {!Topos_gate} on its own reachable graph, under the
    pristine model and under every mutation that pins its statement.

    - [W] is a genuine finite poset (so [E = \[W^op, Set\]] is well-founded
      for this family);
    - [is_true ∘ grade = System.sat] over every subformula of S1 plus the
      spanning constructor battery, at every reachable world, the family's
      instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous. *)

open Telcoin_epistemic

module G =
  Topos_gate.Make (Gossip_auth_model.State) (Gossip_auth_model.View)

(** Pristine plus the single statement pin: the gate must hold on the mutant
    too, since the mutation tests read verdicts off the mutated system. *)
let muts = [ Gossip_auth_model.Pristine; Gossip_auth_model.Drop_publisher_auth ]

(** Exhaustive naming over this family's mutation enum. *)
let mut_name = function
  | Gossip_auth_model.Pristine -> "pristine"
  | Gossip_auth_model.Drop_publisher_auth -> "drop-publisher-auth"

(** Three contingent atoms of this family: the hidden outsider-branch fact,
    a subscriber's own delivery local, and the publish-history bit that the
    crash-post-vote branch withholds. This family has no phase atom, so the
    publish bit plays the terminal role. *)
let seed_atoms =
  List.map
    (fun a -> Formula.Atom a)
    [
      Gossip_auth_model.Outsider_published;
      Gossip_auth_model.Delivered (Validator.V1, Gossip_auth_model.Cert_c);
      Gossip_auth_model.Committee_published Gossip_auth_model.Cert_c;
    ]

(** Every subformula of the family's statements, plus the spanning battery
    over the seed atoms. *)
let formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Gossip_auth_statements.formula
      @ Topos_gate.subformulas st.Gossip_auth_statements.antecedent)
    Gossip_auth_statements.all
  @ Topos_gate.battery ~atoms:seed_atoms ~agent:Validator.V1
      ~group:Gossip_auth_model.subscribers

(** Run the gate on one mutation and hand the verdict to [k], mirroring
    {!Gossip_auth_model.spec_of} exactly. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:[ Gossip_auth_model.initial ]
       ~next:(Gossip_auth_model.next_with mut)
       ~view:Gossip_auth_model.view ~label:Gossip_auth_model.label ~formulas)

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

(** Obligation 3: deleting the classical bridge is not a no-op here. *)
let reflection_non_vacuous () =
  with_verdict Gossip_auth_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

(** The three gate groups, one case per mutation for the first two. *)
let () =
  Alcotest.run "gossip_auth-topos"
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
