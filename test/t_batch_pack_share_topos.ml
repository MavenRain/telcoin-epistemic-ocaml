(** The topos gate for the batch_pack_share family: {!Batch_pack_share_model}
    runs on [Denote.Make], so it owes the three obligations of {!Topos_gate} on
    its own reachable graph, under the pristine model and under every mutation
    that pins one of its statements.

    - [W] is a genuine finite poset. Every transition of this family advances
      {!Batch_pack_share_model.stage} by one position of a fixed order - offers
      submitted, admission run, batch sealed and broadcast, quorum acked or
      refused, pool synced, canonical update seen - and reverses nothing: a seal
      happens once, an ack is final, the pool sync is applied once and the
      canonical update after it. The submission profile and the hidden solvency
      bit are constants of a run. So nothing undoes itself and reachability is
      antisymmetric. That holds under all three mutations too, since each of them
      only changes WHICH successor a stage has, never the direction. This is
      asserted below, not assumed;
    - [is_true (grade phi s) = System.sat phi] at every reachable world for every
      subformula of every statement plus a spanning constructor battery, this
      family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. The battery agent is
    {!Batch_pack_share_model.worker} = V0, whose view is a strict projection of
    the state (it omits the hidden solvency bit entirely), so the battery's [K]
    shapes are evaluated over genuinely non-singleton classes rather than
    collapsing to plain truth. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G =
  Topos_gate.Make (Batch_pack_share_model.State) (Batch_pack_share_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Batch_pack_share_model.Pristine;
    Batch_pack_share_model.Break_on_over_budget;
    Batch_pack_share_model.No_per_sender_slot_cap;
    Batch_pack_share_model.No_post_seal_nonce_hint;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name m =
  match m with
  | Batch_pack_share_model.Pristine -> "pristine"
  | Batch_pack_share_model.Break_on_over_budget -> "break-on-over-budget"
  | Batch_pack_share_model.No_per_sender_slot_cap -> "no-per-sender-slot-cap"
  | Batch_pack_share_model.No_post_seal_nonce_hint -> "no-post-seal-nonce-hint"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Batch_pack_share_statements.formula
      @ Topos_gate.subformulas st.Batch_pack_share_statements.antecedent)
    Batch_pack_share_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Batch_pack_share_model.worker ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list matches {!Batch_pack_share_model.spec_of} exactly: all six roots,
    the three submission profiles crossed with the hidden solvency bit. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run ~init:Batch_pack_share_model.all_initials
       ~next:(Batch_pack_share_model.next_with mut)
       ~view:Batch_pack_share_model.view ~label:Batch_pack_share_model.label
       ~formulas)

(** [W] is a genuine finite poset: reflexive, transitive and antisymmetric. *)
let poset_certified mut () =
  with_verdict mut (fun v ->
      Alcotest.(check bool)
        ("W is a finite poset over " ^ Int.to_string v.G.worlds ^ " worlds")
        true v.G.poset)

(** The topos denotation agrees with the original checker, world by world. *)
let reduction_holds mut () =
  with_verdict mut (fun v ->
      Alcotest.(check (option int))
        ("is_true o grade = System.sat over "
        ^ Int.to_string v.G.checked
        ^ " formulas x "
        ^ Int.to_string v.G.worlds
        ^ " worlds")
        None v.G.mismatch)

(** Deleting the classical bridge changes a verdict here, so the reduction gate
    above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Batch_pack_share_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "batch_pack_share-topos"
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
