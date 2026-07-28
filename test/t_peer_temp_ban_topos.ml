(** The topos gate for the peer_temp_ban family: {!Peer_temp_ban_model} runs on
    [Denote.Make], so it owes the obligations of {!Topos_gate} on its own
    reachable graph, under the pristine model and under every mutation that pins
    one of its statements.

    - [is_true (grade phi s) = System.sat phi] at every reachable world for
      every subformula of every statement plus a spanning constructor battery,
      this family's instance of the DESIGN sec.6 gate 2 differential;
    - the classical reflection is load-bearing here, not vacuous.

    This family has NO poset case, and that is a property of the mechanism, not
    an oversight: the heartbeat keeps ticking after the cache has emptied, so
    two distinct states ([due] set, [due] serviced) are mutually reachable and
    {!Frame.certify_functorial} refuses antisymmetry. It is the "mechanism that
    undoes itself" case the gate documents. A preorder is still a thin category,
    so parallel [W]-arrows are still unique and presheaf restriction is still
    path-independent; the classification is pinned in both directions by
    test/t_topos_frames.ml and the negative pin below keeps that distinction
    live.

    Battery seeds are derived from the family's own statements
    ({!Topos_gate.seeds}) rather than hand-named. *)

open Telcoin_epistemic

(** The gate instantiated at this family's state and view. *)
module G = Topos_gate.Make (Peer_temp_ban_model.State) (Peer_temp_ban_model.View)

(** Pristine plus every gate deletion this family pins a statement with. *)
let muts =
  [
    Peer_temp_ban_model.Pristine;
    Peer_temp_ban_model.No_expiry_guard;
    Peer_temp_ban_model.No_heartbeat_drain;
    Peer_temp_ban_model.No_reinsert_refresh;
  ]

(** Case labels; exhaustive over the mutation sum. *)
let mut_name = function
  | Peer_temp_ban_model.Pristine -> "pristine"
  | Peer_temp_ban_model.No_expiry_guard -> "no-expiry-guard"
  | Peer_temp_ban_model.No_heartbeat_drain -> "no-heartbeat-drain"
  | Peer_temp_ban_model.No_reinsert_refresh -> "no-reinsert-refresh"

(** Every subformula of every statement, formula and antecedent alike. *)
let statement_formulas =
  List.concat_map
    (fun st ->
      Topos_gate.subformulas st.Peer_temp_ban_statements.formula
      @ Topos_gate.subformulas st.Peer_temp_ban_statements.antecedent)
    Peer_temp_ban_statements.all

(** The checked set: the statements plus the spanning battery. *)
let formulas =
  statement_formulas
  @ Topos_gate.battery
      ~atoms:(Topos_gate.seeds statement_formulas)
      ~agent:Validator.V0 ~group:Validator.all

(** Run the gate under one mutation, or fail on an impossible empty init. The
    init list matches {!Peer_temp_ban_model.spec_of} exactly. *)
let with_verdict mut k =
  Result.fold
    ~error:(fun G.Empty_init -> Alcotest.fail "topos gate: empty init")
    ~ok:k
    (G.run
       ~init:
         [ Peer_temp_ban_model.initial; Peer_temp_ban_model.initial_staggered ]
       ~next:(Peer_temp_ban_model.next_with mut) ~view:Peer_temp_ban_model.view
       ~label:Peer_temp_ban_model.label ~formulas)

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

(** The frame really is the preorder case, so t_topos_frames.ml is pinning a
    live distinction and not a stale one. *)
let frame_is_a_preorder () =
  with_verdict Peer_temp_ban_model.Pristine (fun v ->
      Alcotest.(check bool) "reachability is a preorder, not a poset" false
        v.G.poset)

(** Deleting the classical bridge changes a verdict here, so the reduction gate
    above is not green by reflection vacuity. *)
let reflection_non_vacuous () =
  with_verdict Peer_temp_ban_model.Pristine (fun v ->
      Alcotest.(check bool)
        "deleting the classical bridge flips a verdict on this family" true
        v.G.reflection_load_bearing)

let () =
  Alcotest.run "peer_temp_ban-topos"
    [
      ( "reduction",
        List.map
          (fun m -> Alcotest.test_case (mut_name m) `Quick (reduction_holds m))
          muts );
      ( "frame",
        [ Alcotest.test_case "preorder-not-poset" `Quick frame_is_a_preorder ] );
      ( "reflection",
        [ Alcotest.test_case "non-vacuous" `Quick reflection_non_vacuous ] );
    ]
