(** The frame classification: which of the 27 models may host the topos
    layer at all.

    [E = \[W^op, Set\]] (lib/internal/DESIGN.md sec.1) is a presheaf topos
    over a finite POSET [W]. That is a precondition, not a formality: if the
    reachability order has a genuine cycle it is a preorder, two distinct
    states become isomorphic objects of [W], parallel [W]-arrows stop being
    equal, and [Sub(1_E)] stops being the future-closed subsets of anything.
    {!Frame.certify_functorial} is exactly that precondition check
    (reflexive AND transitive AND ANTISYMMETRIC).

    This suite runs the check over every model in the library and pins the
    resulting classification, so the split cannot drift silently in either
    direction:

    - 23 models certify, and their [Checker] is [Denote.Make] - the topos
      denotation - with the per-family gate in [test/t_<family>_topos.ml]
      proving it agrees with {!System} world by world;
    - 4 models do NOT certify ([admission], [epoch_close], [epoch_sync],
      [exex_fanout]) because they model mechanisms that genuinely undo
      themselves - bans expire, connections toggle, a sync loop retries - so
      their [Checker] stays [System.Make]. That exclusion is not a
      precaution: test/t_topos_excluded.ml exhibits an actual world at which
      the topos denotation and the original checker disagree on one of them.

    If a model is later made acyclic, its row here fails and the re-point to
    [Denote.Make] becomes owed. If a re-pointed model later grows a cycle,
    its row fails before anything silently diverges. *)

open Telcoin_epistemic

type row = {
  name : string;  (** The model, by module basename. *)
  poset : bool;  (** Did [Frame.certify_functorial] accept its [W]. *)
  worlds : int;  (** [|reach|] under the pristine transition relation. *)
}

(** Build one row. The state and view modules arrive as first-class modules
    so that all 27 instances of the frame functor can live in one list. The
    atom label is irrelevant to the frame, so it is the constant [false]. *)
let row_of (type s) (type v) name
    (stm : (module System.ORDERED with type t = s))
    (vwm : (module System.ORDERED with type t = v)) (init : s list)
    (next : s -> s list) (view : Validator.t -> s -> v) =
  let module St = (val stm) in
  let module Vw = (val vwm) in
  let module F = Frame.Make (St) (Vw) in
  let spec = { F.init; next; view; label = (fun () _ -> false) } in
  Result.fold
    ~error:(fun F.Empty_init -> { name; poset = false; worlds = 0 })
    ~ok:(fun t ->
      {
        name;
        poset =
          Result.fold ~ok:(fun () -> true) ~error:(fun _ -> false)
            (F.certify_functorial t);
        worlds = F.reachable_count t;
      })
    (F.make spec)

(** Every model in the library, in the order the README lists them. *)
let rows =
  [
    row_of "tn_model" (module Tn_state) (module Tn_state.Local)
      [ Tn_state.initial ]
      (Tn_model.next_with Tn_model.Pristine)
      (fun v s -> Tn_state.local_of s v);
    row_of "admission" (module Admission_model.State) (module Admission_model.View) [ Admission_model.initial ]
      (Admission_model.next_with Admission_model.Pristine) Admission_model.view;
    row_of "ban" (module Ban_model.State) (module Ban_model.View) [ Ban_model.initial ]
      (Ban_model.next_with Ban_model.Pristine) Ban_model.view;
    row_of "batch_verdict" (module Batch_verdict_model.State) (module Batch_verdict_model.View) [ Batch_verdict_model.initial ]
      (Batch_verdict_model.next_with Batch_verdict_model.Pristine) Batch_verdict_model.view;
    row_of "catchup" (module Catchup_model.State) (module Catchup_model.View) [ Catchup_model.initial ]
      (Catchup_model.next_with Catchup_model.Pristine) Catchup_model.view;
    row_of "cert_envelope" (module Cert_envelope_model.State) (module Cert_envelope_model.View) [ Cert_envelope_model.initial ]
      (Cert_envelope_model.next_with Cert_envelope_model.Pristine) Cert_envelope_model.view;
    row_of "discovery" (module Discovery_model.State) (module Discovery_model.View) Discovery_model.initial
      (Discovery_model.next_with Discovery_model.Pristine) Discovery_model.view;
    row_of "epoch_close" (module Epoch_close_model.State) (module Epoch_close_model.View) [ Epoch_close_model.initial ]
      (Epoch_close_model.next_with Epoch_close_model.Pristine) Epoch_close_model.view;
    row_of "epoch_record" (module Epoch_record_model.State) (module Epoch_record_model.View) [ Epoch_record_model.initial ]
      (Epoch_record_model.next_with Epoch_record_model.Pristine) Epoch_record_model.view;
    row_of "epoch_reward" (module Epoch_reward_model.State) (module Epoch_reward_model.View) [ Epoch_reward_model.initial ]
      (Epoch_reward_model.next_with Epoch_reward_model.Pristine) Epoch_reward_model.view;
    row_of "epoch_sync" (module Epoch_sync_model.State) (module Epoch_sync_model.View) [ Epoch_sync_model.initial ]
      (Epoch_sync_model.next_with Epoch_sync_model.Pristine) Epoch_sync_model.view;
    row_of "exec_tally" (module Exec_tally_model.State) (module Exec_tally_model.View) [ Exec_tally_model.initial ]
      (Exec_tally_model.next_with Exec_tally_model.Pristine) Exec_tally_model.view;
    row_of "exec_tip" (module Exec_tip_model.State) (module Exec_tip_model.View) Exec_tip_model.initial
      (Exec_tip_model.next_with Exec_tip_model.Pristine) Exec_tip_model.view;
    row_of "exex_fanout" (module Exex_fanout_model.State) (module Exex_fanout_model.View) [ Exex_fanout_model.initial ]
      (Exex_fanout_model.next_with Exex_fanout_model.Pristine) Exex_fanout_model.view;
    row_of "exex_life" (module Exex_life_model.State) (module Exex_life_model.View) [ Exex_life_model.initial ]
      (Exex_life_model.next_with Exex_life_model.Pristine) Exex_life_model.view;
    row_of "gossip_auth" (module Gossip_auth_model.State) (module Gossip_auth_model.View) [ Gossip_auth_model.initial ]
      (Gossip_auth_model.next_with Gossip_auth_model.Pristine) Gossip_auth_model.view;
    row_of "gossip_reject" (module Gossip_reject_model.State) (module Gossip_reject_model.View) [ Gossip_reject_model.initial ]
      (Gossip_reject_model.next_with Gossip_reject_model.Pristine) Gossip_reject_model.view;
    row_of "identity" (module Identity_model.State) (module Identity_model.View) [ Identity_model.initial ]
      (Identity_model.next_with Identity_model.Pristine) Identity_model.view;
    row_of "own_durable" (module Own_durable_model.State) (module Own_durable_model.View) [ Own_durable_model.initial ]
      (Own_durable_model.next_with Own_durable_model.Pristine) Own_durable_model.view;
    row_of "pending_gc" (module Pending_gc_model.State) (module Pending_gc_model.View) [ Pending_gc_model.initial; Pending_gc_model.initial_peer_holds ]
      (Pending_gc_model.next_with Pending_gc_model.Pristine) Pending_gc_model.view;
    row_of "prefetch" (module Prefetch_model.State) (module Prefetch_model.View) [ Prefetch_model.initial ]
      (Prefetch_model.next_with Prefetch_model.Pristine) Prefetch_model.view;
    row_of "reqres" (module Reqres_model.State) (module Reqres_model.View) [ Reqres_model.initial ]
      (Reqres_model.next_with Reqres_model.Pristine) Reqres_model.view;
    row_of "revote" (module Revote_model.State) (module Revote_model.View) [ Revote_model.initial ]
      (Revote_model.next_with Revote_model.Pristine) Revote_model.view;
    row_of "stall" (module Stall_model.State) (module Stall_model.View) [ Stall_model.initial ]
      (Stall_model.next_with Stall_model.Pristine) Stall_model.view;
    row_of "swap" (module Swap_model.State) (module Swap_model.View) [ Swap_model.initial ]
      (Swap_model.next_with Swap_model.Pristine) Swap_model.view;
    row_of "unres" (module Unres_model.State) (module Unres_model.View) [ Unres_model.initial ]
      (Unres_model.next_with Unres_model.Pristine) Unres_model.view;
    row_of "verif_prov" (module Verif_prov_model.State) (module Verif_prov_model.View) [ Verif_prov_model.initial ]
      (Verif_prov_model.next_with Verif_prov_model.Pristine) Verif_prov_model.view;
  ]

(** The pinned classification: every model that must certify, and every
    model that must not. Both directions are asserted. *)
let excluded = [ "admission"; "epoch_close"; "epoch_sync"; "exex_fanout" ]

(** One case per model: its poset verdict equals its pinned classification. *)
let classified r () =
  Alcotest.(check bool)
    (r.name ^ " (" ^ Int.to_string r.worlds ^ " worlds) certifies as a poset")
    (Bool.not (List.mem r.name excluded))
    r.poset

(** The library really does hold 27 models, so no row was lost. *)
let all_models_present () =
  Alcotest.(check int) "models classified" 27 (List.length rows)

(** Exactly 23 models are eligible for the topos layer, and exactly the 4
    named ones are not - the count the README and DESIGN.md quote. *)
let split_is_23_4 () =
  Alcotest.(check (pair int int))
    "eligible / excluded"
    (23, 4)
    ( List.length (List.filter (fun r -> r.poset) rows),
      List.length (List.filter (fun r -> Bool.not r.poset) rows) )

(** Every model has a non-empty reachable set, so no row certified by being
    vacuously empty. *)
let no_empty_frames () =
  Alcotest.(check bool) "every model has reachable states" true
    (List.for_all (fun r -> r.worlds > 0) rows)

let () =
  Alcotest.run "topos-frames"
    [
      ("classification", List.map (fun r -> Alcotest.test_case r.name `Quick (classified r)) rows);
      ( "totals",
        [
          Alcotest.test_case "27-models" `Quick all_models_present;
          Alcotest.test_case "23-eligible-4-excluded" `Quick split_is_23_4;
          Alcotest.test_case "no-empty-frames" `Quick no_empty_frames;
        ] );
    ]
