(** The frame classification: which of the 69 models have an ANTISYMMETRIC
    reachability order.

    [E = \[W^op, Set\]] (lib/internal/DESIGN.md sec.1) is a presheaf topos
    over a finite preorder [W]; when [W] is additionally antisymmetric it is a
    poset. {!Frame.certify_functorial} is exactly that antisymmetry check
    (reflexive AND transitive AND ANTISYMMETRIC).

    This suite runs the check over every model in the library and pins the
    resulting classification, so the split cannot drift silently in either
    direction:

    - 57 models certify as posets;
    - 12 models do NOT ([admission], [epoch_close], [epoch_sync],
      [exex_fanout], [record_serve_pool], [stream_slot_tenure],
      [vote_cache_retry], [worker_stream_quota], [tel_supply_ledger],
      [archive_hash_index], [peer_temp_ban], [stream_sync_capability]) because they
      model mechanisms that genuinely undo themselves - bans expire,
      connections toggle, a sync loop retries, a serve pool is released, an
      admission slot is pruned and re-opened, a vote slot is released, a
      stream quota is returned.

    {b Antisymmetry is a classification here, not a precondition.} An earlier
    revision of this comment claimed the six were excluded from the topos
    layer and that their [Checker] stayed [System.Make], citing a
    test/t_topos_excluded.ml. Both claims were false: that file has never
    existed, and every model in the library instantiates [Denote.Make],
    verifiable with [rg -l 'module Checker = System\.Make' lib/*.ml] returning
    nothing. The reason the preorder case is sound is that a preorder is still
    a THIN category, so parallel [W]-arrows are still unique and presheaf
    restriction is still path-independent (DESIGN sec.1); antisymmetry only
    buys skeletality. And [is_true] is MEMBERSHIP (sieve.ml:22) rather than
    sieve equality, so the reduction gate is insensitive to the difference -
    which is why all twelve preorder models pass their own
    [test/t_<family>_topos.ml] reduction differential.

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
    so that all 69 instances of the frame functor can live in one list. The
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
    row_of "subdag_leader_walk" (module Subdag_leader_walk_model.State) (module Subdag_leader_walk_model.View) [ Subdag_leader_walk_model.initial; Subdag_leader_walk_model.initial_unsupported_linked; Subdag_leader_walk_model.initial_unsupported_unlinked ]
      (Subdag_leader_walk_model.next_with Subdag_leader_walk_model.Pristine) Subdag_leader_walk_model.view;
    row_of "dag_retention" (module Dag_retention_model.State) (module Dag_retention_model.View) [ Dag_retention_model.initial; Dag_retention_model.initial_peer_c_holds; Dag_retention_model.initial_peer_a_names; Dag_retention_model.initial_peer_a_names_c_holds ]
      (Dag_retention_model.next_with Dag_retention_model.Pristine) Dag_retention_model.view;
    row_of "round_weight_cap" (module Round_weight_cap_model.State) (module Round_weight_cap_model.View) [ Round_weight_cap_model.initial; Round_weight_cap_model.initial_equivocating ]
      (Round_weight_cap_model.next_with Round_weight_cap_model.Pristine) Round_weight_cap_model.view;
    row_of "parent_batch_forward" (module Parent_batch_forward_model.State) (module Parent_batch_forward_model.View) [ Parent_batch_forward_model.initial; Parent_batch_forward_model.initial_catchup ]
      (Parent_batch_forward_model.next_with Parent_batch_forward_model.Pristine) Parent_batch_forward_model.view;
    row_of "fetch_verif_state" (module Fetch_verif_state_model.State) (module Fetch_verif_state_model.View) [ Fetch_verif_state_model.initial ]
      (Fetch_verif_state_model.next_with Fetch_verif_state_model.Pristine) Fetch_verif_state_model.view;
    row_of "causal_handoff" (module Causal_handoff_model.State) (module Causal_handoff_model.View) [ Causal_handoff_model.initial; Causal_handoff_model.initial_peer_holds ]
      (Causal_handoff_model.next_with Causal_handoff_model.Pristine) Causal_handoff_model.view;
    row_of "record_serve_pool" (module Record_serve_pool_model.State) (module Record_serve_pool_model.View) [ Record_serve_pool_model.initial ]
      (Record_serve_pool_model.next_with Record_serve_pool_model.Pristine) Record_serve_pool_model.view;
    row_of "stream_slot_tenure" (module Stream_slot_tenure_model.State) (module Stream_slot_tenure_model.View) [ Stream_slot_tenure_model.initial; Stream_slot_tenure_model.initial_requester_silent ]
      (Stream_slot_tenure_model.next_with Stream_slot_tenure_model.Pristine) Stream_slot_tenure_model.view;
    row_of "parent_claim_binding" (module Parent_claim_binding_model.State) (module Parent_claim_binding_model.View) [ Parent_claim_binding_model.initial; Parent_claim_binding_model.initial_bogus; Parent_claim_binding_model.initial_b_holds; Parent_claim_binding_model.initial_c_holds; Parent_claim_binding_model.initial_author_lean; Parent_claim_binding_model.initial_author_rich ]
      (Parent_claim_binding_model.next_with Parent_claim_binding_model.Pristine) Parent_claim_binding_model.view;
    row_of "vote_cache_retry" (module Vote_cache_retry_model.State) (module Vote_cache_retry_model.View) [ Vote_cache_retry_model.initial ]
      (Vote_cache_retry_model.next_with Vote_cache_retry_model.Pristine) Vote_cache_retry_model.view;
    row_of "worker_stream_quota" (module Worker_stream_quota_model.State) (module Worker_stream_quota_model.View) [ Worker_stream_quota_model.initial ]
      (Worker_stream_quota_model.next_with Worker_stream_quota_model.Pristine) Worker_stream_quota_model.view;
    row_of "batch_quorum_tally" (module Batch_quorum_tally_model.State) (module Batch_quorum_tally_model.View) [ Batch_quorum_tally_model.initial ]
      (Batch_quorum_tally_model.next_with Batch_quorum_tally_model.Pristine) Batch_quorum_tally_model.view;
    row_of "output_forward_gate" (module Output_forward_gate_model.State) (module Output_forward_gate_model.View) [ Output_forward_gate_model.initial; Output_forward_gate_model.initial_rebroadcast_buffered ]
      (Output_forward_gate_model.next_with Output_forward_gate_model.Pristine) Output_forward_gate_model.view;
    row_of "pack_replay" (module Pack_replay_model.State) (module Pack_replay_model.View) [ Pack_replay_model.initial ]
      (Pack_replay_model.next_with Pack_replay_model.Pristine) Pack_replay_model.view;
    row_of "gas_penalty_split" (module Gas_penalty_split_model.State) (module Gas_penalty_split_model.View) [ Gas_penalty_split_model.initial ]
      (Gas_penalty_split_model.next_with Gas_penalty_split_model.Pristine) Gas_penalty_split_model.view;
    row_of "bls_verify_gate" (module Bls_verify_gate_model.State) (module Bls_verify_gate_model.View) [ Bls_verify_gate_model.initial ]
      (Bls_verify_gate_model.next_with Bls_verify_gate_model.Pristine) Bls_verify_gate_model.view;
    row_of "close_block_syscall" (module Close_block_syscall_model.State) (module Close_block_syscall_model.View) Close_block_syscall_model.inits
      (Close_block_syscall_model.next_with Close_block_syscall_model.Pristine) Close_block_syscall_model.view;
    row_of "tel_dispatch_surface" (module Tel_dispatch_surface_model.State) (module Tel_dispatch_surface_model.View) [ Tel_dispatch_surface_model.initial ]
      (Tel_dispatch_surface_model.next_with Tel_dispatch_surface_model.Pristine) Tel_dispatch_surface_model.view;
    row_of "fee_routing_sink" (module Fee_routing_sink_model.State) (module Fee_routing_sink_model.View) [ Fee_routing_sink_model.initial ]
      (Fee_routing_sink_model.next_with Fee_routing_sink_model.Pristine) Fee_routing_sink_model.view;
    row_of "tel_supply_ledger" (module Tel_supply_ledger_model.State) (module Tel_supply_ledger_model.View) [ Tel_supply_ledger_model.initial ]
      (Tel_supply_ledger_model.next_with Tel_supply_ledger_model.Pristine) Tel_supply_ledger_model.view;
    row_of "batch_pack_share" (module Batch_pack_share_model.State) (module Batch_pack_share_model.View) Batch_pack_share_model.all_initials
      (Batch_pack_share_model.next_with Batch_pack_share_model.Pristine) Batch_pack_share_model.view;
    row_of "tx_forward_route" (module Tx_forward_route_model.State) (module Tx_forward_route_model.View) Tx_forward_route_model.inits
      (Tx_forward_route_model.next_with Tx_forward_route_model.Pristine) Tx_forward_route_model.view;
    row_of "cert_bitmap_quorum" (module Cert_bitmap_quorum_model.State) (module Cert_bitmap_quorum_model.View) [ Cert_bitmap_quorum_model.initial ]
      (Cert_bitmap_quorum_model.next_with Cert_bitmap_quorum_model.Pristine) Cert_bitmap_quorum_model.view;
    row_of "boot_order" (module Boot_order_model.State) (module Boot_order_model.View) Boot_order_model.inits
      (Boot_order_model.next_with Boot_order_model.Pristine) Boot_order_model.view;
    row_of "engine_queue" (module Engine_queue_model.State) (module Engine_queue_model.View) [ Engine_queue_model.initial ]
      (Engine_queue_model.next_with Engine_queue_model.Pristine) Engine_queue_model.view;
    row_of "batch_admit" (module Batch_admit_model.State) (module Batch_admit_model.View) Batch_admit_model.inits
      (Batch_admit_model.next_with Batch_admit_model.Pristine) Batch_admit_model.view;
    row_of "serve_slot_quota" (module Serve_slot_quota_model.State) (module Serve_slot_quota_model.View) [ Serve_slot_quota_model.initial ]
      (Serve_slot_quota_model.next_with Serve_slot_quota_model.Pristine) Serve_slot_quota_model.view;
    row_of "exec_absorb" (module Exec_absorb_model.State) (module Exec_absorb_model.View) Exec_absorb_model.inits
      (Exec_absorb_model.next_with Exec_absorb_model.Pristine) Exec_absorb_model.view;
    row_of "archive_pack_heal" (module Archive_pack_heal_model.State) (module Archive_pack_heal_model.View) [ Archive_pack_heal_model.initial ]
      (Archive_pack_heal_model.next_with Archive_pack_heal_model.Pristine) Archive_pack_heal_model.view;
    row_of "archive_digest_lookup" (module Archive_digest_lookup_model.State) (module Archive_digest_lookup_model.View) [ Archive_digest_lookup_model.initial; Archive_digest_lookup_model.initial_no_d_entry ]
      (Archive_digest_lookup_model.next_with Archive_digest_lookup_model.Pristine) Archive_digest_lookup_model.view;
    row_of "archive_epoch_import" (module Archive_epoch_import_model.State) (module Archive_epoch_import_model.View) Archive_epoch_import_model.inits
      (Archive_epoch_import_model.next_with Archive_epoch_import_model.Pristine) Archive_epoch_import_model.view;
    row_of "store_key_order" (module Store_key_order_model.State) (module Store_key_order_model.View) [ Store_key_order_model.initial ]
      (Store_key_order_model.next_with Store_key_order_model.Pristine) Store_key_order_model.view;
    row_of "store_full_memory" (module Store_full_memory_model.State) (module Store_full_memory_model.View) [ Store_full_memory_model.initial ]
      (Store_full_memory_model.next_with Store_full_memory_model.Pristine) Store_full_memory_model.view;
    row_of "archive_hash_index" (module Archive_hash_index_model.State) (module Archive_hash_index_model.View) [ Archive_hash_index_model.initial ]
      (Archive_hash_index_model.next_with Archive_hash_index_model.Pristine) Archive_hash_index_model.view;
    row_of "backend_writer_thread" (module Backend_writer_thread_model.State) (module Backend_writer_thread_model.View) [ Backend_writer_thread_model.initial ]
      (Backend_writer_thread_model.next_with Backend_writer_thread_model.Pristine) Backend_writer_thread_model.view;
    row_of "backend_env_split" (module Backend_env_split_model.State) (module Backend_env_split_model.View) [ Backend_env_split_model.initial ]
      (Backend_env_split_model.next_with Backend_env_split_model.Pristine) Backend_env_split_model.view;
    row_of "store_notify_visibility" (module Store_notify_visibility_model.State) (module Store_notify_visibility_model.View) Store_notify_visibility_model.inits
      (Store_notify_visibility_model.next_with Store_notify_visibility_model.Pristine) Store_notify_visibility_model.view;
    row_of "peer_prune_fairness" (module Peer_prune_fairness_model.State) (module Peer_prune_fairness_model.View) Peer_prune_fairness_model.inits
      (Peer_prune_fairness_model.next_with Peer_prune_fairness_model.Pristine) Peer_prune_fairness_model.view;
    row_of "peer_temp_ban" (module Peer_temp_ban_model.State) (module Peer_temp_ban_model.View) [ Peer_temp_ban_model.initial; Peer_temp_ban_model.initial_staggered ]
      (Peer_temp_ban_model.next_with Peer_temp_ban_model.Pristine) Peer_temp_ban_model.view;
    row_of "rpc_codec_size" (module Rpc_codec_size_model.State) (module Rpc_codec_size_model.View) [ Rpc_codec_size_model.initial ]
      (Rpc_codec_size_model.next_with Rpc_codec_size_model.Pristine) Rpc_codec_size_model.view;
    row_of "stream_inbound_quota" (module Stream_inbound_quota_model.State) (module Stream_inbound_quota_model.View) [ Stream_inbound_quota_model.initial ]
      (Stream_inbound_quota_model.next_with Stream_inbound_quota_model.Pristine) Stream_inbound_quota_model.view;
    row_of "stream_sync_capability" (module Stream_sync_capability_model.State) (module Stream_sync_capability_model.View) Stream_sync_capability_model.inits
      (Stream_sync_capability_model.next_with Stream_sync_capability_model.Pristine) Stream_sync_capability_model.view;
  ]

(** The pinned classification: every model that must certify, and every
    model that must not. Both directions are asserted. *)
let excluded =
  [
    "admission"; "epoch_close"; "epoch_sync"; "exex_fanout"; "record_serve_pool";
    "stream_slot_tenure"; "vote_cache_retry"; "worker_stream_quota";
    "tel_supply_ledger"; "archive_hash_index"; "peer_temp_ban";
    "stream_sync_capability";
  ]

(** One case per model: its poset verdict equals its pinned classification. *)
let classified r () =
  Alcotest.(check bool)
    (r.name ^ " (" ^ Int.to_string r.worlds ^ " worlds) certifies as a poset")
    (Bool.not (List.mem r.name excluded))
    r.poset

(** The library really does hold 69 models, so no row was lost. *)
let all_models_present () =
  Alcotest.(check int) "models classified" 69 (List.length rows)

(** Exactly 57 models are eligible for the topos layer, and exactly the 12
    named ones are not - the count the README and DESIGN.md quote. *)
let split_is_57_12 () =
  Alcotest.(check (pair int int))
    "eligible / excluded"
    (57, 12)
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
          Alcotest.test_case "69-models" `Quick all_models_present;
          Alcotest.test_case "57-eligible-12-excluded" `Quick split_is_57_12;
          Alcotest.test_case "no-empty-frames" `Quick no_empty_frames;
        ] );
    ]
