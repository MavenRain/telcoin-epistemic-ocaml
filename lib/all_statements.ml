(** The full 189-statement report: the seven statements over the shared
    {!Tn_model} and the 182 statements of the 68 isolated family models, each
    proved over its own lean family model (see the family modules). Theorems
    over different State/View types cannot share a list, so the aggregation is
    the flat {!Report.t} projection; the per-family suites carry the actual
    kernel theorems and mutation pins. *)

(** The original seven statements, reported off the pristine {!Tn_model}
    system; a [make] failure degrades to [proved = false] rows rather than an
    exception, matching the family modules' [reports] contract. *)
let original_reports () =
  let row proved st =
    {
      Report.name = st.Statements.name;
      bucket = st.Statements.bucket;
      proved;
    }
  in
  Result.fold
    ~ok:(fun sys ->
      List.map
        (fun (st, r) ->
          row (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false) r) st)
        (Statements.prove_all sys))
    ~error:(fun Tn_model.Checker.Empty_init ->
      List.map (row false) Statements.all)
    (Tn_model.make ())

(** All 189 reports: the seven statements of the shared {!Tn_model} first, then
    each isolated family's [reports] in the order the family calls are listed
    below - 182 statements over 68 family models, 69 models in all. Each family
    call builds and checks its own model. *)
let all () =
  List.concat
    [
      original_reports ();
      Ban_statements.reports ();
      Admission_statements.reports ();
      Gossip_auth_statements.reports ();
      Exec_tally_statements.reports ();
      Identity_statements.reports ();
      Unres_statements.reports ();
      Prefetch_statements.reports ();
      Revote_statements.reports ();
      Swap_statements.reports ();
      Catchup_statements.reports ();
      Stall_statements.reports ();
      Reqres_statements.reports ();
      Epoch_record_statements.reports ();
      Epoch_sync_statements.reports ();
      Epoch_close_statements.reports ();
      Epoch_reward_statements.reports ();
      Cert_envelope_statements.reports ();
      Exec_tip_statements.reports ();
      Exex_fanout_statements.reports ();
      Exex_life_statements.reports ();
      Gossip_reject_statements.reports ();
      Own_durable_statements.reports ();
      Pending_gc_statements.reports ();
      Batch_verdict_statements.reports ();
      Verif_prov_statements.reports ();
      Discovery_statements.reports ();
      Subdag_leader_walk_statements.reports ();
      Dag_retention_statements.reports ();
      Round_weight_cap_statements.reports ();
      Parent_batch_forward_statements.reports ();
      Fetch_verif_state_statements.reports ();
      Causal_handoff_statements.reports ();
      Record_serve_pool_statements.reports ();
      Stream_slot_tenure_statements.reports ();
      Parent_claim_binding_statements.reports ();
      Vote_cache_retry_statements.reports ();
      Worker_stream_quota_statements.reports ();
      Batch_quorum_tally_statements.reports ();
      Output_forward_gate_statements.reports ();
      Pack_replay_statements.reports ();
      Gas_penalty_split_statements.reports ();
      Bls_verify_gate_statements.reports ();
      Close_block_syscall_statements.reports ();
      Tel_dispatch_surface_statements.reports ();
      Fee_routing_sink_statements.reports ();
      Tel_supply_ledger_statements.reports ();
      Batch_pack_share_statements.reports ();
      Tx_forward_route_statements.reports ();
      Cert_bitmap_quorum_statements.reports ();
      Boot_order_statements.reports ();
      Engine_queue_statements.reports ();
      Batch_admit_statements.reports ();
      Serve_slot_quota_statements.reports ();
      Exec_absorb_statements.reports ();
      Archive_pack_heal_statements.reports ();
      Archive_digest_lookup_statements.reports ();
      Archive_epoch_import_statements.reports ();
      Store_key_order_statements.reports ();
      Store_full_memory_statements.reports ();
      Archive_hash_index_statements.reports ();
      Backend_writer_thread_statements.reports ();
      Backend_env_split_statements.reports ();
      Store_notify_visibility_statements.reports ();
      Peer_prune_fairness_statements.reports ();
      Peer_temp_ban_statements.reports ();
      Rpc_codec_size_statements.reports ();
      Stream_inbound_quota_statements.reports ();
      Stream_sync_capability_statements.reports ();
    ]
