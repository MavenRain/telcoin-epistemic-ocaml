(** The categorical laws of the topos layer, run on every one of the 69 real
    model frames (DESIGN sec.6 gate 7).

    test/t_categorical.ml pins the same laws on a synthetic four-state frame
    where each is paired with a deliberately wrong operator. This suite is
    the complementary half: it asks whether the frames the library actually
    reasons over are legitimate homes for those operators, with witness
    subsets drawn from each model's own statements. See {!Topos_laws} for the
    list of laws and for why the verdict carries non-degeneracy counters. *)

open Telcoin_epistemic

(** Assert every law of one model's verdict, and that the witness family was
    not degenerate. A model whose witnesses were all trivial would satisfy
    every law for the wrong reason. *)
let check_model name run () =
  Result.fold
    ~error:(fun Topos_laws.Empty_init ->
      Alcotest.fail (name ^ ": empty init"))
    ~ok:(fun (v : Topos_laws.verdict) ->
      List.iter
        (fun (law, ok) -> Alcotest.(check bool) (name ^ ": " ^ law) true ok)
        v.Topos_laws.laws;
      Alcotest.(check bool)
        (name ^ ": witness family is non-degenerate ("
        ^ Int.to_string v.Topos_laws.nondegenerate
        ^ " of "
        ^ Int.to_string v.Topos_laws.witnesses
        ^ ", pairs over "
        ^ Int.to_string v.Topos_laws.pair_witnesses
        ^ ")")
        true
        (v.Topos_laws.nondegenerate >= 2))
    (run ())

(** [K_i] must lose information on at least SOME model, or the S5 laws above
    would everywhere be laws about the identity operator. Collected across
    all models rather than demanded of each, because a family whose single
    knowledge agent observes everything is a legitimate model, not a defect. *)
let k_nontrivial_somewhere runs () =
  Alcotest.(check bool) "some model has a genuinely partial view map" true
    (List.exists
       (fun (_, run) ->
         Result.fold
           ~error:(fun Topos_laws.Empty_init -> false)
           ~ok:(fun (v : Topos_laws.verdict) -> v.Topos_laws.k_nontrivial)
           (run ()))
       runs)

module L_tn = Topos_laws.Make (Tn_state) (Tn_state.Local)

(** The shared model's statement formulas, the witness source. *)
let sf_tn =
  List.concat_map
    (fun st -> Topos_gate.subformulas st.Statements.formula)
    Statements.all

(** The shared model's law run. *)
let run_tn () =
  L_tn.run ~init:[ Tn_state.initial ]
    ~next:(Tn_model.next_with Tn_model.Pristine)
    ~view:(fun v s -> Tn_state.local_of s v)
    ~label:Tn_model.label ~formulas:sf_tn ~agents:Validator.all
    ~group:Tn_model.honest

module L_admission = Topos_laws.Make (Admission_model.State) (Admission_model.View)

(** The admission family's statement formulas, the witness source. *)
let sf_admission =
  List.concat_map (fun st -> Topos_gate.subformulas st.Admission_statements.formula) Admission_statements.all

(** The admission family's law run. *)
let run_admission () =
  L_admission.run ~init:[ Admission_model.initial ] ~next:(Admission_model.next_with Admission_model.Pristine)
    ~view:Admission_model.view ~label:Admission_model.label ~formulas:sf_admission ~agents:Validator.all
    ~group:Validator.all

module L_ban = Topos_laws.Make (Ban_model.State) (Ban_model.View)

(** The ban family's statement formulas, the witness source. *)
let sf_ban =
  List.concat_map (fun st -> Topos_gate.subformulas st.Ban_statements.formula) Ban_statements.all

(** The ban family's law run. *)
let run_ban () =
  L_ban.run ~init:[ Ban_model.initial ] ~next:(Ban_model.next_with Ban_model.Pristine)
    ~view:Ban_model.view ~label:Ban_model.label ~formulas:sf_ban ~agents:Validator.all
    ~group:Validator.all

module L_batch_verdict = Topos_laws.Make (Batch_verdict_model.State) (Batch_verdict_model.View)

(** The batch_verdict family's statement formulas, the witness source. *)
let sf_batch_verdict =
  List.concat_map (fun st -> Topos_gate.subformulas st.Batch_verdict_statements.formula) Batch_verdict_statements.all

(** The batch_verdict family's law run. *)
let run_batch_verdict () =
  L_batch_verdict.run ~init:[ Batch_verdict_model.initial ] ~next:(Batch_verdict_model.next_with Batch_verdict_model.Pristine)
    ~view:Batch_verdict_model.view ~label:Batch_verdict_model.label ~formulas:sf_batch_verdict ~agents:Validator.all
    ~group:Validator.all

module L_catchup = Topos_laws.Make (Catchup_model.State) (Catchup_model.View)

(** The catchup family's statement formulas, the witness source. *)
let sf_catchup =
  List.concat_map (fun st -> Topos_gate.subformulas st.Catchup_statements.formula) Catchup_statements.all

(** The catchup family's law run. *)
let run_catchup () =
  L_catchup.run ~init:[ Catchup_model.initial ] ~next:(Catchup_model.next_with Catchup_model.Pristine)
    ~view:Catchup_model.view ~label:Catchup_model.label ~formulas:sf_catchup ~agents:Validator.all
    ~group:Validator.all

module L_cert_envelope = Topos_laws.Make (Cert_envelope_model.State) (Cert_envelope_model.View)

(** The cert_envelope family's statement formulas, the witness source. *)
let sf_cert_envelope =
  List.concat_map (fun st -> Topos_gate.subformulas st.Cert_envelope_statements.formula) Cert_envelope_statements.all

(** The cert_envelope family's law run. *)
let run_cert_envelope () =
  L_cert_envelope.run ~init:[ Cert_envelope_model.initial ] ~next:(Cert_envelope_model.next_with Cert_envelope_model.Pristine)
    ~view:Cert_envelope_model.view ~label:Cert_envelope_model.label ~formulas:sf_cert_envelope ~agents:Validator.all
    ~group:Validator.all

module L_discovery = Topos_laws.Make (Discovery_model.State) (Discovery_model.View)

(** The discovery family's statement formulas, the witness source. *)
let sf_discovery =
  List.concat_map (fun st -> Topos_gate.subformulas st.Discovery_statements.formula) Discovery_statements.all

(** The discovery family's law run. *)
let run_discovery () =
  L_discovery.run ~init:Discovery_model.initial ~next:(Discovery_model.next_with Discovery_model.Pristine)
    ~view:Discovery_model.view ~label:Discovery_model.label ~formulas:sf_discovery ~agents:Validator.all
    ~group:Validator.all

module L_epoch_close = Topos_laws.Make (Epoch_close_model.State) (Epoch_close_model.View)

(** The epoch_close family's statement formulas, the witness source. *)
let sf_epoch_close =
  List.concat_map (fun st -> Topos_gate.subformulas st.Epoch_close_statements.formula) Epoch_close_statements.all

(** The epoch_close family's law run. *)
let run_epoch_close () =
  L_epoch_close.run ~init:[ Epoch_close_model.initial ] ~next:(Epoch_close_model.next_with Epoch_close_model.Pristine)
    ~view:Epoch_close_model.view ~label:Epoch_close_model.label ~formulas:sf_epoch_close ~agents:Validator.all
    ~group:Validator.all

module L_epoch_record = Topos_laws.Make (Epoch_record_model.State) (Epoch_record_model.View)

(** The epoch_record family's statement formulas, the witness source. *)
let sf_epoch_record =
  List.concat_map (fun st -> Topos_gate.subformulas st.Epoch_record_statements.formula) Epoch_record_statements.all

(** The epoch_record family's law run. *)
let run_epoch_record () =
  L_epoch_record.run ~init:[ Epoch_record_model.initial ] ~next:(Epoch_record_model.next_with Epoch_record_model.Pristine)
    ~view:Epoch_record_model.view ~label:Epoch_record_model.label ~formulas:sf_epoch_record ~agents:Validator.all
    ~group:Validator.all

module L_epoch_reward = Topos_laws.Make (Epoch_reward_model.State) (Epoch_reward_model.View)

(** The epoch_reward family's statement formulas, the witness source. *)
let sf_epoch_reward =
  List.concat_map (fun st -> Topos_gate.subformulas st.Epoch_reward_statements.formula) Epoch_reward_statements.all

(** The epoch_reward family's law run. *)
let run_epoch_reward () =
  L_epoch_reward.run ~init:[ Epoch_reward_model.initial ] ~next:(Epoch_reward_model.next_with Epoch_reward_model.Pristine)
    ~view:Epoch_reward_model.view ~label:Epoch_reward_model.label ~formulas:sf_epoch_reward ~agents:Validator.all
    ~group:Validator.all

module L_epoch_sync = Topos_laws.Make (Epoch_sync_model.State) (Epoch_sync_model.View)

(** The epoch_sync family's statement formulas, the witness source. *)
let sf_epoch_sync =
  List.concat_map (fun st -> Topos_gate.subformulas st.Epoch_sync_statements.formula) Epoch_sync_statements.all

(** The epoch_sync family's law run. *)
let run_epoch_sync () =
  L_epoch_sync.run ~init:[ Epoch_sync_model.initial ] ~next:(Epoch_sync_model.next_with Epoch_sync_model.Pristine)
    ~view:Epoch_sync_model.view ~label:Epoch_sync_model.label ~formulas:sf_epoch_sync ~agents:Validator.all
    ~group:Validator.all

module L_exec_tally = Topos_laws.Make (Exec_tally_model.State) (Exec_tally_model.View)

(** The exec_tally family's statement formulas, the witness source. *)
let sf_exec_tally =
  List.concat_map (fun st -> Topos_gate.subformulas st.Exec_tally_statements.formula) Exec_tally_statements.all

(** The exec_tally family's law run. *)
let run_exec_tally () =
  L_exec_tally.run ~init:[ Exec_tally_model.initial ] ~next:(Exec_tally_model.next_with Exec_tally_model.Pristine)
    ~view:Exec_tally_model.view ~label:Exec_tally_model.label ~formulas:sf_exec_tally ~agents:Validator.all
    ~group:Validator.all

module L_exec_tip = Topos_laws.Make (Exec_tip_model.State) (Exec_tip_model.View)

(** The exec_tip family's statement formulas, the witness source. *)
let sf_exec_tip =
  List.concat_map (fun st -> Topos_gate.subformulas st.Exec_tip_statements.formula) Exec_tip_statements.all

(** The exec_tip family's law run. *)
let run_exec_tip () =
  L_exec_tip.run ~init:Exec_tip_model.initial ~next:(Exec_tip_model.next_with Exec_tip_model.Pristine)
    ~view:Exec_tip_model.view ~label:Exec_tip_model.label ~formulas:sf_exec_tip ~agents:Validator.all
    ~group:Validator.all

module L_exex_fanout = Topos_laws.Make (Exex_fanout_model.State) (Exex_fanout_model.View)

(** The exex_fanout family's statement formulas, the witness source. *)
let sf_exex_fanout =
  List.concat_map (fun st -> Topos_gate.subformulas st.Exex_fanout_statements.formula) Exex_fanout_statements.all

(** The exex_fanout family's law run. *)
let run_exex_fanout () =
  L_exex_fanout.run ~init:[ Exex_fanout_model.initial ] ~next:(Exex_fanout_model.next_with Exex_fanout_model.Pristine)
    ~view:Exex_fanout_model.view ~label:Exex_fanout_model.label ~formulas:sf_exex_fanout ~agents:Validator.all
    ~group:Validator.all

module L_exex_life = Topos_laws.Make (Exex_life_model.State) (Exex_life_model.View)

(** The exex_life family's statement formulas, the witness source. *)
let sf_exex_life =
  List.concat_map (fun st -> Topos_gate.subformulas st.Exex_life_statements.formula) Exex_life_statements.all

(** The exex_life family's law run. *)
let run_exex_life () =
  L_exex_life.run ~init:[ Exex_life_model.initial ] ~next:(Exex_life_model.next_with Exex_life_model.Pristine)
    ~view:Exex_life_model.view ~label:Exex_life_model.label ~formulas:sf_exex_life ~agents:Validator.all
    ~group:Validator.all

module L_gossip_auth = Topos_laws.Make (Gossip_auth_model.State) (Gossip_auth_model.View)

(** The gossip_auth family's statement formulas, the witness source. *)
let sf_gossip_auth =
  List.concat_map (fun st -> Topos_gate.subformulas st.Gossip_auth_statements.formula) Gossip_auth_statements.all

(** The gossip_auth family's law run. *)
let run_gossip_auth () =
  L_gossip_auth.run ~init:[ Gossip_auth_model.initial ] ~next:(Gossip_auth_model.next_with Gossip_auth_model.Pristine)
    ~view:Gossip_auth_model.view ~label:Gossip_auth_model.label ~formulas:sf_gossip_auth ~agents:Validator.all
    ~group:Validator.all

module L_gossip_reject = Topos_laws.Make (Gossip_reject_model.State) (Gossip_reject_model.View)

(** The gossip_reject family's statement formulas, the witness source. *)
let sf_gossip_reject =
  List.concat_map (fun st -> Topos_gate.subformulas st.Gossip_reject_statements.formula) Gossip_reject_statements.all

(** The gossip_reject family's law run. *)
let run_gossip_reject () =
  L_gossip_reject.run ~init:[ Gossip_reject_model.initial ] ~next:(Gossip_reject_model.next_with Gossip_reject_model.Pristine)
    ~view:Gossip_reject_model.view ~label:Gossip_reject_model.label ~formulas:sf_gossip_reject ~agents:Validator.all
    ~group:Validator.all

module L_identity = Topos_laws.Make (Identity_model.State) (Identity_model.View)

(** The identity family's statement formulas, the witness source. *)
let sf_identity =
  List.concat_map (fun st -> Topos_gate.subformulas st.Identity_statements.formula) Identity_statements.all

(** The identity family's law run. *)
let run_identity () =
  L_identity.run ~init:[ Identity_model.initial ] ~next:(Identity_model.next_with Identity_model.Pristine)
    ~view:Identity_model.view ~label:Identity_model.label ~formulas:sf_identity ~agents:Validator.all
    ~group:Validator.all

module L_own_durable = Topos_laws.Make (Own_durable_model.State) (Own_durable_model.View)

(** The own_durable family's statement formulas, the witness source. *)
let sf_own_durable =
  List.concat_map (fun st -> Topos_gate.subformulas st.Own_durable_statements.formula) Own_durable_statements.all

(** The own_durable family's law run. *)
let run_own_durable () =
  L_own_durable.run ~init:[ Own_durable_model.initial ] ~next:(Own_durable_model.next_with Own_durable_model.Pristine)
    ~view:Own_durable_model.view ~label:Own_durable_model.label ~formulas:sf_own_durable ~agents:Validator.all
    ~group:Validator.all

module L_pending_gc = Topos_laws.Make (Pending_gc_model.State) (Pending_gc_model.View)

(** The pending_gc family's statement formulas, the witness source. *)
let sf_pending_gc =
  List.concat_map (fun st -> Topos_gate.subformulas st.Pending_gc_statements.formula) Pending_gc_statements.all

(** The pending_gc family's law run. *)
let run_pending_gc () =
  L_pending_gc.run ~init:[ Pending_gc_model.initial; Pending_gc_model.initial_peer_holds ] ~next:(Pending_gc_model.next_with Pending_gc_model.Pristine)
    ~view:Pending_gc_model.view ~label:Pending_gc_model.label ~formulas:sf_pending_gc ~agents:Validator.all
    ~group:Validator.all

module L_prefetch = Topos_laws.Make (Prefetch_model.State) (Prefetch_model.View)

(** The prefetch family's statement formulas, the witness source. *)
let sf_prefetch =
  List.concat_map (fun st -> Topos_gate.subformulas st.Prefetch_statements.formula) Prefetch_statements.all

(** The prefetch family's law run. *)
let run_prefetch () =
  L_prefetch.run ~init:[ Prefetch_model.initial ] ~next:(Prefetch_model.next_with Prefetch_model.Pristine)
    ~view:Prefetch_model.view ~label:Prefetch_model.label ~formulas:sf_prefetch ~agents:Validator.all
    ~group:Validator.all

module L_reqres = Topos_laws.Make (Reqres_model.State) (Reqres_model.View)

(** The reqres family's statement formulas, the witness source. *)
let sf_reqres =
  List.concat_map (fun st -> Topos_gate.subformulas st.Reqres_statements.formula) Reqres_statements.all

(** The reqres family's law run. *)
let run_reqres () =
  L_reqres.run ~init:[ Reqres_model.initial ] ~next:(Reqres_model.next_with Reqres_model.Pristine)
    ~view:Reqres_model.view ~label:Reqres_model.label ~formulas:sf_reqres ~agents:Validator.all
    ~group:Validator.all

module L_revote = Topos_laws.Make (Revote_model.State) (Revote_model.View)

(** The revote family's statement formulas, the witness source. *)
let sf_revote =
  List.concat_map (fun st -> Topos_gate.subformulas st.Revote_statements.formula) Revote_statements.all

(** The revote family's law run. *)
let run_revote () =
  L_revote.run ~init:[ Revote_model.initial ] ~next:(Revote_model.next_with Revote_model.Pristine)
    ~view:Revote_model.view ~label:Revote_model.label ~formulas:sf_revote ~agents:Validator.all
    ~group:Validator.all

module L_stall = Topos_laws.Make (Stall_model.State) (Stall_model.View)

(** The stall family's statement formulas, the witness source. *)
let sf_stall =
  List.concat_map (fun st -> Topos_gate.subformulas st.Stall_statements.formula) Stall_statements.all

(** The stall family's law run. *)
let run_stall () =
  L_stall.run ~init:[ Stall_model.initial ] ~next:(Stall_model.next_with Stall_model.Pristine)
    ~view:Stall_model.view ~label:Stall_model.label ~formulas:sf_stall ~agents:Validator.all
    ~group:Validator.all

module L_swap = Topos_laws.Make (Swap_model.State) (Swap_model.View)

(** The swap family's statement formulas, the witness source. *)
let sf_swap =
  List.concat_map (fun st -> Topos_gate.subformulas st.Swap_statements.formula) Swap_statements.all

(** The swap family's law run. *)
let run_swap () =
  L_swap.run ~init:[ Swap_model.initial ] ~next:(Swap_model.next_with Swap_model.Pristine)
    ~view:Swap_model.view ~label:Swap_model.label ~formulas:sf_swap ~agents:Validator.all
    ~group:Validator.all

module L_unres = Topos_laws.Make (Unres_model.State) (Unres_model.View)

(** The unres family's statement formulas, the witness source. *)
let sf_unres =
  List.concat_map (fun st -> Topos_gate.subformulas st.Unres_statements.formula) Unres_statements.all

(** The unres family's law run. *)
let run_unres () =
  L_unres.run ~init:[ Unres_model.initial ] ~next:(Unres_model.next_with Unres_model.Pristine)
    ~view:Unres_model.view ~label:Unres_model.label ~formulas:sf_unres ~agents:Validator.all
    ~group:Validator.all

module L_verif_prov = Topos_laws.Make (Verif_prov_model.State) (Verif_prov_model.View)

(** The verif_prov family's statement formulas, the witness source. *)
let sf_verif_prov =
  List.concat_map (fun st -> Topos_gate.subformulas st.Verif_prov_statements.formula) Verif_prov_statements.all

(** The verif_prov family's law run. *)
let run_verif_prov () =
  L_verif_prov.run ~init:[ Verif_prov_model.initial ] ~next:(Verif_prov_model.next_with Verif_prov_model.Pristine)
    ~view:Verif_prov_model.view ~label:Verif_prov_model.label ~formulas:sf_verif_prov ~agents:Validator.all
    ~group:Validator.all

(** Every model, paired with its law run. *)

module L_subdag_leader_walk = Topos_laws.Make (Subdag_leader_walk_model.State) (Subdag_leader_walk_model.View)

(** The subdag_leader_walk family's statement formulas, the witness source. *)
let sf_subdag_leader_walk =
  List.concat_map (fun st -> Topos_gate.subformulas st.Subdag_leader_walk_statements.formula) Subdag_leader_walk_statements.all

(** The subdag_leader_walk family's law run. *)
let run_subdag_leader_walk () =
  L_subdag_leader_walk.run ~init:[ Subdag_leader_walk_model.initial; Subdag_leader_walk_model.initial_unsupported_linked; Subdag_leader_walk_model.initial_unsupported_unlinked ] ~next:(Subdag_leader_walk_model.next_with Subdag_leader_walk_model.Pristine)
    ~view:Subdag_leader_walk_model.view ~label:Subdag_leader_walk_model.label ~formulas:sf_subdag_leader_walk ~agents:Validator.all
    ~group:Validator.all

module L_dag_retention = Topos_laws.Make (Dag_retention_model.State) (Dag_retention_model.View)

(** The dag_retention family's statement formulas, the witness source. *)
let sf_dag_retention =
  List.concat_map (fun st -> Topos_gate.subformulas st.Dag_retention_statements.formula) Dag_retention_statements.all

(** The dag_retention family's law run. *)
let run_dag_retention () =
  L_dag_retention.run ~init:[ Dag_retention_model.initial; Dag_retention_model.initial_peer_c_holds; Dag_retention_model.initial_peer_a_names; Dag_retention_model.initial_peer_a_names_c_holds ] ~next:(Dag_retention_model.next_with Dag_retention_model.Pristine)
    ~view:Dag_retention_model.view ~label:Dag_retention_model.label ~formulas:sf_dag_retention ~agents:Validator.all
    ~group:Validator.all

module L_round_weight_cap = Topos_laws.Make (Round_weight_cap_model.State) (Round_weight_cap_model.View)

(** The round_weight_cap family's statement formulas, the witness source. *)
let sf_round_weight_cap =
  List.concat_map (fun st -> Topos_gate.subformulas st.Round_weight_cap_statements.formula) Round_weight_cap_statements.all

(** The round_weight_cap family's law run. *)
let run_round_weight_cap () =
  L_round_weight_cap.run ~init:[ Round_weight_cap_model.initial; Round_weight_cap_model.initial_equivocating ] ~next:(Round_weight_cap_model.next_with Round_weight_cap_model.Pristine)
    ~view:Round_weight_cap_model.view ~label:Round_weight_cap_model.label ~formulas:sf_round_weight_cap ~agents:Validator.all
    ~group:Validator.all

module L_parent_batch_forward = Topos_laws.Make (Parent_batch_forward_model.State) (Parent_batch_forward_model.View)

(** The parent_batch_forward family's statement formulas, the witness source. *)
let sf_parent_batch_forward =
  List.concat_map (fun st -> Topos_gate.subformulas st.Parent_batch_forward_statements.formula) Parent_batch_forward_statements.all

(** The parent_batch_forward family's law run. *)
let run_parent_batch_forward () =
  L_parent_batch_forward.run ~init:[ Parent_batch_forward_model.initial; Parent_batch_forward_model.initial_catchup ] ~next:(Parent_batch_forward_model.next_with Parent_batch_forward_model.Pristine)
    ~view:Parent_batch_forward_model.view ~label:Parent_batch_forward_model.label ~formulas:sf_parent_batch_forward ~agents:Validator.all
    ~group:Validator.all

module L_fetch_verif_state = Topos_laws.Make (Fetch_verif_state_model.State) (Fetch_verif_state_model.View)

(** The fetch_verif_state family's statement formulas, the witness source. *)
let sf_fetch_verif_state =
  List.concat_map (fun st -> Topos_gate.subformulas st.Fetch_verif_state_statements.formula) Fetch_verif_state_statements.all

(** The fetch_verif_state family's law run. *)
let run_fetch_verif_state () =
  L_fetch_verif_state.run ~init:[ Fetch_verif_state_model.initial ] ~next:(Fetch_verif_state_model.next_with Fetch_verif_state_model.Pristine)
    ~view:Fetch_verif_state_model.view ~label:Fetch_verif_state_model.label ~formulas:sf_fetch_verif_state ~agents:Validator.all
    ~group:Validator.all

module L_causal_handoff = Topos_laws.Make (Causal_handoff_model.State) (Causal_handoff_model.View)

(** The causal_handoff family's statement formulas, the witness source. *)
let sf_causal_handoff =
  List.concat_map (fun st -> Topos_gate.subformulas st.Causal_handoff_statements.formula) Causal_handoff_statements.all

(** The causal_handoff family's law run. *)
let run_causal_handoff () =
  L_causal_handoff.run ~init:[ Causal_handoff_model.initial; Causal_handoff_model.initial_peer_holds ] ~next:(Causal_handoff_model.next_with Causal_handoff_model.Pristine)
    ~view:Causal_handoff_model.view ~label:Causal_handoff_model.label ~formulas:sf_causal_handoff ~agents:Validator.all
    ~group:Validator.all

module L_record_serve_pool = Topos_laws.Make (Record_serve_pool_model.State) (Record_serve_pool_model.View)

(** The record_serve_pool family's statement formulas, the witness source. *)
let sf_record_serve_pool =
  List.concat_map (fun st -> Topos_gate.subformulas st.Record_serve_pool_statements.formula) Record_serve_pool_statements.all

(** The record_serve_pool family's law run. *)
let run_record_serve_pool () =
  L_record_serve_pool.run ~init:[ Record_serve_pool_model.initial ] ~next:(Record_serve_pool_model.next_with Record_serve_pool_model.Pristine)
    ~view:Record_serve_pool_model.view ~label:Record_serve_pool_model.label ~formulas:sf_record_serve_pool ~agents:Validator.all
    ~group:Validator.all

module L_stream_slot_tenure = Topos_laws.Make (Stream_slot_tenure_model.State) (Stream_slot_tenure_model.View)

(** The stream_slot_tenure family's statement formulas, the witness source. *)
let sf_stream_slot_tenure =
  List.concat_map (fun st -> Topos_gate.subformulas st.Stream_slot_tenure_statements.formula) Stream_slot_tenure_statements.all

(** The stream_slot_tenure family's law run. *)
let run_stream_slot_tenure () =
  L_stream_slot_tenure.run ~init:[ Stream_slot_tenure_model.initial; Stream_slot_tenure_model.initial_requester_silent ] ~next:(Stream_slot_tenure_model.next_with Stream_slot_tenure_model.Pristine)
    ~view:Stream_slot_tenure_model.view ~label:Stream_slot_tenure_model.label ~formulas:sf_stream_slot_tenure ~agents:Validator.all
    ~group:Validator.all

module L_parent_claim_binding = Topos_laws.Make (Parent_claim_binding_model.State) (Parent_claim_binding_model.View)

(** The parent_claim_binding family's statement formulas, the witness source. *)
let sf_parent_claim_binding =
  List.concat_map (fun st -> Topos_gate.subformulas st.Parent_claim_binding_statements.formula) Parent_claim_binding_statements.all

(** The parent_claim_binding family's law run. *)
let run_parent_claim_binding () =
  L_parent_claim_binding.run ~init:[ Parent_claim_binding_model.initial; Parent_claim_binding_model.initial_bogus; Parent_claim_binding_model.initial_b_holds; Parent_claim_binding_model.initial_c_holds; Parent_claim_binding_model.initial_author_lean; Parent_claim_binding_model.initial_author_rich ] ~next:(Parent_claim_binding_model.next_with Parent_claim_binding_model.Pristine)
    ~view:Parent_claim_binding_model.view ~label:Parent_claim_binding_model.label ~formulas:sf_parent_claim_binding ~agents:Validator.all
    ~group:Validator.all


module L_vote_cache_retry = Topos_laws.Make (Vote_cache_retry_model.State) (Vote_cache_retry_model.View)

(** The vote_cache_retry family's statement formulas, the witness source. *)
let sf_vote_cache_retry =
  List.concat_map (fun st -> Topos_gate.subformulas st.Vote_cache_retry_statements.formula) Vote_cache_retry_statements.all

(** The vote_cache_retry family's law run. *)
let run_vote_cache_retry () =
  L_vote_cache_retry.run ~init:[ Vote_cache_retry_model.initial ] ~next:(Vote_cache_retry_model.next_with Vote_cache_retry_model.Pristine)
    ~view:Vote_cache_retry_model.view ~label:Vote_cache_retry_model.label ~formulas:sf_vote_cache_retry ~agents:Validator.all
    ~group:Validator.all

module L_worker_stream_quota = Topos_laws.Make (Worker_stream_quota_model.State) (Worker_stream_quota_model.View)

(** The worker_stream_quota family's statement formulas, the witness source. *)
let sf_worker_stream_quota =
  List.concat_map (fun st -> Topos_gate.subformulas st.Worker_stream_quota_statements.formula) Worker_stream_quota_statements.all

(** The worker_stream_quota family's law run. *)
let run_worker_stream_quota () =
  L_worker_stream_quota.run ~init:[ Worker_stream_quota_model.initial ] ~next:(Worker_stream_quota_model.next_with Worker_stream_quota_model.Pristine)
    ~view:Worker_stream_quota_model.view ~label:Worker_stream_quota_model.label ~formulas:sf_worker_stream_quota ~agents:Validator.all
    ~group:Validator.all

module L_batch_quorum_tally = Topos_laws.Make (Batch_quorum_tally_model.State) (Batch_quorum_tally_model.View)

(** The batch_quorum_tally family's statement formulas, the witness source. *)
let sf_batch_quorum_tally =
  List.concat_map (fun st -> Topos_gate.subformulas st.Batch_quorum_tally_statements.formula) Batch_quorum_tally_statements.all

(** The batch_quorum_tally family's law run. *)
let run_batch_quorum_tally () =
  L_batch_quorum_tally.run ~init:[ Batch_quorum_tally_model.initial ] ~next:(Batch_quorum_tally_model.next_with Batch_quorum_tally_model.Pristine)
    ~view:Batch_quorum_tally_model.view ~label:Batch_quorum_tally_model.label ~formulas:sf_batch_quorum_tally ~agents:Validator.all
    ~group:Validator.all

module L_output_forward_gate = Topos_laws.Make (Output_forward_gate_model.State) (Output_forward_gate_model.View)

(** The output_forward_gate family's statement formulas, the witness source. *)
let sf_output_forward_gate =
  List.concat_map (fun st -> Topos_gate.subformulas st.Output_forward_gate_statements.formula) Output_forward_gate_statements.all

(** The output_forward_gate family's law run. *)
let run_output_forward_gate () =
  L_output_forward_gate.run ~init:[ Output_forward_gate_model.initial; Output_forward_gate_model.initial_rebroadcast_buffered ] ~next:(Output_forward_gate_model.next_with Output_forward_gate_model.Pristine)
    ~view:Output_forward_gate_model.view ~label:Output_forward_gate_model.label ~formulas:sf_output_forward_gate ~agents:Validator.all
    ~group:Validator.all

module L_pack_replay = Topos_laws.Make (Pack_replay_model.State) (Pack_replay_model.View)

(** The pack_replay family's statement formulas, the witness source. *)
let sf_pack_replay =
  List.concat_map (fun st -> Topos_gate.subformulas st.Pack_replay_statements.formula) Pack_replay_statements.all

(** The pack_replay family's law run. *)
let run_pack_replay () =
  L_pack_replay.run ~init:[ Pack_replay_model.initial ] ~next:(Pack_replay_model.next_with Pack_replay_model.Pristine)
    ~view:Pack_replay_model.view ~label:Pack_replay_model.label ~formulas:sf_pack_replay ~agents:Validator.all
    ~group:Validator.all


module L_gas_penalty_split = Topos_laws.Make (Gas_penalty_split_model.State) (Gas_penalty_split_model.View)

(** The gas_penalty_split family's statement formulas, the witness source. *)
let sf_gas_penalty_split =
  List.concat_map (fun st -> Topos_gate.subformulas st.Gas_penalty_split_statements.formula) Gas_penalty_split_statements.all

(** The gas_penalty_split family's law run. *)
let run_gas_penalty_split () =
  L_gas_penalty_split.run ~init:[ Gas_penalty_split_model.initial ] ~next:(Gas_penalty_split_model.next_with Gas_penalty_split_model.Pristine)
    ~view:Gas_penalty_split_model.view ~label:Gas_penalty_split_model.label ~formulas:sf_gas_penalty_split ~agents:Validator.all
    ~group:Validator.all

module L_bls_verify_gate = Topos_laws.Make (Bls_verify_gate_model.State) (Bls_verify_gate_model.View)

(** The bls_verify_gate family's statement formulas, the witness source. *)
let sf_bls_verify_gate =
  List.concat_map (fun st -> Topos_gate.subformulas st.Bls_verify_gate_statements.formula) Bls_verify_gate_statements.all

(** The bls_verify_gate family's law run. *)
let run_bls_verify_gate () =
  L_bls_verify_gate.run ~init:[ Bls_verify_gate_model.initial ] ~next:(Bls_verify_gate_model.next_with Bls_verify_gate_model.Pristine)
    ~view:Bls_verify_gate_model.view ~label:Bls_verify_gate_model.label ~formulas:sf_bls_verify_gate ~agents:Validator.all
    ~group:Validator.all

module L_close_block_syscall = Topos_laws.Make (Close_block_syscall_model.State) (Close_block_syscall_model.View)

(** The close_block_syscall family's statement formulas, the witness source. *)
let sf_close_block_syscall =
  List.concat_map (fun st -> Topos_gate.subformulas st.Close_block_syscall_statements.formula) Close_block_syscall_statements.all

(** The close_block_syscall family's law run. *)
let run_close_block_syscall () =
  L_close_block_syscall.run ~init:Close_block_syscall_model.inits ~next:(Close_block_syscall_model.next_with Close_block_syscall_model.Pristine)
    ~view:Close_block_syscall_model.view ~label:Close_block_syscall_model.label ~formulas:sf_close_block_syscall ~agents:Validator.all
    ~group:Validator.all

module L_tel_dispatch_surface = Topos_laws.Make (Tel_dispatch_surface_model.State) (Tel_dispatch_surface_model.View)

(** The tel_dispatch_surface family's statement formulas, the witness source. *)
let sf_tel_dispatch_surface =
  List.concat_map (fun st -> Topos_gate.subformulas st.Tel_dispatch_surface_statements.formula) Tel_dispatch_surface_statements.all

(** The tel_dispatch_surface family's law run. *)
let run_tel_dispatch_surface () =
  L_tel_dispatch_surface.run ~init:[ Tel_dispatch_surface_model.initial ] ~next:(Tel_dispatch_surface_model.next_with Tel_dispatch_surface_model.Pristine)
    ~view:Tel_dispatch_surface_model.view ~label:Tel_dispatch_surface_model.label ~formulas:sf_tel_dispatch_surface ~agents:Validator.all
    ~group:Validator.all

module L_fee_routing_sink = Topos_laws.Make (Fee_routing_sink_model.State) (Fee_routing_sink_model.View)

(** The fee_routing_sink family's statement formulas, the witness source. *)
let sf_fee_routing_sink =
  List.concat_map (fun st -> Topos_gate.subformulas st.Fee_routing_sink_statements.formula) Fee_routing_sink_statements.all

(** The fee_routing_sink family's law run. *)
let run_fee_routing_sink () =
  L_fee_routing_sink.run ~init:[ Fee_routing_sink_model.initial ] ~next:(Fee_routing_sink_model.next_with Fee_routing_sink_model.Pristine)
    ~view:Fee_routing_sink_model.view ~label:Fee_routing_sink_model.label ~formulas:sf_fee_routing_sink ~agents:Validator.all
    ~group:Validator.all


module L_tel_supply_ledger = Topos_laws.Make (Tel_supply_ledger_model.State) (Tel_supply_ledger_model.View)

(** The tel_supply_ledger family's statement formulas, the witness source. *)
let sf_tel_supply_ledger =
  List.concat_map (fun st -> Topos_gate.subformulas st.Tel_supply_ledger_statements.formula) Tel_supply_ledger_statements.all

(** The tel_supply_ledger family's law run. *)
let run_tel_supply_ledger () =
  L_tel_supply_ledger.run ~init:[ Tel_supply_ledger_model.initial ] ~next:(Tel_supply_ledger_model.next_with Tel_supply_ledger_model.Pristine)
    ~view:Tel_supply_ledger_model.view ~label:Tel_supply_ledger_model.label ~formulas:sf_tel_supply_ledger ~agents:Validator.all
    ~group:Validator.all


module L_batch_pack_share = Topos_laws.Make (Batch_pack_share_model.State) (Batch_pack_share_model.View)

(** The batch_pack_share family's statement formulas, the witness source. *)
let sf_batch_pack_share =
  List.concat_map (fun st -> Topos_gate.subformulas st.Batch_pack_share_statements.formula) Batch_pack_share_statements.all

(** The batch_pack_share family's law run. *)
let run_batch_pack_share () =
  L_batch_pack_share.run ~init:Batch_pack_share_model.all_initials ~next:(Batch_pack_share_model.next_with Batch_pack_share_model.Pristine)
    ~view:Batch_pack_share_model.view ~label:Batch_pack_share_model.label ~formulas:sf_batch_pack_share ~agents:Validator.all
    ~group:Validator.all

module L_tx_forward_route = Topos_laws.Make (Tx_forward_route_model.State) (Tx_forward_route_model.View)

(** The tx_forward_route family's statement formulas, the witness source. *)
let sf_tx_forward_route =
  List.concat_map (fun st -> Topos_gate.subformulas st.Tx_forward_route_statements.formula) Tx_forward_route_statements.all

(** The tx_forward_route family's law run. *)
let run_tx_forward_route () =
  L_tx_forward_route.run ~init:Tx_forward_route_model.inits ~next:(Tx_forward_route_model.next_with Tx_forward_route_model.Pristine)
    ~view:Tx_forward_route_model.view ~label:Tx_forward_route_model.label ~formulas:sf_tx_forward_route ~agents:Validator.all
    ~group:Validator.all

module L_cert_bitmap_quorum = Topos_laws.Make (Cert_bitmap_quorum_model.State) (Cert_bitmap_quorum_model.View)

(** The cert_bitmap_quorum family's statement formulas, the witness source. *)
let sf_cert_bitmap_quorum =
  List.concat_map (fun st -> Topos_gate.subformulas st.Cert_bitmap_quorum_statements.formula) Cert_bitmap_quorum_statements.all

(** The cert_bitmap_quorum family's law run. *)
let run_cert_bitmap_quorum () =
  L_cert_bitmap_quorum.run ~init:[ Cert_bitmap_quorum_model.initial ] ~next:(Cert_bitmap_quorum_model.next_with Cert_bitmap_quorum_model.Pristine)
    ~view:Cert_bitmap_quorum_model.view ~label:Cert_bitmap_quorum_model.label ~formulas:sf_cert_bitmap_quorum ~agents:Validator.all
    ~group:Validator.all

module L_boot_order = Topos_laws.Make (Boot_order_model.State) (Boot_order_model.View)

(** The boot_order family's statement formulas, the witness source. *)
let sf_boot_order =
  List.concat_map (fun st -> Topos_gate.subformulas st.Boot_order_statements.formula) Boot_order_statements.all

(** The boot_order family's law run. *)
let run_boot_order () =
  L_boot_order.run ~init:Boot_order_model.inits ~next:(Boot_order_model.next_with Boot_order_model.Pristine)
    ~view:Boot_order_model.view ~label:Boot_order_model.label ~formulas:sf_boot_order ~agents:Validator.all
    ~group:Validator.all


module L_engine_queue = Topos_laws.Make (Engine_queue_model.State) (Engine_queue_model.View)

(** The engine_queue family's statement formulas, the witness source. *)
let sf_engine_queue =
  List.concat_map (fun st -> Topos_gate.subformulas st.Engine_queue_statements.formula) Engine_queue_statements.all

(** The engine_queue family's law run. *)
let run_engine_queue () =
  L_engine_queue.run ~init:[ Engine_queue_model.initial ] ~next:(Engine_queue_model.next_with Engine_queue_model.Pristine)
    ~view:Engine_queue_model.view ~label:Engine_queue_model.label ~formulas:sf_engine_queue ~agents:Validator.all
    ~group:Validator.all

module L_batch_admit = Topos_laws.Make (Batch_admit_model.State) (Batch_admit_model.View)

(** The batch_admit family's statement formulas, the witness source. *)
let sf_batch_admit =
  List.concat_map (fun st -> Topos_gate.subformulas st.Batch_admit_statements.formula) Batch_admit_statements.all

(** The batch_admit family's law run. *)
let run_batch_admit () =
  L_batch_admit.run ~init:Batch_admit_model.inits ~next:(Batch_admit_model.next_with Batch_admit_model.Pristine)
    ~view:Batch_admit_model.view ~label:Batch_admit_model.label ~formulas:sf_batch_admit ~agents:Validator.all
    ~group:Validator.all

module L_serve_slot_quota = Topos_laws.Make (Serve_slot_quota_model.State) (Serve_slot_quota_model.View)

(** The serve_slot_quota family's statement formulas, the witness source. *)
let sf_serve_slot_quota =
  List.concat_map (fun st -> Topos_gate.subformulas st.Serve_slot_quota_statements.formula) Serve_slot_quota_statements.all

(** The serve_slot_quota family's law run. *)
let run_serve_slot_quota () =
  L_serve_slot_quota.run ~init:[ Serve_slot_quota_model.initial ] ~next:(Serve_slot_quota_model.next_with Serve_slot_quota_model.Pristine)
    ~view:Serve_slot_quota_model.view ~label:Serve_slot_quota_model.label ~formulas:sf_serve_slot_quota ~agents:Validator.all
    ~group:Validator.all

module L_exec_absorb = Topos_laws.Make (Exec_absorb_model.State) (Exec_absorb_model.View)

(** The exec_absorb family's statement formulas, the witness source. *)
let sf_exec_absorb =
  List.concat_map (fun st -> Topos_gate.subformulas st.Exec_absorb_statements.formula) Exec_absorb_statements.all

(** The exec_absorb family's law run. *)
let run_exec_absorb () =
  L_exec_absorb.run ~init:Exec_absorb_model.inits ~next:(Exec_absorb_model.next_with Exec_absorb_model.Pristine)
    ~view:Exec_absorb_model.view ~label:Exec_absorb_model.label ~formulas:sf_exec_absorb ~agents:Validator.all
    ~group:Validator.all

module L_archive_pack_heal = Topos_laws.Make (Archive_pack_heal_model.State) (Archive_pack_heal_model.View)

(** The archive_pack_heal family's statement formulas, the witness source. *)
let sf_archive_pack_heal =
  List.concat_map (fun st -> Topos_gate.subformulas st.Archive_pack_heal_statements.formula) Archive_pack_heal_statements.all

(** The archive_pack_heal family's law run. *)
let run_archive_pack_heal () =
  L_archive_pack_heal.run ~init:[ Archive_pack_heal_model.initial ] ~next:(Archive_pack_heal_model.next_with Archive_pack_heal_model.Pristine)
    ~view:Archive_pack_heal_model.view ~label:Archive_pack_heal_model.label ~formulas:sf_archive_pack_heal ~agents:Validator.all
    ~group:Validator.all

module L_archive_digest_lookup = Topos_laws.Make (Archive_digest_lookup_model.State) (Archive_digest_lookup_model.View)

(** The archive_digest_lookup family's statement formulas, the witness source. *)
let sf_archive_digest_lookup =
  List.concat_map (fun st -> Topos_gate.subformulas st.Archive_digest_lookup_statements.formula) Archive_digest_lookup_statements.all

(** The archive_digest_lookup family's law run. *)
let run_archive_digest_lookup () =
  L_archive_digest_lookup.run ~init:[ Archive_digest_lookup_model.initial; Archive_digest_lookup_model.initial_no_d_entry ] ~next:(Archive_digest_lookup_model.next_with Archive_digest_lookup_model.Pristine)
    ~view:Archive_digest_lookup_model.view ~label:Archive_digest_lookup_model.label ~formulas:sf_archive_digest_lookup ~agents:Validator.all
    ~group:Validator.all


module L_archive_epoch_import = Topos_laws.Make (Archive_epoch_import_model.State) (Archive_epoch_import_model.View)

(** The archive_epoch_import family's statement formulas, the witness source. *)
let sf_archive_epoch_import =
  List.concat_map (fun st -> Topos_gate.subformulas st.Archive_epoch_import_statements.formula) Archive_epoch_import_statements.all

(** The archive_epoch_import family's law run. *)
let run_archive_epoch_import () =
  L_archive_epoch_import.run ~init:Archive_epoch_import_model.inits ~next:(Archive_epoch_import_model.next_with Archive_epoch_import_model.Pristine)
    ~view:Archive_epoch_import_model.view ~label:Archive_epoch_import_model.label ~formulas:sf_archive_epoch_import ~agents:Validator.all
    ~group:Validator.all

module L_store_key_order = Topos_laws.Make (Store_key_order_model.State) (Store_key_order_model.View)

(** The store_key_order family's statement formulas, the witness source. *)
let sf_store_key_order =
  List.concat_map (fun st -> Topos_gate.subformulas st.Store_key_order_statements.formula) Store_key_order_statements.all

(** The store_key_order family's law run. *)
let run_store_key_order () =
  L_store_key_order.run ~init:[ Store_key_order_model.initial ] ~next:(Store_key_order_model.next_with Store_key_order_model.Pristine)
    ~view:Store_key_order_model.view ~label:Store_key_order_model.label ~formulas:sf_store_key_order ~agents:Validator.all
    ~group:Validator.all

module L_store_full_memory = Topos_laws.Make (Store_full_memory_model.State) (Store_full_memory_model.View)

(** The store_full_memory family's statement formulas, the witness source. *)
let sf_store_full_memory =
  List.concat_map (fun st -> Topos_gate.subformulas st.Store_full_memory_statements.formula) Store_full_memory_statements.all

(** The store_full_memory family's law run. *)
let run_store_full_memory () =
  L_store_full_memory.run ~init:[ Store_full_memory_model.initial ] ~next:(Store_full_memory_model.next_with Store_full_memory_model.Pristine)
    ~view:Store_full_memory_model.view ~label:Store_full_memory_model.label ~formulas:sf_store_full_memory ~agents:Validator.all
    ~group:Validator.all


module L_archive_hash_index = Topos_laws.Make (Archive_hash_index_model.State) (Archive_hash_index_model.View)

(** The archive_hash_index family's statement formulas, the witness source. *)
let sf_archive_hash_index =
  List.concat_map (fun st -> Topos_gate.subformulas st.Archive_hash_index_statements.formula) Archive_hash_index_statements.all

(** The archive_hash_index family's law run. *)
let run_archive_hash_index () =
  L_archive_hash_index.run ~init:[ Archive_hash_index_model.initial ] ~next:(Archive_hash_index_model.next_with Archive_hash_index_model.Pristine)
    ~view:Archive_hash_index_model.view ~label:Archive_hash_index_model.label ~formulas:sf_archive_hash_index ~agents:Validator.all
    ~group:Validator.all

module L_backend_writer_thread = Topos_laws.Make (Backend_writer_thread_model.State) (Backend_writer_thread_model.View)

(** The backend_writer_thread family's statement formulas, the witness source. *)
let sf_backend_writer_thread =
  List.concat_map (fun st -> Topos_gate.subformulas st.Backend_writer_thread_statements.formula) Backend_writer_thread_statements.all

(** The backend_writer_thread family's law run. *)
let run_backend_writer_thread () =
  L_backend_writer_thread.run ~init:[ Backend_writer_thread_model.initial ] ~next:(Backend_writer_thread_model.next_with Backend_writer_thread_model.Pristine)
    ~view:Backend_writer_thread_model.view ~label:Backend_writer_thread_model.label ~formulas:sf_backend_writer_thread ~agents:Validator.all
    ~group:Validator.all

module L_backend_env_split = Topos_laws.Make (Backend_env_split_model.State) (Backend_env_split_model.View)

(** The backend_env_split family's statement formulas, the witness source. *)
let sf_backend_env_split =
  List.concat_map (fun st -> Topos_gate.subformulas st.Backend_env_split_statements.formula) Backend_env_split_statements.all

(** The backend_env_split family's law run. *)
let run_backend_env_split () =
  L_backend_env_split.run ~init:[ Backend_env_split_model.initial ] ~next:(Backend_env_split_model.next_with Backend_env_split_model.Pristine)
    ~view:Backend_env_split_model.view ~label:Backend_env_split_model.label ~formulas:sf_backend_env_split ~agents:Validator.all
    ~group:Validator.all

module L_store_notify_visibility = Topos_laws.Make (Store_notify_visibility_model.State) (Store_notify_visibility_model.View)

(** The store_notify_visibility family's statement formulas, the witness source. *)
let sf_store_notify_visibility =
  List.concat_map (fun st -> Topos_gate.subformulas st.Store_notify_visibility_statements.formula) Store_notify_visibility_statements.all

(** The store_notify_visibility family's law run. *)
let run_store_notify_visibility () =
  L_store_notify_visibility.run ~init:Store_notify_visibility_model.inits ~next:(Store_notify_visibility_model.next_with Store_notify_visibility_model.Pristine)
    ~view:Store_notify_visibility_model.view ~label:Store_notify_visibility_model.label ~formulas:sf_store_notify_visibility ~agents:Validator.all
    ~group:Validator.all

module L_peer_prune_fairness = Topos_laws.Make (Peer_prune_fairness_model.State) (Peer_prune_fairness_model.View)

(** The peer_prune_fairness family's statement formulas, the witness source. *)
let sf_peer_prune_fairness =
  List.concat_map (fun st -> Topos_gate.subformulas st.Peer_prune_fairness_statements.formula) Peer_prune_fairness_statements.all

(** The peer_prune_fairness family's law run. *)
let run_peer_prune_fairness () =
  L_peer_prune_fairness.run ~init:Peer_prune_fairness_model.inits ~next:(Peer_prune_fairness_model.next_with Peer_prune_fairness_model.Pristine)
    ~view:Peer_prune_fairness_model.view ~label:Peer_prune_fairness_model.label ~formulas:sf_peer_prune_fairness ~agents:Validator.all
    ~group:Validator.all

module L_peer_temp_ban = Topos_laws.Make (Peer_temp_ban_model.State) (Peer_temp_ban_model.View)

(** The peer_temp_ban family's statement formulas, the witness source. *)
let sf_peer_temp_ban =
  List.concat_map (fun st -> Topos_gate.subformulas st.Peer_temp_ban_statements.formula) Peer_temp_ban_statements.all

(** The peer_temp_ban family's law run. *)
let run_peer_temp_ban () =
  L_peer_temp_ban.run ~init:[ Peer_temp_ban_model.initial; Peer_temp_ban_model.initial_staggered ] ~next:(Peer_temp_ban_model.next_with Peer_temp_ban_model.Pristine)
    ~view:Peer_temp_ban_model.view ~label:Peer_temp_ban_model.label ~formulas:sf_peer_temp_ban ~agents:Validator.all
    ~group:Validator.all

module L_rpc_codec_size = Topos_laws.Make (Rpc_codec_size_model.State) (Rpc_codec_size_model.View)

(** The rpc_codec_size family's statement formulas, the witness source. *)
let sf_rpc_codec_size =
  List.concat_map (fun st -> Topos_gate.subformulas st.Rpc_codec_size_statements.formula) Rpc_codec_size_statements.all

(** The rpc_codec_size family's law run. *)
let run_rpc_codec_size () =
  L_rpc_codec_size.run ~init:[ Rpc_codec_size_model.initial ] ~next:(Rpc_codec_size_model.next_with Rpc_codec_size_model.Pristine)
    ~view:Rpc_codec_size_model.view ~label:Rpc_codec_size_model.label ~formulas:sf_rpc_codec_size ~agents:Validator.all
    ~group:Validator.all

module L_stream_inbound_quota = Topos_laws.Make (Stream_inbound_quota_model.State) (Stream_inbound_quota_model.View)

(** The stream_inbound_quota family's statement formulas, the witness source. *)
let sf_stream_inbound_quota =
  List.concat_map (fun st -> Topos_gate.subformulas st.Stream_inbound_quota_statements.formula) Stream_inbound_quota_statements.all

(** The stream_inbound_quota family's law run. *)
let run_stream_inbound_quota () =
  L_stream_inbound_quota.run ~init:[ Stream_inbound_quota_model.initial ] ~next:(Stream_inbound_quota_model.next_with Stream_inbound_quota_model.Pristine)
    ~view:Stream_inbound_quota_model.view ~label:Stream_inbound_quota_model.label ~formulas:sf_stream_inbound_quota ~agents:Validator.all
    ~group:Validator.all

module L_stream_sync_capability = Topos_laws.Make (Stream_sync_capability_model.State) (Stream_sync_capability_model.View)

(** The stream_sync_capability family's statement formulas, the witness source. *)
let sf_stream_sync_capability =
  List.concat_map (fun st -> Topos_gate.subformulas st.Stream_sync_capability_statements.formula) Stream_sync_capability_statements.all

(** The stream_sync_capability family's law run. *)
let run_stream_sync_capability () =
  L_stream_sync_capability.run ~init:Stream_sync_capability_model.inits ~next:(Stream_sync_capability_model.next_with Stream_sync_capability_model.Pristine)
    ~view:Stream_sync_capability_model.view ~label:Stream_sync_capability_model.label ~formulas:sf_stream_sync_capability ~agents:Validator.all
    ~group:Validator.all

let runs =
  [
    ("tn_model", run_tn);
    ("admission", run_admission);
    ("ban", run_ban);
    ("batch_verdict", run_batch_verdict);
    ("catchup", run_catchup);
    ("cert_envelope", run_cert_envelope);
    ("discovery", run_discovery);
    ("epoch_close", run_epoch_close);
    ("epoch_record", run_epoch_record);
    ("epoch_reward", run_epoch_reward);
    ("epoch_sync", run_epoch_sync);
    ("exec_tally", run_exec_tally);
    ("exec_tip", run_exec_tip);
    ("exex_fanout", run_exex_fanout);
    ("exex_life", run_exex_life);
    ("gossip_auth", run_gossip_auth);
    ("gossip_reject", run_gossip_reject);
    ("identity", run_identity);
    ("own_durable", run_own_durable);
    ("pending_gc", run_pending_gc);
    ("prefetch", run_prefetch);
    ("reqres", run_reqres);
    ("revote", run_revote);
    ("stall", run_stall);
    ("swap", run_swap);
    ("unres", run_unres);
    ("verif_prov", run_verif_prov);
    ("subdag_leader_walk", run_subdag_leader_walk);
    ("dag_retention", run_dag_retention);
    ("round_weight_cap", run_round_weight_cap);
    ("parent_batch_forward", run_parent_batch_forward);
    ("fetch_verif_state", run_fetch_verif_state);
    ("causal_handoff", run_causal_handoff);
    ("record_serve_pool", run_record_serve_pool);
    ("stream_slot_tenure", run_stream_slot_tenure);
    ("parent_claim_binding", run_parent_claim_binding);
    ("vote_cache_retry", run_vote_cache_retry);
    ("worker_stream_quota", run_worker_stream_quota);
    ("batch_quorum_tally", run_batch_quorum_tally);
    ("output_forward_gate", run_output_forward_gate);
    ("pack_replay", run_pack_replay);
    ("gas_penalty_split", run_gas_penalty_split);
    ("bls_verify_gate", run_bls_verify_gate);
    ("close_block_syscall", run_close_block_syscall);
    ("tel_dispatch_surface", run_tel_dispatch_surface);
    ("fee_routing_sink", run_fee_routing_sink);
    ("tel_supply_ledger", run_tel_supply_ledger);
    ("batch_pack_share", run_batch_pack_share);
    ("tx_forward_route", run_tx_forward_route);
    ("cert_bitmap_quorum", run_cert_bitmap_quorum);
    ("boot_order", run_boot_order);
    ("engine_queue", run_engine_queue);
    ("batch_admit", run_batch_admit);
    ("serve_slot_quota", run_serve_slot_quota);
    ("exec_absorb", run_exec_absorb);
    ("archive_pack_heal", run_archive_pack_heal);
    ("archive_digest_lookup", run_archive_digest_lookup);
    ("archive_epoch_import", run_archive_epoch_import);
    ("store_key_order", run_store_key_order);
    ("store_full_memory", run_store_full_memory);
    ("archive_hash_index", run_archive_hash_index);
    ("backend_writer_thread", run_backend_writer_thread);
    ("backend_env_split", run_backend_env_split);
    ("store_notify_visibility", run_store_notify_visibility);
    ("peer_prune_fairness", run_peer_prune_fairness);
    ("peer_temp_ban", run_peer_temp_ban);
    ("rpc_codec_size", run_rpc_codec_size);
    ("stream_inbound_quota", run_stream_inbound_quota);
    ("stream_sync_capability", run_stream_sync_capability);
  ]

let () =
  Alcotest.run "topos-laws"
    [
      ( "laws-on-real-frames",
        List.map
          (fun (name, run) ->
            Alcotest.test_case name `Quick (check_model name run))
          runs );
      ( "non-degeneracy",
        [
          Alcotest.test_case "69-models" `Quick (fun () ->
              Alcotest.(check int) "models covered" 69 (List.length runs));
          Alcotest.test_case "K-nontrivial-somewhere" `Quick
            (k_nontrivial_somewhere runs);
        ] );
    ]
