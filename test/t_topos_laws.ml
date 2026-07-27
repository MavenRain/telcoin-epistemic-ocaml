(** The categorical laws of the topos layer, run on every one of the 27 real
    model frames (DESIGN sec.6 gate 5).

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
          Alcotest.test_case "27-models" `Quick (fun () ->
              Alcotest.(check int) "models covered" 27 (List.length runs));
          Alcotest.test_case "K-nontrivial-somewhere" `Quick
            (k_nontrivial_somewhere runs);
        ] );
    ]
