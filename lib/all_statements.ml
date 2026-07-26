(** The full 63-statement report: the original seven statements over
    {!Tn_model}, the fourteen first-expansion statements, and the forty-two
    second-expansion statements, each proved over its own lean isolated family
    model (see the family modules). Theorems over different State/View types
    cannot share a list, so the aggregation is the flat {!Report.t} projection;
    the per-family suites carry the actual kernel theorems and mutation pins. *)

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

(** All 63 reports: the seven originals, then the fourteen first-expansion
    statements in DESIGN-spec family order (ban, admission, gossip-auth,
    exec-tally, identity, then the consensus-ext and request-response
    families), then the forty-two second-expansion statements in family order
    (the four epoch families, then execution, exex, gossip, storage, primary,
    worker and libp2p-discovery). Each family call builds and checks its own
    model. *)
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
    ]
