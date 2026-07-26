(** The full 21-statement report: the original seven statements over
    {!Tn_model} plus the fourteen expansion statements, each proved over its
    own lean isolated family model (see the family modules). Theorems over
    different State/View types cannot share a list, so the aggregation is the
    flat {!Report.t} projection; the per-family suites carry the actual
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

(** All 21 reports: the seven originals followed by the fourteen expansion
    statements in DESIGN-spec family order (ban, admission, gossip-auth,
    exec-tally, identity, then the consensus-ext and request-response
    families). Each family call builds and checks its own model. *)
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
    ]
