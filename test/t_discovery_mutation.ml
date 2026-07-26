(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    DISCOVERY family. Four gate deletions, each pinning the statement that rests
    on it and leaving the other two proving, so every refutation is cleanly
    attributable:

    - {!Discovery_model.No_query_max_fold} deletes the strict-max arm of
      [process_kad_query_result] (consensus.rs:1995-1997), adding
      (got_r1=false,res=Q_r0) --recv_r1--> (got_r1=true,res=Q_r0) and its closed
      twin (reachable 35 -> 39): the query statement's [fold_keeps_max] and
      [commit_is_max] both go false there, while its [knows_newer] and
      [currency_unknown] survive. The only recency predicate in the crate,
      [is_newer_record] (consensus.rs:1954-1972), has its ONE call site on the
      PUT route (consensus.rs:1916); nothing on the GET route re-establishes the
      max, so no sibling path repairs the deletion.
    - {!Discovery_model.No_put_freshness_gate} deletes the [is_newer_record]
      conditional (consensus.rs:1916), so the stale relayed record reaches
      [add_self_advertised_peer] -> [cache_known_peer] -> [known_peers.insert]
      and regresses the cache EVEN WHEN THE LOCAL KAD STORE STILL HOLDS A RECORD
      FOR A'S KEY: [no_regression_while_store_fresh] goes false. That
      [St_fresh] half is where the conditional is genuinely load-bearing - on
      the [St_absent] half [is_newer_record] already returns true
      (consensus.rs:1968-1971), so deleting the conditional changes nothing
      there and the pin would be a no-op. Downstream is an unconditional
      overwrite ([KadStore::put] kad.rs:339-379, [AllPeers::upsert_peer]
      all_peers.rs:212-256, [known_peers.insert] manager.rs:868), and
      [peer_record_valid] (consensus.rs:531-565) never inspects the timestamp,
      so nothing repairs it.
    - {!Discovery_model.Penalize_stale_record} deletes the deliberate no-penalty
      carve-out (consensus.rs:1932-1937) and assesses the invalid branch's Fatal
      instead, so in the honest restarted-replicator world
      [attribution_sound] goes false. The [TrustBasis] exemption
      (peer.rs:213-233) that could suppress the penalty is committee/allowlist
      scoped and cannot fire for the modelled non-committee DHT replicator.
    - {!Discovery_model.Px_binds_identity} deletes the BLS-key discard in
      [process_peer_exchange] (manager.rs:624), so ingesting an UNSIGNED
      exchange map confers a binding and [identity_needs_signature] goes false.
      [AllPeers::upsert_peer] performs no validation and
      [eligible_for_discovery] (manager.rs:980-987) screens no provenance, so
      nothing rejects or undoes the unsigned binding.

    Each row asserts the proof FLIPS to an error on the mutated model; the
    pristine rows are the matching positive half. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Discovery_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Discovery_model.Checker.make (Discovery_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Discovery_statements.name name))
    Discovery_statements.all

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " flips to refuted under the mutation")
            false
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Discovery_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Discovery_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Discovery_statements.prove sys st)))

(** The attributability half of a pin: a statement this gate does NOT target
    still proves under the mutation, so the refutation above is not collateral
    damage from a model-wide change. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " still proves under the unrelated mutation")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Discovery_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** Attributability rows: the statements the gate must leave alone. *)
let untouched mut names =
  List.map
    (fun name ->
      Alcotest.test_case (name ^ ":survives") `Quick (survives_under mut name))
    names

(** The kad GET statement. *)
let query_stmt = "kad-query-adopts-max-timestamp-record-yet-currency-stays-unknown"

(** The inbound kad PUT statement. *)
let put_stmt = "stale-replay-regression-is-gated-only-by-the-local-kad-store"

(** The peer-exchange statement. *)
let px_stmt = "peer-exchange-confers-no-identity-and-no-sybil-knowledge"

let () =
  Alcotest.run "discovery_mutation"
    [
      ( "dropped in-query strict-max fold kills max-timestamp adoption",
        pin Discovery_model.No_query_max_fold query_stmt
        @ untouched Discovery_model.No_query_max_fold [ put_stmt; px_stmt ] );
      ( "dropped is_newer_record gate kills store-fresh non-regression",
        pin Discovery_model.No_put_freshness_gate put_stmt
        @ untouched Discovery_model.No_put_freshness_gate
            [ query_stmt; px_stmt ] );
      ( "penalizing a stale republish kills attribution soundness",
        pin Discovery_model.Penalize_stale_record put_stmt
        @ untouched Discovery_model.Penalize_stale_record
            [ query_stmt; px_stmt ] );
      ( "px binding identity kills the signed-record requirement",
        pin Discovery_model.Px_binds_identity px_stmt
        @ untouched Discovery_model.Px_binds_identity [ query_stmt; put_stmt ]
      );
    ]
