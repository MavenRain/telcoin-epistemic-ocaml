(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    ROUND_WEIGHT_CAP family. Each row asserts the proof FLIPS to an error on
    the mutated model, paired with the matching positive half on the pristine
    one.

    - {!Round_weight_cap_model.No_distinct_origin_guard} deletes
      aggregators/certificates.rs:83-85
      ([if !self.authorities_seen.insert(origin.clone()) { return None; }]), so
      a duplicate certificate for an already-counted origin falls through to
      the accumulation at :88-89 and adds a second unit of voting power. S1
      conjunct (A) - the cap itself - fails at the first duplicate, and S3
      conjunct (A) - the containment of an equivocating identity - fails
      because the node then reaches the :92 threshold with only two distinct
      origins appended.

      SIBLING HUNT. The digest dedup at cert_validator.rs:93-98 catches exact
      retransmissions only, and the catch-up ingress bypasses it entirely
      ([process_fetched_certificates_in_parallel] :235-243 ->
      [forward_verified_certs] :133, with neither [verify_collection] :246-268
      nor [classify_certificates_for_verification] :272-296 reading the
      certificate store); two equivocating headers are two distinct digests, so
      it could not see them in any case.
      [CertificateManager::process_verified_certificates]
      (cert_manager.rs:74-135) checks verification, pending status and missing
      parents, never [(round, origin)] uniqueness, and
      [accept_verified_certificates] (:189-220) calls [append_certificate]
      unconditionally at :205-211. [save_cert]
      (storage/src/stores/certificate_store.rs:128-147) OVERWRITES the
      [(round, origin)] index at :137-138 instead of flagging a conflict.
      [append_certificate] (certificates.rs:24-44) has no error arm but the
      channel send. The proposer never re-derives distinctness
      (proposer.rs:384-467, :338-365, :751). [DagError::AuthorityReuse] is
      raised only by the VOTE aggregator (votes.rs:42-45), a different
      aggregator on a different message type. The ONE real repair - the remote
      voters' [DuplicateParents] / [Inquorate] re-check at handler.rs:700,
      :725-728, :730, :733-738 - is MODELLED as the [header] field and stays
      LIVE under this mutation; it repairs the network-visible effect one round
      later on somebody else's machine and does not touch the local emission
      event these conjuncts are about, which is exactly why S1 conjunct (C)
      still proves while conjunct (A) dies. PINS S1 and S3.
    - {!Round_weight_cap_model.No_quorum_threshold_gate} deletes
      aggregators/certificates.rs:91-92
      ([if self.weight >= committee.quorum_threshold()]), so every successful
      append returns [Some(parents)] and the manager forwards a
      one-certificate parent batch to the proposer (:39-41). S2 conjunct (A)
      dies: the node emits with a single distinct origin appended, at which
      point its view class contains worlds where the supermajority is not yet
      certified.

      SIBLING HUNT. Nothing on the emitting node re-derives the round quorum:
      [process_parents] (proposer.rs:384-467) only warns on a round mismatch
      (:385-390) and extends [last_parents] (:447); [ready] (:374-379)
      delegates to [update_leader] (:319-327) or [enough_votes] (:338-365),
      which tallies stake over [last_parents] purely to set [advance_round] and
      applies no distinctness or round-quorum test; and the propose gate is the
      bare [let enough_parents = !self.last_parents.is_empty();] (:751). The
      remote voters DO reject the resulting inquorate header
      (handler.rs:733-738); that repair is modelled and stays live, and again
      it does not touch the local emission event. PINS S2.

    NOTE, so it is never mistaken for a further pin: S2 conjunct (A) and S3
    conjunct (A) BOTH also die under the other mutation. That is the intended
    reading rather than an accident - the inference from "my aggregator fired"
    to "2f+1 distinct members are certified" needs the distinctness guard AND
    the threshold comparison, and either deletion breaks it. Every antecedent
    of this family stays reachable under both mutations, so no flip here is a
    masked [Vacuous_antecedent]; each mutated verdict was checked to be
    [Refuted], and conjunct by conjunct only the ones named above change. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Round_weight_cap_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Round_weight_cap_model.Checker.make (Round_weight_cap_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Round_weight_cap_statements.name name))
    Round_weight_cap_statements.all

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
               (Round_weight_cap_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Round_weight_cap_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Round_weight_cap_statements.prove sys st)))

(** The mutated model must keep the statement's antecedent reachable, so a
    flip is a genuine refutation and never a masked [Vacuous_antecedent]. *)
let antecedent_still_reachable mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " keeps a reachable antecedent under the mutation")
            true
            (Round_weight_cap_model.Checker.satisfiable sys
               st.Round_weight_cap_statements.antecedent))

(** A pristine-proves plus mutated-refutes pair for one statement, with the
    non-vacuity row that makes the refutation attributable. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":antecedent-live") `Quick
      (antecedent_still_reachable mut name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "round_weight_cap_mutation"
    [
      ( "dropped distinctness guard inflates the round weight",
        pin Round_weight_cap_model.No_distinct_origin_guard
          "per-origin-round-weight-cap-is-exactly-one" );
      ( "dropped distinctness guard lets an equivocation be the marginal vote",
        pin Round_weight_cap_model.No_distinct_origin_guard
          "equivocating-origin-drop-is-silent-and-unattributable" );
      ( "dropped threshold gate emits on a single certificate",
        pin Round_weight_cap_model.No_quorum_threshold_gate
          "round-quorum-emission-implies-known-distinct-supermajority" );
    ]
