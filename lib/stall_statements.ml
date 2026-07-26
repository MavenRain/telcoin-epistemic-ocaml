(** The stalled-commit / timeout-fetch statement family over the
    {!Stall_model} interpreted system (DESIGN family CONSENSUS-EXT #14).
    Mined from telcoin-network, adversarially verified against the code
    (grounding) and against the finite-model semantics (encodability), and
    stated in the form that survived both skeptics. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide: [K (V2, _)] is grounded in the victim's local state (its
    dag / certificate store, its pending fetch targets, and its committed
    flag) - {!Stall_model.Checker} evaluates it by indistinguishability of
    that view over all reachable global states. [V2] is the ONLY knowledge
    agent of this family; the cooperative peers [V0], [V1], [V3] carry the
    constant empty view and so never appear under [K]. The epistemically
    strict content is that a TOTALLY starved validator's local state at the
    end of the withheld [Deliver R1] is bit-identical to its state before
    any certificate formed, so the round-R1 quorum's existence is genuinely
    unknowable to it - and stays so, because the timeout Kick fetches
    nothing for a validator with no pending target
    (certificate_fetcher.rs:184); possession recovery through the fetch is
    claimed exactly where the real gate passes: the lagged flavor whose
    received forward-reference certificate populated its targets. *)

open Stall_model

(** A statement over the stall model: name, bucket (the shared vocabulary
    from {!Statements}), formula, and the reachability witness required by
    [prove_nonvacuous] - the proof is refused if the antecedent never holds,
    so no statement is certified on the strength of a false antecedent. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S14 - stalled-commit-timeout-fetch-gated-by-pending-targets
    [liveness]. The commit-timeout certificate fetch is honest about its
    pending-targets gate, in both directions.

    Ignorance direction: a validator stalled at commit evaluation - phase
    past [Commit_eval] with its own consensus uncommitted (the stall the
    commit-progress timer detects,
    crates/consensus/primary/src/state_sync/gc.rs) - that was TOTALLY
    starved (no R1 certificate in its dag) and holds NO pending fetch
    target never learns that the round-R1 certificate quorum exists:
    G(stalled_v2 /\ starved_v2 /\ cert_quorum_exists(R1)
      /\ ~has_fetch_targets_v2 -> ~K_v2 cert_quorum_exists(R1)).
    Ground: the gc timeout ([GarbageCollector::ready] ->
    [process_max_round_timeout], gc.rs:51) only sends
    [CertificateFetcherCommand::Kick], and the Kick arm fetches nothing
    unless the targets map is non-empty (certificate_fetcher.rs:184);
    targets are populated ONLY at certificate_fetcher.rs:212 in the
    [Ancestors] branch, whose only senders both require receiving a
    certificate (cert_manager.rs:169-175 missing parents,
    cert_validator.rs:203 too-new) - a totally starved validator receives
    none, and round-1 certificates short-circuit on genesis parents
    (cert_manager.rs:144-153).

    Recovery direction: a stalled validator WITH a pending fetch target -
    it received a forward-reference R2 certificate whose missing R1
    parents parked it pending and populated the targets map - provably
    regains possession of the R1 quorum:
    G(stalled_v2 /\ cert_quorum_exists(R1) /\ has_fetch_targets_v2
      -> AF own_quorum(v2,R1)).
    The tick fires, the gate passes, and the bounded fetch
    (certificate_fetcher.rs:241-256, :259-286) pulls the withheld quorum
    certificates from peers into the victim's own dag, releasing the
    pending certificate. cert_quorum_exists(R1) := at least 2f+1 = 3
    distinct R1 certificates in the UNION of all validators' dags;
    stalled_v2 := phase >= Commit_eval and V2 uncommitted. Knowledge of
    quorum EXISTENCE is deliberately NOT claimed here: the pending R2
    certificate is in the victim's view and its formation entails an R1
    quorum, so that knowledge predates the fetch - possession is what the
    fetch restores.

    Non-vacuity: the antecedent conjoins EF of each clause's trigger, so
    the proof is refused unless the total-starvation states AND the lagged
    pending-target states are both reachable. The ignorance clause's [~K]
    is genuine: the starved victim's view (empty dag, empty pending,
    uncommitted) collides with the end-[Vote R1] states where no
    certificate has entered any dag, so the operand is false inside the
    same view class; and the operand does not collapse to falsehood - [K]
    holds at the [Deliver_all] post-delivery states. Mutation pin:
    {!Stall_model.No_timeout_fetch} deletes the gc tick arm - the lagged
    victim's pending target is never served (fetch-on-vote suppressed, no
    force-repair), so AF own_quorum(v2,R1) fails and the recovery clause
    refutes; the ignorance clause is unaffected. *)
let s14 =
  {
    name = "stalled-commit-timeout-fetch-gated-by-pending-targets";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        ( Formula.Ag
            (Formula.Implies
               ( Formula.And
                   ( atom Stalled_v2,
                     Formula.And
                       ( atom V2_starved,
                         Formula.And
                           ( atom Cert_quorum_r1,
                             Formula.Not (atom V2_has_fetch_targets) ) ) ),
                 Formula.Not (Formula.K (Validator.V2, atom Cert_quorum_r1))
               )),
          Formula.Ag
            (Formula.Implies
               ( Formula.And
                   ( atom Stalled_v2,
                     Formula.And
                       (atom Cert_quorum_r1, atom V2_has_fetch_targets) ),
                 Formula.Af (atom V2_holds_r1_quorum) )) );
    antecedent =
      Formula.And
        ( Formula.Ef
            (Formula.And
               ( atom Stalled_v2,
                 Formula.And
                   ( atom V2_starved,
                     Formula.And
                       ( atom Cert_quorum_r1,
                         Formula.Not (atom V2_has_fetch_targets) ) ) )),
          Formula.Ef
            (Formula.And
               ( atom Stalled_v2,
                 Formula.And (atom Cert_quorum_r1, atom V2_has_fetch_targets)
               )) );
  }

(** All statements of this family: exactly S14. *)
let all = [ s14 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure
    degrades to [proved = false] rows rather than an exception. *)
let reports () =
  let row proved st =
    { Report.name = st.name; bucket = st.bucket; proved }
  in
  Result.fold
    ~ok:(fun sys ->
      List.map
        (fun (st, r) ->
          row (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false) r) st)
        (prove_all sys))
    ~error:(fun Checker.Empty_init -> List.map (row false) all)
    (make ())
