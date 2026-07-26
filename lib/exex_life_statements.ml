(** The EXEX_LIFE statement family, encoded over the {!Exex_life_model}
    interpreted system. All three statements were mined from telcoin-network,
    re-grounded against the working tree at HEAD 0c59c15b, and stated here in
    the form that survived both the grounding skeptic and the finite-model
    encodability skeptic. They share one model because they share one subject:
    the ExEx notification surface of a single consensus-following host - the two
    [notify_exex_*] producers (consensus_bus.rs:582-608), the two epoch/committee
    gates that feed them, and the spawn policy of the task that consumes them.

    Reading guide for the K operands:
    - [K (V1, _)] targets [net], the highest epoch in which a quorum EXCLUDING
      V1 committed, and [Cert_quorum_genuine], whether 2f+1 real members of the
      epoch-(E+2) committee signed a gossiped header. Neither is a function of
      V1's view ([ep], [out], [cert_trace], [exex]) and neither is rigid: [net]
      ranges over three values on the reachable set, and the genuine/forged
      discriminator collapses to a single observable trace exactly when
      [get_committee] returns [None].
    - [K (V2, _)] targets [Exex_task_stopped], V1's own extension task having
      resolved. V2's view is ([net], responding/silent), which holds no component
      of V1's ExEx state - [TnExExContext] carries no network handle and the
      [TnExExManagerHandle] reverse channel is dropped unread (context.rs:12-39,
      node.rs:964-974).

    Two conjuncts that the mining cards asked for were DROPPED rather than
    manufactured. S1's card asserted a [leads_to] re-delivery of the withheld
    output on the grounds that [last_consensus_height] never advances past it;
    that mechanism is wrong (state-sync/src/lib.rs:326 hands the WITHHELD header
    back as the new [from] and the caller at :231-233 then terminates the whole
    streaming task), and the real re-delivery is an indirection through the next
    epoch's freshly spawned task, so the card's claim became the [t_out] enabling
    condition instead. S2's card asserted [leads_to (unevaluable,
    committee_known)]; nothing in the code guarantees the epoch record ever syncs
    ([get_committee]'s DB branch is best-effort), so asserting inevitability
    would be manufactured liveness under R8. S2 gained both polarities of the
    ignorance claim in exchange, which is strictly stronger.

    POST-REVIEW REWORK (adversarial round, finding D7 against S1 conjunct C).
    The original conjunct C - AG( (net_reached(E+2) /\\ ~host_epoch=E+1) ->
    ~K_V1(net_reached(E+2)) ) - was true only because the model hardwired away
    [get_committee]'s third source: the epoch-record fallback
    [record_by_epoch(E+1).next_committee] (handler.rs:215-223,
    storage/src/epoch_records.rs:354-367) answers for epoch E+2 with NO epoch
    advance, and the node-scoped record collector deliberately fetches past the
    node's own epoch (node.rs:888-895, state-sync/src/epoch.rs:46-150). That
    branch is now in the model, so a verified epoch-(E+2) certificate is
    reachable at [ep = Ep_e] and it does tell V1 the lead. Conjunct C was
    therefore WEAKENED with the [~exex_cert_signal] guard and the statement
    renamed with the [-until-a-cert-verifies] suffix. Conjuncts A and B are
    unchanged and were untouched by the finding. A second confirmed finding was
    documentation-only: the sibling-hunt prose claiming the ExEx's read-only
    [ConsensusChain] is a closed back-door is false, and is corrected in
    {!Exex_life_model} under MODELLING SCOPE - the atoms are notifications, never
    database contents. *)

open Exex_life_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a false antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 -
    exex-output-window-is-a-lower-bound-that-hides-a-two-epoch-network-lead-until-a-cert-verifies
    [safety]. The ExEx output stream is a certified LOWER bound on network
    progress that never outruns its host - and precisely because it is only a
    lower bound, it cannot itself reveal a two-epoch lead; the one thing that
    can is a certificate that verified against a collected epoch record.

    (A) THE WINDOW: the ExEx is never handed a [ConsensusOutput] whose sub-DAG
    leader epoch exceeds the epoch its host has entered -
    AG( exex_output(E+1) -> host_epoch=E+1 ). Grounding: [handle_sync_output]
    no-ops when [consensus_output.sub_dag().leader_epoch() >
    self.inner.committee.epoch()] (subscriber.rs:143-147), one line before the
    sole [notify_exex_consensus_output] call site (subscriber.rs:175); and the
    state-sync forward drain returns before its single
    [sync_output().send(output)] under the identical predicate
    (state-sync/src/lib.rs:324-327 then :380), whose caller re-tests the returned
    header and terminates the epoch-scoped task (state-sync/src/lib.rs:231-233).

    (B) THE POSITIVE KNOWLEDGE: being handed epoch-(E+1) output lets the host
    conclude that a quorum elsewhere committed in epoch E+1 -
    AG( exex_output(E+1) -> K_V1( net_reached(E+1) ) ). Grounding: the output
    arrives complete and already verified by state-sync before the send
    (state-sync/src/lib.rs:300-303 resolves it from the verified sync cache or a
    local pack, :378-380 sends it), and the host only enters epoch E+1 by reading
    the committee and [epoch_start] back out of the executed canonical tip
    ([configure_consensus], start_epoch.rs:238-266). This K is NOT collapsed:
    [net] is absent from V1's view, and [net_reached(E+1)] is false at the
    initial state, so the knowledge is contingent (test [k-v1-net-e1-contingent])
    and the operative view class is non-singleton (test
    [s1-b-class-non-singleton]: the worlds (Ep_e1, Net_e1, Out_e1, Cert_none,
    Exex_live) and (Ep_e1, Net_e2, Out_e1, Cert_none, Exex_live) share
    View_v1 (Ep_e1, Out_e1, Tr_none, Exex_live)).

    (C) THE IGNORANCE, GUARDED BY THE CERTIFICATE SIGNAL: while the host is
    still configured at epoch E AND no epoch-(E+2) certificate has verified, it
    cannot know that the network already reached E+2 -
    AG( (net_reached(E+2) /\\ ~host_epoch=E+1 /\\ ~exex_cert_signal)
        -> ~K_V1( net_reached(E+2) ) ),
    equivalently AG( (net_reached(E+2) /\\ ~host_epoch=E+1
    /\\ K_V1(net_reached(E+2))) -> exex_cert_signal ): the verified-certificate
    notification is the ONLY channel through which a still-lagging host learns of
    a two-epoch lead.

    WHY THE GUARD (the unguarded form was false of the Rust, and this is the
    repair). [get_committee]'s third branch is
    [self.consensus_chain.epochs().get_committee_keys(epoch)]
    (handler.rs:215-223), which answers for epoch E+2 out of
    [record_by_epoch(E+1).next_committee]
    (storage/src/epoch_records.rs:354-367). The node-scoped
    [spawn_epoch_record_collector] (node.rs:888-895) back-fills epoch records
    from epoch 0 and deliberately runs PAST the node's own latest epoch
    (state-sync/src/epoch.rs:46-150), while [ConsensusConfig]'s epoch advances
    only by executing the epoch-closing block (start_epoch.rs:238-266). So an
    epoch-(E+2) certificate can verify at [committee.epoch() = E] with no epoch
    advance at all; a lone forger cannot produce that trace ([verify_cert] fails,
    handler.rs:278), so the verified class is genuine-only and V1 DOES then know
    the lead. That branch is now MODELED
    ([Exex_life_model.epoch_record_committee_available], the epoch-record branch
    of [t_cert_arrive], the relaxed guard of [t_cert_regossip]) and the leak it
    creates is asserted reachable by test [s1-c-verified-cert-leaks-the-lead].
    Conjunct C is stated only outside it.

    The remaining ignorance is real, over three routes: (i) the output stream is
    shut by the very gate of conjunct A; (ii) an unevaluable certificate yields
    only a warn-and-drop that a lone forger reproduces byte for byte
    (handler.rs:280-286); (iii) the REJECTED trace of a forgery checked against a
    record-derived key set is reachable both with and without an epoch-(E+2)
    commit, because the epoch-(E+1) record exists as soon as epoch E+1 CLOSES.
    R3 collisions: (Ep_e, Net_e2, Out_e, Cert_unknown_genuine, Exex_live) with
    (Ep_e, Net_e, Out_e, Cert_unknown_forged, Exex_live), sharing
    View_v1 (Ep_e, Out_e, Tr_dropped, Exex_live); and
    (Ep_e, Net_e2, Out_e, Cert_invalid_forged, Exex_live) with
    (Ep_e, Net_e1, Out_e, Cert_invalid_forged, Exex_live), sharing
    View_v1 (Ep_e, Out_e, Tr_invalid, Exex_live).

    Mutation pin: {!Exex_life_model.No_epoch_window} deletes all three copies of
    the [leader_epoch() > epoch] bail, adding (Ep_e, Net_e1, Out_e, _, _) ->
    (Ep_e, Net_e1, Out_e1, _, _), so conjunct A fails at an ExEx handed
    next-epoch output by a host that has not entered that epoch. Conjuncts B and
    C survive the mutation - every [out = Out_e1] class member still has
    [net >= Net_e1], and the (Ep_e, Out_e1) classes still contain a [Net_e1]
    world for each of the traces Tr_none, Tr_dropped and Tr_invalid - so the
    refutation is cleanly attributable to A. *)
let s1 =
  let window =
    Formula.Ag (Formula.Implies (atom Exex_output_e1, atom Host_epoch_e1))
  in
  let delivery_certifies_lower_bound =
    Formula.Ag
      (Formula.Implies
         (atom Exex_output_e1, Formula.K (Validator.V1, atom Net_reached_e1)))
  in
  let still_lagging_and_no_cert_signal =
    Formula.And
      ( atom Net_reached_e2,
        Formula.And
          ( Formula.Not (atom Host_epoch_e1),
            Formula.Not (atom Exex_cert_signal) ) )
  in
  let two_epoch_lead_hidden =
    Formula.Ag
      (Formula.Implies
         ( still_lagging_and_no_cert_signal,
           Formula.Not (Formula.K (Validator.V1, atom Net_reached_e2)) ))
  in
  {
    name =
      "exex-output-window-is-a-lower-bound-that-hides-a-two-epoch-network-lead-until-a-cert-verifies";
    bucket = Statements.Safety;
    formula =
      Formula.And
        (window, Formula.And (delivery_certifies_lower_bound, two_epoch_lead_hidden));
    antecedent = still_lagging_and_no_cert_signal;
  }

(** S2 - unknown-committee-blocks-the-exex-certificate-signal-and-leaves-
    genuineness-unknown [security]. When a gossiped certificate names an epoch
    the host holds no committee for, [get_committee] returns [None], the handler
    takes the else arm and drops it: no [CertificateAccepted] notification ever
    reaches any installed ExEx, and the host can neither confirm nor rule out
    that 2f+1 real members of that epoch's committee signed it.

    (A) NO SIGNAL: AG( cert_unverifiable -> ~exex_cert_signal ). Grounding: the
    [if let Some(committee) = self.get_committee(epoch).await] gate
    (handler.rs:251) wraps [verify_cert], the state-sync hand-off
    (handler.rs:259), the inactive-CVV storage write (handler.rs:261-268) and
    [notify_exex_certificate] (handler.rs:274-276); the else arm only warns
    (handler.rs:280-286). [notify_exex_certificate] (consensus_bus.rs:593-600) is
    the SOLE producer of [TnExExNotification::CertificateAccepted] and has
    exactly ONE call site.

    (B) CANNOT CONFIRM: AG( cert_unverifiable -> ~K_V1( cert_quorum_genuine ) ).
    Grounding: [get_committee] answers [Some] only from the current committee,
    [next_committee_keys], or an epoch record (handler.rs:215-223), and
    [Certificate::validate_received] merely re-arms
    [SignatureVerificationState::Unverified] without checking anything
    (types/src/primary/certificate.rs:294-301) - with no key set the aggregate
    signature is simply not evaluable.

    (C) CANNOT RULE OUT: AG( cert_unverifiable ->
    ~K_V1( ~cert_quorum_genuine ) ). The drop is not a verdict; the handler's own
    comment says so ("it's bogus or we are catching up", handler.rs:280-286).

    R3 witness for both (B) and (C): (Ep_e, Net_e2, Out_e, Cert_unknown_genuine,
    Exex_live) - the real epoch-(E+2) committee certified a header and it was
    gossiped to V1 - and (Ep_e, Net_e, Out_e, Cert_unknown_forged, Exex_live) -
    Byzantine V0 alone fabricated a certificate carrying the same epoch field.
    Both project to View_v1 (Ep_e, Out_e, Tr_dropped, Exex_live), the identical
    warn-and-drop trace, and they disagree on [cert_quorum_genuine].

    Mutation pin: {!Exex_life_model.No_committee_gate} deletes the Option gate,
    so an unevaluable certificate is forwarded to the ExEx: on the [ep = Ep_e]
    arrival branch [Cert_unknown_*] is replaced by [Cert_leaked_*], where
    [cert_unverifiable] and [exex_cert_signal] hold together and conjunct A
    fails. Conjuncts B and C survive - V1 still holds no key set, and the
    [Tr_leaked] class still contains both a genuine and a forged world - so the
    refutation is cleanly attributable to A. *)
let s2 =
  let no_signal =
    Formula.Ag
      (Formula.Implies (atom Cert_unverifiable, Formula.Not (atom Exex_cert_signal)))
  in
  let cannot_confirm =
    Formula.Ag
      (Formula.Implies
         ( atom Cert_unverifiable,
           Formula.Not (Formula.K (Validator.V1, atom Cert_quorum_genuine)) ))
  in
  let cannot_rule_out =
    Formula.Ag
      (Formula.Implies
         ( atom Cert_unverifiable,
           Formula.Not
             (Formula.K (Validator.V1, Formula.Not (atom Cert_quorum_genuine))) ))
  in
  {
    name =
      "unknown-committee-blocks-the-exex-certificate-signal-and-leaves-genuineness-unknown";
    bucket = Statements.Security;
    formula = Formula.And (no_signal, Formula.And (cannot_confirm, cannot_rule_out));
    antecedent = atom Cert_unverifiable;
  }

(** S3 - isolated-exex-failure-never-halts-the-host-and-is-internode-opaque
    [liveness]. With the shipped default [exex_critical = false], an ExEx that
    panics, errors or simply finishes can never stop its host from following
    consensus across the epoch boundary, and no other validator can learn that it
    happened.

    (A) PARTICIPATION PRESERVED: leads_to( exex_task_stopped, host_epoch=E+1 ),
    i.e. AG( exex_task_stopped -> AF host_epoch=E+1 ). Grounding: the default
    branch spawns the ExEx with the NON-critical
    [spawner.spawn_task(label, run_isolated_exex_future(label, exex_fut))]
    (node.rs:953-957, manager copy at node.rs:982-989), and
    [run_isolated_exex_future] [catch_unwind]s and always resolves [Ok(())]
    (manager/exex.rs:15-36); independently of that, the task manager [continue]s
    over ANY non-critical task result - [Ok], [Err] or join error
    ([if !info.critical { continue }], task_manager.rs:459-461 and :470-472). So
    the host keeps running [t_ep] and crosses the boundary
    (start_epoch.rs:238-266). The [AF] is honest here: the reachable graph is a
    finite DAG and every pristine terminal has [ep = Ep_e1], because a running
    host with [ep = Ep_e] always has [t_net] or [t_ep] enabled.

    (B) INTERNODE OPACITY: AG( ~K_V2( exex_task_stopped ) ) - no committee peer
    can ever learn that V1's ExEx died. Grounding: the ExEx's only outward
    channel is [TnExExEvent::FinishedHeight] into a watch whose
    [TnExExManagerHandle] is intentionally dropped unread (node.rs:964-974), and
    [TnExExContext] holds only read-only reth and consensus handles with private
    fields, precisely so third-party code cannot back-pressure the manager
    (context.rs:12-39). R3 witness: (Ep_e, Net_e, Out_e, Cert_none,
    Exex_dead_isolated) and (Ep_e, Net_e, Out_e, Cert_none, Exex_live) share
    View_v2 (Net_e, Responding) and disagree on [exex_task_stopped]. That
    collision exists at EVERY reachable state - [exex] is a free factor over
    {Exex_live, Exex_dead_isolated} because [node_up] holds for both - which is
    why conjunct B is an unconditional AG.

    Note on the retarget: "V1 still participates" cannot be stated as
    byte-identical certificates or votes, because a node on the ExEx delivery
    path is by construction NOT an active CVV (handler.rs:274 gates
    [notify_exex_certificate] on [!is_active_cvv], subscriber.rs:169-174 says the
    active path deliberately omits ExEx delivery), so V1 publishes no
    [ConsensusResult] a peer could compare. Participation is therefore stated as
    "the host still crosses the epoch boundary".

    Mutation pin: {!Exex_life_model.Spawn_exex_critical} always takes the
    [spawn_critical_task] arm, so [t_exex_stop] lands in [Exex_dead_fatal] and
    every V1-local transition is removed while [t_net] keeps running. The path
    initial -> (Ep_e, Net_e, Out_e, Cert_none, Exex_dead_fatal) -> Net_e1 ->
    Net_e2 ends in a stutter-closed terminal with [ep = Ep_e], refuting conjunct
    A; and every ([net], Silent) class member has [exex = Exex_dead_fatal],
    making [K_V2 (exex_task_stopped)] true and refuting conjunct B as well. Both
    halves flip for the same reason - a critical ExEx is no longer isolated. *)
let s3 =
  let participation_preserved =
    Formula.leads_to (atom Exex_task_stopped) (atom Host_epoch_e1)
  in
  let internode_opacity =
    Formula.Ag
      (Formula.Not (Formula.K (Validator.V2, atom Exex_task_stopped)))
  in
  {
    name = "isolated-exex-failure-never-halts-the-host-and-is-internode-opaque";
    bucket = Statements.Liveness;
    formula = Formula.And (participation_preserved, internode_opacity);
    antecedent = atom Exex_task_stopped;
  }

(** The family's statements: the output window (safety), the committee gate
    (security) and the isolated-ExEx spawn policy (liveness). *)
let all = [ s1; s2; s3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure degrades
    every row to [proved = false] rather than raising. *)
let reports () =
  let row proved st = { Report.name = st.name; bucket = st.bucket; proved } in
  Result.fold
    ~ok:(fun sys ->
      List.map
        (fun (st, r) ->
          row (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false) r) st)
        (prove_all sys))
    ~error:(fun Checker.Empty_init -> List.map (row false) all)
    (make ())
