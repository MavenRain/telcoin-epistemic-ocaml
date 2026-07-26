(** The ahead-certificate round catch-up statement family, encoded over the
    {!Catchup_model} interpreted system (DESIGN family CONSENSUS-EXT #13).
    Mined from telcoin-network, adversarially verified against the code
    (grounding) and against the finite-model semantics (encodability), and
    stated here in the refined form that survived both skeptics. File
    citations refer to Telcoin-Association/telcoin-network.

    Reading guide: this family is PURE TEMPORAL LIVENESS - no [K]. An
    earlier draft wrapped quorum progress ("some honest pair holds every
    formed sub-R2 certificate") in [K (V2, _)], but that knowledge is
    degenerate exactly where the implication is live: the antecedent holds
    at one reachable state only, whose V2 view class is a singleton, and
    the operand is entailed by V2's own holdings anyway - a well-signed R2
    certificate is transferable evidence of a 2f+1 quorum that could not
    have formed without every parent round (signature verification precedes
    forwarding, cert_validator.rs:103-108 and 114-128; vote handlers block
    on parent possession, network/handler.rs; acceptance requires parents
    in storage, state_sync/cert_manager.rs:103-120) - so [K] collapsed to
    view-derivable truth and was dropped. What survives is the operational
    consequence telcoin-network actually implements:
    [forward_verified_certs] sends [(vec![], r - 1)] as
    [minimal_round_for_parents] (cert_validator.rs:133-158, the send at
    157-158) and [Proposer::process_parents] jumps [self.round] forward on
    its Greater arm (proposer.rs:384-426, entry 704), so a lagging proposer
    stops emitting obsolete headers. *)

open Catchup_model

(** A statement over this family's atom vocabulary; [bucket] reuses the
    shared vocabulary of the frozen {!Statements} module, [antecedent] is the
    reachability witness [prove_nonvacuous] requires - the proof is refused
    if it never holds, so the statement is never certified on the strength of
    a false antecedent. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** The antecedent of S13, matching
    [forward_verified_certs] firing only on ahead certificates
    (cert_validator.rs:133-158): the lag victim V2 holds SOME round-R2
    certificate ([disj] over the R2 digests) while its own proposer round is
    still at or below R0 ([Proposer_round_le]) - the genuinely AHEAD case, a
    validator that verified an ahead certificate without having proposed past
    R0. Reachable only in the [Lag_v2] branch at the [Catch_up] micro-phase,
    after the forced [Deliver R2] repair delivers the R2 certificates but
    before the round jump (proposer.rs:642-652) - see the module header of
    {!Catchup_model} for why the micro-phase must be its own step. *)
let catch_up_antecedent =
  let r2_digests = List.map (fun v -> { author = v; round = R2 }) Validator.all in
  Formula.And
    ( Formula.disj (List.map (fun d -> atom (In_dag (victim, d))) r2_digests),
      atom (Proposer_round_le (victim, R0)) )

(** S13 - ahead-certificate-implies-round-catchup [liveness]. A lagging
    proposer's possession of an ahead (round-R2) certificate drags its own
    proposer round forward so obsolete proposals stop:
    catch_up_antecedent ~> Proposer_round_ge(V2, R1). The [Catch_up]
    micro-phase (the model analog of the [minimal_round_for_parents] send,
    cert_validator.rs:157-158, consumed by [Proposer::process_parents]'
    Greater arm, proposer.rs:384-426) jumps V2's proposer round to
    R2 - 1 = R1.

    The original candidate's "known-quorum-progress" AG conjunct -
    AG(catch_up_antecedent -> K_V2(some honest pair holds every formed
    sub-R2 certificate)) - is DROPPED as epistemically degenerate: the
    antecedent holds at exactly one reachable state ([Lag_v2], [Catch_up],
    V2 view = all ten certificates at proposer round R0), whose V2 view
    class is a singleton, and the operand is entailed by V2's own R2
    holding (a well-signed certificate cannot form without a 2f+1 = 3
    signer quorum, at least f+1 = 2 honest, that processed every parent
    round - the vote parent gate in network/handler.rs and the
    parents-in-storage acceptance rule, state_sync/cert_manager.rs:103-120),
    so K_V2 there is bare truth. This is the same i-local collapse that
    already dropped the r = 0 and r = 1 instances: an R0 prefix operand is
    rigidly true and an R1 operand is entailed by any post-[Deliver R0]
    local view (every formed certificate is broadcast-delivered in one
    phase).

    Mutation pin: {!Catchup_model.Drop_catch_up} deletes the [Catch_up] jump
    (analog of deleting the cert_validator.rs:157-158 send). No sibling path
    repairs it - the only other proposer-round writer is [propose], which in
    the [Lag_v2] branch never lists V2 after R0 and never runs again after
    [Deliver R2] (in the real system the only other parents sender is the
    certificate aggregator, aggregators/certificates.rs, needing a 2f+1
    same-round quorum the starved node cannot assemble) - so the terminal
    [Done] state is reached with [Proposer_round_le (V2, R0)] still true while
    V2 holds an R2 certificate, and the leads-to - now the whole statement -
    is refuted. *)
let s13 =
  {
    name = "ahead-certificate-implies-round-catchup";
    bucket = Statements.Liveness;
    formula =
      Formula.leads_to catch_up_antecedent
        (atom (Proposer_round_ge (victim, R1)));
    antecedent = catch_up_antecedent;
  }

(** The family's statements: exactly S13. *)
let all = [ s13 ]

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
