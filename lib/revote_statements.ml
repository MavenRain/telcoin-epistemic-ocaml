(** The re-vote statement family over the {!Revote_model} interpreted
    system (DESIGN family CONSENSUS-EXT #11). Mined from telcoin-network,
    adversarially verified against the code (grounding) and the
    finite-model semantics (encodability), and stated in the form that
    survived both skeptics. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide: [K (V1, _)] is grounded in V1's local state (its vote
    record, its own dag's certificate possession, its re-vote latch) -
    {!Revote_model.Checker} evaluates it by indistinguishability of that
    view over all reachable global states. The epistemically strict
    content is that a certificate for the slot may exist WITHHELD in the
    Byzantine author's hands: the withhold and skip-aggregate runs are
    honest-view-identical, so a re-voting V1 provably cannot know whether
    the certificate its old vote fed exists. *)

open Revote_model

(** A statement over the re-vote model: name, bucket (the shared
    vocabulary from {!Statements}), formula, and the reachability witness
    required by [prove_nonvacuous] - the proof is refused if the
    antecedent never holds, so no statement is certified on the strength
    of a false antecedent. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S11 - revote-only-under-global-cert-ignorance [security].
    A validator re-votes a conflicting header for an (author, round) slot
    only under GLOBAL certificate ignorance: whenever V1's re-vote latch
    is set, V1 does not know that a certificate for the slot exists -
    AG(revote(V1,V3,R0) -> ~K_V1 cert_exists(V3,R0)) - and yet the
    dangerous co-occurrence is genuinely reachable -
    EF(revote(V1,V3,R0) /\ cert_exists(V3,R0)) - because the Byzantine
    author can aggregate the certificate and withhold it.

    Mechanism: the local cert-evidence guard in [vote_inner]'s
    conflicting-digest branch
    (crates/consensus/primary/src/network/handler.rs:807-847; the
    [cert_exists] store read at handler.rs:824-839 via
    crates/storage/src/stores/certificate_store.rs:219-228) permits the
    re-vote only when the voter's OWN store has no certificate for the
    slot. That check reads purely local state, so it can enforce local
    ignorance only: the withheld-aggregate run
    ({!Revote_model.Aggregate_withhold}) is view-identical to the
    never-aggregated run ({!Revote_model.Skip_aggregate}), which is
    exactly why the AG conjunct holds as a knowledge statement and why
    the EF conjunct is satisfiable. The re-vote path itself presupposes
    the durable [VoteInfo] conflict
    (crates/storage/src/stores/vote_digest_store.rs:15-30, consulted at
    handler.rs:772-786) surviving past the [auth_last_vote] cache
    (handler.rs:510-596). Mutation pin:
    {!Revote_model.No_cert_evidence_guard} deletes the guard, V1 re-votes
    while holding the certificate in its own dag, and the AG conjunct is
    refuted. *)
let s11 =
  {
    name = "revote-only-under-global-cert-ignorance";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( Formula.Ag
            (Formula.Implies
               ( atom Revoted,
                 Formula.Not (Formula.K (Validator.V1, atom Cert_exists)) )),
          Formula.Ef (Formula.And (atom Revoted, atom Cert_exists)) );
    antecedent = Formula.And (atom Revoted, atom Cert_exists);
  }

(** All statements of this family. *)
let all = [ s11 ]

(** Prove one statement on a system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every statement of the family, pairing each with its outcome. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** The uniform cross-model projection for the meta-tests: build the
    pristine system and report per-statement proved flags; a [make] error
    maps every row to [proved = false]. *)
let reports () =
  Result.fold
    ~ok:(fun sys ->
      List.map
        (fun (st, outcome) ->
          {
            Report.name = st.name;
            bucket = st.bucket;
            proved =
              Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false) outcome;
          })
        (prove_all sys))
    ~error:(fun Checker.Empty_init ->
      List.map
        (fun st -> { Report.name = st.name; bucket = st.bucket; proved = false })
        all)
    (make ())
