(** The UNRESOLVED-AUTHOR statement family (DESIGN family CONSENSUS-EXT #3),
    encoded over the {!Unres_model} interpreted system. Mined from
    telcoin-network, adversarially verified against the code (grounding) and
    against the finite-model semantics (encodability), and stated here in the
    refined form that survived both skeptics. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide: [K (V2, _)] is grounded in V2's local state - its
    attribute-free reject flag, the certificates it holds, its ban set, its
    penalty latch - and {!Unres_model.Checker} evaluates it by
    indistinguishability of that view over all reachable global states. The
    strict epistemic content is that the rejected frame leaves NO attribution
    behind (network-libp2p consensus.rs:1499-1513): the honest-author lag run
    ({!Unres_model.Unres_lag_v1}) and the Byzantine-junk run
    ({!Unres_model.Unres_junk_drop}) are V2-view-identical at every phase from
    the reject through [Done], so a flagged V2 provably cannot know whether the
    rejected author was honest or Byzantine - which is exactly why the
    author_resolved guard (consensus.rs:2094-2095) must SKIP the penalty. *)

open Unres_model

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

(** A statement over the unresolved-author model: name, bucket (the shared
    vocabulary from {!Statements}), formula, and the reachability witness
    required by [prove_nonvacuous] - the proof is refused if the antecedent
    never holds, so no statement is certified on the strength of a false
    antecedent. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** "V2 has banned nobody": the checkable [banned_2 = {}] conjunct, spelled as
    the absence of a ban over the whole committee. In every pristine run this
    holds because the author_resolved guard (consensus.rs:2094-2095) skips the
    Fatal charge; the mutation is precisely what makes a [Banned_2] atom true
    (peers/all_peers.rs:853-873). *)
let no_ban_by_2 =
  Formula.conj
    (List.map (fun v -> Formula.Not (atom (Banned_2 v))) roster)

(** S3 - unresolved-author-reject-skips-penalty-and-liveness-recovers
    [liveness]. A gossip frame whose author cannot be resolved to a committee
    member is rejected by gossip verification (consensus.rs:1499-1513) and
    routed through [RejectReason::penalty] (consensus.rs:2087-2097) via the
    reject-handling path (consensus.rs:1007-1026, 1049-1099); the
    author_resolved guard (consensus.rs:2094-2095) SKIPS the penalty, so an
    unattributable reject charges nobody -
    [G(saw_unres_2 -> (~K_V2(unres_author_honest) /\ ~K_V2(unres_author_byz)
    /\ banned_2 = {} /\ ~penalized_by_2))] - and the dropped honest
    certificate is recovered by the missing-parent fetch at vote time
    (handler.rs:225-230), so liveness survives the reject: [F done].

    The two [~K_V2] conjuncts are the epistemic teeth. The reject flag stores
    no digest, content, or author, so at a flagged state the honest-author lag
    run and the Byzantine-junk run present V2 an identical local view: at a lag
    state [unres_author_honest] is true yet a view-identical junk state makes
    it false (and symmetrically for [unres_author_byz]), so neither knowledge
    conjunct can hold - the punish-only-what-you-know rule. The no-ban /
    no-penalty conjuncts are deliberately non-epistemic and V2-local: they are
    the checkable Skip. Mutation pin: {!Unres_model.No_author_resolved_guard}
    deletes the author_resolved guard so the reject unconditionally
    Fatal-charges its propagation source, unjustly banning honest V1 at V2 in
    the lag branch (peers/all_peers.rs:853-873, peers/peer.rs:213-237); this
    refutes the statement through the no-ban / no-penalty (Skip) conjuncts.
    Liveness is NOT the refuting lever: the vote-time recovery is
    proposer-sourced (the MissingParents flow, handler.rs:653-668), so a ban on
    the certificate's author does not block a third party from supplying it and
    the quorum still reassembles - [Af done] survives the mutation. *)
let s3 =
  let skip_body =
    Formula.conj
      [
        Formula.Not (Formula.K (Validator.V2, atom Unres_author_honest));
        Formula.Not (Formula.K (Validator.V2, atom Unres_author_byz));
        no_ban_by_2;
        Formula.Not (atom Penalized_by_2);
      ]
  in
  {
    name = "unresolved-author-reject-skips-penalty-and-liveness-recovers";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        ( Formula.Ag (Formula.Implies (atom Saw_unres_2, skip_body)),
          Formula.Af (atom At_done) );
    antecedent = atom Saw_unres_2;
  }

(** All statements of this family: exactly S3. *)
let all = [ s3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** The uniform cross-model projection for the meta-tests: build the pristine
    system and report per-statement proved flags; a [make] error degrades
    every row to [proved = false] rather than raising. *)
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
        (fun st ->
          { Report.name = st.name; bucket = st.bucket; proved = false })
        all)
    (make ())
