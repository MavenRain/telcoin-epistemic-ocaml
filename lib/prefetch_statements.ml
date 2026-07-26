(** The prefetch statement family over the {!Prefetch_model} interpreted
    system (DESIGN family CONSENSUS-EXT #6). Mined from telcoin-network,
    adversarially verified against the code (grounding) and the
    finite-model semantics (encodability), and stated in the form that
    survived both skeptics. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide: [K (V1, _)] is grounded in V1's local state - whether it
    received a digest gossip from V3, whether it holds a batch under key b,
    and whether a cert references b in its dag - and {!Prefetch_model.Checker}
    evaluates it by indistinguishability of that view over all reachable
    global states. The epistemically strict content is that a bare gossiped
    digest (a hash) is not knowledge that a holder exists: a Byzantine
    committee author can gossip the SAME digest with no payload behind it
    ([Forge_digest]), a run view-identical to the honest ([Cooperate]) one.
    Knowledge of a holder is earned only by a content-address-verified
    fetch that actually lands the payload. *)

open Prefetch_model

(** A statement over the prefetch model: name, bucket (the shared
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

(** S6 - batch-digest-gossip-prefetch-knowledge-via-verified-fetch
    [liveness]. Two conjuncts over the honest listener V1 and the committee
    author V3:

    (1) Verified-fetch knowledge (leads-to): when V1 has received b's digest
    from V3 and the hidden branch is the honest [Cooperate] one, V1
    inevitably comes to HOLD b and, at that point, KNOWS some other
    validator holds b's payload -
    (recv_digest_V1(b, pub=V3) /\ byz=Cooperate) ~> (holds_V1(b) /\
    K_V1(exists j != V1: held_j(b))). This is sound only because in the
    pristine model storage under key b is CONTENT-ADDRESSED: the stored key
    is the payload's recomputed digest (handle.rs:509,523) filtered to the
    requested set (handle.rs:241-244) and inserted under that key
    (handler.rs:201-202), so occupying key b takes the genuine preimage,
    i.e. a responder that really held the payload (worker.rs:293-320
    seal-then-publish).

    (2) Received-digest ignorance (invariant): whenever V1 has merely
    received b's digest but does not hold b and no cert references b in its
    dag, V1 does NOT know that a holder exists -
    Ag((recv_digest_V1(b, pub=V3) /\ ~holds_V1(b) /\ ~referenced_in_dag_V1(b))
    -> ~K_V1(exists holder of b)). It holds non-vacuously because the
    [Forge_digest] pre-fetch state (no holder) is view-identical to the
    [Cooperate] pre-fetch state (real holder), publisher pinned to V3 in
    both, so the operand is genuinely contingent under V1's view.

    Both operands are the single atom {!Prefetch_model.Held_by_other}: under
    the invariant's [~holds_V1(b)] guard, "exists holder" and "exists other
    holder" coincide.

    Mutation pin: {!Prefetch_model.No_content_addressing} keys fetched
    batches by the GOSSIPED digest instead of the recomputed one
    (handle.rs:509,523), so a Byzantine bogus payload is stored under key b
    in the [Forge_digest] branch and V1 comes to hold b with no real holder
    (worker.rs no seal ever ran). That state is view-identical to the
    [Cooperate] faithful-hold state, so [K (V1, Held_by_other)] there
    collapses to false and conjunct (1)'s knowledge promise is refuted. No
    sibling path repairs THIS deletion: nothing downstream recomputes the
    digest - the requested-digests filter (handle.rs:241-244) and the store
    insert (handler.rs:201-202) both consume the mutated key unchanged.
    (Deleting only the digest-binding stream abort at handle.rs:512-516
    WOULD be silently repaired by content-addressed keying plus that
    filter, which is why the pin is anchored on the keying instead.) *)
let s6 =
  let held_by_other = Formula.K (Validator.V1, atom Held_by_other) in
  {
    name = "batch-digest-gossip-prefetch-knowledge-via-verified-fetch";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        ( Formula.leads_to
            (Formula.And (atom Recv_digest, atom Byz_cooperate))
            (Formula.And (atom Holds, held_by_other)),
          Formula.Ag
            (Formula.Implies
               ( Formula.conj
                   [
                     atom Recv_digest;
                     Formula.Not (atom Holds);
                     Formula.Not (atom Referenced_in_dag);
                   ],
                 Formula.Not held_by_other )) );
    antecedent = Formula.And (atom Recv_digest, atom Byz_cooperate);
  }

(** All statements of this family. *)
let all = [ s6 ]

(** Prove one statement on a system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every statement of the family, pairing each with its outcome. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** The uniform cross-model projection for the meta-tests: build the
    pristine system and report per-statement proved flags; a [make] error
    maps every row to [proved = false]. *)
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
