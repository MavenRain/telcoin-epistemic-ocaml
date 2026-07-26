(** The reqres statement family over the {!Reqres_model} interpreted
    system (DESIGN replacement for the dropped #10). Mined from
    telcoin-network, adversarially verified against the code (grounding)
    and against the finite-model semantics (encodability), and stated in
    the form that survived both skeptics. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide: [K (V1, _)] is grounded in the requester V1's local
    state - its outstanding request slot and its verified cache (the sync
    stream opened to one chosen peer,
    crates/consensus/primary/src/network/mod.rs:714-722, and the
    [ConsensusCache] insert that runs only after the digest gate,
    crates/state-sync/src/consensus.rs:84-89). {!Reqres_model.Checker}
    evaluates it by indistinguishability of that view over all reachable
    global states. The K is deliberately pinned to the Byzantine responder
    V3, whose possession is a hidden contingent fact: V3 may genuinely hold
    the requested bytes and serve them ([Genuine]), hold them yet shed with
    a Deny frame ([Withhold], the acknowledged load-shed path,
    mod.rs:791-795 and :1892-1910), shed while lacking them exactly as an
    honest lacker would ([Deny], sync_codec.rs:330-347), or serve
    digest-invalid bytes ([Fabricate]). The rigid honest holder V2 is NOT
    under K - K over
    its constant possession (storage consensus.rs:882-904) would collapse
    to a triviality, so it carries no epistemic content and is excluded. *)

open Reqres_model

(** A statement over the reqres model: name, bucket (the shared vocabulary
    from {!Statements}), formula, and the reachability witness required by
    [prove_nonvacuous] - the proof is refused if the antecedent never
    holds, so no statement is certified on the strength of a false
    antecedent. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** V1 digest-verified and cached a fetched output served by V3 - the
    [ConsensusCache] insert that runs only after the requester-side digest
    gate (state-sync consensus.rs:84-89). *)
let verified_from_v3 = atom (Verified_from Resp_v3)

(** V1 issued a fetch to V3 and holds nothing verified yet - the
    outstanding request slot of mod.rs:774-806, invisible past the peer id
    to the rest of the run. *)
let pending_from_v3 = atom (Pending_from Resp_v3)

(** V3's responder-side possession of the exact requested bytes: true only
    on the hidden [Genuine] branch, where the local read (storage
    consensus.rs:882-904) can produce bytes matching the verified digest;
    false when V3 denies or fabricates. *)
let held_v3 = atom (Held Resp_v3)

(** V1 knows V3 possessed the served bytes. The knowledge agent is the
    requester V1; the operand is pinned to the Byzantine responder V3, so
    the operator ranges over V3's contingent hidden possession rather than
    a rigid fact. *)
let k_v1_held_v3 = Formula.K (Validator.V1, held_v3)

(** S10 - verified-response-implies-known-responder-possession [security].
    Once the requester V1 digest-verifies and caches a fetched consensus
    output served by the Byzantine responder V3, V1 KNOWS V3 possessed
    those exact bytes when it served them. The mechanism is
    [get_consensus_output] (state-sync consensus.rs:42-94): the digest gate
    (consensus.rs:84-87) rejects any wrong/forked response with [Retry], so
    only bytes whose decoded header digest matches the already-verified
    hash reach the [ConsensusCache] insert (consensus.rs:89) - and by
    digest unforgeability those bytes can only have existed at a node that
    held the genuine output (invariant doc consensus.rs:34-41).

    Four conjuncts:
    - [Ag(verified-from-v3 -> K_v1(held-v3))]: verified possession is
      knowledge. In the pristine model V1 caches from V3 only on the
      [Genuine] branch, so the verified state's V1-view class is a
      singleton where [held-v3] holds - the digest gate grounds the
      knowledge, and the mutation pin below certifies the singleton is
      gate-produced, not structural.
    - [Ag(verified-from-v3 -> held-v3)]: the same possession as a plain
      fact (the gate never caches unheld bytes). This is the conjunct the
      mutation refutes first.
    - [Ag((pending-from-v3 /\ ~verified-from-v3) -> ~K_v1(held-v3))]: the
      non-vacuity teeth. Every outstanding-request state with an empty
      cache shares ONE V1-view [Vw_requester (Some Resp_v3, Uncached)],
      and that class spans the [Genuine], [Withhold], [Deny] and
      [Fabricate] branches, so [held-v3] varies across it and V1 provably
      cannot know possession while the request is in flight. Deleting the
      unheld false-witness ([Deny]/[Fabricate]) branches would refute this
      conjunct, guarding against a collapsed-K vacuous proof.
    - [Ef(verified-from-v3)]: the verified antecedent is genuinely
      reachable (the [Genuine] fetch completes).

    Deliberately NOT claimed: inevitability. An asked-and-possessing V3
    ([Withhold]) may shed with a Deny frame and conclude the fetch
    unverified - deny-while-holding is acknowledged telcoin-network
    behavior (requester gloss "sync-capable, but shedding load or lacking
    the output", mod.rs:791-795; an at-capacity responder denies without
    reading, mod.rs:1892-1910) and a Byzantine holder is a fortiori
    unconstrained - so [Ag((pending-from-v3 /\ held-v3) ->
    Af(verified-from-v3))] is FALSE here exactly as in the real system;
    the statement is the DESIGN K-possession lens only.

    Mutation pin: {!Reqres_model.No_digest_gate} deletes the requester-side
    digest-mismatch reject (state-sync consensus.rs:84-87), so a [Fabricate]
    V3 payload caches exactly like a valid one and [verified-from-v3 /\
    ~held-v3] becomes reachable, refuting conjuncts 1 and 2. No sibling
    path repairs the deletion: the responder-side Deny gate
    (sync_codec.rs:320-347) is the honest responder's own self-check, which
    a fabricating V3 never runs, and retrying another peer is a separate
    run - the Verifying transition is self-contained. *)
let s10 =
  {
    name = "verified-response-implies-known-responder-possession";
    bucket = Statements.Security;
    formula =
      Formula.conj
        [
          Formula.Ag (Formula.Implies (verified_from_v3, k_v1_held_v3));
          Formula.Ag (Formula.Implies (verified_from_v3, held_v3));
          Formula.Ag
            (Formula.Implies
               ( Formula.And (pending_from_v3, Formula.Not verified_from_v3),
                 Formula.Not k_v1_held_v3 ));
          Formula.Ef verified_from_v3;
        ];
    antecedent = verified_from_v3;
  }

(** The family's statements: exactly S10. *)
let all = [ s10 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure
    degrades to [proved = false] rows rather than an exception. *)
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
