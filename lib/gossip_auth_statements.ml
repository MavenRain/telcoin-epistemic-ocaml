(** The GOSSIP-AUTH statement family (DESIGN family GOSSIP-AUTH, statement
    #1), encoded over the {!Gossip_auth_model} interpreted system.
    Adversarially verified against telcoin-network (grounding) and against
    the finite-model semantics (encodability); stated here in the refined
    form that survived both skeptics. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide: the knowledge agents are the honest committee subscribers
    V1 and V2, whose view is exactly their {!Gossip_auth_model.local} (own
    anchor vote, own delivery bits). K_i is grounded in that local state -
    {!Gossip_auth_model.Checker} evaluates it by indistinguishability over
    all reachable global states. The strict epistemic content is that
    acceptance of a certificate frame off the gossip topic (delivery to the
    application layer, crates/network-libp2p/src/consensus.rs:1004-1047)
    carries knowledge that a CURRENT committee member published it: the
    envelope author is bound to a committee BLS key by strict signed
    validation and the verified node record (consensus.rs:342-362 and
    529-565), and the per-topic authorized-publisher set is exactly the
    committee (consensus.rs:194-198, installed with the epoch's committee
    keys at start_epoch.rs:481-486 and 517-524), so verify_gossip accepts
    only committee-authored frames (consensus.rs:1491-1514). The knowledge
    is grounded, not rigid: the leader-crash-post-vote branch is
    subscriber-view-identical to the cooperative run's delivery window, so
    before delivery a subscriber provably cannot know publishing happened. *)

open Gossip_auth_model

(** A statement over this family's atom vocabulary; [bucket] reuses the
    shared vocabulary of the frozen {!Statements} module and [antecedent]
    is the reachability witness [prove_nonvacuous] requires - the proof is
    refused if it never holds, so the statement is never certified on the
    strength of a false antecedent. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - accepted-gossip-implies-known-committee-publisher [security].
    A certificate frame accepted off the gossip topic carries knowledge of
    a committee publisher, no outsider frame is ever accepted, and the
    authorized publish reaches every honest subscriber. Three conjuncts,
    each ranging over the knowledge agents i in {V1, V2} (the i = V0
    instance collapses - its operand is V0's own publish act - so V0 is
    never placed under K; V3 is epistemically inert):

    - [AG (delivered_i(C) -> K_i(exists committee j: published_j(C)))]:
      whenever i accepted V0's anchor certificate [C] into the application
      layer (consensus.rs:1004-1047), i knows a current committee member
      published it. In this model the only committee publish act for [C] is
      V0's aggregate-and-publish (publish_certificate,
      crates/consensus/primary/src/network/mod.rs:423-428), so the
      existential is the [Committee_published Cert_c] history bit. The K
      holds because delivery only ever writes [delivered_c] behind a live
      publish, and it is contingent because the delay window and the
      crash-post-vote branch share i's view while the publish bit differs.

    - [AG (~delivered_i(C'))]: the outsider frame [C'] - signed by the
      phantom non-committee node O and published on the certificate topic -
      is never accepted, because verify_gossip's authorized-publisher
      containment rejects it (Reject(UnauthorizedAuthor),
      consensus.rs:1491-1514, the [auth.contains(&bls_key)] arm at
      1504-1508). This is the non-epistemic safety face of the same gate;
      for [C'] the K-implication would only be vacuously true, so the
      outsider case is pulled out as an explicit invariant.

    - [published_V0(C) ~> AND_i delivered_i(C)]: once V0 performs the
      publish act, bounded-delay mesh delivery inevitably forwards [C] to
      every honest subscriber (the delayed one is repaired at the forced
      second deliver phase).

    Mutation pin: {!Gossip_auth_model.Drop_publisher_auth} deletes the
    authorized-publisher containment arm (consensus.rs:1504-1508); the
    outsider's validly-signed [C'] then passes every remaining check and is
    delivered, so [delivered_i(C')] becomes reachable at states where no
    committee member ever published it, refuting the second conjunct. No
    sibling path repairs the deletion: {!Gossip_auth_model.deliver_c_prime}
    is the unique writer of the [delivered_c_prime] bits and there is no
    second committee-containment check behind the deleted one. *)
let s1 =
  let delivered_knows_publisher i =
    Formula.Implies
      ( atom (Delivered (i, Cert_c)),
        Formula.K (i, atom (Committee_published Cert_c)) )
  in
  let no_outsider_frame i = Formula.Not (atom (Delivered (i, Cert_c_prime))) in
  let all_delivered =
    Formula.conj (List.map (fun i -> atom (Delivered (i, Cert_c))) subscribers)
  in
  {
    name = "accepted-gossip-implies-known-committee-publisher";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( Formula.Ag
            (Formula.conj (List.map delivered_knows_publisher subscribers)),
          Formula.And
            ( Formula.Ag
                (Formula.conj (List.map no_outsider_frame subscribers)),
              Formula.leads_to
                (atom (Committee_published Cert_c))
                all_delivered ) );
    antecedent =
      Formula.And
        ( atom (Committee_published Cert_c),
          atom (Delivered (Validator.V1, Cert_c)) );
  }

(** The family's statements: exactly S1. *)
let all = [ s1 ]

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
