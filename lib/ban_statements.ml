(** The peer-scoring / ban statement family, encoded over the {!Ban_model}
    interpreted system (DESIGN family BAN, statements #2 and #5). Mined from
    telcoin-network, adversarially verified against the code (grounding) and
    against the finite-model semantics (encodability), and stated here in the
    refined form that survived both skeptics. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide: the only knowledge agents are the honest peers
    {!Ban_model.honest} = [V0; V1; V2]; each [K (i, _)] is grounded in i's
    peer-manager local (evidence held, fatal charge issued, ban applied), which
    is exactly i's view. [V3] is the Byzantine peer, carries no peer-score state
    and is never a knowledge agent. The strict epistemic content is that a fatal
    content-fault charge names the message's UNFORGEABLE author, so it can only
    land on a peer the charger KNOWS authored the bad payload - while the honest
    relayer of that same payload is knowably-innocent, which is what forbids the
    ban. The hidden run-fact byz(V3) := "this run's branch is an Invalid_gossip
    plan" is contingent (false in the Cooperate branch, invisible pre-delivery),
    so it is knowable only by the peers that received the invalid envelope. *)

open Ban_model

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

(** A statement over the ban model: name, bucket (the shared vocabulary from
    the frozen {!Statements} module), formula, and the reachability witness
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

(** S2 - content-fault-ban-requires-known-author [fairness]. A fatal
    content-fault charge routes to the message's unforgeable authenticated
    author, never the relayer that propagated it
    (crates/consensus/primary/src/network/mod.rs:1780-1812, the
    is_author_content_fault selection at mod.rs:1803), and gossip
    deep-validation failure raises exactly the Fatal content-fault error
    (crates/consensus/primary/src/error/network.rs:73-139 and 141-206;
    verdict handling crates/network-libp2p/src/consensus.rs:1004-1100 and
    2046-2098). So an honest node's charge against a peer p entails knowledge
    that p authored the bad payload -
    AG(AND_{honest i, p != i} fatal_charge_i(p) -> K_i authored_p(bad)) - and
    no honest node ever bans another honest node -
    AG(AND_{honest i != honest j} ~banned_i(j)). The knowledge is grounded,
    not rigid: authored_p(bad) holds only for the Byzantine [V3] and only in
    the invalid branches, and an honest node forwards gossip on the mesh
    before its own deep-validation verdict lands
    (crates/network-libp2p/src/consensus.rs:346-359 and 783-795), so an
    honest relayer's pre-delivery view collides with the Cooperate branch and
    K stays contingent. Fatal penalty processing jumps to the ban floor in one
    step (crates/network-libp2p/src/peers/manager.rs:424-443, score.rs:84-100,
    all_peers.rs:853-895); committee exemption suppresses the ban for [V3]
    (peer.rs:209-237), while the honest relayers are modeled non-exempt inside
    the committee-slot seeding-lag window, so author routing is their sole
    protection. Mutation pin: {!Ban_model.Charge_relayer} deletes the author
    selection at mod.rs:1803, the relayed run charges and bans the honest
    relayer where authored_relayer(bad) is false, and both conjuncts flip. *)
let s2 =
  let known_author =
    Formula.conj
      (List.concat_map
         (fun i ->
           List.map
             (fun p ->
               Formula.Implies
                 (atom (Fatal_charge (i, p)), Formula.K (i, atom (Authored_bad p))))
             (List.filter (fun p -> Bool.not (Validator.equal p i)) roster))
         honest)
  in
  let no_honest_ban =
    Formula.conj
      (List.concat_map
         (fun i ->
           List.map
             (fun j -> Formula.Not (atom (Banned (i, j))))
             (List.filter (fun j -> Bool.not (Validator.equal j i)) honest))
         honest)
  in
  {
    name = "content-fault-ban-requires-known-author";
    bucket = Statements.Fairness;
    formula = Formula.And (Formula.Ag known_author, Formula.Ag no_honest_ban);
    antecedent = atom (Fatal_charge (Validator.V2, byz));
  }

(** S5 - committee-exemption-liveness-known-but-unbannable-byzantine
    [liveness]. Peer scoring can never partition the committee: the TrustBasis
    exemption short-circuits the score model for committee validators, so no
    honest node ever bans the Byzantine committee member [V3] -
    AG(AND_{honest i} ~banned_i(V3)) - even though, in the all-honest
    broadcast branch, every honest node comes to KNOW byz(V3) -
    AG(bcast -> AF E_{honest}(byz V3)); yet that knowledge never becomes
    common - AG(~C_{honest}(byz V3)) - and consensus still terminates -
    AF done. byz(V3) is the hidden RUN-FACT strategy = Invalid_gossip, not the
    rigid designation "V3 is Byzantine". The exemption bypass is the
    if-let-Some(basis) short-circuit in Peer::apply_penalty
    (crates/network-libp2p/src/peers/peer.rs:209-237, exemption basis
    peer.rs:239-253); Fatal penalty processing that it suppresses is
    all_peers.rs:847-895 and 261-303. Common knowledge fails because the
    targeted branch (only V1 receives the invalid payload) is honest-view-
    identical to the broadcast branch for V1, so V1 cannot know that V2 knows
    byz(V3). Mutation pin: {!Ban_model.No_exemption} deletes the short-circuit
    at peer.rs:218-231, every honest node bans V3 in the broadcast branch, and
    conjunct 1 is refuted while AF done survives. *)
let s5 =
  let no_ban =
    Formula.conj (List.map (fun i -> Formula.Not (atom (Banned (i, byz)))) honest)
  in
  let everyone_knows = Formula.Everyone (honest, atom Byz_v3) in
  let bcast_leads_to_knowledge =
    Formula.Ag (Formula.Implies (atom Bcast, Formula.Af everyone_knows))
  in
  let no_common =
    Formula.Ag (Formula.Not (Formula.Common (honest, atom Byz_v3)))
  in
  {
    name = "committee-exemption-liveness-known-but-unbannable-byzantine";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        ( Formula.Ag no_ban,
          Formula.And
            ( bcast_leads_to_knowledge,
              Formula.And (no_common, Formula.Af (atom At_done)) ) );
    antecedent = atom Bcast;
  }

(** The family's statements: the fairness charge-routing statement and the
    liveness committee-exemption statement, sharing {!Ban_model}. *)
let all = [ s2; s5 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure degrades
    every row to [proved = false] rather than raising. *)
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
