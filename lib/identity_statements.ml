(** The signed-peer-record identity family over the {!Identity_model}
    interpreted system (DESIGN family IDENTITY #9). Mined from
    telcoin-network, adversarially verified against the code (grounding) and
    against the finite-model semantics (encodability), and stated here in the
    form that survived both skeptics. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide: K_i is grounded in honest node i's local state - the
    NodeRecords its kad store has admitted and its peer-manager confirmed map
    (crates/network-libp2p/src/peers/manager.rs:799-838,
    peers/all_peers.rs:190-210). The epistemically strict content is that a
    remote validator's private signing act - encoded as membership in the
    global monotone [signed] set, the unforgeability behind
    NodeRecord::decode_and_verify (consensus.rs:534-535) - is NOT i-local:
    during the Propose-to-Deliver in-flight window the Cooperate run (V3
    signed and pushed its record) and the Silent run (V3 never signed) share
    honest i's empty view, so K_i cannot yet know the binding; it flips to
    knowledge only when the signature gate fires at confirmation. The self
    conjuncts (a node knowing its OWN binding) are epistemically trivial and
    are carried by the [Provisioned] escape hatch instead, so K appears only
    on CROSS bindings (i != v). *)

open Identity_model

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

(** A statement over the identity family; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module, and [antecedent] is the
    reachability witness [prove_nonvacuous] requires so the implication is
    never certified on a false hypothesis. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** The genuine committee bindings each validator signs and broadcasts at
    startup - its own BLS key at its canonical PeerId (record publish
    consensus.rs:397-440, PeerId space peers/types.rs:13-34): one
    [(peer, validator)] per committee slot, including the Byzantine slot's
    genuine [(p3, V3)]. *)
let genuine_bindings = List.map (fun v -> (peer_of v, v)) roster

(** The forged binding the Byzantine [Forge_record] strategy pushes: V1's
    committee key claimed at V3's fresh PeerId p3. In the pristine model the
    [NodeRecord::decode_and_verify] signature gate (consensus.rs:534-535)
    drops it; only the {!Identity_model.Drop_record_verify} mutation admits
    it. *)
let forged_binding = (P3, Validator.V1)

(** The confirm targets the safety half ranges over: every genuine committee
    binding plus the forged one, so a conjunct guarding the forged binding is
    present for the mutation to flip (confirm rule manager.rs:799-838,
    confirmed map all_peers.rs:190-210). *)
let confirm_targets = forged_binding :: genuine_bindings

(** The safety conjunct for honest [i] and confirm target [(p, v)]: a
    confirmed identity carries either KNOWLEDGE of the remote signing act
    (the record-admission path, peer_record_valid consensus.rs:529-565, gated
    by decode_and_verify at :534-535 and the committee-key/self-advertised
    scope at :1912-1944, all_peers.rs:213-256) or an operator-provisioned
    local binding (bootstrap/kad-DB restore all_peers.rs:823-829,
    start_epoch.rs:780-782). The [Provisioned] disjunct is false on every
    CROSS binding (i != v), so those reduce to the pure knowledge claim. *)
let known_or_provisioned i (p, v) =
  Formula.Implies
    ( atom (Confirmed (i, p, v)),
      Formula.Or
        (Formula.K (i, atom (Signed_binding (v, p))), atom (Provisioned (i, v, p)))
    )

(** The safety half: for every honest node and every confirm target, a
    confirmed identity implies the known-or-provisioned signed binding
    (peer_record_valid consensus.rs:529-565, confirm bookkeeping
    manager.rs:799-838, 851-875). *)
let safety =
  Formula.conj
    (List.concat_map
       (fun i -> List.map (known_or_provisioned i) confirm_targets)
       honest)

(** The honest ordered cross pairs [(i, v)] with i != v: the only pairs the
    liveness half ranges over, since a validator's own signing act is i-local
    (self conjuncts collapse) and the Byzantine endpoint never signs under
    the withhold strategy, so [first_connect(_, V3)] would have no knowable
    consequent (static-committee connect consensus.rs:713-756). *)
let honest_cross_pairs =
  List.concat_map
    (fun i ->
      List.filter_map
        (fun v -> if Validator.equal i v then None else Some (i, v))
        honest)
    honest

(** The cross-knowledge consequent for an honest pair [(i, v)]: i knows v's
    signed binding and v knows i's - the two CROSS conjuncts that replace the
    collapsing self conjuncts of the card's [E_{i,v}(...)]; each direction is
    grounded by confirm-on-delivery (manager.rs:799-838). *)
let cross_knowledge (i, v) =
  Formula.And
    ( Formula.K (i, atom (Signed_binding (v, peer_of v))),
      Formula.K (v, atom (Signed_binding (i, peer_of i))) )

(** The liveness half: the single static-committee startup connect
    (consensus.rs:713-756, start_epoch.rs:780-782) inevitably yields mutual
    cross-knowledge of the endpoints' signed bindings once the pushed records
    are delivered (kad record paths consensus.rs:1602-1613, 1744-1771,
    2014-2024). *)
let propagation =
  Formula.conj
    (List.map
       (fun (i, v) ->
         Formula.leads_to (atom (First_connect (i, v))) (cross_knowledge (i, v)))
       honest_cross_pairs)

(** S9 - confirmed-identity-implies-known-signed-binding [security].
    An honest node confirms a remote (BLS key, PeerId) binding only through a
    signature-verified NodeRecord, so a confirmed identity carries knowledge
    of the remote signing act - unless it is an operator-provisioned local
    binding. Two halves:

    - safety, over honest nodes and every confirm target -
      [Ag( confirmed_i(p, v) -> ( K_i signed_binding(v, p)
      \/ provisioned_i(v, p) ) )] (peer_record_valid consensus.rs:529-565
      with its decode_and_verify gate at :534-535; confirm bookkeeping
      manager.rs:799-838, 851-875; provisioning all_peers.rs:823-829,
      start_epoch.rs:780-782). The provisioned disjunct discharges only the
      SELF bindings (i = v), whose K would be a validator knowing its own
      signing act; on every CROSS binding it is false, so those reduce to the
      pure knowledge claim - the epistemically strict content;

    - liveness, over honest cross pairs i != v -
      [first_connect(i, v) ~> ( K_i signed_binding(v, peer_of v)
      /\ K_v signed_binding(i, peer_of i) )] (static-committee connect
      consensus.rs:713-756, start_epoch.rs:780-782; delivery
      consensus.rs:1602-1613, 1744-1771, 2014-2024). This is the card's
      [E_{i,v}(...)] with the two SELF conjuncts dropped (they collapse to
      plain truth), leaving only cross knowledge, restricted to honest v
      (under the withhold strategy the Byzantine endpoint never signs).

    Contingency: in the Propose-to-Deliver in-flight window the Cooperate run
    (V3 signed and pushed [(V3, p3)]) and the Silent run (V3 never signed)
    share every honest node's empty view, so [K_i signed_binding(V3, p3)] is
    non-trivially false there and flips to true only when the signature gate
    fires at confirmation.

    Mutation pin: {!Identity_model.Drop_record_verify} deletes the
    decode_and_verify gate (consensus.rs:534-535); the forged record binding
    V1's key to p3 then validates, an honest node confirms
    [confirmed_i(p3) = V1] while [signed_binding(V1, p3)] is false, and the
    safety half is refuted. The antecedent is the genuine Byzantine confirm
    [confirmed_0(p3, V3)] - reachable in the Cooperate branch - so the proof
    is never certified vacuously. *)
let s9 =
  {
    name = "confirmed-identity-implies-known-signed-binding";
    bucket = Statements.Security;
    formula = Formula.And (Formula.Ag safety, propagation);
    antecedent = atom (Confirmed (Validator.V0, P3, Validator.V3));
  }

(** The family's statements: exactly S9. *)
let all = [ s9 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator; a [make] failure
    degrades to [proved = false] rows rather than raising. *)
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
