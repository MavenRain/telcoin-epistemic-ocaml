(** The EPOCH_SYNC statement family, encoded over the {!Epoch_sync_model}
    interpreted system: what a node that is behind can and cannot conclude when
    it adopts an epoch record fetched trustlessly from an anonymous peer. All
    three statements were mined from telcoin-network, re-grounded against the
    Rust in this checkout, and stated in the form that survived that pass. File
    citations refer to Telcoin-Association/telcoin-network.

    Reading guide for the K operands. V1 - the syncing node - sees only
    [(phase, holds_record(e), marked)]: its own control point, whether its
    epoch DB holds SOME record under [e], and whether [result_epoch] advanced.
    Every K operand in this family is therefore a GLOBAL or HIDDEN fact, never
    a function of that view:
    - [served_requested_epoch] is a property of ANOTHER node's ACT - which
      record an untrusted, unauthenticated peer chose to put on the wire in
      answer to a request that named epoch [e] (mod.rs:815). It is false at the
      reachable Pending/replay and Rejected/replay states, so it is not rigid.
    - [quorum_certified(response)] asserts that at least 2f+1 OTHER validators
      independently executed epoch [e] and each performed a sign act over the
      same digest (types/primary/epoch.rs:49-56, :59-89). V1 has executed
      nothing; [final_state] / [final_consensus] / [next_committee] are runtime
      values it cannot recompute. It is false at the reachable Pending/forged
      and Rejected/forged states.
    - [source_in_committee] is a fact about ANOTHER node's identity and role,
      appearing only NEGATED. It is structurally unavailable: the peer field is
      dropped at the single call site (mod.rs:821), the protocol imposes no
      membership constraint on responders (consensus.rs:868-881,
      handler.rs:990-1003), and no penalty path ever names the responder.

    Deliberately NOT asserted (conservatism): the two "ignorance at the Pending
    phase" conjuncts - AG(pending -> ~K_V1(served_requested_epoch)) and
    AG(pending -> ~K_V1(quorum_certified(response))). They would prove, but only
    because the model orders the arrival of the bytes before the evaluation of
    the gate: V1 physically holds the record at epoch.rs:79 and could compute
    either answer. That is computation-order ignorance, not partial
    information. The [Pending] phase is kept as a real modeled program point
    (the response IS in hand at :79 and the gate DOES run at :103) and supplies
    the non-rigidity witnesses for both positive K operands, but no epistemic
    claim is asserted there. *)

open Epoch_sync_model

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

(** S1 - adopted-record-answers-the-requested-epoch [safety]. In the trustless
    epoch-record sync loop (stable validator set, syncing node V1 already
    holding the certified record [R_0] and fetching epoch [e = 1] from an
    anonymous peer):

    (A) The collector never credits epoch [e] as retrieved unless its epoch DB
    really holds a record keyed [e] -
    AG( marked_synced(V1,e) -> holds_record(V1,e) ). Grounding: epoch.rs:107
    [save(epoch_rec, cert)] then :115 [result_epoch = epoch] is executed on the
    strength of [save] returning [Ok], while epoch_records.rs:570-576
    [save_record] keys strictly by [record.epoch] (idx = epoch - start_epoch)
    and returns [Ok(())] IDEMPOTENTLY - storing nothing - when that epoch is
    already present, and the actor's [save] (:597-617) then only adds the
    certificate. A replayed older record therefore makes the save succeed while
    leaving the DB with no entry under [e]. :147
    [if result_epoch != epoch { break; }] does NOT fire, the walk advances to
    [e + 1], [record_by_epoch(e)] at :88 is [None] and :96 returns [e] - the
    collector re-requests [e] forever with no error.

    (B) Whenever V1 adopts a response for epoch [e] it KNOWS the anonymous
    responder actually answered for the epoch that was asked for, rather than
    substituting an older, genuinely-certified epoch record -
    AG( adopted(V1,e) -> K_V1( served_requested_epoch ) ). Grounding:
    epoch.rs:78 [request_epoch_cert(Some(epoch), None)] names the epoch
    ([PrimaryRequest::EpochRecord { epoch, hash }], mod.rs:815), but the
    adoption gate at :103 is exactly
    [parents_match && epoch_committee_valid && epoch_valid] with
    [parents_match = parent_hash == epoch_rec.parent_hash] (:100) where
    [parent_hash = prev.digest()] (:88-90). There is NO comparison of
    [epoch_rec.epoch] to [epoch] anywhere in the branch (epoch.rs:78-137 read
    in full). On a stable committee the other two conjuncts are satisfied by a
    replayed record ([epoch_committee_valid]'s [Equal] branch, :22-44;
    [verify_with_cert] passes on a genuine old certificate,
    types/primary/epoch.rs:59-89), so the parent-hash conjunct is the SOLE
    binding - which is exactly what makes the knowledge in (B) load-bearing
    rather than incidental.

    R2 non-degeneracy for (B): at the operative [Adopted] states the V1-view
    class (Adopted, true, true) contains TWO reachable worlds -
    w1 = {Adopted; R_genuine; Src_committee; Store_genuine; marked} and
    w2 = {Adopted; R_genuine; Src_observer; Store_genuine; marked} - which
    disagree on [source_in_committee]; and the operand is contingent, being
    false at the reachable Pending/replay and Rejected/replay states.

    Mutation pin: {!Epoch_sync_model.No_parent_hash_check} deletes the
    [parents_match] conjunct (epoch.rs:100 as consumed at :103), ADDING
    [Pending(R_replay, src) -> Adopted] with [store] unchanged at [Store_empty]
    and [marked := true]. That single added state refutes (A) directly
    (marked_synced while ~holds_record) and refutes (B) by factivity
    ([served_requested_epoch] is false there, so K_V1 of it cannot hold).
    Neither conjunct of S2 nor any conjunct of S3 is touched. *)
let s1 =
  let credited_only_when_stored =
    Formula.Ag
      (Formula.Implies (atom Marked_epoch_synced, atom Holds_epoch_record))
  in
  let known_answered_the_request =
    Formula.Ag
      (Formula.Implies
         ( atom Phase_adopted,
           Formula.K (Validator.V1, atom Served_requested_epoch) ))
  in
  {
    name = "adopted-record-answers-the-requested-epoch";
    bucket = Statements.Safety;
    formula = Formula.And (credited_only_when_stored, known_answered_the_request);
    antecedent = Formula.And (atom Phase_adopted, atom Marked_epoch_synced);
  }

(** S2 - adoption-implies-known-super-quorum-certification [security].

    (A) A record only ever lands in V1's epoch DB carrying a genuine
    super-quorum certificate over its own digest -
    AG( holds_record(V1,e) -> quorum_certified(stored) ). Grounding:
    epoch.rs:102-103 [let epoch_valid = epoch_rec.verify_with_cert(&cert);] is a
    required conjunct of the [if] that guards the only save on this path (:107);
    [EpochRecord::verify_with_cert] (types/primary/epoch.rs:59-89) re-derives
    the digest and compares it with [cert.epoch_hash] (:60-63), expands
    [cert.signed_authorities] against [self.committee] (:65-79), refuses when
    [auth_iter < self.super_quorum()] (:84-86, super_quorum = 2n/3+1 at :94-96)
    and only then runs the aggregate BLS verification (:87). Nothing verifies a
    record on the way OUT of storage: [record_by_epoch]
    (epoch_records.rs:261-268), [get_epoch_by_number] (:370-377) and the
    serving side [retrieve_epoch_record] (handler.rs:990-1003) hand back
    whatever is stored.

    (B) At the moment of adoption V1 KNOWS that at least 2f+1 members of the
    epoch-[e] committee each performed a sign act over the digest that binds
    ([final_state], [final_consensus], [next_committee], [parent_hash], [epoch])
    - AG( adopted(V1,e) -> K_V1( quorum_certified(response) ) ). Grounding:
    types/primary/epoch.rs:21-38 (the record's fields) and :42-46 (the digest
    covers all of them, including the record's own [epoch]); :49-56 [sign_vote]
    signs [digest()] under [Intent::consensus(IntentScope::EpochBoundary)];
    :59-89 [verify_with_cert]. Adopting ONE record is how a syncing node learns
    the successor committee without executing anything - epoch.rs:90 shows the
    next iteration's expected committee is exactly this record's
    [next_committee] - and the knowledge is manufactured ENTIRELY by the
    [verify_with_cert] conjunct, because the other two conjuncts compare against
    values ([prev.digest()], [prev.next_committee]) that are PUBLIC fields of a
    record every peer already serves.

    R2 non-degeneracy for (B): the same two-world class as S1 -
    w1 = {Adopted; R_genuine; Src_committee; Store_genuine; marked} and
    w2 = {Adopted; R_genuine; Src_observer; Store_genuine; marked}, which
    disagree on [source_in_committee]; and the operand is contingent, being
    false at the reachable Pending/forged and Rejected/forged states.

    Mutation pin: {!Epoch_sync_model.No_cert_quorum_check} deletes the
    super-quorum plus aggregate-verify guard INSIDE the shared helper
    [EpochRecord::verify_with_cert] (types/primary/epoch.rs:84-88), which
    removes the [epoch_valid] conjunct at epoch.rs:103 and simultaneously
    disables the identical check on the sibling writer path
    (epoch_votes.rs:156 and :200). It ADDS
    [Pending(R_forged, src) -> Adopted] with [store := Store_forged]; (A) is
    refuted there (holds_record while ~quorum_certified(stored)) and (B) is
    refuted at all four [Adopted] states, which then share the one V1-view
    class (Adopted, true, true) while disagreeing on the operand. S1 and S3 are
    untouched: a forged record still answers for the requested epoch and still
    comes from a hidden source. *)
let s2 =
  let stored_is_certified =
    Formula.Ag
      (Formula.Implies (atom Holds_epoch_record, atom Stored_quorum_certified))
  in
  let known_quorum_certified =
    Formula.Ag
      (Formula.Implies
         ( atom Phase_adopted,
           Formula.K (Validator.V1, atom Response_quorum_certified) ))
  in
  {
    name = "adoption-implies-known-super-quorum-certification";
    bucket = Statements.Security;
    formula = Formula.And (stored_is_certified, known_quorum_certified);
    antecedent = Formula.And (atom Phase_adopted, atom Holds_epoch_record);
  }

(** S3 - epoch-record-adoption-is-source-blind [security]. The syncing node
    learns the CONTENT of an epoch record but provably not its SOURCE.

    (A) AG( adopted(V1,e) -> ~K_V1( source_in_committee ) ) - after adopting,
    V1 cannot confirm its supplier was a committee member. Grounding:
    mod.rs:819 [let res = self.handle.send_request_any(request.clone()).await?;]
    then :820-823 destructures
    [NetworkResponseMessage { peer: _, result: ... }], discarding the responder
    identity before the record reaches [collect_epoch_records];
    consensus.rs:868-881 [SendRequestAny] does [rotate_left(1)] on
    [connected_peers] and sends to the front with NO committee filter, and
    consensus.rs:1616 push_back's EVERY connected peer into that deque.

    (B) AG( adopted(V1,e) -> ~K_V1( ~source_in_committee ) ) - nor can V1 rule
    it out. Grounding: handler.rs:990-1003 [retrieve_epoch_record] serves any
    requester from local storage with no authorization and no proof of the
    server's own role, so any synced non-committee full node is a legal
    supplier; and the certificate identifies SIGNERS
    (types/primary/epoch.rs:130-145 [signed_authorities]), never the server, so
    nothing in the received bytes recovers the source.

    (C) AG( rejected(V1,e) -> EF( adopted(V1,e) /\\ ~source_in_committee ) ) -
    rejecting a bad response costs the responder nothing and narrows nothing,
    so V1 can still go on to adopt from an unauthenticated non-committee
    observer. Grounding: epoch.rs:128-137 a failed gate only [error!]s and
    returns [epoch.saturating_sub(1)];
    [rg 'report_penalty|Penalty' crates/state-sync/src/] is EMPTY even though
    network-libp2p/src/types.rs:383-393 documents that the caller of
    [SendRequestAny] "is responsible for ... reporting peers who return bad
    data"; epoch.rs:206-212 just re-runs after [EPOCH_COLLECT_RETRY_SECS] and
    mod.rs:818-827 re-rotates with no memory.

    R3 ignorance witness for (A) and (B): the colliding pair is
    s1' = {Adopted; R_genuine; Src_committee; Store_genuine; marked} and
    s2' = {Adopted; R_genuine; Src_observer; Store_genuine; marked}. Both are
    reachable (Wait -> Pending(R_genuine, src) -> Adopted for either [src]),
    both project to View_v1 (Adopted, true, true), and they disagree on
    [source_in_committee].

    Mutation pin: {!Epoch_sync_model.Committee_targeted_fetch} removes the
    anonymity of the fetch (mod.rs:819 / consensus.rs:868-881), REMOVING every
    [Wait -> Pending(resp, Src_observer)] transition. The [Adopted] view class
    collapses to the singleton {Adopted; R_genuine; Src_committee; ...}, so
    K_V1(source_in_committee) becomes TRUE and both (A) and (B) fail; (C) fails
    too, because no [Adopted] state with ~source_in_committee remains reachable
    while [Rejected] states still are (a Byzantine committee member can still
    serve a replay or a forgery). S1 and S2 both survive this mutation. *)
let s3 =
  let cannot_confirm_committee_source =
    Formula.Ag
      (Formula.Implies
         ( atom Phase_adopted,
           Formula.Not (Formula.K (Validator.V1, atom Source_is_committee)) ))
  in
  let cannot_rule_out_committee_source =
    Formula.Ag
      (Formula.Implies
         ( atom Phase_adopted,
           Formula.Not
             (Formula.K
                (Validator.V1, Formula.Not (atom Source_is_committee))) ))
  in
  let rejection_narrows_nothing =
    Formula.Ag
      (Formula.Implies
         ( atom Phase_rejected,
           Formula.Ef
             (Formula.And
                (atom Phase_adopted, Formula.Not (atom Source_is_committee))) ))
  in
  {
    name = "epoch-record-adoption-is-source-blind";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( cannot_confirm_committee_source,
          Formula.And
            (cannot_rule_out_committee_source, rejection_narrows_nothing) );
    antecedent = atom Phase_adopted;
  }

(** The family's statements: one safety and two security, each pinned by its
    own gate deletion. *)
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
