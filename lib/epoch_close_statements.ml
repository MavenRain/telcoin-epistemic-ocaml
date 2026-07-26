(** The EPOCH_CLOSE statement family, encoded over the
    {!Epoch_close_model} interpreted system. Three statements about the single
    epoch boundary [e-1 -> e]: what a certificate in the epoch-record store
    proves about the rest of the committee, what the idempotent save guarantees
    (and hides) from a diverged member, and what the entry-time committee
    pre-dial buys. File citations refer to Telcoin-Association/telcoin-network.

    Reading guide for the [K] operands. V1 is the only knowledge agent. It sees
    its own pipeline position, its own epoch-record store as
    [get_epoch_by_number] presents it, its own vote tally, whether an
    unverified peer response is in hand, and its connected-peer count. Every
    [K] operand here is a fact V1 cannot read off any of those:

    - [quorum_backs_stored] - "at least 2n/3+1 members of epoch e-1's committee
      signed the record my store returns". A fact about OTHER validators'
      execution results and signing acts (each member signs its own computed
      record, epoch_votes.rs:58-73). V1 never observes those acts; on the
      acquisition path it was not even a participant in that epoch. It is not
      rigid: it is FALSE at every reachable state where V1 holds an uncertified
      own record and at every pre-store state. Pristine, the super-quorum count
      in [verify_with_cert] (epoch.rs:84-88) is what makes it hold at every
      state of the store-with-cert view class - exactly the shape of the frozen
      exemplar's [K_V1(~banned_2(V1))], and exactly what the mutation breaks.
    - [candidate_sound] - "the unverified bytes in my hand would survive
      [verify_with_cert]". [request_epoch_cert] (network/mod.rs:809-829)
      rotates over up to three arbitrary peers and hands back the response with
      NO network-layer validation, so the flavour is coarsened out of V1's view
      and V1 can neither confirm nor rule it out while it is merely in hand.
    - [committee_chose_other] - "the super-quorum signed a record other than
      the one I computed", i.e. my execution diverged. A claim about the other
      validators' execution outputs, invisible to V1 in exactly the modelled
      situation: V1 got there because it could NOT observe a quorum. *)

open Epoch_close_model

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

(** S1 - certified-epoch-record-implies-known-supermajority-endorsement
    [security].

    (c1) Whenever V1's epoch-record store yields a record WITH a certificate
    attached - [get_epoch_by_number(e-1) = Some((rec, Some(cert)))] - V1 KNOWS
    that a super-quorum (2n/3+1 = 3 of 4) of that epoch's committee actually
    signed that very record, even though V1 never observes the signing acts:
    AG( holds_cert -> K_V1(quorum_backs_stored) ).
    [EpochRecord::verify_with_cert] is the SOLE content gate on every
    certificate that reaches the store (crates/types/src/primary/epoch.rs:59-89;
    the count check at :84-85 against [super_quorum] at :94-96). Its three
    production callers are the self-tally save
    (crates/node/src/manager/epoch_votes.rs:152-173), the failed-quorum
    recovery (epoch_votes.rs:196-231, gate at :200) and the state-sync
    collector (crates/state-sync/src/epoch.rs:100-114, gate at :102). Nothing
    downstream re-validates: [EpochRecordDb::save]
    (crates/storage/src/epoch_records.rs:229-243) and [Inner::save] (:597-617)
    only append.

    (c2) While an unverified peer response is merely in hand, V1 can neither
    confirm nor rule out that it carries a genuine super-quorum:
    AG( response_in_hand -> ~K_V1(candidate_sound) /\\
    ~K_V1(~candidate_sound) ). [request_epoch_cert]
    (crates/consensus/primary/src/network/mod.rs:809-829) rotates over up to
    three arbitrary peers and hands back [(EpochRecord, EpochCertificate)] with
    NO verification; the caller alone verifies (epoch_votes.rs:200,
    state-sync/epoch.rs:102). The model therefore coarsens the candidate
    flavour out of V1's view: V1 sees "a response is in hand", not whether the
    bytes are sound.

    R2 (c1 is a positive K): at the operative branch-B state (Sg_open,
    St_far_cert, held = Hd_quorum, byz = Bz_silent) the V1-view class also
    contains its byz twin with byz = Bz_signed - the fourth committee member
    cast a vote for the endorsed record that never reached V1 before the
    collector timed out (epoch_votes.rs:83-144, timeout arm :130-140; gossip is
    best-effort). Class size 2. Likewise at the branch-A operative state
    (Sg_settled, St_own_cert, Tl_quorum). R3 (c2): the colliding pair is
    (Sg_recover, St_own, Tl_short, Cd_sound) and (Sg_recover, St_own, Tl_short,
    Cd_lone) - identical V1 view (a response is in hand), disagreeing on
    [candidate_sound].

    Mutation pins (c1 rests on two independent gates, and BOTH pin it):
    {!Epoch_close_model.No_cert_quorum_count} deletes the super-quorum count
    (epoch.rs:84-88), adding (Sg_wait, Cd_lone) -> (Sg_open, St_far_cert,
    held = Hd_lone). That state's V1 view is IDENTICAL to the honest (Sg_open,
    St_far_cert, held = Hd_quorum), so [K] fails at both (the operand is false
    at the new state and therefore unknown at the honest one), refuting c1.
    {!Epoch_close_model.No_cert_digest_binding} deletes the certificate index's
    content-addressing (epoch_records.rs:601 + :612-614 write vs :374-375
    read), adding (Sg_settled, St_own_cert, held = Hd_far): a certificate a
    super-quorum signed over ANOTHER record now answers
    [get_epoch_by_number] for V1's own, so [holds_cert] holds where
    [quorum_backs_stored] fails and c1 is refuted outright. c2 is untouched by
    both, so each refutation is attributable to the endorsement conjunct. *)
let s1 =
  let known_endorsement =
    Formula.Ag
      (Formula.Implies
         ( atom Holds_cert,
           Formula.K (Validator.V1, atom Quorum_backs_stored) ))
  in
  let candidate_opacity =
    Formula.Ag
      (Formula.Implies
         ( atom Response_in_hand,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom Candidate_sound)),
               Formula.Not
                 (Formula.K
                    (Validator.V1, Formula.Not (atom Candidate_sound))) ) ))
  in
  {
    name = "certified-epoch-record-implies-known-supermajority-endorsement";
    bucket = Statements.Security;
    formula = Formula.And (known_endorsement, candidate_opacity);
    antecedent = Formula.And (atom Holds_cert, atom Holds_foreign_record);
  }

(** S2 - self-closed-epoch-record-is-never-displaced-and-divergence-stays-hidden
    [safety].

    (c1) A committee member that closed epoch e-1 itself can NEVER have its own
    stored record displaced by a peer's:
    AG( holds_own_record -> AG holds_own_record ). Once the record is written by
    [write_epoch_record] (crates/node/src/manager/node/close_epoch.rs:238-249,
    [save_record] at :247) the epoch slot is filled, and the storage layer is
    append-only in THREE independent ways: [Inner::save_record] returns [Ok(())]
    early on an already-filled slot (crates/storage/src/epoch_records.rs:574-576);
    with that early return gone, [idx < len] falls into the out-of-order arm
    (:577-582) whose [Err] [Inner::save] propagates with [?] at :604, before the
    cert append at :611-614; and with that arm gone too, [epoch_idx.save]
    (:590-592) still refuses, because [PositionIndex::save] accepts only
    [key == len] and APPENDS rather than overwrites
    (crates/storage/src/archive/position_index/index.rs:247-261). On top of
    that, [EpochRecordDb] exposes no delete/replace writer at all - only
    [save_dummy_epoch0] (:191, writing a separate epoch-0 slot at :556-566),
    [save_record] (:219), [save] (:231) and [save_certificate] (:247,
    certificates only).

    c1 is therefore pinned by NO mutation in this family, and deliberately so:
    displacement is not gated by a deletable guard, it is the shape of the
    writer surface, so any single-gate deletion that claimed to produce it would
    be fiction. (The family's earlier pin claimed exactly that fiction -
    deleting :574-576 was said to let a peer's record replace V1's; it does not,
    it makes the save fail and leaves the store untouched.) What one deletion
    CAN break is c2, and that is where the pin now sits.

    (c2) Consequently a member whose execution diverged from the supermajority
    ends the boundary with NO certificate attached:
    AG( (settled /\\ tally_short /\\ committee_chose_other) -> ~holds_cert ).
    A diverged member cannot reach local quorum on its own digest
    (epoch_votes.rs:94-111, threshold at :103), and the recovery's save
    (epoch_votes.rs:196-231 -> :21-40 -> epoch_records.rs:229-243) stores the
    fetched cert keyed by the FETCHED record's digest (epoch_records.rs:601),
    while [get_epoch_by_number] looks the cert up by the STORED record's digest
    (:369-377). Result: [Some((own_rec, None))]. The "Over wrote expected epoch
    record" log at epoch_votes.rs:203-206 is therefore misleading - no
    overwrite occurs.

    (c3) And the member cannot tell that divergence, rather than mere vote
    loss, is the reason:
    AG( (settled /\\ tally_short /\\ ~holds_cert) ->
    ~K_V1(committee_chose_other) /\\ ~K_V1(~committee_chose_other) ). The
    collector loop breaks on timeout (epoch_votes.rs:130-134, [timeouts > 24])
    and the five recovery fetches can all fail (epoch_votes.rs:196-231), so an
    uncertified settle is equally consistent with "the committee endorsed my
    record and I never saw the votes" and "my execution diverged".

    R3 (c3): the colliding pair, both reachable, sharing V1's entire view
    (Sg_settled, St_own, Tl_short, no response, Pr_some): world 1 has
    truth = Tr_own - the committee DID endorse V1's record, V1 simply never
    received enough votes and all five recovery fetches failed; world 2 has
    truth = Tr_far - V1's execution diverged, the fetch returned the majority's
    record, and the idempotent save left V1 uncertified. They disagree on
    [committee_chose_other], so both [K]s fail. Each of the two additionally has
    its byz twin, so the class has four members.

    Mutation pin: {!Epoch_close_model.No_cert_digest_binding} deletes the
    certificate index's content-addressing inside [Inner::save] - the fetched
    certificate is filed under the FETCHED record's digest
    (epoch_records.rs:601, :612-614) precisely so that the
    [cert_by_digest(record.digest())] lookup on the STORED record (:374-375)
    cannot resolve it. Filing it under the epoch slot's own record digest
    instead adds (Sg_recover, Cd_sound, Tr_far) -> (Sg_settled, St_own_cert,
    held = Hd_far): the record is still not displaced (c1 holds under the
    mutation too, as it must), but the diverged member now ends the boundary
    reporting a certificate - one a super-quorum signed over a DIFFERENT
    record - refuting c2. c3 survives the mutation, because the give-up path
    still supplies both colliding worlds, so the refutation is attributable to
    c2 alone. The same deletion also refutes S1's endorsement conjunct, which
    is honest: the digest binding is exactly what makes "there is a certificate
    on my record" mean "a super-quorum signed my record". *)
let s2 =
  let own_record_never_displaced =
    Formula.Ag
      (Formula.Implies (atom Holds_own_record, Formula.Ag (atom Holds_own_record)))
  in
  let diverged_member_uncertified =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [ atom Settled; atom Tally_short; atom Committee_chose_other ],
           Formula.Not (atom Holds_cert) ))
  in
  let divergence_hidden =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [ atom Settled; atom Tally_short; Formula.Not (atom Holds_cert) ],
           Formula.And
             ( Formula.Not
                 (Formula.K (Validator.V1, atom Committee_chose_other)),
               Formula.Not
                 (Formula.K
                    (Validator.V1, Formula.Not (atom Committee_chose_other)))
             ) ))
  in
  {
    name = "self-closed-epoch-record-is-never-displaced-and-divergence-stays-hidden";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [ own_record_never_displaced; diverged_member_uncertified; divergence_hidden ];
    antecedent =
      Formula.conj
        [ atom Settled; atom Tally_short; atom Committee_chose_other ];
  }

(** S3 - entry-predial-preserves-record-acquisition [liveness].

    When epoch entry finds the previous epoch's record missing,
    [open_epoch_pack] pre-dials the whole committee before it blocks, precisely
    because peer connections are otherwise only established in
    [spawn_primary_network_for_epoch], which runs AFTER [open_epoch_pack]
    returns (crates/node/src/manager/node/run_epoch.rs:219 vs :258-267).

    (c1) That pre-dial is what keeps acquisition of the record REACHABLE from
    the blocking wait: AG( waiting -> EF opened ). The pre-dial block is at
    run_epoch.rs:487-503, guarded on [connected_peers_count() == 0] at :489,
    with the in-code rationale at :483-486 ("Without this we deadlock"). With
    zero connected peers the collector's only fetch route returns
    [NetworkError::NoPeers] (crates/network-libp2p/src/consensus.rs:868-880) on
    every attempt.

    (c2) The wait can still time out into a node halt:
    AG( (waiting /\\ ~response_in_hand) -> EF halted ).
    [record_by_epoch_with_timeout(previous_epoch, 30s)] returns [None] on expiry
    (crates/storage/src/epoch_records.rs:270-288) and [open_epoch_pack] then
    returns [Err] (run_epoch.rs:512-516), which [run_epochs] propagates with [?]
    (crates/node/src/manager/node.rs:1200-1241, the [?] at :1227), aborting the
    epoch loop. Acquisition is genuinely a RACE, not a guarantee - which is why
    no [Af] / [leads_to] is asserted anywhere in this statement (rule R8): even
    with peers the collector can be answered with junk, which pristine verify
    rejects (state-sync/epoch.rs:102), and it retries on a 5s timer inside a 30s
    deadline.

    (c3) The pack is never opened without a record:
    AG( opened -> holds_record ). [consensus_chain.new_epoch] is reached only
    with a resolved [previous_epoch_rec] (run_epoch.rs:451-518).

    (c4) And when what unblocked entry is a record V1 ACQUIRED - rather than
    one it wrote itself - it is a record V1 knows a super-quorum endorsed:
    AG( (opened /\\ holds_foreign_record) -> K_V1(quorum_backs_stored) ). An
    acquired record comes from the collector, whose three-conjunct gate
    ([parents_match && epoch_committee_valid && epoch_valid]) includes
    [verify_with_cert] (crates/state-sync/src/epoch.rs:100-103), and it is
    saved into an EMPTY slot together with its certificate (:107), so
    [get_epoch_by_number] really does resolve the cert through the stored
    record's digest.

    The [holds_foreign_record] relativisation is NOT decoration, and the model
    contains its counterexample. [open_epoch_pack] runs on every epoch
    (run_epoch.rs:219), and its found-record branch imposes no certificate
    requirement at all: it reads [record_by_epoch(previous_epoch)] (:451-452),
    nudges [requested_missing_epoch] (:453-463) and opens the pack at :518. A
    committee member writes its own record with [save_record] and NO
    certificate (close_epoch.rs:238-249) and can end the boundary certless when
    quorum fails and all five recovery fetches fail
    (epoch_votes.rs:188-231, the [!got_epoch_record] arm at :225-231). So
    [opened /\\ ~holds_cert /\\ ~quorum_backs_stored] is a real state of the
    system - the model reaches it through the [Sg_settled] -> [Sg_open] edge -
    and the unrelativised AG( opened -> K_V1(quorum_backs_stored) ) is simply
    FALSE. [test/t_epoch_close.ml] asserts both halves of that: the certless
    open is reachable, and the unrelativised form fails at it.

    R2 (c4 is a positive K): at (Sg_open, St_far_cert, held = Hd_quorum,
    byz = Bz_silent) the V1-view class contains its byz twin byz = Bz_signed
    (an unobserved fourth vote), so the class has two members. For c1/c2 the
    non-degeneracy is the pristine UNREACHABILITY of (Sg_wait, Pr_none):
    [Waiting /\\ ~Peers_connected] is unsatisfiable pristine and satisfiable
    under {!Epoch_close_model.No_committee_predial}.

    Mutation pins: {!Epoch_close_model.No_committee_predial} deletes the
    pre-dial (run_epoch.rs:487-503), replacing (Sg_entry, Pr_none) ->
    (Sg_wait, Pr_some) with (Sg_entry, Pr_none) -> (Sg_wait, Pr_none), whose
    only successor is [Sg_halt] - so [EF opened] is false at a reachable
    waiting state, refuting c1. Independently
    {!Epoch_close_model.No_cert_quorum_count} refutes c4 by adding
    (Sg_open, St_far_cert, held = Hd_lone) into the opened view class - that
    state is FOREIGN-record, so it lands inside the relativised antecedent and
    the weakened c4 flips exactly as the unweakened one did.
    {!Epoch_close_model.No_cert_digest_binding} leaves this statement standing:
    it only ever attaches a mis-bound certificate to an OWN record, which
    [holds_foreign_record] excludes. *)
let s3 =
  let acquisition_reachable =
    Formula.Ag (Formula.Implies (atom Waiting, Formula.Ef (atom Opened)))
  in
  let halt_still_possible =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Waiting, Formula.Not (atom Response_in_hand)),
           Formula.Ef (atom Halted) ))
  in
  let opened_implies_record =
    Formula.Ag (Formula.Implies (atom Opened, atom Holds_record))
  in
  let acquired_open_implies_known_endorsement =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Opened, atom Holds_foreign_record),
           Formula.K (Validator.V1, atom Quorum_backs_stored) ))
  in
  {
    name = "entry-predial-preserves-record-acquisition";
    bucket = Statements.Liveness;
    formula =
      Formula.conj
        [
          acquisition_reachable;
          halt_still_possible;
          opened_implies_record;
          acquired_open_implies_known_endorsement;
        ];
    antecedent = atom Waiting;
  }

(** The family's statements: the certificate-endorsement security claim, the
    never-displaced / divergence-hidden safety claim, and the entry-pre-dial
    liveness claim. *)
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
