(** Finite interpreted system for the EPOCH_RECORD family: how an honest
    committee member comes to hold - and to KNOW it holds - a super-quorum
    certified epoch record, what its own transient vote tally already tells
    it, and what a committee that certified SOMEBODY ELSE'S record leaves
    behind in its database. File citations refer to
    Telcoin-Association/telcoin-network (HEAD 0c59c15b), read in this checkout.

    The modeled mechanism, over a three-epoch window in which epochs 0 and 2
    are CONSTANTS (record AND certificate already stored) and only epoch 1
    varies:

    - EPOCH CLOSE. At the epoch boundary the node builds its own
      [EpochRecord] and persists it with [save_record], i.e. with NO
      certificate (close_epoch.rs:238-247); [get_epoch_by_number] therefore
      returns [(EpochRecord, Option<EpochCertificate>)] and the [None] case
      is first-class and persistent (epoch_records.rs:369-377). A committee
      member also signs and gossips its own [EpochVote] at this moment
      (epoch_votes.rs:59-73), so its OWN signature is never in doubt - what
      is in doubt is who else signed, and what they signed.
    - VOTE TALLY. [manage_epoch_votes] collects gossiped votes
      (epoch_votes.rs:83-144). Each vote was already admitted by the gossip
      handler only after a committee-membership check and a full BLS verify
      (handler.rs:452-461). The instant [signed_authorities.len() >= quorum]
      the collector sets [reached_quorum = true] (epoch_votes.rs:103-104) -
      strictly BEFORE the aggregation (:152), the [verify_with_cert] recheck
      (:156) and the [save_certificate] (:159). So there is a real window in
      which the node holds quorum-many individually verified signatures over
      [digest(R1)] while its database still holds no certificate; that window
      is modelled explicitly as {!Sg_tally_quorum} rather than hidden, because
      inside it the node's knowledge is NOT the ignorance a certless database
      suggests. The window is bounded: every exit arm (aggregate [Err]
      :181-186, [verify_with_cert] false :174-179, [save_certificate] [Err]
      :158-166) returns from [manage_epoch_votes], dropping [sigs] and
      [signed_authorities], and the model's next stage is a process restart.
    - DIVERGENT CERTIFICATION. A member's vote for a FORKED record is
      admitted on purpose (handler.rs:446-450: "a member's vote for a
      forked/alternative record is still admitted (the collector's
      equivocation path needs it)"), and the collector tallies those votes in
      [alt_recs], erroring with "Reached quorum on epoch record X instead of
      Y" once they reach quorum (epoch_votes.rs:112-127). If the committee
      certifies R1' <> V1's own R1, V1's database NEVER acquires a
      certificate for epoch 1, and yet its collector cursor still advances
      past epoch 1: [collect_epoch_records] verifies the FETCHED pair
      (epoch.rs:100-103), calls [save(epoch_rec, cert)] (:107) and sets
      [result_epoch = epoch] (:115), while [Inner::save] computes
      [record_digest] from the FETCHED record (epoch_records.rs:601), has
      [save_record] silently no-op because the epoch slot is already filled
      (:570-576) and files the certificate under [digest(R1')] (:611-614) -
      whereas [get_epoch_by_number] resolves the certificate through the
      STORED record's digest (:374-375). The pair stays [(R1, None)] for ever
      (a rescan re-takes the same path and the cert-already-stored early
      return fires at :607-609). The same non-overwriting outcome holds on
      the epoch-close recovery route, whose "Over wrote expected epoch
      record" warning (epoch_votes.rs:202-207) precedes exactly the same
      [save]. This branch is modelled as {!E_alt}.
    - COLLECTOR SPAWN. [spawn_epoch_record_collector] initialises its scan
      cursor with [let mut last_epoch: Epoch = 0;] (epoch.rs:190) under the
      comment "Always start from epoch 0 so any gaps ... are back-filled on
      restart" (epoch.rs:185-189). The binding is OUTSIDE the loop, so this
      is a PROCESS-START behaviour, not a per-tick one; within one process
      the cursor is monotone non-decreasing and only ever lowered by one via
      [return epoch.saturating_sub(1)] (epoch.rs:96, :113, :136). The model
      therefore encodes the reset as the one-shot [Sg_boot] step and needs no
      "restarts infinitely often" fairness assumption.
    - SCAN. [collect_epoch_records] walks epochs upward. An epoch with record
      AND certificate is skipped and the cursor advanced (epoch.rs:61-64,
      publishing [rec.final_consensus] at :66-73). Otherwise it fetches with
      [request_epoch_cert] (epoch.rs:78) and only saves when parents match,
      the committee is valid and [verify_with_cert] passes (epoch.rs:100-107);
      any failure returns [epoch.saturating_sub(1)] and the outer select
      re-arms on the 5s [EPOCH_COLLECT_RETRY_SECS] timer (epoch.rs:15-16,
      :206-212).
    - QUORUM GATE. [EpochRecord::verify_with_cert] first refuses a
      certificate whose [epoch_hash] is not the record's own digest
      (epoch.rs:59-63), then walks the committee against the certificate's
      sorted [RoaringBitmap], counting matched indices into [auth_iter]
      (epoch.rs:65-79), and returns false BEFORE the pairing check when
      [auth_iter < self.super_quorum()] (epoch.rs:84-88); [super_quorum] is
      [((committee.len() * 2) / 3) + 1] = 3 for n = 4 (epoch.rs:94-96).
      Distinctness is structural: the bitmap yields sorted distinct indices
      and the closure advances [auth_iter] at most once per committee slot.

    CRYPTO ABSTRACTION (stated so the model's honesty is auditable).
    [BlsAggregateSignature::verify_secure] aggregate-verifies one copy of the
    intent message per listed public key and returns false ONLY for an EMPTY
    key list (bls_signature.rs:270-286). So a peer can exhibit only signatures
    that were really produced: a genuine 3-of-4 certificate exists iff at
    least three committee members actually signed the record's digest, while a
    SUB-quorum certificate is always producible, because V1's own vote is
    gossiped in the clear (epoch_votes.rs:71) and one real signature is enough
    to satisfy [verify_secure] once the count gate is gone. That asymmetry is
    the whole content of the {!No_quorum_count} mutation.

    FAULT ASSUMPTION (used once, by {!E_alt}). n = 4, f = 1 - the assumption
    [super_quorum] is built for ("we are safe unless a super majority of
    validators are byzantine", epoch.rs:90-93). Two DISTINCT epoch-1 records
    can therefore not both be super-quorum certified: two 3-subsets of a
    4-set intersect in at least 2 members, and each of those would have had
    to vote twice, whereas a non-equivocating member votes exactly once (the
    collector's own [committee_keys.remove] bookkeeping, epoch_votes.rs:98
    and :115, is annotated "so a validator can only vote once (correct or
    alt), no equivocation"). Hence {!E_alt} - the committee certified R1' -
    entails that V1's own R1 was NOT super-quorum certified.

    MEMORYLESSNESS (stated because the kernel's K is view-based, not
    history-based). V1's knowledge is a function of its CURRENT view. That is
    faithful here because the only stage at which V1 holds tally evidence,
    {!Sg_tally_quorum}, is itself part of the view, and every later stage is
    reached through {!Sg_boot} - a process restart, which drops the in-memory
    [sigs]/[signed_authorities] of [manage_epoch_votes] (they are locals of a
    function that has returned, epoch_votes.rs:54-55, :232). No claim in this
    family asserts ignorance at a stage whose real process still holds that
    evidence.

    Components (four, all finite):
    - [endorse] - the HIDDEN GLOBAL FACT: what the epoch-1 committee signed.
      V1 always signs its own record, so the honest floor for [digest(R1)] is
      one; the committee may also have certified a DIFFERENT record;
    - [store] - V1's epoch DB for epoch 1 as [get_epoch_by_number] reports it
      (epoch_records.rs:374-375): record only ([save_record],
      close_epoch.rs:247) or record + a certificate filed under THAT record's
      digest;
    - [stage] - V1's OWN sequential position: epoch close, the vote-tally
      window (short of quorum, or holding quorum-many verified signatures),
      the collector task spawn, then the scan cursor at 0, 1, 2;
    - [byz] - a ONE-SLOT budget for the Byzantine committee member V3
      answering a [request_epoch_cert] with a sub-quorum certificate. The
      budget is grounded in the client's own loop: [request_epoch_cert]
      retries up to three times from three DIFFERENT peers
      (network/mod.rs:809-829), which with f = 1 of 4 reaches a correct peer,
      so exactly one adversarial/failed answer per gap is the faithful
      encoding - not a manufactured fairness assumption.

    ROLE MAPPING (knowledge agents must be validators with a real,
    non-constant view; a blank-view party may never appear under K):
    - V1 is the SOLE knowledge agent: an honest epoch-1 committee member that
      runs BOTH [manage_epoch_votes] (epoch_votes.rs:43-233) and the
      epoch-record collector (epoch.rs:176-216). V1 SEES its own task stage
      (including whether its own tally reached quorum, and its own scan
      cursor), its own epoch-1 DB status (record vs record + certificate),
      and whether a sub-quorum certificate has already been delivered to it
      and refused - V1 runs [verify_with_cert] itself and logs the failure
      (epoch.rs:129-136), so that event is V1-observable.
    - V1 DOES NOT SEE [endorse]. That is the hidden fact. Outside its own
      tally window V1 only ever holds an aggregate group element plus a
      [RoaringBitmap] (the [EpochCertificate] fields, epoch.rs:135-145),
      neither self-authenticating as a signer roster, and the aggregator's
      early break at quorum (epoch_votes.rs:103-110, which shortens the
      timeout to 1s and only breaks outright at full committee) means the
      frozen bitmap can UNDER-report the true signer set.
    - V0 and V2 are the other honest epoch-1 committee members and V3 is the
      Byzantine member / sub-quorum-certificate offerer. All three are idle
      non-agents here: constant blank view, never under K. *)

(** What the epoch-1 committee signed. V1 always signs its own record R1 at
    epoch close (epoch_votes.rs:59-73), so no constructor means "nobody
    signed R1"; [E_pending] is the pre-close placeholder, before the gossip
    window has settled the collective fact. *)
type endorse =
  | E_pending  (** epoch 1 has not closed yet: the fact is not yet settled *)
  | E_solo
      (** only V1 signed [digest(R1)]: 1 of 4, far below [super_quorum] = 3 *)
  | E_byz
      (** V1 and the Byzantine member V3 signed [digest(R1)]: 2 of 4, still
          short *)
  | E_quorum3
      (** V1, V0 and V2 signed [digest(R1)]: exactly 3 of 4, V3 did NOT sign *)
  | E_quorum4  (** all four members signed [digest(R1)] *)
  | E_alt
      (** the DIVERGENT branch: V0, V2 and V3 reached quorum on a different
          epoch-1 record R1' and V1 alone holds R1. Votes for a forked record
          are admitted on purpose by the gossip handler (handler.rs:446-450)
          and tallied by [alt_recs] (epoch_votes.rs:112-127). Under n = 4,
          f = 1 this entails that [digest(R1)] itself was NOT super-quorum
          signed (quorum intersection, see the header's fault assumption), so
          {!quorum_endorsed} is false here while {!some_record_certified} is
          true. *)

(** Total order index for {!endorse}. *)
let endorse_index = function
  | E_pending -> 0
  | E_solo -> 1
  | E_byz -> 2
  | E_quorum3 -> 3
  | E_quorum4 -> 4
  | E_alt -> 5

(** Total order on {!endorse}. *)
let endorse_compare a b = Int.compare (endorse_index a) (endorse_index b)

(** V1's epoch DB for epoch 1, as [get_epoch_by_number] reports it - i.e. the
    certificate is looked up under the STORED record's digest
    (epoch_records.rs:374-375). *)
type store =
  | St_rec
      (** record only, the [(record, None)] shape [get_epoch_by_number]
          returns (epoch_records.rs:369-377) after [save_record]
          (close_epoch.rs:247) - and also the shape left behind when the
          committee certified a DIFFERENT record, since that certificate is
          filed under the other record's digest (epoch_records.rs:601,
          :611-614) *)
  | St_cert
      (** record AND a certificate that has cleared [verify_with_cert] AND is
          filed under THIS record's digest - written either by the tally path
          ([save_certificate] keyed by [cert.epoch_hash] = [digest(R1)],
          epoch_votes.rs:155-159) or by the collector ([save], epoch.rs:107)
          when the fetched record was R1 itself *)

(** Total order index for {!store}. *)
let store_index = function St_rec -> 0 | St_cert -> 1

(** Total order on {!store}. *)
let store_compare a b = Int.compare (store_index a) (store_index b)

(** V1's own sequential position: the epoch-1 close, the [manage_epoch_votes]
    window (split at the [reached_quorum] flag), the collector task spawn
    (epoch.rs:184-190), then the scan cursor at epoch 0, 1 and 2. *)
type stage =
  | Sg_close
      (** epoch 1 is closing: build and [save_record] (close_epoch.rs:238-247) *)
  | Sg_tally
      (** inside [manage_epoch_votes]' collection loop (epoch_votes.rs:83-144)
          with [reached_quorum] still false: fewer than [super_quorum]
          verified signatures over [digest(R1)] are in hand, which is also the
          state the alt-record break (:118-126) and the timeout exhaustion
          (:132-134) leave behind *)
  | Sg_tally_quorum
      (** inside the same loop with [reached_quorum = true]
          (epoch_votes.rs:103-104): quorum-many individually BLS-verified
          signatures over [digest(R1)] are in [sigs]/[signed_authorities] and
          NOTHING is persisted yet - the [save_certificate] is downstream at
          :159. Reachable only when a super-quorum really signed R1, because
          every counted vote cleared handler.rs:452-461 *)
  | Sg_boot
      (** process (re)start: [spawn_epoch_record_collector] sets the cursor
          (epoch.rs:190) *)
  | Sg_scan0  (** the scan cursor sits at epoch 0, which is complete *)
  | Sg_scan1  (** the scan cursor sits at epoch 1, the epoch under study *)
  | Sg_scan2
      (** the scan cursor has passed epoch 1 and sits at epoch 2; epoch 3 does
          not exist, so the fetch Errs, the loop breaks (epoch.rs:139-149) and
          the 5s timer re-enters at the same cursor forever *)

(** Total order index for {!stage}. *)
let stage_index = function
  | Sg_close -> 0
  | Sg_tally -> 1
  | Sg_tally_quorum -> 2
  | Sg_boot -> 3
  | Sg_scan0 -> 4
  | Sg_scan1 -> 5
  | Sg_scan2 -> 6

(** Total order on {!stage}. *)
let stage_compare a b = Int.compare (stage_index a) (stage_index b)

(** The one-slot budget for a Byzantine answer to [request_epoch_cert]
    (network/mod.rs:809-829: three tries from three different peers, so with
    f = 1 of 4 at most one answer is adversarial before a correct peer is
    reached). *)
type byz =
  | B_avail  (** the Byzantine member has not yet answered a fetch for epoch 1 *)
  | B_spent
      (** it has answered once with a sub-quorum certificate; the budget is
          used up *)

(** Total order index for {!byz}. *)
let byz_index = function B_avail -> 0 | B_spent -> 1

(** Total order on {!byz}. *)
let byz_compare a b = Int.compare (byz_index a) (byz_index b)

(** [true] iff at least [super_quorum] = 3 of the 4 epoch-1 committee members
    signed [digest(R1)] - V1's OWN record (epoch.rs:94-96). False on the
    divergent branch [E_alt], where the quorum formed on R1' instead. *)
let quorum_endorsed = function
  | E_pending -> false
  | E_solo -> false
  | E_byz -> false
  | E_quorum3 -> true
  | E_quorum4 -> true
  | E_alt -> false

(** [true] iff SOME epoch-1 record - V1's own R1 or the divergent R1' - was
    signed by at least [super_quorum] = 3 committee members, i.e. iff a pair
    that clears [verify_with_cert] (epoch.rs:59-88) exists anywhere for
    epoch 1. *)
let some_record_certified = function
  | E_pending -> false
  | E_solo -> false
  | E_byz -> false
  | E_quorum3 -> true
  | E_quorum4 -> true
  | E_alt -> true

(** [true] iff the certified epoch-1 record is NOT V1's own R1, i.e. the
    [alt_recs] quorum of epoch_votes.rs:118-126. *)
let alt_record_certified = function
  | E_pending -> false
  | E_solo -> false
  | E_byz -> false
  | E_quorum3 -> false
  | E_quorum4 -> false
  | E_alt -> true

(** [true] iff the Byzantine committee member V3 is among the signers of
    [digest(R1)] - the fact V1 cannot resolve, because the aggregator freezes
    the bitmap once quorum is reached (epoch_votes.rs:103-110). On [E_alt] V3
    signed R1', not R1, so this is false. *)
let byz_endorsed = function
  | E_pending -> false
  | E_solo -> false
  | E_byz -> true
  | E_quorum3 -> false
  | E_quorum4 -> true
  | E_alt -> false

(** [true] iff V1's epoch DB holds a certificate for its epoch-1 record. *)
let store_has_cert = function St_rec -> false | St_cert -> true

(** [true] iff the collector's scan cursor has advanced ABOVE epoch 1, i.e.
    epoch 1 will not be revisited in this process (epoch.rs:61-64, :115,
    :147-149). *)
let stage_past_epoch1 = function
  | Sg_close -> false
  | Sg_tally -> false
  | Sg_tally_quorum -> false
  | Sg_boot -> false
  | Sg_scan0 -> false
  | Sg_scan1 -> false
  | Sg_scan2 -> true

(** [true] iff V1 is inside the [reached_quorum]-but-unpersisted window of its
    own [manage_epoch_votes] loop (epoch_votes.rs:103-104 set the flag, :159
    persists). *)
let stage_tally_quorum_held = function
  | Sg_close -> false
  | Sg_tally -> false
  | Sg_tally_quorum -> true
  | Sg_boot -> false
  | Sg_scan0 -> false
  | Sg_scan1 -> false
  | Sg_scan2 -> false

(** [true] iff the Byzantine one-slot answer budget has been consumed. *)
let byz_answer_spent = function B_avail -> false | B_spent -> true

(** The joint global state: the hidden endorsement fact, V1's epoch DB, V1's
    own task position, and the Byzantine answer budget. *)
type state = { endorse : endorse; store : store; stage : stage; byz : byz }

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = endorse_compare s1.endorse s2.endorse in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = store_compare s1.store s2.store in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = stage_compare s1.stage s2.stage in
      if Bool.not (Int.equal c2 0) then c2 else byz_compare s1.byz s2.byz

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. [View_v1] is V1's projection - (stage, store,
    byz): its own task position (including whether its own vote tally has
    reached quorum), its own epoch-1 DB contents, and whether a sub-quorum
    certificate has already been delivered to it and refused (the [error!] at
    epoch.rs:129-136 is V1-observable). It carries NO component of
    {!endorse}. [View_idle] is the constant blank view of the non-agents V0,
    V2 and V3. *)
type view = View_v1 of stage * store * byz | View_idle

(** Total deterministic order over ALL fields of V1's view. *)
let view_v1_compare (sa, ta, ba) (sa', ta', ba') =
  let c = stage_compare sa sa' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = store_compare ta ta' in
    if Bool.not (Int.equal c1 0) then c1 else byz_compare ba ba'

(** Total order on views: [View_idle] < [View_v1], with the field-wise order
    within the agent constructor. Every constructor pair is spelled: no
    wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_v1 _ -> -1
  | View_v1 _, View_idle -> 1
  | View_v1 (sa, ta, ba), View_v1 (sa', ta', ba') ->
      view_v1_compare (sa, ta, ba) (sa', ta', ba')

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 is the sole knowledge agent (a real, non-constant
    view); V0, V2 and V3 are idle non-agents with the constant blank view and
    never appear under K. *)
let view v s =
  match v with
  | Validator.V1 -> View_v1 (s.stage, s.store, s.byz)
  | Validator.V0 | Validator.V2 | Validator.V3 -> View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_quorum_count
      (** delete the [if auth_iter < self.super_quorum()] branch inside
          [EpochRecord::verify_with_cert] (crates/types/src/primary/epoch.rs:84,
          with [auth_iter] accumulated at :65-79 and [super_quorum] at :94-96),
          leaving only [aggregate_signature.verify_secure(&intent, &pks[..])]
          (epoch.rs:87). Changes exactly ONE transition: at [Sg_scan1] with
          [store = St_rec] and [byz = B_avail] the Byzantine sub-quorum answer
          goes from [{ byz = B_spent }] (refused at epoch.rs:84, cursor lowered
          at :136, retried on the 5s timer) to
          [{ byz = B_spent; store = St_cert }] (accepted and saved at
          epoch.rs:107), so [(E_solo, St_cert, Sg_scan1 | Sg_scan2, B_spent)]
          becomes reachable.

          NO SIBLING REPAIRS IT. Every production write of an
          [EpochCertificate] is downstream of one of exactly three
          [verify_with_cert] call sites - state-sync/src/epoch.rs:102,
          epoch_votes.rs:156 and epoch_votes.rs:200 (writes at epoch.rs:107,
          epoch_votes.rs:159, and :207/:213 via [save_and_persist_with_logs]);
          close_epoch.rs:247 writes a RECORD only. [verify_secure] rejects only
          an EMPTY key list (bls_signature.rs:274-276), so it is not a repair
          for a 1-of-4 or 2-of-4 bitmap. The digest-equality guard at
          epoch.rs:59-63 is not a repair either: the Byzantine peer serves the
          pair, so it simply serves R1 together with a certificate whose
          [epoch_hash] is [digest(R1)]. [epoch_committee_valid]
          (epoch.rs:22-44) bounds committee SIZE only and never inspects the
          bitmap. Storage counts nothing (epoch_records.rs:369-377 just
          returns whatever was written). ONE genuine sibling exists - the
          PRODUCER-side count [signed_authorities.len() >= quorum] at
          epoch_votes.rs:103 - and it repairs ONLY V1's own tally route, not
          the two network-fed routes; the model therefore KEEPS that sibling
          LIVE under this mutation (the [Sg_tally] and [Sg_tally_quorum] steps
          are mutation-independent), so the refutation is attributable to
          epoch.rs:84 alone and not to a modelling gap. *)
  | Cert_conjunct_dropped
      (** relax the [Some(_)] certificate conjunct of
          [if let Some((rec, Some(_))) = ... get_epoch_by_number(epoch)]
          (crates/state-sync/src/epoch.rs:61) to [Some((rec, _))], so the
          collector treats a CERTLESS record as complete, advances the cursor
          (epoch.rs:64) and publishes [rec.final_consensus] as a trusted sync
          checkpoint (epoch.rs:66-73). At [Sg_scan1] with [store = St_rec] this
          replaces the whole fetch fan-out with the single step
          [{ stage = Sg_scan2 }], removing the Byzantine answer, the honest
          fetch and the divergent fetch alike, and making
          [(E_solo, St_rec, Sg_scan2, B_avail)] reachable - a cursor past an
          epoch NOBODY certified.

          NO SIBLING REPAIRS IT. (a) The cursor advances past epoch 1 and a
          restart re-enters the SAME relaxed skip at epoch.rs:61, so the epoch
          is never re-fetched; the three in-scan lowerings
          ([return epoch.saturating_sub(1)] at epoch.rs:96, :113, :136) all sit
          INSIDE the fetch arm the mutation bypasses. (b) The epoch-close
          recovery loop (epoch_votes.rs:196-224) runs only inside
          [manage_epoch_votes] for a member's own close, never for a historical
          gap. (c) The epoch-PACK route cannot manufacture a certificate:
          [request_epochs] iterates only over epochs whose record is ALREADY
          stored (state-sync/src/consensus.rs:110-135) and asks for pack files,
          not certificates. (d) Storage returns [(record, Option<cert>)] forever
          with no back-fill (epoch_records.rs:369-377). The one place that still
          demands a certificate is the SERVER side, handler.rs:1010-1025, which
          refuses to serve a certless record to peers - that limits contagion
          but does nothing for V1's own belief, so it is not a repair. *)
  | Cursor_starts_at_latest
      (** replace [let mut last_epoch: Epoch = 0;] inside
          [spawn_epoch_record_collector]
          (crates/state-sync/src/epoch.rs:190, whose comment at :185-189 states
          the intent verbatim - "Always start from epoch 0 so any gaps ... are
          back-filled on restart") with the DB's highest stored record epoch,
          which is 2 in this window. Changes exactly the [Sg_boot] step:
          [{ stage = Sg_scan0 }] becomes [{ stage = Sg_scan2 }], so [Sg_scan0]
          and [Sg_scan1] become unreachable and
          [(E_quorum3, St_rec, Sg_scan2, B_avail)] sits on its [Sg_scan2]
          self-loop forever, never acquiring the certificate.

          NO SIBLING REPAIRS IT. (1) The in-scan lowering
          [return epoch.saturating_sub(1)] (epoch.rs:96, :113, :136) only lowers
          to a gap the scan already REACHED; starting at 2 the scan can never
          reach 1. (2) The watch driver never lowers the cursor: the guard is
          [if requested_epoch >= last_epoch] (epoch.rs:193) and both nudge sites
          use [current.max(previous_epoch)] (run_epoch.rs:461-462, :479-480), so
          [requested_missing_epoch] is monotone UP - it can skip the collect
          call entirely but never re-aim it lower. (3) [request_epochs]
          (consensus.rs:110-135) requests pack files only for epochs whose
          record is already present, so it cannot supply a missing certificate.
          (4) The epoch-close recovery loop (epoch_votes.rs:196-224) is
          per-close, not a historical back-fill. *)

(** The tally stages an endorsement outcome can enter at the epoch-1 close.
    [Sg_tally_quorum] - [reached_quorum = true] at epoch_votes.rs:103-104 -
    requires quorum-many votes over [digest(R1)] that each cleared the gossip
    handler's BLS verify (handler.rs:452-461), so it exists exactly on the
    branches where a super-quorum really signed V1's own record. Those
    branches may ALSO end short of quorum (votes lost, the timeout exhaustion
    at epoch_votes.rs:132-134), which is why they carry both stages. *)
let tally_entry_stages e =
  if quorum_endorsed e then [ Sg_tally; Sg_tally_quorum ] else [ Sg_tally ]

(** The epoch-1 close step: V1 [save_record]s its own R1 without a certificate
    (close_epoch.rs:247) and gossips its own vote (epoch_votes.rs:59-73); the
    committee's collective act - a quorum on [digest(R1)], a quorum on a
    divergent R1', or neither - is settled by the gossip window
    (handler.rs:446-461). Mutation-independent. *)
let close_next s =
  List.concat_map
    (fun e ->
      List.map (fun stage -> { s with endorse = e; stage }) (tally_entry_stages e))
    [ E_solo; E_byz; E_alt; E_quorum3; E_quorum4 ]

(** Leaving the tally window WITHOUT [reached_quorum]: [manage_epoch_votes]
    takes the else arm (epoch_votes.rs:188-231) and tries up to five fetches
    from peers. On a branch where a super-quorum really signed R1 that fetch
    can return [(R1, cert)], which verifies (:200) and is saved (:207/:213),
    so the DB may or may not gain the certificate. On [E_alt] the same fetch
    returns [(R1', cert')]: the "Over wrote expected epoch record" warning
    (:202-207) is aspirational, because [save] files the certificate under
    [digest(R1')] (epoch_records.rs:601, :611-614) and [save_record] no-ops on
    the already-filled epoch slot (:570-576), so [get_epoch_by_number] still
    answers [(R1, None)] (:374-375) and the store stays [St_rec]. *)
let tally_short_next s =
  let base = { s with stage = Sg_boot } in
  if quorum_endorsed s.endorse then [ { base with store = St_cert }; base ]
  else [ base ]

(** Leaving the tally window WITH [reached_quorum]: aggregate
    (epoch_votes.rs:152), re-verify (:156) and [save_certificate] (:159)
    succeed and the DB gains the certificate, or one of the failure arms
    (aggregate [Err] :181-186, [verify_with_cert] false :174-179,
    [save_certificate] [Err] :158-166, or the node dying before :159) leaves
    the DB certless. Either way the function returns and the in-memory
    signatures are dropped. *)
let tally_quorum_next s =
  let base = { s with stage = Sg_boot } in
  [ { base with store = St_cert }; base ]

(** The state a Byzantine answer to [request_epoch_cert] leads to. Pristine
    (and under the two mutations that do not touch the quorum gate) the
    sub-quorum certificate FAILS [verify_with_cert] at epoch.rs:84, the
    collector logs and returns [epoch.saturating_sub(1)] (epoch.rs:129-136) and
    only the budget is consumed. Under {!No_quorum_count} the same certificate
    passes and is saved at epoch.rs:107, so the store also flips to
    [St_cert] - a certified record with no real super-quorum behind it. *)
let byz_answer mut s =
  match mut with
  | Pristine -> { s with byz = B_spent }
  | Cert_conjunct_dropped -> { s with byz = B_spent }
  | Cursor_starts_at_latest -> { s with byz = B_spent }
  | No_quorum_count -> { s with byz = B_spent; store = St_cert }

(** The scan step at [Sg_scan1] holding only a record: the collector fetches
    with [request_epoch_cert] (epoch.rs:78). Either the Byzantine member
    answers first (one-slot budget), or a correct peer answers - and what a
    correct peer can serve is decided by the hidden fact:

    - a super-quorum signed [digest(R1)]: the peer serves [(R1, cert)], the
      three conjuncts at epoch.rs:100-103 pass, [save] files the certificate
      under [digest(R1)] which IS the stored record's digest, so
      [get_epoch_by_number] now answers [(R1, Some cert)] - the store flips to
      [St_cert] and the cursor advances on the next step through the complete
      arm at epoch.rs:61-64;
    - a super-quorum signed a DIFFERENT record R1' ([E_alt]): the peer serves
      [(R1', cert')], which also passes epoch.rs:100-103 (same parent hash,
      same committee, and the pair is internally consistent), so
      [result_epoch = epoch] advances the cursor at :115 - but [save] files the
      certificate under [digest(R1')] (epoch_records.rs:601, :611-614) and
      [save_record] no-ops because the epoch slot is filled (:570-576), so
      [get_epoch_by_number(1)] answers [(R1, None)] for ever (:374-375) and the
      store stays [St_rec]. Rescans re-take this path and hit the
      cert-already-stored early return (:607-609), so the gap never closes;
    - nobody reached quorum on anything: no certificate exists anywhere, the
      server returns [Err(UnavailableEpoch)] (handler.rs:1022), the scan breaks
      and the 5s timer re-enters at the same cursor (the self-loop).

    Under {!Cert_conjunct_dropped} the fetch never happens: the relaxed
    conjunct at epoch.rs:61 marks the certless record complete and advances the
    cursor. *)
let scan1_gap_next mut s =
  match mut with
  | Cert_conjunct_dropped -> [ { s with stage = Sg_scan2 } ]
  | Pristine | No_quorum_count | Cursor_starts_at_latest ->
      let byz_branch =
        match s.byz with B_avail -> [ byz_answer mut s ] | B_spent -> []
      in
      let honest_branch =
        if quorum_endorsed s.endorse then [ { s with store = St_cert } ]
        else if alt_record_certified s.endorse then [ { s with stage = Sg_scan2 } ]
        else [ s ]
      in
      List.append byz_branch honest_branch

(** The transition relation under a mutation, driven by V1's own [stage].

    - [Sg_close]: epoch 1 closes, seven outcomes, mutation-independent
      ({!close_next}).
    - [Sg_tally] / [Sg_tally_quorum]: the two exits of [manage_epoch_votes]
      ({!tally_short_next}, {!tally_quorum_next}). MUTATION-INDEPENDENT on
      purpose: the producer-side count at epoch_votes.rs:103 is a SIBLING gate
      that {!No_quorum_count} does not delete, so this route never yields
      [St_cert] without a real quorum on [digest(R1)].
    - [Sg_boot]: process (re)start, the cursor initialisation at epoch.rs:190.
    - [Sg_scan0]: epoch 0 is complete, skipped at epoch.rs:61-64.
    - [Sg_scan1]: a complete epoch 1 is skipped; otherwise {!scan1_gap_next}.
    - [Sg_scan2]: the cursor sits above the last epoch; the fetch Errs, the
      loop breaks (epoch.rs:139-149) and the 5s retry timer
      (epoch.rs:206-212) re-enters at the same cursor forever. *)
let next_with mut s =
  match s.stage with
  | Sg_close -> close_next s
  | Sg_tally -> tally_short_next s
  | Sg_tally_quorum -> tally_quorum_next s
  | Sg_boot -> (
      match mut with
      | Pristine -> [ { s with stage = Sg_scan0 } ]
      | No_quorum_count -> [ { s with stage = Sg_scan0 } ]
      | Cert_conjunct_dropped -> [ { s with stage = Sg_scan0 } ]
      | Cursor_starts_at_latest -> [ { s with stage = Sg_scan2 } ])
  | Sg_scan0 -> [ { s with stage = Sg_scan1 } ]
  | Sg_scan1 -> (
      match s.store with
      | St_cert -> [ { s with stage = Sg_scan2 } ]
      | St_rec -> scan1_gap_next mut s)
  | Sg_scan2 -> [ s ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: epoch 1 is closing, the collective endorsement fact is
    not yet settled, V1's DB holds nothing for epoch 1 beyond the record it is
    about to write, and the Byzantine answer budget is intact. *)
let initial =
  { endorse = E_pending; store = St_rec; stage = Sg_close; byz = B_avail }

(** The atom vocabulary the three EPOCH_RECORD statements quantify over. *)
type atom =
  | Quorum_endorsed
      (** a super-quorum - 3 of the 4 epoch-1 committee members - signed
          [digest(R1)], V1's OWN record: [endorse] in \{[E_quorum3],
          [E_quorum4]\}. [super_quorum] = ((4 * 2) / 3) + 1 = 3
          (epoch.rs:94-96) *)
  | Some_record_certified
      (** a super-quorum signed SOME epoch-1 record - V1's R1 or the divergent
          R1': [endorse] in \{[E_quorum3], [E_quorum4], [E_alt]\}. This is
          exactly "a record/certificate pair that clears [verify_with_cert]
          (epoch.rs:59-88) exists somewhere for epoch 1" *)
  | Byz_endorsed
      (** the Byzantine committee member V3 also signed [digest(R1)]:
          [endorse] in \{[E_byz], [E_quorum4]\} - the fact V1 cannot resolve,
          because the aggregator freezes the bitmap at quorum
          (epoch_votes.rs:103-110) *)
  | Store_cert
      (** V1's epoch DB holds a certificate for its epoch-1 record:
          [store = St_cert], i.e. [get_epoch_by_number] returns
          [Some((rec, Some(cert)))] (epoch_records.rs:369-377) *)
  | Collector_past_epoch
      (** the collector's scan cursor has advanced above epoch 1:
          [stage = Sg_scan2], i.e. [result_epoch] > 1 (epoch.rs:61-64, :115,
          :147-149) - epoch 1 will not be revisited *)
  | Byz_cert_delivered
      (** the Byzantine peer has answered a [request_epoch_cert] for epoch 1
          with a sub-quorum certificate: [byz = B_spent] (epoch.rs:78 ->
          :102 [verify_with_cert] -> :129-136 error and retry) *)
  | Tally_quorum_held
      (** V1 is inside its own [manage_epoch_votes] window with
          [reached_quorum = true] (epoch_votes.rs:103-104): quorum-many
          individually verified signatures over [digest(R1)] are in hand and
          no certificate is persisted yet (the save is at :159).
          [stage = Sg_tally_quorum] *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Quorum_endorsed -> quorum_endorsed s.endorse
  | Some_record_certified -> some_record_certified s.endorse
  | Byz_endorsed -> byz_endorsed s.endorse
  | Store_cert -> store_has_cert s.store
  | Collector_past_epoch -> stage_past_epoch1 s.stage
  | Byz_cert_delivered -> byz_answer_spent s.byz
  | Tally_quorum_held -> stage_tally_quorum_held s.stage

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Quorum_endorsed -> "quorum_endorsed(R1)"
  | Some_record_certified -> "quorum_certified(some epoch-1 record)"
  | Byz_endorsed -> "byz_endorsed(R1)"
  | Store_cert -> "store_has_cert(1)"
  | Collector_past_epoch -> "cursor>1"
  | Byz_cert_delivered -> "byz_cert_delivered(1)"
  | Tally_quorum_held -> "tally_quorum_held(R1)"

(** The exact CTLK checker over this family's ordered state and view. *)
module Checker = System.Make (State) (View)

(** The checker spec under a mutation: single initial state,
    mutation-parameterized transitions, the single-agent view, the atom
    valuation. The endorsement choice is made by the [Sg_close] transition
    rather than by multiple initial states, so every branch is reachable
    through [next_with] and the mutation parameter reaches all of them. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
