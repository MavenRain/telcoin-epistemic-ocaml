(** Finite interpreted system for the EPOCH_CLOSE family: ONE epoch boundary
    (the close of epoch [e-1] and the entry into epoch [e]) as walked by the
    knowledge agent V1, in two disjoint scenario cones that branch out of a
    single start state. File citations refer to
    Telcoin-Association/telcoin-network (git HEAD 0c59c15b, working tree).

    BRANCH A - "I closed epoch e-1 myself". A committee member finalizes the
    epoch, writes its own record and then tries to certify it:
    - [write_epoch_record] builds the record and calls [save_record]
      (crates/node/src/manager/node/close_epoch.rs:238-249, save at :247),
      then publishes it on [epoch_record_watch] (:248) so the vote task starts.
      For any epoch > 0 an already-present record short-circuits the whole
      function unconditionally (close_epoch.rs:199-205);
    - [manage_epoch_votes] signs and gossips its own vote and collects peer
      votes (crates/node/src/manager/epoch_votes.rs:58-73 sign+publish,
      :83-144 the collector loop, quorum test :103-107, timeout break
      :130-134 with the [timeouts > 24] give-up). On quorum it aggregates and
      calls [save_certificate] keyed by its OWN record's digest (:152-173);
    - on failed quorum it makes up to FIVE [request_epoch_cert] attempts
      (epoch_votes.rs:196-231, content gate [verify_with_cert] at :200) and
      hands whatever verifies to [save_and_persist_with_logs] (:21-40) ->
      [EpochRecordDb::save] (crates/storage/src/epoch_records.rs:231-243) ->
      [Inner::save] (:597-617). CRITICALLY [Inner::save] computes the cert key
      from the FETCHED record's digest (:601, index write :612-614) and routes
      the record through [Inner::save_record] (:604), which returns [Ok(())]
      EARLY when the epoch slot is already filled (:568-582, guard :574-576).
      A committee member always filled that slot at close, so the peer's record
      is NOT stored and its certificate is filed under a digest that
      [get_epoch_by_number] - which looks the cert up by the STORED record's
      digest (:369-377, [cert_by_digest(record.digest())] at :375) - never
      queries. The "Over wrote expected epoch record" log at
      epoch_votes.rs:203-206 is therefore misleading: no overwrite happens, and
      a diverged member ends the boundary holding its own record with NO
      certificate attached.

      The load-bearing gate there is the DIGEST BINDING, not the idempotent
      early return. Nothing in this codebase can displace a filled epoch slot:
      delete :574-576 and [idx < len] falls into the out-of-order arm
      (:577-582), whose [Err] [Inner::save] propagates with [?] at :604 before
      the cert append at :611-614, so neither record nor cert lands; delete
      that arm too and [epoch_idx.save] still refuses, because
      [PositionIndex::save] takes only [key == len] and APPENDS rather than
      overwrites (crates/storage/src/archive/position_index/index.rs:247-261),
      an error propagated at :590-592. Hence the family's own-record-stability
      claim is pinned by no mutation - it is not a single gate but the
      append-only shape of the whole writer surface ([save_dummy_epoch0] :191
      writing a separate epoch-0 slot at :556-566, [save_record] :219, [save]
      :231, [save_certificate] :247 for certificates only; no delete/replace
      API exists) - while what a single deletion CAN break is the certificate's
      content-addressing, which is what {!No_cert_digest_binding} deletes.

      Branch A does not end at the settle. [run_epochs] loops straight into
      epoch e, whose [open_epoch_pack] finds [record_by_epoch(e-1)] present
      (run_epoch.rs:451-463) and opens the pack at :518 with NO certificate
      requirement - so an uncertified member opens the epoch pack exactly like
      a certified one.

    BRANCH B - "I have no record for epoch e-1". A node entering epoch [e]
    finds [record_by_epoch(e-1)] empty and takes [open_epoch_pack]'s
    missing-record branch (crates/node/src/manager/node/run_epoch.rs:444-520):
    - it PRE-DIALS the whole committee before blocking, guarded on
      [connected_peers_count() == 0] (:487-503), with the in-code rationale at
      :483-486 ("Without this we deadlock ... peer connections are only
      established in spawn_primary_network_for_epoch which runs after
      open_epoch_pack returns"). That ordering is real: [open_epoch_pack] is
      awaited at run_epoch.rs:219, [create_consensus] (which reaches
      [spawn_primary_network_for_epoch] and the per-epoch committee dial) only
      at :258-267. With zero connected peers every fetch route returns
      [NetworkError::NoPeers] (crates/network-libp2p/src/consensus.rs:868-880);
    - it then blocks in [record_by_epoch_with_timeout(e-1, 30s)]
      (epoch_records.rs:270-288) while the epoch-record collector races to
      fetch and store the record. The collector's three-conjunct content gate
      is [parents_match && epoch_committee_valid && epoch_valid], the last
      being [verify_with_cert] (crates/state-sync/src/epoch.rs:100-103); on
      success it calls [EpochRecordDb::save] into an EMPTY slot, so here the
      peer's record really is stored and its cert really is reachable through
      [get_epoch_by_number] (state-sync/epoch.rs:107). A rejected candidate is
      simply retried on the collector's 5s timer (state-sync/epoch.rs:202-212);
    - if the 30s expires the wait returns [None] and [open_epoch_pack] returns
      [Err] (run_epoch.rs:512-516), which [run_epochs] propagates with [?]
      (crates/node/src/manager/node.rs:1213-1240, the [?] at :1227), aborting
      the epoch loop. Acquisition is therefore a RACE, never a guarantee -
      which is why the liveness statement asserts [Ef], never [Af].

    THE SINGLE CONTENT GATE. [EpochRecord::verify_with_cert]
    (crates/types/src/primary/epoch.rs:59-89) is the sole place a
    certificate's super-quorum is established: it rejects a digest mismatch
    (:60-63), rebuilds the signer key vector from the bitmap (:65-79) and then
    demands [auth_iter >= self.super_quorum()] before the aggregate check
    (:84-88), with [super_quorum() = 2n/3 + 1] (:94-96). Its three production
    callers are epoch_votes.rs:156 (self-tally), epoch_votes.rs:200 (recovery)
    and state-sync/epoch.rs:102 (collector). Nothing downstream re-validates:
    [request_epoch_cert] rotates over up to three arbitrary peers and returns
    the raw bytes (crates/consensus/primary/src/network/mod.rs:809-829), and
    the storage layer only appends (epoch_records.rs:229-243, :597-617).

    COMPONENTS. Six observable: [stage] (pipeline position), [store] (what
    [get_epoch_by_number(e-1)] yields), [tally] (own vote-collection outcome),
    [cand] (an unverified peer response in hand), [peers] (connected-peer
    count), plus the derived response bit. Three hidden: [truth] (which record
    the committee's super-quorum actually signed - i.e. whether V1's own
    execution diverged), [byz] (a fourth committee member's vote that was cast
    but never arrived before the collector timed out), [held] (the provenance
    of the certificate material actually attached to the stored record).

    ROLE MAPPING. V1 is the ONLY knowledge agent and the only validator with a
    non-constant view. V0 is idle; V2 is the honest peer that answers
    [request_epoch_cert]; V3 is the byzantine committee member that is both the
    source of a lone-signature candidate and the caster of the unobserved
    fourth vote. V0, V2 and V3 all get the constant blank {!View_idle} and
    NEVER appear under [K]. *)

(** Where V1 sits in the epoch-boundary pipeline. [Sg_start] is the pre-branch
    root; [Sg_close] .. [Sg_settled] are branch A (I closed the epoch myself);
    [Sg_entry] .. [Sg_halt] are branch B (I have no record and must acquire
    one). *)
type stage =
  | Sg_start
      (** the pre-branch root: the environment (which record the committee
          actually endorsed, whether the fourth member voted, whether this node
          starts with peers) is not yet fixed *)
  | Sg_close
      (** branch A: [write_epoch_record] is about to build and save this
          node's own record for epoch e-1 (close_epoch.rs:238-249) *)
  | Sg_tally
      (** branch A: [manage_epoch_votes] has signed and gossiped this node's
          vote and is collecting peer votes (epoch_votes.rs:58-73, :83-144) *)
  | Sg_recover
      (** branch A: quorum was NOT reached, so the five-attempt
          [request_epoch_cert] recovery loop is running
          (epoch_votes.rs:188-231) *)
  | Sg_settled
      (** branch A: the boundary is over, with or without a certificate
          attached to this node's own record. Not terminal - [run_epochs]
          loops straight into epoch e, whose [open_epoch_pack] finds the
          record present and opens the pack (run_epoch.rs:219, :451-463,
          :518) *)
  | Sg_entry
      (** branch B: [open_epoch_pack] has found no record for epoch e-1 and is
          at the pre-dial decision (run_epoch.rs:473-503) *)
  | Sg_wait
      (** branch B: blocked in [record_by_epoch_with_timeout(e-1, 30s)] while
          the collector races to acquire the record
          (run_epoch.rs:505-510, epoch_records.rs:270-288) *)
  | Sg_open
      (** terminal: [consensus_chain.new_epoch] opened the pack for epoch e
          (run_epoch.rs:518). Reached BOTH ways - on branch B when the awaited
          record finally arrived (:505-511), and on branch A when the member
          that just closed e-1 re-enters [open_epoch_pack] and finds its own
          record already present (:451-463), certificate or not *)
  | Sg_halt
      (** branch B terminal: the 30s wait expired, [open_epoch_pack] returned
          [Err] (run_epoch.rs:512-516) and [run_epochs] aborted the epoch loop
          on the [?] at node.rs:1227 *)

(** Total order index for {!stage}. *)
let stage_index = function
  | Sg_start -> 0
  | Sg_close -> 1
  | Sg_tally -> 2
  | Sg_recover -> 3
  | Sg_settled -> 4
  | Sg_entry -> 5
  | Sg_wait -> 6
  | Sg_open -> 7
  | Sg_halt -> 8

(** Total order on {!stage}. *)
let stage_compare a b = Int.compare (stage_index a) (stage_index b)

(** What [get_epoch_by_number(e-1)] yields out of this node's epoch-record
    store (epoch_records.rs:369-377): the record it finds by epoch index,
    paired with the certificate found under THAT record's digest. *)
type store =
  | St_none  (** [None]: no record for epoch e-1 at all *)
  | St_own
      (** [Some((own_rec, None))]: this node's own record, no certificate
          under its digest *)
  | St_own_cert
      (** [Some((own_rec, Some(cert)))]: this node's own record with a
          certificate attached (epoch_votes.rs:159 saves it keyed by
          [cert.epoch_hash], which [verify_with_cert] pinned to the record's
          own digest at epoch.rs:60-63) *)
  | St_far_cert
      (** [Some((peer_rec, Some(cert)))]: a peer's record, stored into an
          EMPTY slot by the collector together with its certificate
          (state-sync/epoch.rs:107) *)

(** Total order index for {!store}. *)
let store_index = function
  | St_none -> 0
  | St_own -> 1
  | St_own_cert -> 2
  | St_far_cert -> 3

(** [true] iff [get_epoch_by_number(e-1)] yields any record at all. *)
let store_has_record = function
  | St_none -> false
  | St_own -> true
  | St_own_cert -> true
  | St_far_cert -> true

(** [true] iff the stored record is the one this node computed itself. *)
let store_is_own = function
  | St_none -> false
  | St_own -> true
  | St_own_cert -> true
  | St_far_cert -> false

(** [true] iff the stored record is a peer's rather than this node's own. *)
let store_is_foreign = function
  | St_none -> false
  | St_own -> false
  | St_own_cert -> false
  | St_far_cert -> true

(** [true] iff [get_epoch_by_number(e-1)] yields [Some((rec, Some(cert)))],
    i.e. a certificate is attached to the record actually stored. *)
let store_has_cert = function
  | St_none -> false
  | St_own -> false
  | St_own_cert -> true
  | St_far_cert -> true

(** The outcome of this node's own vote collection
    (epoch_votes.rs:94-111 with the threshold at :103). *)
type tally =
  | Tl_pending  (** the collector loop has not finished *)
  | Tl_quorum
      (** [signed_authorities.len() >= quorum]: a super-quorum of votes on this
          node's OWN digest was observed (epoch_votes.rs:103-107) *)
  | Tl_short
      (** the loop broke without quorum - either the [timeouts > 24] give-up
          (epoch_votes.rs:130-134) or a quorum observed on an ALTERNATIVE
          digest (:112-128) *)

(** Total order index for {!tally}. *)
let tally_index = function Tl_pending -> 0 | Tl_quorum -> 1 | Tl_short -> 2

(** [true] iff the vote collection ended without quorum on this node's own
    record. *)
let tally_is_short = function
  | Tl_pending -> false
  | Tl_quorum -> false
  | Tl_short -> true

(** An unverified peer response currently in hand. [request_epoch_cert]
    (network/mod.rs:809-829) rotates over up to three arbitrary peers and
    returns [(EpochRecord, EpochCertificate)] with NO network-layer
    validation, so the FLAVOUR of what is in hand is not observable until
    [verify_with_cert] runs. *)
type cand =
  | Cd_none  (** no response in hand *)
  | Cd_sound
      (** a genuinely super-quorum-certified record: [verify_with_cert] will
          accept it (epoch.rs:84-88) *)
  | Cd_lone
      (** a lone byzantine member's record carrying a certificate with ONE
          genuine signature: the aggregate verifies but [auth_iter <
          super_quorum()], so [verify_with_cert] rejects it pristine *)

(** Total order index for {!cand}. *)
let cand_index = function Cd_none -> 0 | Cd_sound -> 1 | Cd_lone -> 2

(** [true] iff any response is in hand - this bit, and NOT the flavour, is
    what V1 observes. *)
let cand_in_hand = function
  | Cd_none -> false
  | Cd_sound -> true
  | Cd_lone -> true

(** [true] iff the response in hand would survive [verify_with_cert]. *)
let cand_is_sound = function
  | Cd_none -> false
  | Cd_sound -> true
  | Cd_lone -> false

(** This node's connected-peer count as [open_epoch_pack] reads it
    (run_epoch.rs:489). *)
type peers =
  | Pr_none
      (** [connected_peers_count() == 0]: every [send_request_any] returns
          [NetworkError::NoPeers] (consensus.rs:868-880) *)
  | Pr_some  (** at least one peer is connected, so fetches can be answered *)

(** Total order index for {!peers}. *)
let peers_index = function Pr_none -> 0 | Pr_some -> 1

(** [true] iff at least one peer is connected. *)
let peers_connected = function Pr_none -> false | Pr_some -> true

(** HIDDEN. Which record epoch e-1's committee super-quorum actually signed -
    a fact about the OTHER validators' execution outputs and signing acts
    (each member signs its own computed record, epoch_votes.rs:58-73). V1 is
    never told this: on branch A it only ever sees how many votes reached its
    own collector before the timeout. *)
type truth =
  | Tr_undecided
      (** only at {!Sg_start}, so that no endorsement atom takes an arbitrary
          value before the environment is fixed by the first transition *)
  | Tr_own
      (** the super-quorum signed the record V1 computed: V1's execution
          agreed with the committee *)
  | Tr_far
      (** the super-quorum signed a DIFFERENT record: V1's execution diverged
          (branch A), or V1 never computed one at all (branch B) *)

(** Total order index for {!truth}. *)
let truth_index = function Tr_undecided -> 0 | Tr_own -> 1 | Tr_far -> 2

(** [true] iff the committee's super-quorum endorsed a record other than the
    one V1 computed. *)
let truth_is_far = function
  | Tr_undecided -> false
  | Tr_own -> false
  | Tr_far -> true

(** HIDDEN spectator. Whether the fourth committee member cast a vote for the
    endorsed record that never reached V1's collector before it timed out.
    Gossip is best-effort ([publish_epoch_vote] is fire-and-forget,
    epoch_votes.rs:71 and the republish at :137-139) and the loop breaks on
    [timeouts > 24] (:130-134), so a cast-but-unseen vote is a real
    possibility. Nothing in the transition relation reads this field: it exists
    solely to keep V1's view classes non-singleton, which is what makes the
    positive knowledge claims non-degenerate (rule R2). *)
type byz =
  | Bz_silent  (** the fourth member never voted *)
  | Bz_signed
      (** the fourth member voted for the endorsed record, and V1 never saw it *)

(** Total order index for {!byz}. *)
let byz_index = function Bz_silent -> 0 | Bz_signed -> 1

(** [true] iff the fourth committee member cast the unobserved vote. *)
let byz_voted = function Bz_silent -> false | Bz_signed -> true

(** HIDDEN. The provenance of the certificate material actually attached to
    the record that [get_epoch_by_number(e-1)] returns. Pristine this is a
    function of {!store} precisely BECAUSE the super-quorum count in
    [verify_with_cert] (epoch.rs:84-88) gates every path into the store; the
    mutation is exactly what breaks that alignment. It is never projected into
    any view. *)
type held =
  | Hd_none  (** no certificate is attached to the stored record *)
  | Hd_quorum
      (** the attached certificate carries at least [2n/3 + 1] genuine
          committee signatures on the stored record *)
  | Hd_lone
      (** the attached certificate carries a SINGLE genuine signature: only
          reachable once the super-quorum count is deleted *)
  | Hd_far
      (** the attached certificate is a genuine super-quorum certificate, but
          on a DIFFERENT record than the one sitting in the epoch slot: the
          material a diverged member fetches during recovery. Pristine this is
          unreachable, because [Inner::save] files that certificate under the
          FETCHED record's digest (epoch_records.rs:601, :612-614) while
          [get_epoch_by_number] resolves it by the STORED record's digest
          (:374-375); it becomes reachable exactly when that content-addressing
          is deleted *)

(** Total order index for {!held}. *)
let held_index = function
  | Hd_none -> 0
  | Hd_quorum -> 1
  | Hd_lone -> 2
  | Hd_far -> 3

(** [true] iff a super-quorum of epoch e-1's committee signed the record that
    V1's store currently returns. [Hd_far] is a super-quorum certificate on
    ANOTHER record, so it does not back the stored one. *)
let held_is_quorum = function
  | Hd_none -> false
  | Hd_quorum -> true
  | Hd_lone -> false
  | Hd_far -> false

(** The joint global state: six observable components and three hidden ones
    ([truth], [byz], [held]). *)
type state = {
  stage : stage;  (** V1's position in the epoch-boundary pipeline *)
  store : store;  (** what [get_epoch_by_number(e-1)] yields *)
  tally : tally;  (** V1's own vote-collection outcome *)
  cand : cand;  (** the unverified peer response in hand, if any *)
  peers : peers;  (** V1's connected-peer count *)
  truth : truth;  (** HIDDEN: which record the committee actually endorsed *)
  byz : byz;  (** HIDDEN: the unobserved fourth vote *)
  held : held;  (** HIDDEN: provenance of the stored record's certificate *)
}

(** Total deterministic comparison over ALL eight state fields. *)
let state_compare s1 s2 =
  let c = stage_compare s1.stage s2.stage in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Int.compare (store_index s1.store) (store_index s2.store) in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Int.compare (tally_index s1.tally) (tally_index s2.tally) in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Int.compare (cand_index s1.cand) (cand_index s2.cand) in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Int.compare (peers_index s1.peers) (peers_index s2.peers) in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Int.compare (truth_index s1.truth) (truth_index s2.truth) in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = Int.compare (byz_index s1.byz) (byz_index s2.byz) in
              if Bool.not (Int.equal c6 0) then c6
              else Int.compare (held_index s1.held) (held_index s2.held)

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    [View_v1] is V1's projection - (stage, store, tally, response-in-hand,
    peers). V1 SEES: its own pipeline position; its own epoch-record store
    exactly as every consumer reads it ([get_epoch_by_number]); its own
    vote-tally outcome; whether an unverified peer response is currently in
    hand; and its connected-peer count (run_epoch.rs:489). V1 does NOT see:
    (i) [truth] - which record the committee's super-quorum actually signed,
    hence whether its own execution diverged; (ii) the FLAVOUR of the response
    bytes - [Cd_sound] and [Cd_lone] collapse to the same bool, because
    [request_epoch_cert] hands back unvalidated peer bytes
    (network/mod.rs:809-829) and [verify_with_cert] is the only thing that
    separates them; (iii) [byz] - whether the fourth committee member cast a
    vote that never arrived (epoch_votes.rs:130-140); (iv) [held] - the
    provenance of the certificate material that actually got stored.

    [View_idle] is the constant blank view of the non-agents V0 (idle), V2
    (the honest serving peer behind [request_epoch_cert]) and V3 (the
    byzantine member); none of them ever appears under [K]. *)
type view =
  | View_v1 of stage * store * tally * bool * peers
  | View_idle

(** Total deterministic order over ALL fields of V1's view. *)
let view_v1_compare (sg, st, tl, cd, pr) (sg', st', tl', cd', pr') =
  let c = stage_compare sg sg' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Int.compare (store_index st) (store_index st') in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Int.compare (tally_index tl) (tally_index tl') in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare cd cd' in
        if Bool.not (Int.equal c3 0) then c3
        else Int.compare (peers_index pr) (peers_index pr')

(** Total order on views: [View_idle] < [View_v1], with the field-wise order
    within the agent constructor. Every constructor pair is spelled: no
    wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_v1 _ -> -1
  | View_v1 _, View_idle -> 1
  | View_v1 (sg, st, tl, cd, pr), View_v1 (sg', st', tl', cd', pr') ->
      view_v1_compare (sg, st, tl, cd, pr) (sg', st', tl', cd', pr')

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 is the sole knowledge agent; V0, V2 and V3 are idle
    non-agents with the constant blank view and never appear under [K]. The
    candidate is projected as the bare bit [cand_in_hand], NOT its flavour -
    that coarsening is the whole epistemic content of "an unverified peer
    response is merely in hand". *)
let view v s =
  match v with
  | Validator.V1 ->
      View_v1 (s.stage, s.store, s.tally, cand_in_hand s.cand, s.peers)
  | Validator.V0 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine  (** the faithful model *)
  | No_cert_quorum_count
      (** delete the [if auth_iter < self.super_quorum() { false } else { ... }]
          tail of [EpochRecord::verify_with_cert]
          (crates/types/src/primary/epoch.rs:84-88, [super_quorum] = 2n/3+1 at
          :94-96), so a certificate carrying a SINGLE genuine signature
          verifies. Adds (Sg_wait, Pr_some, Cd_lone) -> (Sg_open, St_far_cert,
          held = Hd_lone): the entry-blocking node adopts and stores a record
          only one (byzantine) committee member ever signed. Branch A is
          observationally unchanged, because accepting a lone-signed FOREIGN
          record there only files a cert under a digest
          [get_epoch_by_number] never queries (the idempotent save,
          epoch_records.rs:574-576). NO SIBLING REPAIRS IT: (1) the deletion
          is at the shared DEFINITION and all three production callers
          (epoch_votes.rs:156, :200, state-sync/epoch.rs:102) go through it;
          (2) the network layer does not verify - [request_epoch_cert]
          (network/mod.rs:809-829) returns peer bytes as-is; (3) storage only
          appends ([EpochRecordDb::save] epoch_records.rs:229-243 ->
          [Inner::save] :597-617); (4) once the poisoned entry IS stored the
          collector cannot re-examine it, because [get_epoch_by_number]
          returns [Some((rec, Some(_)))] and [collect_epoch_records] hits the
          [continue] at state-sync/epoch.rs:61-76; (5) [open_epoch_pack] tests
          presence only (run_epoch.rs:451-463); (6) [write_epoch_record]
          short-circuits on an existing record (close_epoch.rs:199-205);
          (7) [verify_epoch_meta] (consensus_pack.rs:1319-1364) rejects later
          imports that disagree with the poisoned record - a detector, never a
          repair of what is stored. *)
  | No_cert_digest_binding
      (** delete the content-addressing of the certificate index inside
          [Inner::save] (crates/storage/src/epoch_records.rs:597-617): the
          fetched certificate is filed under [record_digest = record.digest()]
          of the FETCHED record (:601, index write at :612-614), while
          [get_epoch_by_number] resolves a stored record's certificate by the
          STORED record's digest ([cert_by_digest(record.digest())],
          :374-375). Deleting that binding - filing the arriving certificate
          under the epoch slot's own record digest instead - adds
          (Sg_recover, Cd_sound, Tr_far) -> (Sg_settled, St_own_cert, held =
          Hd_far): the diverged member's own record stays exactly where it was
          (nothing in this codebase can displace a filled slot) but now
          answers [get_epoch_by_number] WITH a certificate, one that a
          super-quorum signed over a DIFFERENT record. This is the gate the
          family's earlier [No_record_idempotence] mutation got wrong:
          deleting the already-stored early return (:574-576) does NOT
          displace anything, because [idx < len] then falls into the
          out-of-order arm (:577-582) and [Inner::save] propagates that [Err]
          with [?] at :604 BEFORE the cert append at :611-614 - store
          unchanged - and even that guard removed, [epoch_idx] is a
          [PositionIndex<u64>] whose [save] rejects any key other than [len]
          and appends rather than overwrites
          (archive/position_index/index.rs:247-261). NO SIBLING REPAIRS THIS
          ONE: (1) nothing re-verifies the pair on read - [get_epoch_by_number]
          just pairs record and cert (:370-377) and the serving path hands the
          pair straight out (crates/node/src/lib.rs:88-94); (2) the collector,
          the only background writer that could refill the slot, SKIPS any
          epoch whose [get_epoch_by_number] already yields [Some((rec,
          Some(_)))] (state-sync/epoch.rs:61-76), so the bogus attachment
          disables the one repair path; (3) [write_epoch_record]
          short-circuits unconditionally on an existing record for any epoch >
          0 (close_epoch.rs:199-205); (4) [manage_epoch_votes] is never
          re-entered for the same epoch - [get_new_vote_channel] [take()]s the
          receiver once and returns [None] thereafter
          (epoch_votes.rs:236-248); (5) a fetching PEER would reject the
          mismatched pair on [verify_with_cert]'s digest check
          (types/src/primary/epoch.rs:60-63) - a downstream detector, never a
          repair of what this node's own store returns. *)
  | No_committee_predial
      (** delete the [if connected_peers_count() == 0 {
          prepare_committee_dial(...); for bls_key in committee.bls_keys() {
          dial_peer_bls(...) } }] block in [open_epoch_pack]'s missing-record
          branch (crates/node/src/manager/node/run_epoch.rs:487-503, in-code
          rationale at :483-486). Removes (Sg_entry, Pr_none) -> (Sg_wait,
          Pr_some) and replaces it with (Sg_entry, Pr_none) -> (Sg_wait,
          Pr_none), whose only successor is [Sg_halt]: the zero-peer wait
          state, unreachable pristine, becomes reachable and can no longer
          reach [Sg_open]. NO SIBLING REPAIRS IT - two candidates exist and
          BOTH are already encoded here: (1) [dial_peer_bls] tasks spawned in
          a PREVIOUS [run_epoch] iteration live on the node-lifetime spawner
          and keep retrying across epochs (start_epoch.rs:567-586, doc at
          :569-573) - that is exactly the (Sg_entry, Pr_some) start line,
          which this mutation deliberately leaves intact, and the statement
          survives it because it quantifies over EVERY waiting state including
          the zero-peer one that only the pre-dial can rescue;
          (2) bootstrap-peer registration and the per-epoch committee dial
          happen inside [init_network_for_epoch] (start_epoch.rs:772-787,
          [add_bootstrap_peers] at :780-782) and start_epoch.rs:526-543, both
          reached only via [spawn_primary_network_for_epoch] inside
          [create_consensus], which [run_epoch] calls at :258-267 - strictly
          AFTER [open_epoch_pack] at :219, so they cannot repair this
          iteration. The collector's 5s retry (state-sync/epoch.rs:202-212)
          re-attempts, but every attempt still returns
          [NetworkError::NoPeers] (consensus.rs:868-880). *)

(** The four branch-A openings out of {!Sg_start}: a committee member that
    closed epoch e-1 itself, with peers connected (it just ran a whole epoch),
    over both endorsement truths and both values of the unobserved fourth
    vote. *)
let branch_a_starts s =
  List.concat_map
    (fun tr ->
      List.map
        (fun bz -> { s with stage = Sg_close; peers = Pr_some; truth = tr; byz = bz })
        [ Bz_silent; Bz_signed ])
    [ Tr_own; Tr_far ]

(** The four branch-B openings out of {!Sg_start}: a node with NO record for
    epoch e-1, over both connected-peer counts (a fresh restart has none, an
    already-dialing node has some) and both values of the unobserved fourth
    vote. [truth] is [Tr_far] throughout: V1 computed no record of its own, so
    whatever the committee endorsed is by construction not V1's. *)
let branch_b_starts s =
  List.concat_map
    (fun pr ->
      List.map
        (fun bz -> { s with stage = Sg_entry; peers = pr; truth = Tr_far; byz = bz })
        [ Bz_silent; Bz_signed ])
    [ Pr_none; Pr_some ]

(** Branch A, the [Sg_tally] step: [manage_epoch_votes] finishes collecting.
    With [Tr_own] the committee endorsed V1's own record, so V1 either observes
    the super-quorum (epoch_votes.rs:103-107, then aggregate + save_certificate
    at :152-173) or times out short of it (:130-134); with [Tr_far] only the
    short outcome is possible, because with n = 4 and f = 1 a super-quorum on
    ANOTHER record leaves at most two signatures available for V1's own. *)
let tally_next s =
  match s.truth with
  | Tr_own ->
      [
        { s with stage = Sg_settled; store = St_own_cert; tally = Tl_quorum; held = Hd_quorum };
        { s with stage = Sg_recover; tally = Tl_short };
      ]
  | Tr_far -> [ { s with stage = Sg_recover; tally = Tl_short } ]
  | Tr_undecided -> []

(** Branch A, the [Sg_recover] step: the five-attempt [request_epoch_cert]
    recovery loop (epoch_votes.rs:196-231). With nothing in hand a fetch either
    returns sound bytes, returns a lone-signed candidate, or all five attempts
    fail and the loop gives up (:225-231). A sound candidate whose digest
    matches V1's own record simply attaches the certificate
    ([Inner::save] files it under the fetched record's digest, which here IS
    V1's own, and [Inner::save_record] returns [Ok(())] early on the
    already-filled slot so the append is reached, epoch_records.rs:574-576 then
    :607-614). A sound candidate for a DIFFERENT record leaves
    [get_epoch_by_number] answering exactly as before: the record is NOT
    displaced (the slot is filled, and no writer in this codebase can replace a
    filled slot - :574-582 plus the append-only [PositionIndex]
    archive/position_index/index.rs:247-261) and the certificate is filed under
    the PEER's digest (:601, :612-614), which the [cert_by_digest(record
    .digest())] lookup at :374-375 never queries. Deleting that digest binding
    is what makes the diverged member look certified. A lone candidate is
    rejected by [verify_with_cert] under EVERY mutation here: pristine the
    quorum count rejects it, and with the count deleted its certificate is
    still filed under the peer's digest, so branch A is observationally
    unchanged either way. *)
let recover_next mut s =
  match s.cand with
  | Cd_none ->
      [
        { s with cand = Cd_sound };
        { s with cand = Cd_lone };
        { s with stage = Sg_settled };
      ]
  | Cd_sound -> (
      match s.truth with
      | Tr_own ->
          [
            {
              s with
              stage = Sg_settled;
              store = St_own_cert;
              cand = Cd_none;
              held = Hd_quorum;
            };
          ]
      | Tr_far -> (
          match mut with
          | Pristine -> [ { s with stage = Sg_settled; cand = Cd_none } ]
          | No_cert_quorum_count -> [ { s with stage = Sg_settled; cand = Cd_none } ]
          | No_committee_predial -> [ { s with stage = Sg_settled; cand = Cd_none } ]
          | No_cert_digest_binding ->
              [
                {
                  s with
                  stage = Sg_settled;
                  store = St_own_cert;
                  cand = Cd_none;
                  held = Hd_far;
                };
              ])
      | Tr_undecided -> [])
  | Cd_lone -> [ { s with cand = Cd_none } ]

(** Branch B, the [Sg_entry] step: [open_epoch_pack] (run_epoch.rs:444-520).
    With a record already present it goes straight on to open the pack
    (:451-463); those arms are unreachable from [Sg_entry], which by
    construction is the empty-slot entry, but the branch they describe is
    modelled - it is the [Sg_settled] -> [Sg_open] edge a member takes when it
    re-enters [open_epoch_pack] holding the record it wrote itself. With no
    record
    it pre-dials the whole committee when the connected-peer count is zero
    (:487-503) and then blocks; with peers already connected the [== 0] guard
    at :489 skips the pre-dial. Deleting the pre-dial leaves the zero-peer node
    blocking with no peers at all. *)
let entry_next mut s =
  match s.store with
  | St_none -> (
      match s.peers with
      | Pr_none -> (
          match mut with
          | Pristine -> [ { s with stage = Sg_wait; peers = Pr_some } ]
          | No_cert_quorum_count -> [ { s with stage = Sg_wait; peers = Pr_some } ]
          | No_cert_digest_binding -> [ { s with stage = Sg_wait; peers = Pr_some } ]
          | No_committee_predial -> [ { s with stage = Sg_wait } ])
      | Pr_some -> [ { s with stage = Sg_wait } ])
  | St_own -> [ { s with stage = Sg_open } ]
  | St_own_cert -> [ { s with stage = Sg_open } ]
  | St_far_cert -> [ { s with stage = Sg_open } ]

(** Branch B, the [Sg_wait] step: blocked in
    [record_by_epoch_with_timeout(e-1, 30s)] (epoch_records.rs:270-288) while
    the collector races. With no peers every fetch attempt returns
    [NetworkError::NoPeers] (consensus.rs:868-880), so the only outcome is the
    30s expiry -> [Err] (run_epoch.rs:512-516) -> the [?] at node.rs:1227.
    With peers, a fetch either brings back sound bytes, brings back a
    lone-signed candidate, or the deadline expires first. Sound bytes clear the
    collector's three-conjunct gate (state-sync/epoch.rs:100-103) and are saved
    into the EMPTY slot together with their certificate (:107), so
    [get_epoch_by_number] now yields the peer's record WITH a cert. A lone
    candidate is rejected pristine and the collector simply retries on its 5s
    timer (state-sync/epoch.rs:202-212); with the super-quorum count deleted it
    is accepted and stored instead. *)
let wait_next mut s =
  match s.peers with
  | Pr_none -> [ { s with stage = Sg_halt } ]
  | Pr_some -> (
      match s.cand with
      | Cd_none ->
          [
            { s with cand = Cd_sound };
            { s with cand = Cd_lone };
            { s with stage = Sg_halt };
          ]
      | Cd_sound ->
          [
            {
              s with
              stage = Sg_open;
              store = St_far_cert;
              cand = Cd_none;
              held = Hd_quorum;
            };
          ]
      | Cd_lone -> (
          match mut with
          | Pristine -> [ { s with cand = Cd_none } ]
          | No_cert_digest_binding -> [ { s with cand = Cd_none } ]
          | No_committee_predial -> [ { s with cand = Cd_none } ]
          | No_cert_quorum_count ->
              [
                {
                  s with
                  stage = Sg_open;
                  store = St_far_cert;
                  cand = Cd_none;
                  held = Hd_lone;
                };
              ]))

(** The transition relation under a mutation. [Sg_start] fans out into the two
    disjoint scenario cones; [Sg_close] writes and publishes V1's own record
    (close_epoch.rs:238-249); [Sg_open] and [Sg_halt] are terminal and
    stutter-closed by the kernel.

    [Sg_settled] is NOT terminal: [run_epochs] loops, so the member that just
    closed epoch e-1 immediately runs epoch e and awaits [open_epoch_pack]
    (run_epoch.rs:219). That call takes the FOUND-record branch - it reads
    [record_by_epoch(previous_epoch)] (:451-452), and on [Some] it only nudges
    [requested_missing_epoch] (:453-463) - and then opens the pack at
    [consensus_chain.new_epoch(previous_epoch_rec, committee)] (:518). There is
    NO certificate requirement anywhere on that path: a member that ended the
    boundary with an uncertified own record still opens the pack. Modelling
    that edge is what keeps [opened] honest - it makes [opened /\\ ~holds_cert]
    reachable, which is exactly why S3's acquired-record knowledge conjunct is
    relativised to [holds_foreign_record] rather than asserted of every opened
    state. *)
let next_with mut s =
  match s.stage with
  | Sg_start -> List.append (branch_a_starts s) (branch_b_starts s)
  | Sg_close -> [ { s with stage = Sg_tally; store = St_own } ]
  | Sg_tally -> tally_next s
  | Sg_recover -> recover_next mut s
  | Sg_settled -> [ { s with stage = Sg_open } ]
  | Sg_entry -> entry_next mut s
  | Sg_wait -> wait_next mut s
  | Sg_open -> []
  | Sg_halt -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The single initial state: the pre-branch root, with [Tr_undecided] so that
    no endorsement atom takes an arbitrary value before the environment is
    fixed by the first transition. *)
let initial =
  {
    stage = Sg_start;
    store = St_none;
    tally = Tl_pending;
    cand = Cd_none;
    peers = Pr_none;
    truth = Tr_undecided;
    byz = Bz_silent;
    held = Hd_none;
  }

(** The atom vocabulary this family's statements quantify over. The last four
    are HIDDEN: none of them is a component of any view. *)
type atom =
  | Holds_record
      (** [get_epoch_by_number(e-1)] yields a record at all
          (run_epoch.rs:451-463 tests exactly this) *)
  | Holds_own_record
      (** the stored record for epoch e-1 is the one V1 computed itself
          (close_epoch.rs:247) *)
  | Holds_foreign_record
      (** the stored record for epoch e-1 is a peer's, acquired through the
          collector (state-sync/epoch.rs:107) *)
  | Holds_cert
      (** [get_epoch_by_number(e-1)] yields [Some((rec, Some(cert)))]:
          a certificate is attached to the record actually stored
          (epoch_records.rs:369-377) *)
  | Response_in_hand
      (** an unverified [request_epoch_cert] response is currently in hand
          (network/mod.rs:809-829) *)
  | Tally_short
      (** V1's own vote collection ended without quorum on its own record
          (epoch_votes.rs:130-134) *)
  | Peers_connected
      (** [connected_peers_count() > 0] (run_epoch.rs:489,
          consensus.rs:868-880) *)
  | Settled  (** branch A is over: the epoch boundary has been left behind *)
  | Waiting
      (** V1 is blocked in the missing-record wait
          (run_epoch.rs:505-510) *)
  | Opened
      (** [consensus_chain.new_epoch] opened the pack (run_epoch.rs:518) *)
  | Halted
      (** the wait expired and the epoch loop aborted (run_epoch.rs:512-516,
          node.rs:1227) *)
  | Quorum_backs_stored
      (** HIDDEN: at least [2n/3 + 1] members of epoch e-1's committee signed
          the record V1's store currently returns *)
  | Candidate_sound
      (** HIDDEN (coarsened out of V1's view): the response in hand would
          survive [verify_with_cert] (epoch.rs:59-89) *)
  | Committee_chose_other
      (** HIDDEN: the committee's super-quorum signed a record other than the
          one V1 computed - i.e. V1's execution diverged *)
  | Byz_fourth_vote
      (** HIDDEN spectator: the fourth committee member cast a vote that never
          reached V1's collector (epoch_votes.rs:130-140) *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Holds_record -> store_has_record s.store
  | Holds_own_record -> store_is_own s.store
  | Holds_foreign_record -> store_is_foreign s.store
  | Holds_cert -> store_has_cert s.store
  | Response_in_hand -> cand_in_hand s.cand
  | Tally_short -> tally_is_short s.tally
  | Peers_connected -> peers_connected s.peers
  | Settled -> ( match s.stage with
      | Sg_settled -> true
      | Sg_start -> false
      | Sg_close -> false
      | Sg_tally -> false
      | Sg_recover -> false
      | Sg_entry -> false
      | Sg_wait -> false
      | Sg_open -> false
      | Sg_halt -> false)
  | Waiting -> ( match s.stage with
      | Sg_wait -> true
      | Sg_start -> false
      | Sg_close -> false
      | Sg_tally -> false
      | Sg_recover -> false
      | Sg_settled -> false
      | Sg_entry -> false
      | Sg_open -> false
      | Sg_halt -> false)
  | Opened -> ( match s.stage with
      | Sg_open -> true
      | Sg_start -> false
      | Sg_close -> false
      | Sg_tally -> false
      | Sg_recover -> false
      | Sg_settled -> false
      | Sg_entry -> false
      | Sg_wait -> false
      | Sg_halt -> false)
  | Halted -> ( match s.stage with
      | Sg_halt -> true
      | Sg_start -> false
      | Sg_close -> false
      | Sg_tally -> false
      | Sg_recover -> false
      | Sg_settled -> false
      | Sg_entry -> false
      | Sg_wait -> false
      | Sg_open -> false)
  | Quorum_backs_stored -> held_is_quorum s.held
  | Candidate_sound -> cand_is_sound s.cand
  | Committee_chose_other -> truth_is_far s.truth
  | Byz_fourth_vote -> byz_voted s.byz

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Holds_record -> "holds_record(e-1)"
  | Holds_own_record -> "holds_own_record(e-1)"
  | Holds_foreign_record -> "holds_foreign_record(e-1)"
  | Holds_cert -> "holds_cert(e-1)"
  | Response_in_hand -> "response_in_hand"
  | Tally_short -> "tally_short"
  | Peers_connected -> "peers_connected"
  | Settled -> "settled"
  | Waiting -> "waiting"
  | Opened -> "opened"
  | Halted -> "halted"
  | Quorum_backs_stored -> "quorum_backs_stored"
  | Candidate_sound -> "candidate_sound"
  | Committee_chose_other -> "committee_chose_other"
  | Byz_fourth_vote -> "byz_fourth_vote"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml).

    This family's reachability relation is a PREORDER rather than a poset: it
    models a mechanism that undoes itself, so two distinct states can be
    mutually reachable and {!Frame.certify_functorial} refuses antisymmetry.
    That is recorded in test/t_topos_frames.ml and it does not obstruct the
    denotation: [W] is still a thin category, so parallel arrows are still
    unique and presheaf restriction is still path-independent, and the
    executable reduction gate is green on this family. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: single initial state, mutation-
    parameterized transitions, the single-agent view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
