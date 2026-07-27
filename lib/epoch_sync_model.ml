(** Finite interpreted system for the EPOCH_SYNC family: the TRUSTLESS
    epoch-record sync loop of telcoin-network, i.e. how a node that is behind
    obtains the certified {!EpochRecord} of an epoch it never executed, and
    thereby learns the successor committee. File citations refer to
    Telcoin-Association/telcoin-network (git HEAD 0c59c15b), read in this
    checkout.

    The modeled mechanism ([crates/state-sync/src/epoch.rs:46-150],
    [collect_epoch_records]), scoped to ONE syncing node walking ONE epoch
    [e = 1] on a STABLE validator set, already holding the certified record
    [R_0] for [e - 1] (the [prev] of epoch.rs:88-90, carried as background, not
    as a state component):

    - FETCH: [primary_handle.request_epoch_cert(Some(epoch), None)]
      (epoch.rs:78) names the epoch on the wire
      ([PrimaryRequest::EpochRecord { epoch, hash }], mod.rs:815) and is served
      by [send_request_any] (mod.rs:819) - a rotation over EVERY connected peer
      with no committee filter (consensus.rs:868-881 rotating
      [connected_peers], which consensus.rs:1616 push_back's unconditionally).
      The responder identity is destructured away at the single call site
      ([peer: _], mod.rs:821).
    - GATE: [parents_match && epoch_committee_valid && epoch_valid]
      (epoch.rs:100-103), where [parents_match] compares [prev.digest()] with
      [epoch_rec.parent_hash], [epoch_committee_valid] compares committee SETS
      (epoch.rs:22-44) and [epoch_valid] is
      [EpochRecord::verify_with_cert] (types/primary/epoch.rs:59-89). There is
      NO [epoch_rec.epoch == epoch] comparison anywhere in the branch
      (epoch.rs:78-137 read in full), so the parent-hash conjunct is the only
      thing binding the response to the epoch that was requested.
    - ADOPT: [save(epoch_rec, cert)] (epoch.rs:107) then
      [result_epoch = epoch] (epoch.rs:115) on the strength of [save] returning
      [Ok]. [save]/[save_record] key strictly by [record.epoch]
      (epoch_records.rs:570-576, idx = epoch - start_epoch) and return
      [Ok(())] IDEMPOTENTLY, storing nothing, when that epoch is already
      present - so a replayed older record makes the save report success while
      leaving the DB with no entry under [e].
    - REJECT: any failed conjunct only [error!]s the three booleans
      (epoch.rs:129-135) and returns [epoch.saturating_sub(1)] (:136). No
      penalty is ever reported: [rg 'report_penalty|Penalty'
      crates/state-sync/src/] is EMPTY, even though
      network-libp2p/src/types.rs:383-393 documents that the [SendRequestAny]
      caller must report peers returning bad data. The 5s retry
      (epoch.rs:206-212) then re-runs the whole attempt with no memory.

    Components (five):
    - [phase] - the collector's program point in one attempt;
    - [resp] - the HIDDEN response shape the anonymous responder chose;
    - [src] - the HIDDEN responder role (committee member or unauthenticated
      observer);
    - [store] - the syncing node's epoch DB at key [e];
    - [marked] - whether [result_epoch] has advanced to [e] (epoch.rs:115),
      which persists as the next call's [last_epoch].

    Role mapping (a knowledge agent must be a validator with a real,
    non-constant view; a blank-view party may never appear under K):
    - V1 is the ONLY knowledge agent: the syncing node running
      [collect_epoch_records]. Its view is [(phase, holds_record(e), marked)].
    - V0, V2 and V3 are idle non-agents with the constant blank view and NEVER
      appear under K. This is deliberate: the responder in this protocol need
      not be a {!Validator.t} at all - any synced non-committee full node
      legally serves the record from local storage
      (handler.rs:990-1003, no authorization) - so the responder is modeled as
      the hidden [src] component rather than as a validator.

    What V1 does NOT see, and why:
    - [src]: structurally destroyed at mod.rs:821 ([peer: _]); the certificate
      names SIGNERS of epoch e (types/primary/epoch.rs:130-145,
      [signed_authorities]),
      never the server; and no penalty path ever names the responder.
    - [resp]: which of the three shapes an untrusted peer chose is a hidden
      adversary branch.
    - WHICH record sits in the store: {!store_holds} collapses [Store_genuine]
      and [Store_forged] to [true], because a node that adopted a forged record
      cannot tell it apart from the genuine one.
    - the INDIVIDUAL gate booleans: epoch.rs:103 branches only on their
      CONJUNCTION and the individual values reach nothing but the [error!] log
      at :129-135, so the collector's control state - hence V1's view - carries
      [Adopted] vs [Rejected], not the conjuncts.

    HONESTY CAVEAT, stated openly rather than hidden: the family is scoped to a
    STABLE validator set. On a stable set [epoch_committee_valid]'s [Equal]
    branch (epoch.rs:28) accepts a replayed older record, and with 4 validators
    the [Greater] branch (epoch.rs:29-42) is unreachable, so exact set equality
    is what is enforced. {!committee_ok} therefore encodes that conjunct as
    constant-true: it repairs NEITHER gate deletion. epoch.rs:18-21 itself notes
    these sets "will usually be equal", so this is a real reachable
    configuration, not an omission. If the committee rotates between e-1 and e,
    [epoch_committee_valid] does catch most replays on its own and the
    parent-hash conjunct is no longer the sole binding. *)

(** The collector's program point inside ONE attempt at epoch [e]. *)
type phase =
  | Wait
      (** between attempts: the [Err] arm at epoch.rs:139-145 (no peer
          answered) and the 5s retry timer at epoch.rs:206-212. *)
  | Pending
      (** a peer response is in hand (the [Ok((epoch_rec, cert))] arm,
          epoch.rs:79) and the adoption gate at epoch.rs:103 has not been
          evaluated yet. *)
  | Adopted
      (** the gate at epoch.rs:103 passed, [save] returned [Ok] (:107) and
          [result_epoch = epoch] was executed (:115). *)
  | Rejected
      (** a conjunct of the gate failed: [error!] with the three booleans
          (epoch.rs:129-135) then [return epoch.saturating_sub(1)] (:136). *)

(** Total order index for {!phase}. *)
let phase_index = function
  | Wait -> 0
  | Pending -> 1
  | Adopted -> 2
  | Rejected -> 3

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The HIDDEN shape of the response the anonymous peer chose to put on the
    wire in answer to a request that named epoch [e]. *)
type resp =
  | R_none  (** no response in hand (the [Wait] phase). *)
  | R_genuine
      (** the real certified epoch-[e] record: parent hash matches
          [prev.digest()], the committee set matches, and the certificate
          carries a genuine super-quorum of signatures. All three conjuncts of
          epoch.rs:103 pass. *)
  | R_replay
      (** a genuinely certified OLDER record, i.e. [R_0] itself, replayed in
          answer to the request for [e]. Its [parent_hash] is
          [EpochDigest::default()], so [parents_match] (epoch.rs:100) FAILS;
          but on a stable set the committee sets are equal (epoch.rs:28) and
          the certificate is genuine (types/primary/epoch.rs:59-89), so the
          other two conjuncts PASS. *)
  | R_forged
      (** attacker-chosen [final_state] / [final_consensus] /
          [next_committee], wrapped with the PUBLIC parent hash
          [prev.digest()] and the PUBLIC committee [prev.next_committee] (both
          are fields of a record every peer already serves,
          types/primary/epoch.rs:21-38), plus a certificate no quorum signed.
          [parents_match] and [epoch_committee_valid] PASS,
          [verify_with_cert] FAILS. *)

(** Total order index for {!resp}. *)
let resp_index = function
  | R_none -> 0
  | R_genuine -> 1
  | R_replay -> 2
  | R_forged -> 3

(** Total order on {!resp}. *)
let resp_compare a b = Int.compare (resp_index a) (resp_index b)

(** [true] iff the responder answered for the epoch the request NAMED
    (mod.rs:815) rather than substituting an older certified record. A replay
    does not: it answers for [e - 1]. *)
let resp_serves_requested_epoch = function
  | R_none -> false
  | R_genuine -> true
  | R_replay -> false
  | R_forged -> true

(** [true] iff the record in hand carries at least [super_quorum] genuine
    committee signatures over its own digest (types/primary/epoch.rs:59-89,
    :94-96). A replayed record does: its certificate is real, just stale. *)
let resp_quorum_certified = function
  | R_none -> false
  | R_genuine -> true
  | R_replay -> true
  | R_forged -> false

(** The HIDDEN role of the peer that answered. There is no [Src_self]: the
    fetch is [send_request_any] over every connected peer
    (consensus.rs:868-881, :1616). *)
type src =
  | Src_none  (** no responder yet (the [Wait] phase). *)
  | Src_committee  (** the supplier is a member of the current committee. *)
  | Src_observer
      (** the supplier is an unauthenticated NON-committee full node that has
          synced and therefore serves the record from local storage with no
          authorization check (handler.rs:990-1003). *)

(** Total order index for {!src}. *)
let src_index = function Src_none -> 0 | Src_committee -> 1 | Src_observer -> 2

(** Total order on {!src}. *)
let src_compare a b = Int.compare (src_index a) (src_index b)

(** [true] iff the supplier is a committee member. *)
let src_is_committee = function
  | Src_none -> false
  | Src_committee -> true
  | Src_observer -> false

(** The syncing node's epoch DB at key [e]. A replay NEVER creates an entry
    for [e]: [save_record] keys by [record.epoch] and returns [Ok(())]
    idempotently for an epoch already present (epoch_records.rs:570-576), and
    the actor's [save] only adds the certificate in that case (:597-617). *)
type store =
  | Store_empty  (** nothing is stored under key [e]. *)
  | Store_genuine  (** the genuine quorum-certified record for [e] is stored. *)
  | Store_forged
      (** a forged record is stored under key [e]. Nothing verifies a record on
          the way OUT of storage ([record_by_epoch] epoch_records.rs:261-268,
          [get_epoch_by_number] :370-377, [retrieve_epoch_record]
          handler.rs:990-1003), so the poisoning is permanent and is re-served
          to other peers. *)

(** Total order index for {!store}. *)
let store_index = function
  | Store_empty -> 0
  | Store_genuine -> 1
  | Store_forged -> 2

(** Total order on {!store}. *)
let store_compare a b = Int.compare (store_index a) (store_index b)

(** [true] iff the epoch DB holds SOME record keyed [e]. This is all V1 can
    observe about its own store: it cannot tell a forged entry from the genuine
    one. *)
let store_holds = function
  | Store_empty -> false
  | Store_genuine -> true
  | Store_forged -> true

(** [true] iff the record actually in the DB under key [e] is quorum-certified.
    This is a GLOBAL fact, not a view component. *)
let store_quorum_certified = function
  | Store_empty -> false
  | Store_genuine -> true
  | Store_forged -> false

(** The joint global state of one sync attempt for epoch [e = 1]. *)
type state = {
  phase : phase;  (** the collector's program point. *)
  resp : resp;  (** the hidden response shape in hand. *)
  src : src;  (** the hidden responder role. *)
  store : store;  (** the epoch DB at key [e]. *)
  marked : bool;
      (** [result_epoch] has advanced to [e] (epoch.rs:115) and persists as the
          next call's [last_epoch] (epoch.rs:190-201). *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = resp_compare s1.resp s2.resp in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = src_compare s1.src s2.src in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = store_compare s1.store s2.store in
        if Bool.not (Int.equal c3 0) then c3 else Bool.compare s1.marked s2.marked

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. *)
type view =
  | View_v1 of phase * bool * bool
      (** V1's projection: its own control phase, whether its epoch DB holds
          ANY record keyed [e] (NOT which record), and whether [result_epoch]
          has advanced to [e]. Neither the responder's identity nor the
          response shape nor the individual gate booleans appear. *)
  | View_idle  (** the constant blank view of the non-agents V0, V2, V3. *)

(** Total deterministic order over ALL fields of V1's view. *)
let view_v1_compare (pa, ha, ma) (pb, hb, mb) =
  let c = phase_compare pa pb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Bool.compare ha hb in
    if Bool.not (Int.equal c1 0) then c1 else Bool.compare ma mb

(** Total order on views: [View_idle] < [View_v1], with the field-wise order
    within the constructor. Every constructor pair is spelled: no wildcard arm
    on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_v1 _ -> -1
  | View_v1 _, View_idle -> 1
  | View_v1 (pa, ha, ma), View_v1 (pb, hb, mb) ->
      view_v1_compare (pa, ha, ma) (pb, hb, mb)

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 is the only knowledge agent (the syncing node running
    [collect_epoch_records]); V0, V2 and V3 are idle non-agents with the
    constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V1 -> View_v1 (s.phase, store_holds s.store, s.marked)
  | Validator.V0
  | Validator.V2
  | Validator.V3
  | Validator.V4
  | Validator.V5
  | Validator.V6
  | Validator.V7
  | Validator.V8
  | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. Each deletes exactly one
    real guard and is refuted by exactly one statement. *)
type mutation =
  | Pristine  (** the faithful model. *)
  | No_parent_hash_check
      (** delete the [parents_match] conjunct
          (crates/state-sync/src/epoch.rs:100, consumed by the guard at :103),
          where [parent_hash] is [prev.digest()] of the record V1 already holds
          for [e - 1] (:88-90). ADDS [Pending(R_replay, src) -> Adopted] for
          BOTH [src] values, with [store] left UNCHANGED at [Store_empty]
          ([save_record]'s idempotent no-op, epoch_records.rs:570-576) and
          [marked := true]; correspondingly REMOVES
          [Pending(R_replay, src) -> Rejected]. NO SIBLING REPAIRS IT: (1) there
          is no [epoch_rec.epoch == epoch] comparison anywhere in
          epoch.rs:78-137 - the guard at :103 is exactly the three conjuncts;
          (2) [epoch_committee_valid] (:22-44) compares SETS and its [Equal]
          branch (:28) accepts a replay on a stable validator set; (3) the
          replayed certificate is genuine, so [verify_with_cert] passes;
          (4) the storage layer reports SUCCESS - [update_finals]
          (epoch_records.rs:201-215) only errors when [epoch > finals_len] and a
          replay takes the silent overwrite at :209-210, while [save_record]
          (:570-576) returns [Ok(())] idempotently; (5) the loop's
          [if result_epoch != epoch { break; }] (:147) does NOT fire, because
          :115 already set [result_epoch = epoch] - the walk advances to
          [e + 1], finds no parent at :88 and returns [e] at :96, a
          detection-free livelock rather than a repair; (6)
          [request_epoch_cert]'s 3-peer rotation (mod.rs:818-827) returns on the
          FIRST well-formed response and cross-checks nothing. *)
  | No_cert_quorum_check
      (** delete the super-quorum guard plus aggregate verification inside the
          SHARED helper [EpochRecord::verify_with_cert]
          (crates/types/src/primary/epoch.rs:84-88), which is what makes
          [epoch_valid] (crates/state-sync/src/epoch.rs:102) a real conjunct at
          :103. ADDS [Pending(R_forged, src) -> Adopted] for BOTH [src] values
          with [store := Store_forged] and [marked := true]; REMOVES
          [Pending(R_forged, src) -> Rejected]. NO SIBLING REPAIRS IT: (1) the
          surviving conjuncts compare against [prev.digest()] and
          [prev.next_committee], BOTH public fields of a record every peer
          already serves (types/primary/epoch.rs:21-38), so an attacker
          satisfies them while choosing [final_state] / [final_consensus] /
          [next_committee] freely; (2) nothing verifies a record on the way out
          of storage (epoch_records.rs:261-268, :370-377, handler.rs:990-1003),
          so the poisoned entry is permanent and is re-served; (3) the one
          genuine sibling writer - the failed-quorum recovery at
          epoch_votes.rs:198-217, which re-fetches through the SAME
          [request_epoch_cert] and gates ONLY on [verify_with_cert] with no
          parent or committee check at all - is disabled by this mutation TOO,
          because the deletion is inside the shared helper (epoch_votes.rs:156
          and :200 both lose it); that is precisely why the gate is taken inside
          [verify_with_cert] rather than at the epoch.rs:103 call site. *)
  | Committee_targeted_fetch
      (** delete the source-blindness of the fetch: replace
          [send_request_any] (crates/consensus/primary/src/network/mod.rs:819,
          with the identity-discarding destructure [peer: _] at :821, served by
          the unfiltered [connected_peers] rotation at
          crates/network-libp2p/src/consensus.rs:868-881 into which
          consensus.rs:1616 push_back's EVERY connected peer) with a
          committee-targeted request that retains the responder identity.
          REMOVES every [Wait -> Pending(resp, Src_observer)] transition,
          leaving only committee suppliers. NO SIBLING REPAIRS IT - and, more
          to the point, nothing in the pristine code already leaks the identity
          that this mutation restores: (1) the peer field is discarded at the
          single call site (mod.rs:821) and the other caller of
          [request_epoch_cert] (epoch_votes.rs:198) goes through the identical
          path; (2) the received bytes do not carry it - [EpochRecord] has no
          server field (types/primary/epoch.rs:21-38) and the certificate's
          [signed_authorities] names SIGNERS of epoch [e], not the server;
          (3) no penalty path implicitly identifies a bad responder -
          [rg 'report_penalty|Penalty' crates/state-sync/src/] is EMPTY even
          though network-libp2p/src/types.rs:383-393 documents that the
          [SendRequestAny] caller must report peers returning bad data, and
          epoch.rs:128-137 only logs while :206-212 just retries; (4) the peer
          manager's committee bookkeeping governs banning and exemption, not
          request routing. *)

(** The responder roles reachable under a mutation. Only
    {!Committee_targeted_fetch} narrows them; every mutation constructor is
    spelled. *)
let sources_of = function
  | Pristine -> [ Src_committee; Src_observer ]
  | No_parent_hash_check -> [ Src_committee; Src_observer ]
  | No_cert_quorum_check -> [ Src_committee; Src_observer ]
  | Committee_targeted_fetch -> [ Src_committee ]

(** [parents_match] (epoch.rs:100): [prev.digest() == epoch_rec.parent_hash].
    A replay carries the parent hash of the epoch BEFORE it, so it fails; a
    forgery copies the PUBLIC [prev.digest()], so it passes. *)
let parents_ok = function
  | R_none -> false
  | R_genuine -> true
  | R_replay -> false
  | R_forged -> true

(** [epoch_committee_valid] (epoch.rs:22-44), a CONSTANT-TRUE conjunct in this
    family: on a stable validator set the [Equal] branch (:28) holds for a
    replayed record, and a forgery copies the PUBLIC [prev.next_committee]. It
    therefore repairs NEITHER gate deletion - see the honesty caveat in the
    module header. *)
let committee_ok = function
  | R_none -> true
  | R_genuine -> true
  | R_replay -> true
  | R_forged -> true

(** [epoch_valid] (epoch.rs:102) = [EpochRecord::verify_with_cert]
    (types/primary/epoch.rs:59-89): digest match, bitmap expansion against the
    record's own committee, [auth_iter >= super_quorum] and the aggregate BLS
    verification. A replayed certificate is genuine and passes; a forged one
    does not. *)
let cert_ok = function
  | R_none -> false
  | R_genuine -> true
  | R_replay -> true
  | R_forged -> false

(** The adoption guard of epoch.rs:103 under a mutation. Every mutation
    constructor is spelled; each deletion drops exactly one conjunct. *)
let gate_passes mut r =
  match mut with
  | Pristine -> parents_ok r && committee_ok r && cert_ok r
  | No_parent_hash_check -> committee_ok r && cert_ok r
  | No_cert_quorum_check -> parents_ok r && committee_ok r
  | Committee_targeted_fetch -> parents_ok r && committee_ok r && cert_ok r

(** The epoch DB after [save(epoch_rec, cert)] (epoch.rs:107) succeeded. A
    replay leaves the store UNCHANGED: [save_record] keys by [record.epoch] and
    returns [Ok(())] idempotently for an epoch already present
    (epoch_records.rs:570-576), so the save reports success while storing
    nothing under [e]. *)
let adopt_store r st =
  match r with
  | R_none -> st
  | R_genuine -> Store_genuine
  | R_replay -> st
  | R_forged -> Store_forged

(** The transition relation under a mutation, one collector step per move.

    [Wait] self-loops (the [Err] arm at epoch.rs:139-145 plus the 5s retry
    timer at :206-212 - no peer answered, nothing changes) and branches to a
    [Pending] state for each hidden (response shape, responder role) the
    adversary may choose. [Pending] evaluates the gate exactly once. [Adopted]
    is TERMINAL when a record really landed under key [e] (the next pass
    short-circuits at epoch.rs:61-76 and the walk for [e] is over); when
    nothing landed - the replay case - the loop advances to [e + 1], finds no
    parent at :88, returns [e] at :96 and the retry re-requests [e], so the
    collector falls back to [Wait] with [marked] still set. [Rejected] returns
    [epoch.saturating_sub(1)] (:136) and the retry timer re-runs the attempt. *)
let next_with mut s =
  match s.phase with
  | Wait ->
      s
      :: List.concat_map
           (fun r ->
             List.map
               (fun sr -> { s with phase = Pending; resp = r; src = sr })
               (sources_of mut))
           [ R_genuine; R_replay; R_forged ]
  | Pending ->
      if gate_passes mut s.resp then
        [
          {
            s with
            phase = Adopted;
            store = adopt_store s.resp s.store;
            marked = true;
          };
        ]
      else [ { s with phase = Rejected } ]
  | Adopted -> (
      match s.store with
      | Store_empty -> [ { s with phase = Wait; resp = R_none; src = Src_none } ]
      | Store_genuine -> []
      | Store_forged -> [])
  | Rejected -> [ { s with phase = Wait; resp = R_none; src = Src_none } ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: V1 is behind, waiting between attempts, with nothing
    stored for [e = 1] and [result_epoch] not yet advanced. The certified
    record [R_0] for [e - 1] is background (the [prev] of epoch.rs:88-90), not
    a state component. *)
let initial =
  { phase = Wait; resp = R_none; src = Src_none; store = Store_empty; marked = false }

(** The atom vocabulary the three EPOCH_SYNC statements quantify over. *)
type atom =
  | Phase_adopted
      (** adopted(V1,e) : the gate at epoch.rs:103 passed and [save] returned
          [Ok]. *)
  | Phase_rejected
      (** rejected(V1,e) : a conjunct failed (epoch.rs:128-137). *)
  | Marked_epoch_synced
      (** marked_synced(V1,e) : [result_epoch] advanced to [e]
          (epoch.rs:115) and persists as the next call's [last_epoch]. *)
  | Holds_epoch_record
      (** holds_record(V1,e) : the epoch DB has SOME record keyed [e]
          (epoch_records.rs:570-595). *)
  | Served_requested_epoch
      (** served_requested_epoch : the responder answered for the epoch the
          request NAMED (mod.rs:815) instead of substituting an older certified
          record. A hidden property of ANOTHER node's act. *)
  | Response_quorum_certified
      (** quorum_certified(response) : the record in hand carries at least
          [super_quorum] genuine committee signatures over its own digest
          (types/primary/epoch.rs:59-89) - i.e. at least 2f+1 OTHER validators
          each performed a sign act. *)
  | Stored_quorum_certified
      (** quorum_certified(stored) : the record actually in the DB under key
          [e] is quorum-certified. *)
  | Source_is_committee
      (** source_in_committee : the supplier is a committee member rather than
          an unauthenticated observer. *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Phase_adopted -> (
      match s.phase with
      | Wait -> false
      | Pending -> false
      | Adopted -> true
      | Rejected -> false)
  | Phase_rejected -> (
      match s.phase with
      | Wait -> false
      | Pending -> false
      | Adopted -> false
      | Rejected -> true)
  | Marked_epoch_synced -> s.marked
  | Holds_epoch_record -> store_holds s.store
  | Served_requested_epoch -> resp_serves_requested_epoch s.resp
  | Response_quorum_certified -> resp_quorum_certified s.resp
  | Stored_quorum_certified -> store_quorum_certified s.store
  | Source_is_committee -> src_is_committee s.src

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Phase_adopted -> "adopted(V1,e)"
  | Phase_rejected -> "rejected(V1,e)"
  | Marked_epoch_synced -> "marked_synced(V1,e)"
  | Holds_epoch_record -> "holds_record(V1,e)"
  | Served_requested_epoch -> "served_requested_epoch"
  | Response_quorum_certified -> "quorum_certified(response)"
  | Stored_quorum_certified -> "quorum_certified(stored)"
  | Source_is_committee -> "source_in_committee"

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
    parameterized transitions, the one-agent view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
