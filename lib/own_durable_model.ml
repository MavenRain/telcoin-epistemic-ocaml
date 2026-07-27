(** Finite interpreted system for the OWN_DURABLE family: the durability of a
    validator's OWN certificate record, and what that durability is (and is not)
    knowable to. File citations refer to Telcoin-Association/telcoin-network at
    git HEAD [0c59c15b]; every line range below was opened in that checkout.

    The modelled mechanism. V1 has just assembled its own certificate C1 over its
    own header H from a quorum of votes (certifier.rs:440-442). Four things then
    happen, in this order, and the whole family is about the seams between them.

    - OWN-STORE WRITE. [spawn_header_proposal] inserts the certificate into the
      [ProposedCertificates] table keyed by the HEADER digest
      (certifier.rs:443); an insert error takes the [return Err(TaskError…)]
      arm at :444-446, strictly BEFORE [process_own_certificate] (:448) and
      before [network.publish_certificate] (:454). So a release is always
      downstream of a successful own-store write.
    - THE WRITE IS ASYNCHRONOUS. [ProposedCertificates] carries
      [TableHint::Epoch] (lib.rs:94) and the epoch DB is a [LayeredDatabase]
      opened with [full_memory = true] (composite_db.rs:33). Plain
      [Database::insert] therefore writes the mem layer IMMEDIATELY and only
      QUEUES a [DBMessage::Insert] on the background writer thread
      (layered_db.rs:391-396, routed via composite_db.rs:93-95). The physical
      write happens later on that thread, by one of exactly two routes:
      [ins.insert(&db)] when no physical txn is open (layered_db.rs:220-227),
      or [insert_txn] into the open txn (:210-219) which [end_txn] commits once
      the overlap count falls to 1 (:155-174, dispatched from :199-201 and
      :202-208).
    - A CRASH BEFORE THAT LOSES THE WRITE. The writer thread lives inside the
      process ([std::thread::spawn] in [LayeredDatabase::open],
      layered_db.rs:306-315) and its queue is a plain [mpsc] channel, so a
      restart discards anything still queued; [open_table] then refills the
      full-memory mem layer from whatever actually reached disk
      (layered_db.rs:347-356).
    - THE RE-CERTIFY GUARD. After a restart the proposer re-sends the SAME
      stored header verbatim ([repropose_header], proposer.rs:563-586) and the
      certifier re-enters [spawn_header_proposal], whose early return at
      certifier.rs:418-430 looks the header digest up in
      [ProposedCertificates] and, on a hit, re-publishes the STORED certificate
      instead of re-running vote collection. Its own comment (:422-424) says
      re-running "could produce signature equivocation and destroy
      deterministic randomness". The guard is only as strong as the write
      behind it - and that write is the asynchronous one above.

    Why a re-run really can equivocate: [Certificate::digest()] is just the
    header digest and EXCLUDES the aggregate signature (certificate.rs:473-479),
    so a second aggregate C2 over the same header collides with C1 as a key; and
    the vote-aggregation loop breaks the instant a quorum forms, in arrival
    order (certifier.rs:318-322, :331-347), so a second run over a different
    responding 2f+1 subset yields a different aggregate under the same key. It
    is NOT forced to differ: [handler.rs:494-506] recasts the identical vote for
    a header it already voted on, so the same aggregate is equally possible -
    which is why the re-certify transition here branches TWO ways.

    Components (eight; the reachable graph is exactly 22 states):
    - [mem] : what every IN-PROCESS read of V1's own store returns. The epoch DB
      is full-memory and [get] is mem-first (layered_db.rs:383-389), so this is
      the value the certifier's guard sees at certifier.rs:419.
    - [disk] : the physical mdbx/redb entry, i.e. exactly what a restart
      reloads (layered_db.rs:347-356).
    - [pend] : an [Insert]/[CommitTxn] for the current mem content is queued on
      the background DB thread but not yet applied to the physical DB.
    - [pub_c1] : C1 has been gossiped (certifier.rs:454, or the guard's
      re-publish at :426).
    - [pub_c2] : a SECOND, differently-signed certificate under the same header
      digest has been gossiped.
    - [restarted] : the one-shot process restart has happened. A crash budget of
      ONE bounds the graph; it is also what makes the liveness statement honest
      rather than manufactured (see [Own_durable_statements.s1]).
    - [stored] : monotone run-history flag - the [ProposedCertificates] insert
      for digest(H) has executed at least once (certifier.rs:443).
    - [recert] : vote collection has been re-run since the restart. One-shot: it
      is what stops the mutated re-certify transition from self-looping and
      manufacturing a livelock that would refute the liveness statement as
      collateral damage.

    Role mapping (knowledge agents must be validators with a real, non-constant
    view; a blank-view party may never appear under K):
    - V1 is the AUTHOR and a knowledge agent. It sees [mem] (its own reads),
      [pub_c1] and [pub_c2] (its own publications), [restarted] and [recert] (it
      knows whether this process re-ran certification). It does NOT see [disk]:
      there is no API on the write path that reports physical residency -
      [commit]'s own doc comment warns the data "may not be committed on-disk
      yet" (layered_db.rs:118-124), [persist]/[sync_persist] merely drain the
      queue via [DBMessage::CaughtUp] and report nothing (:463-495, answered by
      a bare oneshot at :247-249), and [LayeredDatabase::stats] does expose
      [open_txn_count] (:250-255, :317-333) but no consensus write path calls
      it. It does NOT see [pend] (the queue depth is likewise unobservable) and
      does NOT see [stored], because V1's RAM dies with the process - which is
      precisely why the guard has to consult the DATABASE (certifier.rs:418-420)
      rather than an in-memory set.
    - V2 is a GOSSIP PEER and a knowledge agent. Its view is
      [(pub_c1, pub_c2, recert)] - the two observation channels the
      header-certification protocol actually exposes to a peer:
      (i) WHICH CERTIFICATES FOR H HAVE APPEARED ON THE GOSSIP TOPIC.
      [publish_certificate] carries the certificate bytes and nothing about
      V1's storage, and the guard's re-publish (certifier.rs:426) sends the
      IDENTICAL stored bytes, so THAT release route leaves no trace.
      (ii) WHETHER A REPEAT VOTE REQUEST FOR digest(H) HAS ARRIVED. This is the
      channel an earlier draft of this model wrongly omitted. The OTHER
      post-restart route - the one T5 below models, taken when the
      [ProposedCertificates] lookup MISSES - is not byte-identical silence: the
      lookup falls through to [propose_header] (certifier.rs:431-440), which
      spawns a fresh [request_vote] task to EVERY other primary
      ([others_primaries_by_id], certifier.rs:286-312), and the peer's handler
      recognises the repeat directly - [read_vote_info] finds
      [vote_info.vote_digest == header.digest()] and logs "we have already cast
      a vote for this header … recast it quickly" (handler.rs:494-506), after a
      peer check that pins the requester to the header's own author
      (:485-493). So a re-run of vote collection IS visible to V2, and [recert]
      belongs in V2's view.
      Scope note (deliberate, not a hardwiring): this is the protocol surface of
      header certification - gossip releases and vote RPCs. Transport-level
      signals of a peer process dying (a libp2p disconnect/redial) are outside
      the modelled mechanism, and every statement below that quantifies over
      V2's ignorance is a claim about the certification protocol only.
    - V0 and V3 are idle: constant blank view, never under K. *)

(** The certificate value stored under digest(H) in V1's [ProposedCertificates]
    slot. [Cell_c2] is a SECOND aggregate over the SAME header digest -
    [Certificate::digest()] excludes the aggregate signature
    (certificate.rs:473-479), so C1 and C2 collide as keys. *)
type cell =
  | Cell_none  (** no entry under digest(H) *)
  | Cell_c1  (** the first aggregate C1 *)
  | Cell_c2  (** a second, differently-signed aggregate C2 over the same H *)

(** Total order index for {!cell}. *)
let cell_index = function Cell_none -> 0 | Cell_c1 -> 1 | Cell_c2 -> 2

(** Total order on {!cell}. *)
let cell_compare a b = Int.compare (cell_index a) (cell_index b)

(** [true] iff the slot is empty - the case in which the certifier's
    [ProposedCertificates] lookup MISSES (certifier.rs:418-420). *)
let cell_is_none = function
  | Cell_none -> true
  | Cell_c1 -> false
  | Cell_c2 -> false

(** [true] iff the cell holds the first aggregate C1. *)
let cell_is_c1 = function
  | Cell_none -> false
  | Cell_c1 -> true
  | Cell_c2 -> false

(** [true] iff the cell holds the second aggregate C2. *)
let cell_is_c2 = function
  | Cell_none -> false
  | Cell_c1 -> false
  | Cell_c2 -> true

(** The joint global state. There is no separate "queued value" component: a
    pending write can only have been queued by the same step that set [mem], and
    no transition changes [mem] while [pend] stays set, so the queued value is
    always the current [mem]. *)
type state = {
  mem : cell;
      (** V1's mem-layer entry: what every in-process read returns
          (layered_db.rs:383-389, full-memory epoch DB at composite_db.rs:33) *)
  disk : cell;
      (** V1's physical-DB entry: what a restart reloads
          (layered_db.rs:347-356) *)
  pend : bool;
      (** an [Insert]/[CommitTxn] is queued on the background writer thread
          (layered_db.rs:391-396) but not yet applied to the physical DB *)
  pub_c1 : bool;  (** C1 has been gossiped (certifier.rs:454 / :426) *)
  pub_c2 : bool;
      (** a second, differently-signed certificate for the same header digest
          has been gossiped *)
  restarted : bool;
      (** the one-shot process restart has happened - the crash budget is spent *)
  stored : bool;
      (** run history: the [ProposedCertificates] insert for digest(H) has
          executed at least once (certifier.rs:443) *)
  recert : bool;
      (** vote collection has been re-run since the restart (one-shot). This is
          also V2's second observation channel: re-running means
          [propose_header] (certifier.rs:431-440) spawned a fresh
          [request_vote] to every other primary (:286-312), and the peer
          recognises the repeat for a header it already voted on
          (handler.rs:494-506) *)
}

(** Total deterministic comparison over ALL state fields, in field order
    [mem, disk, pend, pub_c1, pub_c2, restarted, stored, recert]. *)
let state_compare s1 s2 =
  let c = cell_compare s1.mem s2.mem in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = cell_compare s1.disk s2.disk in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Bool.compare s1.pend s2.pend in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare s1.pub_c1 s2.pub_c1 in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.pub_c2 s2.pub_c2 in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Bool.compare s1.restarted s2.restarted in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = Bool.compare s1.stored s2.stored in
              if Bool.not (Int.equal c6 0) then c6
              else Bool.compare s1.recert s2.recert

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. [View_v1] is the AUTHOR's projection -
    [(mem, pub_c1, pub_c2, restarted, recert)] - which deliberately EXCLUDES
    [disk], [pend] and [stored] (see the header: physical residency and queue
    depth have no reporting API on this path, and pre-crash RAM is gone).
    [View_v2] is a gossip peer's projection - [(pub_c1, pub_c2, recert)] - which
    holds no component whatever of V1's STORAGE ([mem], [disk], [pend] and
    [stored] are all absent) but does carry the two protocol events a peer
    genuinely receives: certificates for H on the gossip topic, and a repeat
    [request_vote] for digest(H) (certifier.rs:286-312, handler.rs:494-506).
    [View_idle] is the constant blank view of the non-agents V0 and V3. *)
type view =
  | View_v1 of cell * bool * bool * bool * bool
      (** V1, the author: (mem, pub_c1, pub_c2, restarted, recert) *)
  | View_v2 of bool * bool * bool
      (** V2, a gossip peer: (pub_c1, pub_c2, recert) - the two gossip releases
          it can see, plus whether a repeat vote request for digest(H) arrived *)
  | View_idle  (** the constant blank view of the non-agents V0, V3 *)

(** Total deterministic order over ALL fields of the author's view. *)
let view_v1_compare (m, p1, p2, r, rc) (m', p1', p2', r', rc') =
  let c = cell_compare m m' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Bool.compare p1 p1' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Bool.compare p2 p2' in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare r r' in
        if Bool.not (Int.equal c3 0) then c3 else Bool.compare rc rc'

(** Total deterministic order over ALL fields of the gossip peer's view. *)
let view_v2_compare (p1, p2, rc) (p1', p2', rc') =
  let c = Bool.compare p1 p1' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Bool.compare p2 p2' in
    if Bool.not (Int.equal c1 0) then c1 else Bool.compare rc rc'

(** Total order on views: [View_idle] < [View_v1] < [View_v2], with the
    field-wise order within each constructor. Every constructor is spelled: no
    wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_v1 _ | View_v2 _) -> -1
  | (View_v1 _ | View_v2 _), View_idle -> 1
  | View_v1 (m, p1, p2, r, rc), View_v1 (m', p1', p2', r', rc') ->
      view_v1_compare (m, p1, p2, r, rc) (m', p1', p2', r', rc')
  | View_v1 _, View_v2 _ -> -1
  | View_v2 _, View_v1 _ -> 1
  | View_v2 (p1, p2, rc), View_v2 (p1', p2', rc') ->
      view_v2_compare (p1, p2, rc) (p1', p2', rc')

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 (the author) and V2 (a gossip peer) are the knowledge
    agents with real, non-constant views; V0 and V3 are idle non-agents with the
    constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V1 -> View_v1 (s.mem, s.pub_c1, s.pub_c2, s.restarted, s.recert)
  | Validator.V2 -> View_v2 (s.pub_c1, s.pub_c2, s.recert)
  | Validator.V0 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 -> View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at HEAD [0c59c15b] *)
  | No_disk_write
      (** delete BOTH physical-write routes of the background DB thread: the
          [ins.insert(&db)] call in the no-open-txn arm of the
          [DBMessage::Insert] handler (layered_db.rs:220-227) TOGETHER WITH the
          [if count <= 1 { current_txn.commit() }] branch inside [end_txn]
          (layered_db.rs:160-163, reached from :199-201 [CommitTxn] and :202-208
          [EndTxn]). The persist transition then only clears the queue and
          leaves the physical DB untouched, so [Disk_c1] becomes unreachable and
          the liveness statement's [Af] fails on the crash-free tail.

          Why both arms and not one: a [ProposedCertificates] write goes through
          the plain [Database::insert] (certifier.rs:443 -> composite_db.rs:93-95
          -> layered_db.rs:391-396), which takes whichever arm matches the
          background thread's txn state at that instant - the two arms are a
          genuine SIBLING PAIR, so deleting only one would be silently repaired
          by the other. Why nothing ELSE repairs it: [persist]/[sync_persist]
          only send [DBMessage::CaughtUp], answered by a bare oneshot reply, and
          perform no write (layered_db.rs:463-495, :247-249) - and nothing on
          the certifier path calls them anyway; [TxnGuard::drop]'s [EndTxn]
          (:60-70) routes into the SAME [end_txn] (:202-208), so it is not a
          third commit path; [db.compact()] on startup and every 24h (:182-184,
          :258-264) does not commit; [DBMessage::Shutdown] breaks the loop
          WITHOUT ending the txn (:256), which is an abort, not a repair; and
          [CertificateStore::write]/[write_all] (certificate_store.rs:176-186,
          :191-209) reach disk only through [txn.commit()], which is
          [DBMessage::CommitTxn] -> [end_txn], already covered. *)
  | No_proposed_cert_guard
      (** delete the [if let Ok(Some(cert)) = …get::<ProposedCertificates>(…) {
          … publish_certificate(cert); return Ok(()) }] early return in
          [spawn_header_proposal] (certifier.rs:418-430). The re-certify
          transition then loses its "the lookup MISSED" precondition and fires
          at ANY mem value, so from a state whose write already reached disk the
          node re-runs vote collection, can form a different aggregate over the
          same header digest, and gossips it: signature equivocation from a
          durable record.

          Why no sibling path repairs it: (a) [proposal_lock]
          (certifier.rs:411-416) is an in-process tokio [Mutex] - it serialises
          concurrent proposals within one process, does not survive a restart,
          and does not compare digests. (b) The dangerous one, checked by
          reading it: [process_own_certificate] -> [process_certificate] does
          test [node_storage().contains(&digest)] but merely returns [Ok(())]
          and SKIPS DAG insertion (cert_validator.rs:93-98), so the certifier
          does NOT take the [Err] arm at certifier.rs:449-451 and still reaches
          [publish_certificate] at :454 - the duplicate check does not stop C2
          from reaching gossip. (c) Voter-side dedup does not block a re-run
          either: handler.rs:494-506 RECASTS the identical vote for the same
          header digest. (d) There is exactly ONE writer and ONE reader of
          [ProposedCertificates] in the whole tree (certifier.rs:443 and :419);
          the table is cleared only at the epoch boundary (close_epoch.rs:268),
          the same scope as the claim. (e) [save_cert]
          (certificate_store.rs:129-147) uses [txn.insert::<Certificates>], an
          overwrite, so the local [Certificates] store does not reject C2
          either. *)
  | No_store_before_publish
      (** delete the [return Err(TaskError::from_message(e.to_string()))] in the
          insert-failure arm at certifier.rs:443-446, so a failed own-store
          write is only logged and execution falls through to
          [process_own_certificate] (:448) and [network.publish_certificate]
          (:454). The publish transition then gains a second enabling clause -
          release with NO own-store write at all - so a certificate reaches the
          gossip topic that was never persisted, and a peer can no longer infer
          the author's own write from having seen the certificate.

          Why no sibling path repairs it: (a) the certifier's caller does not
          retry [spawn_header_proposal] on [Err] - the [TaskError] propagates
          (certifier.rs:445, :472-479) and the task ends; there is no retry loop
          over the insert. (b) There is no other
          [insert::<ProposedCertificates>] anywhere in the tree - a whole-tree
          search finds the single write site at certifier.rs:443. (c)
          [process_own_certificate] (:448) writes the [Certificates] table via
          state_sync, NOT [ProposedCertificates], so it does not re-establish
          the guard's precondition; and under the mutation it runs too, which
          WIDENS the leak rather than closing it. (d) The epoch-boundary clear
          (close_epoch.rs:268) only removes entries. (e) A peer-side fetch would
          read [Certificates], written strictly AFTER the
          [ProposedCertificates] insert in the pristine order, so it is not an
          earlier release route. *)

(** [enabled_list cond succs] is [succs] when the transition guard [cond] holds
    and the empty list otherwise. Every transition family below is one guard and
    one successor list, so no loop keyword and no mutable accumulator appears. *)
let enabled_list cond succs = if cond then succs else []

(** T1 - the own-store write (certifier.rs:443,
    [insert::<ProposedCertificates>]). Enabled before any store, publication or
    restart. The mem layer is written IMMEDIATELY and the physical write is only
    QUEUED (layered_db.rs:391-396), which is why this sets [pend] rather than
    [disk]. *)
let t1_store_own_cert s =
  enabled_list
    (cell_is_none s.mem
    && Bool.not s.stored
    && Bool.not s.pub_c1
    && Bool.not s.restarted)
    [ { s with mem = Cell_c1; pend = true; stored = true } ]

(** T2 - the background DB thread applies the queued write to the PHYSICAL
    database: [ins.insert(&db)] in the no-open-txn arm (layered_db.rs:220-227),
    or [insert_txn] plus the [current_txn.commit()] inside [end_txn]
    (:155-174, dispatched at :199-208). Under {!No_disk_write} both routes are
    deleted, so the queue drains with the physical DB untouched. *)
let t2_db_thread_persist mut s =
  enabled_list s.pend
    (match mut with
    | Pristine -> [ { s with disk = s.mem; pend = false } ]
    | No_disk_write -> [ { s with pend = false } ]
    | No_proposed_cert_guard -> [ { s with disk = s.mem; pend = false } ]
    | No_store_before_publish -> [ { s with disk = s.mem; pend = false } ])

(** T3 - release C1 on the gossip topic ([process_own_certificate] then
    [network.publish_certificate], certifier.rs:448-456), reachable in the
    pristine code only because the insert-failure arm at :443-446 did NOT return
    [Err]; the same clause also covers the guard's re-publish at :426, which has
    the identical enabling condition and effect. Under
    {!No_store_before_publish} a SECOND clause is enabled - release with the
    own-store slot still empty and [stored] still false. *)
let t3_publish_c1 mut s =
  let after_store =
    enabled_list
      (cell_is_c1 s.mem && Bool.not s.pub_c1)
      [ { s with pub_c1 = true } ]
  in
  let without_store =
    enabled_list
      (match mut with
      | Pristine -> false
      | No_disk_write -> false
      | No_proposed_cert_guard -> false
      | No_store_before_publish ->
          cell_is_none s.mem
          && Bool.not s.stored
          && Bool.not s.pub_c1
          && Bool.not s.restarted)
      [ { s with pub_c1 = true } ]
  in
  List.concat [ after_store; without_store ]

(** T4 - the one-shot process restart. The queued [Insert] dies with the process
    (its writer thread and [mpsc] channel are in-process,
    layered_db.rs:306-315), and [open_table] refills the full-memory mem layer
    from whatever actually reached disk (layered_db.rs:347-356) - hence
    [mem := disk] and [pend := false]. [stored] is run history, not node RAM, so
    it is preserved; [recert] is reset because it describes only the CURRENT
    process (it is false here anyway, being settable only post-restart). *)
let t4_restart s =
  enabled_list (Bool.not s.restarted)
    [ { s with mem = s.disk; pend = false; restarted = true; recert = false } ]

(** T5 - re-certification after the restart: the proposer re-sends the same
    stored header ([repropose_header], proposer.rs:563-586) and the certifier
    re-enters [spawn_header_proposal], where the [ProposedCertificates] lookup
    at certifier.rs:418-420 decides. PRISTINE this fires only when the lookup
    MISSED ([mem = Cell_none]); under {!No_proposed_cert_guard} the early return
    is gone, so it fires at ANY mem and overwrites it. TWO successors, because a
    re-run is not forced to differ: handler.rs:494-506 recasts the identical
    vote (so the same aggregate C1 is possible), while the aggregation loop
    breaks at quorum in ARRIVAL ORDER (certifier.rs:318-322, :331-347) so a
    different responding 2f+1 subset yields a different aggregate C2. [recert]
    makes this one-shot: without it the mutated form self-loops and manufactures
    a livelock that would refute the liveness statement as collateral damage.

    This transition is NOT silent on the wire, and that is why [recert] is a
    component of {!View_v2}: the missed lookup falls through to
    [propose_header] (certifier.rs:431-440), which spawns a fresh
    [request_vote] task to every other primary (:286-312), and the peer's
    handler recognises the repeat for a header it already voted on
    (handler.rs:494-506). The guard's re-publish path (:426) is the byte-
    identical one; THIS path is not. *)
let t5_recertify mut s =
  let guard_missed =
    match mut with
    | Pristine -> cell_is_none s.mem
    | No_disk_write -> cell_is_none s.mem
    | No_store_before_publish -> cell_is_none s.mem
    | No_proposed_cert_guard -> true
  in
  enabled_list
    (s.restarted && Bool.not s.recert && guard_missed)
    [
      { s with mem = Cell_c1; pend = true; stored = true; recert = true };
      { s with mem = Cell_c2; pend = true; stored = true; recert = true };
    ]

(** T6 - release the second aggregate C2 on the gossip topic
    (certifier.rs:454). [process_own_certificate] returns [Ok] early on the
    duplicate digest (cert_validator.rs:93-98) and does NOT block the publish,
    so nothing between the re-run and the wire filters C2 out. *)
let t6_publish_c2 s =
  enabled_list
    (cell_is_c2 s.mem && Bool.not s.pub_c2)
    [ { s with pub_c2 = true } ]

(** The transition relation: the six families unioned, one step per successor.
    A state with no successor at all (the terminals R4, S2', Q7, Q8 of the
    pristine graph) is stutter-closed by the kernel, which is what makes [Af]
    honest here. *)
let next_with mut s =
  List.concat
    [
      t1_store_own_cert s;
      t2_db_thread_persist mut s;
      t3_publish_c1 mut s;
      t4_restart s;
      t5_recertify mut s;
      t6_publish_c2 s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: V1 has just assembled C1 from a quorum of votes
    (certifier.rs:440-442) and is about to persist it. Nothing is stored,
    nothing is on disk, nothing is queued, nothing is published. *)
let initial =
  {
    mem = Cell_none;
    disk = Cell_none;
    pend = false;
    pub_c1 = false;
    pub_c2 = false;
    restarted = false;
    stored = false;
    recert = false;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Mem_c1
      (** mem = C1 : V1's own read of [ProposedCertificates[digest(H)]] returns
          the first aggregate (mem-first, layered_db.rs:383-389) *)
  | Mem_c2
      (** mem = C2 : V1's own store holds a SECOND, differently-signed aggregate
          under the same header digest *)
  | Disk_c1
      (** disk = C1 : C1 has reached V1's physical database, i.e. it survives a
          restart (layered_db.rs:347-356) *)
  | Commit_pending
      (** an [Insert]/[CommitTxn] for the current mem content is queued on the
          background DB thread (layered_db.rs:391-396, applied at :199-227) *)
  | Pub_c1  (** C1 has been gossiped (certifier.rs:454 / :426) *)
  | Pub_c2
      (** a second, differently-signed certificate for the same header digest
          has been gossiped *)
  | Restarted
      (** V1's process has restarted - its one-shot crash budget is spent *)
  | Own_cert_stored
      (** the [ProposedCertificates] insert for digest(H) has executed at least
          once (certifier.rs:443) *)
  | Revote_requested
      (** vote collection for digest(H) has been RE-RUN, i.e. [propose_header]
          (certifier.rs:431-440) spawned a fresh [request_vote] to every other
          primary (:286-312) for a header the peers had already voted on
          (handler.rs:494-506). This is an event on V2's wire, not a fact about
          V1's storage, which is why it is a component of {!View_v2}. *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Mem_c1 -> cell_is_c1 s.mem
  | Mem_c2 -> cell_is_c2 s.mem
  | Disk_c1 -> cell_is_c1 s.disk
  | Commit_pending -> s.pend
  | Pub_c1 -> s.pub_c1
  | Pub_c2 -> s.pub_c2
  | Restarted -> s.restarted
  | Own_cert_stored -> s.stored
  | Revote_requested -> s.recert

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Mem_c1 -> "mem=C1"
  | Mem_c2 -> "mem=C2"
  | Disk_c1 -> "disk=C1"
  | Commit_pending -> "commit_pending"
  | Pub_c1 -> "published(C1)"
  | Pub_c2 -> "published(C2)"
  | Restarted -> "restarted"
  | Own_cert_stored -> "own_cert_stored"
  | Revote_requested -> "revote_requested"

(** The exact CTLK checker over this family's ordered state and view. *)
module Checker = System.Make (State) (View)

(** The checker spec under a mutation: single initial state, mutation-
    parameterized transitions, the two-agent view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
