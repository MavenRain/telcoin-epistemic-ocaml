(** The VOTE_CACHE_RETRY interpreted system: the primary's per-author vote
    response cache and the certifier retry loop that feeds it.

    {2 Mechanism}

    [RequestHandler::vote] (crates/consensus/primary/src/network/handler.rs:475-600)
    keeps one [TokioMutex] per committee author
    ([AuthEquivocationMap], handler.rs:55-58, preloaded per authority at
    handler.rs:111-116) holding the last
    [(Epoch, Round, HeaderDigest, Option<PrimaryResponse>)] that author was
    answered with. On every vote request the entry is {b taken} out of the cell
    (handler.rs:513-515 [auth_last_vote.take()]) and then dispatched on:

    - [None | Some(RecoverableError(_))] -> the empty arm (handler.rs:517-518):
      the request falls through to a fresh [vote_inner] and the outcome is
      re-cached at handler.rs:591-595;
    - [Some(MissingParents(missing))] with an {b empty} parents vector
      (handler.rs:519-534) -> the entry is written back verbatim and the same
      [MissingParents(missing)] is re-issued, under the verbatim comment "This
      avoids a deadlock where the proposer's certifier restarts (losing the
      missing parent hint) and the cached state here causes a fatal
      WrongNumberOfParents error on every subsequent attempt";
    - [Some(MissingParents(missing))] with a matching parents vector
      (handler.rs:537-548) -> falls through to [vote_inner] with the parents
      supplied; a {b non-matching} length takes handler.rs:549-562, which writes
      [MissingParents(missing)] back and returns [WrongNumberOfParents];
    - [Some(res)] otherwise (handler.rs:564) -> the answer is replayed and, note,
      {b not} written back, so a final error is replayed exactly once.

    The requester side is [Certifier::request_vote]
    (crates/consensus/primary/src/certifier.rs:124-219): [missing_parents]
    starts at [None] (certifier.rs:133), so the first attempt of every vote
    request carries [parents = vec![]] (certifier.rs:143-168
    [.unwrap_or(Ok(vec![]))?]); a [MissingParents] response stores the hint
    (certifier.rs:180-184); a non-fatal network error resets it to [None]
    (certifier.rs:195); and [NetworkError::RPCError] is {b fatal} to that peer's
    vote task (certifier.rs:185-190). [PrimaryNetworkHandle::request_vote]
    (network/mod.rs:463-505) retries a [RecoverableError] in place, at most six
    sends (:474-484), and then collapses {b both} [RecoverableError] and [Error]
    into the same [NetworkError::RPCError] (:487-488). The classification that
    decides which one a rejection becomes is
    [PrimaryResponse::into_error_ref] (network/message.rs:329-357): only
    [InvalidHeader(HeaderError::InvalidEpoch { ours, theirs })] with
    [*theirs == ours + 1] is [RecoverableError]; every other variant is [Error].
    The epoch rejection itself is raised first thing in [vote_inner]
    (handler.rs:612 -> types/src/primary/header.rs:100-107).

    {2 Components}

    - [cache]: j's [auth_last_vote] entry for author i at header h.
    - [hint]: i's certifier-local [missing_parents] for h.
    - [req]: whether a vote request from i is currently under evaluation at j,
      i.e. whether j holds author i's [TokioMutex] (handler.rs:510-512). The
      parents vector of that request is not a separate component: it is computed
      from [missing_parents] at send time (certifier.rs:143-168) and cannot
      change while the response is awaited (the [tokio::select!] at
      certifier.rs:171-204 has no other branch that writes it).
    - [task]: i's per-peer vote task for h (spawned at certifier.rs:295-311).
    - [epoch]: whether j's committee epoch is exactly one behind h's epoch.
      Monotone: j crosses the boundary and never goes back.
    - [peer]: whether the concurrent vote request of a {b second} committee
      author k has been answered by j.

    {2 Role mapping}

    - [Validator.V0] = j, the voter. Its view is its own cache entry for i, its
      own committee epoch, the parents vector of the request from i it is
      currently evaluating, and whether it has answered author k. It does
      {b not} see i's [missing_parents], i's attempt count or whether i's vote
      task is still alive - the wire request carries only
      [Vote { header, parents }] (network/message.rs:52-58, constructed at
      network/mod.rs:470), with no session id and no attempt counter.
    - [Validator.V1] = i, the header author, running the certifier. Its view is
      its own [missing_parents] hint, the state of its vote task for h, and
      whether a request is outstanding. It does {b not} see j's cache entry,
      j's committee epoch, or whether j has answered author k.
    - [Validator.V2] = k, the second committee author. Its view is only whether
      its own request has been answered; k never appears under [K].
    - [Validator.V3] .. [Validator.V9] are the idle non-agents of the ten-member
      committee: constant blank view, never under [K].

    {2 Honest scope}

    The model covers one header digest h at one round, an {b honest} author i
    (certifier.rs:143-168 reads the requested parents back out of i's own
    certificate store and errors locally rather than sending a mismatched set,
    so the [InvalidParents] arm at handler.rs:537-548 is unreachable for it),
    and an epoch skew of at most one in the direction message.rs:331-335 cares
    about. A voter that has advanced PAST h's epoch is not a separate component:
    that rejection is [InvalidEpoch] with [theirs < ours], which takes the same
    generic [Self::Error] arm (message.rs:337-357) as every other final
    rejection already modelled, and no statement of this family is stated over
    it.

    The run modelled is one in which {b j does not restart}: [auth_last_vote]
    is process-local
    (handler.rs:93, rebuilt empty at handler.rs:111-116), so a restart of j
    would clear the cache without i learning of it. A restart of {b i} is
    modelled, as the re-propose of the same stored header
    (proposer.rs:758-822 [should_repropose_header] ->
    [Proposer::repropose_header] on [get_last_proposed]) followed by a fresh
    vote task whose [missing_parents] starts at [None] (certifier.rs:133).

    j's independent acquisition of the missing parent is {b not} a separate
    state bit: [check_for_missing_parents] (handler.rs:879-924) is consulted
    only on a request whose parents vector is empty {b and} whose cache entry
    fell through, so the model branches on it there rather than tracking it. The
    consequence is deliberately not hidden: it is exactly why the deletion at
    handler.rs:520-534 is unrepairable, since the cached [MissingParents] arm
    returns before [vote_inner] is ever reached again. *)

(** j's [auth_last_vote] entry for author i at header h: the
    [Option<PrimaryResponse>] slot of the tuple at handler.rs:55-58. *)
type cache =
  | Cache_none
      (** [None]: no entry, or an entry whose response slot was taken
          (handler.rs:513-515) and never written back. *)
  | Cache_missing
      (** [Some(MissingParents(M))]: j answered with the missing-parent list
          (handler.rs:661-668, re-cached at :595, written back verbatim by the
          re-issue at :527-532 and by the wrong-count branch at :551-556). *)
  | Cache_recoverable
      (** [Some(RecoverableError(_))]: the one-epoch-ahead classification of
          message.rs:331-335. *)
  | Cache_final
      (** [Some(Error(_))]: the generic classification of message.rs:337-357,
          cached at handler.rs:591-595. *)
  | Cache_vote
      (** [Some(Vote(_))]: j voted and cached the vote (handler.rs:872,
          :591-595). *)

(** Total order index for {!cache}. *)
let cache_index = function
  | Cache_none -> 0
  | Cache_missing -> 1
  | Cache_recoverable -> 2
  | Cache_final -> 3
  | Cache_vote -> 4

(** Total order on {!cache}. *)
let cache_compare a b = Int.compare (cache_index a) (cache_index b)

(** i's certifier-local [missing_parents] for h (certifier.rs:133). *)
type hint =
  | Hint_lost
      (** [None]: a fresh vote task (certifier.rs:133) or a hint cleared by a
          non-fatal network error (certifier.rs:195). The next request carries
          [parents = vec![]] (certifier.rs:168). *)
  | Hint_held
      (** [Some(M)]: the hint from a [MissingParents] response
          (certifier.rs:180-184). The next request carries exactly M, read back
          out of i's own certificate store (certifier.rs:143-168). *)

(** Total order index for {!hint}. *)
let hint_index = function Hint_lost -> 0 | Hint_held -> 1

(** Total order on {!hint}. *)
let hint_compare a b = Int.compare (hint_index a) (hint_index b)

(** Whether j currently holds author i's evaluation slot: the [TokioMutex]
    acquired at handler.rs:510-512 and released when [vote] returns. *)
type req =
  | Req_idle  (** no request from i is under evaluation. *)
  | Req_pending
      (** a vote request from i is under evaluation; its parents vector is
          [vec![]] when {!Hint_lost} and exactly M when {!Hint_held}. *)

(** Total order index for {!req}. *)
let req_index = function Req_idle -> 0 | Req_pending -> 1

(** Total order on {!req}. *)
let req_compare a b = Int.compare (req_index a) (req_index b)

(** i's per-peer vote task for h (spawned at certifier.rs:295-311). *)
type task =
  | Task_live  (** still in the retry loop of certifier.rs:138-219. *)
  | Task_dead
      (** ended by [NetworkError::RPCError], which certifier.rs:185-190 treats
          as irrecoverable; the task is not respawned for this header until the
          proposer re-proposes (proposer.rs:802-822). *)
  | Task_voted  (** j's vote for h was received and verified (certifier.rs:178,
          :221-251). *)

(** Total order index for {!task}. *)
let task_index = function Task_live -> 0 | Task_dead -> 1 | Task_voted -> 2

(** Total order on {!task}. *)
let task_compare a b = Int.compare (task_index a) (task_index b)

(** j's committee epoch relative to h's epoch (header.rs:100-107). *)
type epoch =
  | Epoch_behind
      (** [committee.epoch() + 1 = header.epoch()]: the boundary race that
          message.rs:331-335 singles out. *)
  | Epoch_aligned  (** [committee.epoch() = header.epoch()]. *)

(** Total order index for {!epoch}. *)
let epoch_index = function Epoch_behind -> 0 | Epoch_aligned -> 1

(** Total order on {!epoch}. *)
let epoch_compare a b = Int.compare (epoch_index a) (epoch_index b)

(** The concurrent vote request of the second committee author k. *)
type peer_reply =
  | Peer_waiting  (** k's vote request is at j and not yet answered. *)
  | Peer_answered  (** j has answered k. *)

(** Total order index for {!peer_reply}. *)
let peer_index = function Peer_waiting -> 0 | Peer_answered -> 1

(** Total order on {!peer_reply}. *)
let peer_compare a b = Int.compare (peer_index a) (peer_index b)

(** The joint global state: j's cache slot for i, i's hint, i's outstanding
    request, i's vote task, j's epoch skew, and k's competing request. *)
type state = {
  cache : cache;  (** j's [auth_last_vote] response slot for author i at h *)
  hint : hint;  (** i's certifier [missing_parents] for h *)
  req : req;  (** whether j holds author i's evaluation slot *)
  task : task;  (** i's per-peer vote task for h *)
  epoch : epoch;  (** j's committee epoch relative to h's epoch *)
  peer : peer_reply;  (** whether author k's competing request was answered *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = cache_compare s1.cache s2.cache in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = hint_compare s1.hint s2.hint in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = req_compare s1.req s2.req in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = task_compare s1.task s2.task in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = epoch_compare s1.epoch s2.epoch in
          if Bool.not (Int.equal c4 0) then c4
          else peer_compare s1.peer s2.peer

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  (** The joint global state. *)
  type t = state

  (** Total order on states. *)
  let compare = state_compare
end

(** The parents vector j sees on the request it is currently evaluating: the
    [parents: Vec<Certificate>] field of [PrimaryRequest::Vote]
    (network/message.rs:52-58). *)
type seen =
  | Seen_idle  (** no request from i under evaluation *)
  | Seen_empty  (** [parents.is_empty()], the test at handler.rs:520 *)
  | Seen_full  (** exactly the missing set M, the test at handler.rs:537 *)

(** Total order index for {!seen}. *)
let seen_index = function Seen_idle -> 0 | Seen_empty -> 1 | Seen_full -> 2

(** Total order on {!seen}. *)
let seen_compare a b = Int.compare (seen_index a) (seen_index b)

(** What j observes of the request under evaluation. Grounded: the request
    carries the header and the parents vector and nothing else, so the
    distinction between "i's first attempt" and "i retried after losing the
    hint" is invisible here. *)
let seen_of s =
  match s.req with
  | Req_idle -> Seen_idle
  | Req_pending -> (
      match s.hint with Hint_lost -> Seen_empty | Hint_held -> Seen_full)

(** A validator's local view.

    - [View_voter] is j: its own cache slot for i, its own committee epoch, the
      parents vector of the request from i it is evaluating, and whether it has
      answered author k. j does NOT see i's hint, i's task liveness or i's
      attempt count.
    - [View_author] is i: its own hint, its own vote task for h, and whether a
      request is outstanding. i does NOT see j's cache slot, j's epoch, or
      whether j has answered author k.
    - [View_peer] is k: only whether its own request has been answered.
    - [View_idle] is the constant blank view of the non-agent V3. *)
type view =
  | View_voter of cache * epoch * seen * peer_reply  (** V0 = j, the voter *)
  | View_author of hint * task * req  (** V1 = i, the header author *)
  | View_peer of peer_reply  (** V2 = k, the competing author *)
  | View_idle  (** V3, the idle non-agent *)

(** Total order on the voter's view fields. *)
let view_voter_compare (c, e, s, p) (c', e', s', p') =
  let a = cache_compare c c' in
  if Bool.not (Int.equal a 0) then a
  else
    let b = epoch_compare e e' in
    if Bool.not (Int.equal b 0) then b
    else
      let d = seen_compare s s' in
      if Bool.not (Int.equal d 0) then d else peer_compare p p'

(** Total order on the author's view fields. *)
let view_author_compare (h, t, r) (h', t', r') =
  let a = hint_compare h h' in
  if Bool.not (Int.equal a 0) then a
  else
    let b = task_compare t t' in
    if Bool.not (Int.equal b 0) then b else req_compare r r'

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_voter (c, e, s, p), View_voter (c', e', s', p') ->
      view_voter_compare (c, e, s, p) (c', e', s', p')
  | View_voter _, (View_author _ | View_peer _ | View_idle) -> -1
  | View_author _, View_voter _ -> 1
  | View_author (h, t, r), View_author (h', t', r') ->
      view_author_compare (h, t, r) (h', t', r')
  | View_author _, (View_peer _ | View_idle) -> -1
  | View_peer _, (View_voter _ | View_author _) -> 1
  | View_peer p, View_peer p' -> peer_compare p p'
  | View_peer _, View_idle -> -1
  | View_idle, (View_voter _ | View_author _ | View_peer _) -> 1
  | View_idle, View_idle -> 0

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  (** A validator's local view. *)
  type t = view

  (** Total order on views. *)
  let compare = view_compare
end

(** View projection. V0 is the voter j and V1 the header author i; both are
    knowledge agents with genuinely partial, non-constant views. V2 is the
    competing author k, which never appears under [K]. V3 is idle and blank. *)
let view v s =
  match v with
  | Validator.V0 -> View_voter (s.cache, s.epoch, seen_of s, s.peer)
  | Validator.V1 -> View_author (s.hint, s.task, s.req)
  | Validator.V2 -> View_peer s.peer
  | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7
  | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at 0c59c15b *)
  | No_empty_parent_reissue
      (** delete the [if parents.is_empty() { ... return
          Ok(PrimaryResponse::MissingParents(missing)); }] block at
          handler.rs:520-534. The empty retry then falls into the wrong-count
          branch at handler.rs:549-562, which writes [MissingParents(missing)]
          back into the cache (:551-556) and returns
          [WrongNumberOfParents(|M|, 0)]. That error is an
          [InvalidHeader(_)], so message.rs:337-357 makes it
          [PrimaryResponse::Error], network/mod.rs:487-488 makes it
          [NetworkError::RPCError] and certifier.rs:185-190 treats it as fatal:
          the transition [(Cache_missing, Hint_lost, Req_pending) ->
          hint re-delivered] is removed and [-> Task_dead] added.

          No sibling path repairs it. (a) The cache entry is written back at
          :551-556, so every later empty retry meets the same branch - unlike
          the replay at handler.rs:564, this branch does not leave the slot
          cleared. (b) The requester cannot recover the hint: a fresh vote task
          starts from [missing_parents = None] (certifier.rs:133) and the
          proposer re-proposes the SAME stored header (proposer.rs:802-822), so
          the cache key [(epoch, round, digest)] read at handler.rs:577-579 is
          unchanged. (c) [PrimaryNetworkHandle::request_vote] retries only
          [RecoverableError] (network/mod.rs:474-484), never [Error]. (d) The
          fast recast at handler.rs:494-506 requires j to have already voted for
          this digest, which it has not. (e) j obtaining the missing parent by
          itself does not help either, because the cached [MissingParents] arm
          returns at :519-562 before [vote_inner] - and therefore before
          [check_for_missing_parents] (handler.rs:879-924) - is reached again. *)
  | No_one_epoch_ahead_arm
      (** delete the [if *theirs == ours + 1] guarded arm at
          message.rs:331-335, so [InvalidEpoch] falls into the generic
          [Self::Error] arm at message.rs:337-357. This removes the transition
          into [Cache_recoverable] and adds one into [Cache_final] with the
          vote task killed: the boundary-race rejection is no longer retried in
          place by network/mod.rs:474-484 and no longer takes the cache
          fall-through arm at handler.rs:517-518.

          No sibling path repairs it. (a) [Certifier::request_vote] retries only
          NON-[RPCError] network errors (certifier.rs:185-196), and an [Error]
          response is exactly [RPCError] (network/mod.rs:487-488). (b) The
          proposer's max-delay re-propose re-sends the same stored header
          (proposer.rs:802-822), so the cache key at handler.rs:577-579 is
          unchanged. (c) The fast recast at handler.rs:494-506 requires a prior
          vote. The one real relief - that the replay at handler.rs:564 leaves
          the slot cleared, so a third attempt does re-evaluate - is modelled
          explicitly, and the statement is stated so that it survives it. *)
  | Single_shared_vote_lock
      (** replace the per-author lookup [self.auth_last_vote.get(header.author())]
          at handler.rs:510 with a single shared lock (equivalently: key the map
          of handler.rs:55-58 by a constant instead of by
          [AuthorityIdentifier]). Author k's request can then only be answered
          while author i's slot is free, removing every transition that answers
          k during an evaluation of i.

          No sibling path repairs it. (a) [PrimaryNetwork::process_vote_request]
          (network/mod.rs:1517-1554) spawns one task per request, so concurrency
          exists at the network layer, but with the map collapsed every task
          contends for the SAME mutex - the spawn is not a repair. (b) The
          per-request [cancel] oneshot (network/mod.rs:1523, :1550) drops the
          vote future and with it the guard, which is why it repairs a deletion
          of the INNER timeout at handler.rs:582-586 - and precisely why this
          mutation is anchored on the KEYING and not on that timeout. (c)
          [requested_parents] (handler.rs:897-921) is a separate [parking_lot]
          mutex held only across a synchronous filter, never across an await, so
          it supplies no cross-identity isolation either. *)

(** Whether i's vote task for h is still in the retry loop. *)
let task_is_live t =
  match t with Task_live -> true | Task_dead -> false | Task_voted -> false

(** Whether j currently holds author i's evaluation slot. *)
let slot_is_free r = match r with Req_idle -> true | Req_pending -> false

(** Whether i's certifier still holds the missing-parent hint. *)
let hint_is_held h = match h with Hint_held -> true | Hint_lost -> false

(** j crosses the epoch boundary. Monotone and unguarded: the environment step
    the boundary race at message.rs:331-335 is waiting for. *)
let epoch_step s =
  match s.epoch with
  | Epoch_behind -> [ { s with epoch = Epoch_aligned } ]
  | Epoch_aligned -> []

(** j answers the competing author k. Pristine, k has its own [TokioMutex]
    (handler.rs:55-58, :510-512) so this is enabled whatever i's slot is doing;
    under {!Single_shared_vote_lock} the single lock forces it to wait for i. *)
let peer_step mut s =
  let slot_free =
    match mut with
    | Pristine | No_empty_parent_reissue | No_one_epoch_ahead_arm -> true
    | Single_shared_vote_lock -> slot_is_free s.req
  in
  match s.peer with
  | Peer_waiting -> if slot_free then [ { s with peer = Peer_answered } ] else []
  | Peer_answered -> []

(** i sends the next vote request for h (certifier.rs:143-172). Its parents
    vector is [vec![]] when the hint is lost and exactly M when it is held. *)
let send_step s =
  if task_is_live s.task && slot_is_free s.req then [ { s with req = Req_pending } ]
  else []

(** A non-fatal network error clears i's hint (certifier.rs:191-195), so the
    next attempt carries an empty parents vector again. Unbounded on purpose:
    bounding it would be a fairness assumption, and no statement of this family
    needs one. *)
let hint_reset_step s =
  if task_is_live s.task && slot_is_free s.req && hint_is_held s.hint then
    [ { s with hint = Hint_lost } ]
  else []

(** The proposer re-proposes the last stored header after [max_header_delay]
    (proposer.rs:758-760, :802-822) and the certifier spawns a fresh vote task
    (certifier.rs:295-311) whose [missing_parents] starts at [None]
    (certifier.rs:133). *)
let repropose_step s =
  match s.task with
  | Task_dead -> [ { s with task = Task_live; hint = Hint_lost } ]
  | Task_live -> []
  | Task_voted -> []

(** A fresh [vote_inner] run (handler.rs:577-596) on a cache slot that has
    already been cleared by [take()].

    [header.validate] is the first thing [vote_inner] does (handler.rs:612 ->
    header.rs:100-107), so an epoch mismatch short-circuits every later branch.
    With the epochs aligned there are three outcomes: j reports the parents it
    lacks (handler.rs:659-668, only reachable on an empty parents vector), j
    votes (handler.rs:772-872), or the evaluation ends in a final error - either
    the [max_header_delay] timeout at handler.rs:582-586, whose [?] returns
    BEFORE the cache write at :591-595 and so leaves the slot cleared, or a
    header-level rejection such as [TooNew] (handler.rs:622-630), [TooOld]
    (handler.rs:887-894) or [UnknownExecutionResult] (handler.rs:642-650), which
    IS cached as [Error] at :591-595. Both reach i as
    [PrimaryResponse::Error] (message.rs:337-357) and are fatal
    (network/mod.rs:487-488, certifier.rs:185-190). *)
let eval_inner mut s =
  let released s' = { s' with req = Req_idle } in
  match s.epoch with
  | Epoch_behind -> (
      match mut with
      | Pristine | No_empty_parent_reissue | Single_shared_vote_lock ->
          (* message.rs:331-335: RecoverableError. network/mod.rs:474-484
             retries in place; the branch that kills the task is the sixth
             send still meeting a behind voter (:481-483 then :487-488). *)
          [
            released { s with cache = Cache_recoverable };
            released { s with cache = Cache_recoverable; task = Task_dead };
          ]
      | No_one_epoch_ahead_arm ->
          (* message.rs:337-357 generic arm: Error, hence RPCError, hence
             fatal at certifier.rs:185-190. *)
          [ released { s with cache = Cache_final; task = Task_dead } ])
  | Epoch_aligned ->
      let voted = released { s with cache = Cache_vote; task = Task_voted } in
      let timed_out = released { s with cache = Cache_none; task = Task_dead } in
      let rejected = released { s with cache = Cache_final; task = Task_dead } in
      (match s.hint with
      | Hint_lost ->
          (* parents.is_empty(): handler.rs:659-669 consults
             check_for_missing_parents, which may or may not report a gap. *)
          [
            released { s with cache = Cache_missing; hint = Hint_held };
            voted;
            timed_out;
            rejected;
          ]
      | Hint_held ->
          (* parents supplied: handler.rs:670-686 accepts them, then :693
             blocks until every parent is stored. *)
          [ voted; timed_out; rejected ])

(** j answers the request from i currently under evaluation: the dispatch on the
    TAKEN cache slot at handler.rs:513-565, then [vote_inner]. *)
let answer_step mut s =
  if slot_is_free s.req then []
  else
    match s.cache with
    | Cache_missing -> (
        match s.hint with
        | Hint_lost -> (
            (* handler.rs:519-534 versus :549-562 *)
            match mut with
            | Pristine | No_one_epoch_ahead_arm | Single_shared_vote_lock ->
                [ { s with req = Req_idle; hint = Hint_held } ]
            | No_empty_parent_reissue ->
                [ { s with req = Req_idle; task = Task_dead } ])
        | Hint_held ->
            (* handler.rs:537-548: the parents match M exactly, so the match
               falls through to :577-596 with the slot already cleared. *)
            eval_inner mut { s with cache = Cache_none })
    | Cache_final ->
        (* handler.rs:564 replays the final answer and does NOT write the slot
           back, so the entry is gone afterwards. *)
        [ { s with req = Req_idle; cache = Cache_none; task = Task_dead } ]
    | Cache_vote ->
        (* the same replay arm for a cached vote (handler.rs:564). *)
        [ { s with req = Req_idle; cache = Cache_none; task = Task_voted } ]
    | Cache_none | Cache_recoverable ->
        (* handler.rs:517-518: the empty arm falls through to a fresh
           evaluation. *)
        eval_inner mut { s with cache = Cache_none }

(** The transition relation: one component advances per step. *)
let next_with mut s =
  List.concat
    [
      epoch_step s;
      peer_step mut s;
      send_step s;
      hint_reset_step s;
      repropose_step s;
      answer_step mut s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: j is exactly one epoch behind h, its cache slot for i is
    empty, i's certifier has just spawned its vote task so the hint is [None]
    (certifier.rs:133), nothing is in flight, and author k's competing request
    is waiting. *)
let initial =
  {
    cache = Cache_none;
    hint = Hint_lost;
    req = Req_idle;
    task = Task_live;
    epoch = Epoch_behind;
    peer = Peer_waiting;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Cache_missing_hint
      (** j's slot for i is [Some(MissingParents(M))] (handler.rs:55-58) *)
  | Cache_final_answer  (** j's slot for i is [Some(Error(_))] *)
  | Cache_recoverable_answer
      (** j's slot for i is [Some(RecoverableError(_))] *)
  | Cache_reevaluates
      (** j's slot for i is [None] or [Some(RecoverableError(_))]: the empty
          arm at handler.rs:517-518, the one that re-runs [vote_inner] *)
  | Author_holds_hint  (** i's [missing_parents] is [Some(M)] *)
  | Vote_request_in_flight
      (** j holds author i's evaluation slot (handler.rs:510-512) *)
  | Vote_task_live  (** i's vote task for h is still in the retry loop *)
  | Vote_task_dead  (** i's vote task for h ended on an [RPCError] *)
  | Vote_obtained  (** i holds j's vote for h *)
  | Voter_epoch_behind  (** [committee.epoch() + 1 = header.epoch()] at j *)
  | Peer_k_answered  (** j has answered author k's competing request *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Cache_missing_hint -> (
      match s.cache with
      | Cache_missing -> true
      | Cache_none | Cache_recoverable | Cache_final | Cache_vote -> false)
  | Cache_final_answer -> (
      match s.cache with
      | Cache_final -> true
      | Cache_none | Cache_missing | Cache_recoverable | Cache_vote -> false)
  | Cache_recoverable_answer -> (
      match s.cache with
      | Cache_recoverable -> true
      | Cache_none | Cache_missing | Cache_final | Cache_vote -> false)
  | Cache_reevaluates -> (
      match s.cache with
      | Cache_none | Cache_recoverable -> true
      | Cache_missing | Cache_final | Cache_vote -> false)
  | Author_holds_hint -> hint_is_held s.hint
  | Vote_request_in_flight -> Bool.not (slot_is_free s.req)
  | Vote_task_live -> task_is_live s.task
  | Vote_task_dead -> (
      match s.task with
      | Task_dead -> true
      | Task_live | Task_voted -> false)
  | Vote_obtained -> (
      match s.task with
      | Task_voted -> true
      | Task_live | Task_dead -> false)
  | Voter_epoch_behind -> (
      match s.epoch with Epoch_behind -> true | Epoch_aligned -> false)
  | Peer_k_answered -> (
      match s.peer with Peer_answered -> true | Peer_waiting -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Cache_missing_hint -> "cached(j,i,h) = MissingParents(M)"
  | Cache_final_answer -> "cached(j,i,h) = Error"
  | Cache_recoverable_answer -> "cached(j,i,h) = RecoverableError"
  | Cache_reevaluates -> "cached(j,i,h) in {none, RecoverableError}"
  | Author_holds_hint -> "hint_i(h) = M"
  | Vote_request_in_flight -> "evaluating(j,i,h)"
  | Vote_task_live -> "vote_task(i->j,h) = live"
  | Vote_task_dead -> "vote_task(i->j,h) = dead"
  | Vote_obtained -> "vote_j(h) @ i"
  | Voter_epoch_behind -> "epoch(j) + 1 = epoch(h)"
  | Peer_k_answered -> "replied(j,k)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every reachable
    world by test/t_vote_cache_retry_topos.ml. The hint reset
    (certifier.rs:191-195) and the re-propose (proposer.rs:802-822) both undo
    earlier steps, so reachability here is expected to be a preorder rather than
    a poset - but that is settled by RUNNING the gate, not by this comment. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state,
    mutation-parameterized transitions, the four-role view, the atom
    valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
