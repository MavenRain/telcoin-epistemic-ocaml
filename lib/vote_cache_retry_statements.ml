(** The VOTE_CACHE_RETRY statement family, encoded over the
    {!Vote_cache_retry_model} interpreted system. Three statements mined from
    the primary's per-author vote response cache and the certifier retry loop
    that feeds it: the empty-parent re-issue that keeps a lost hint from
    becoming a permanent bilateral deadlock, the one-epoch-ahead classification
    that keeps a boundary race out of the final-answer slot, and the per-author
    keying of the evaluation mutex. File citations refer to
    Telcoin-Association/telcoin-network at 0c59c15b.

    {2 Reading guide for the K operands}

    There is exactly one positive knowledge operand in the family and three
    ignorance operands; none of them is a projection of its own knower's view or
    rigid over the reachable set.

    - [K_V1(cached(j,i,h) = MissingParents(M))] (S1 conjunct C) is the positive
      claim. Its operand is a slot in {b j's} process
      ([auth_last_vote], handler.rs:93 and :55-58), of which i's view - its own
      hint, its own vote task, whether a request is outstanding - contains no
      component. It is not rigid: the slot is [None] at the initial state, and
      [Error], [Vote] and [RecoverableError] are all reachable. The V1-view
      class at the operative state is not a singleton either: it contains both
      values of [replied(j,k)], because i has no way to see whether j has
      answered the other committee author. The contingency suite proves both
      halves.

    - [~K_V1(epoch(j) + 1 = epoch(h))] (S2 conjunct C) is the sharpest
      ignorance in the family, and it is the whole reason the classification arm
      has to exist. network/mod.rs:487-488 collapses BOTH
      [PrimaryResponse::RecoverableError(PrimaryRPCError(s))] and
      [PrimaryResponse::Error(PrimaryRPCError(s))] into the same
      [NetworkError::RPCError(s)], and certifier.rs:186 matches only the
      variant, never the payload. A vote task that died because the voter was
      one epoch behind for six sends is therefore bit-identical, at i, to one
      that died because the header was rejected outright.

    - [~K_V0(vote_task(i->j,h) = dead)] (S2 conjunct D) is the mirror ignorance
      at the voter. The wire request is [Vote { header, parents }]
      (network/message.rs:52-58) with no session id and no attempt counter, so
      after returning a final answer j cannot tell whether it has terminated i's
      certifier task or whether i will re-propose the same header
      (proposer.rs:802-822) and ask again.

    {2 Honest scope}

    S3 conjunct B (the evaluation slot is always released) is {b not} the
    mutation-sensitive half of S3 and is not claimed to be: it is the "bounds"
    half of the mechanism, and it holds under {!Vote_cache_retry_model.Single_shared_vote_lock}
    too. What that mutation refutes is conjunct A, the isolation half. The
    release itself is doubly guaranteed in the real code - the
    [max_header_delay] timeout at handler.rs:582-586 and the network layer's
    per-request [cancel] oneshot at network/mod.rs:1523 and :1550 - which is
    exactly why deleting either one alone would have been a repaired mutation
    and the keying was chosen instead. *)

open Vote_cache_retry_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;  (** statement name, unique across every family *)
  bucket : Statements.bucket;  (** the shared bucket vocabulary *)
  formula : atom Formula.t;  (** the CTLK claim *)
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a false antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - empty-parent-retry-reissues-the-missing-parent-hint [liveness].

    Once j has answered i's header h with "I am missing M", an empty-parented
    retry from i is answered by re-issuing exactly M rather than by falling
    through to the wrong-number-of-parents branch.

    (A) The hint is always re-delivered:
    AG( cached(j,i,h) = MissingParents(M) /\\ ~hint_i(h) /\\ live -> AF hint_i(h) ).
    The empty retry takes handler.rs:519-534, which writes the entry back
    verbatim (:527-532) and returns [MissingParents(missing)] (:533); i stores
    it at certifier.rs:180-184. The first attempt of every vote request is
    empty by construction (certifier.rs:133 and :143-168
    [.unwrap_or(Ok(vec![]))?]), so this arm is not an edge case - it is the
    normal shape of a retry whose hint did not survive.

    (B) That answer costs i nothing:
    AG( cached = MissingParents(M) /\\ evaluating /\\ ~hint_i(h) ->
    AX( cached = MissingParents(M) /\\ ~dead ) ). The write-back at :527-532 is
    what keeps the entry, and the early [return Ok(..)] at :533 is what keeps
    the vote task alive: the alternative branch at :549-562 returns
    [WrongNumberOfParents], which message.rs:337-357 turns into
    [PrimaryResponse::Error], network/mod.rs:487-488 turns into
    [NetworkError::RPCError], and certifier.rs:185-190 treats as irrecoverable.

    (C) The requester knows the voter is holding the hint for it:
    AG( hint_i(h) /\\ live /\\ ~evaluating -> K_V1( cached(j,i,h) = MissingParents(M) ) ).
    The operand is a slot in j's process (handler.rs:93, :55-58) and i's view
    carries no component of it; what makes the knowledge true is the protocol
    invariant that the hint is delivered only together with the write-back
    (handler.rs:661-668 then :591-595, or :527-532), and nothing clears the slot
    while i's task is alive and idle. It is not degenerate: the class also
    contains both values of [replied(j,k)].

    Mutation pin: {!Vote_cache_retry_model.No_empty_parent_reissue} deletes the
    [if parents.is_empty()] block at handler.rs:520-534. The empty retry then
    takes :549-562, which writes [MissingParents(missing)] back into the slot
    and returns a fatal error - so conjunct B fails at once and conjunct A fails
    forever: a fresh vote task starts from [missing_parents = None]
    (certifier.rs:133), the proposer re-sends the SAME stored header
    (proposer.rs:802-822) so the cache key at handler.rs:577-579 is unchanged,
    and the entry that was just written back sends the next empty retry into
    exactly the same branch. Sibling-repair hunt: the handle retries only
    [RecoverableError] (network/mod.rs:474-484); the fast recast at
    handler.rs:494-506 needs a prior vote; and j acquiring the parent by itself
    is no help, because the cached-[MissingParents] arm returns before
    [vote_inner] and therefore before [check_for_missing_parents]
    (handler.rs:879-924) runs again. The one route that DOES clear a slot -
    the replay arm at handler.rs:564, which does not write back - is not on this
    path, because :549-562 writes back explicitly. *)
let s1 =
  let hint_is_reissued =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             ( atom Cache_missing_hint,
               Formula.And
                 (Formula.Not (atom Author_holds_hint), atom Vote_task_live) ),
           Formula.Af (atom Author_holds_hint) ))
  in
  let retry_is_free =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             ( atom Cache_missing_hint,
               Formula.And
                 ( atom Vote_request_in_flight,
                   Formula.Not (atom Author_holds_hint) ) ),
           Formula.Ax
             (Formula.And
                (atom Cache_missing_hint, Formula.Not (atom Vote_task_dead))) ))
  in
  let author_knows_the_slot_is_pinned =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             ( atom Author_holds_hint,
               Formula.And
                 ( atom Vote_task_live,
                   Formula.Not (atom Vote_request_in_flight) ) ),
           Formula.K (Validator.V1, atom Cache_missing_hint) ))
  in
  {
    name = "empty-parent-retry-reissues-the-missing-parent-hint";
    bucket = Statements.Liveness;
    formula =
      Formula.conj
        [ hint_is_reissued; retry_is_free; author_knows_the_slot_is_pinned ];
    antecedent =
      Formula.And
        ( atom Cache_missing_hint,
          Formula.And
            (Formula.Not (atom Author_holds_hint), atom Vote_task_live) );
  }

(** S2 - one-epoch-ahead-rejection-is-classified-recoverable [liveness].

    A vote request that arrives while the voter is exactly one epoch behind is
    classified RECOVERABLE, so it is never frozen into the voter's final-answer
    slot and the requester's vote task can survive it.

    (A) The boundary race never becomes a final answer:
    AG( epoch(j)+1 = epoch(h) /\\ evaluating /\\ cached in {none, RecoverableError}
    -> AX( cached(j,i,h) /= Error ) ). [Header::validate] is the first thing
    [vote_inner] does (handler.rs:612 -> header.rs:100-107), so the rejection is
    [InvalidHeader(InvalidEpoch { ours, theirs })] with [theirs = ours + 1], and
    [into_error_ref] sends exactly that shape to
    [Self::RecoverableError] (message.rs:331-335) instead of the generic
    [Self::Error] arm (:337-357). The cached value at handler.rs:591-595 is
    therefore the recoverable one.

    (B) And it leaves a live continuation:
    AG( same antecedent -> EX( cached = RecoverableError /\\ live ) ).
    [PrimaryNetworkHandle::request_vote] loops on [RecoverableError]
    (network/mod.rs:474-484) instead of returning, so the task is not killed by
    the first rejection; the sixth send still meeting a behind voter DOES kill
    it (:481-483 then :487-488 then certifier.rs:185-190), which is why this is
    stated as EX and not as AX - the retry budget is real and is modelled.

    (C) The requester cannot tell a boundary race from a rejection:
    AG( dead -> ~K_V1( epoch(j)+1 = epoch(h) ) ). network/mod.rs:487-488
    collapses [RecoverableError(PrimaryRPCError(s))] and
    [Error(PrimaryRPCError(s))] into one [NetworkError::RPCError(s)] and
    certifier.rs:186 matches only the variant, so a task killed by a persistent
    boundary race and a task killed by a header rejection are indistinguishable
    at i.

    (D) And the voter cannot tell that its final answer killed anything:
    AG( cached = Error /\\ ~evaluating -> ~K_V0( dead ) ). The request carries
    only [Vote { header, parents }] (network/message.rs:52-58) - no session id,
    no attempt counter - and the same digest may well come back, because the
    proposer re-proposes the stored header after [max_header_delay]
    (proposer.rs:758-760, :802-822).

    Mutation pin: {!Vote_cache_retry_model.No_one_epoch_ahead_arm} deletes the
    [if *theirs == ours + 1] guarded arm at message.rs:331-335. [InvalidEpoch]
    then falls into the generic [Self::Error] arm, so the very first
    boundary-race rejection is cached as final (conjunct A refuted) and killed
    on arrival (conjunct B refuted): the handle does not loop on [Error]
    (network/mod.rs:474-484 tests only [RecoverableError]) and
    certifier.rs:185-190 is fatal. Sibling-repair hunt: the certifier's own loop
    retries only NON-[RPCError] errors (certifier.rs:191-196); the re-propose
    re-sends the same header so the cache key at handler.rs:577-579 does not
    move (proposer.rs:802-822); and the fast recast at handler.rs:494-506 needs
    a prior vote. The one genuine relief is modelled rather than omitted: the
    replay arm at handler.rs:564 does NOT write the slot back after [take()]
    (handler.rs:513-515), so a later attempt does re-evaluate - which is exactly
    why conjunct A is stated over the step that caches the rejection and not as
    "the answer is replayed forever". *)
let s2 =
  let race =
    Formula.And
      ( atom Voter_epoch_behind,
        Formula.And (atom Vote_request_in_flight, atom Cache_reevaluates) )
  in
  let never_frozen_final =
    Formula.Ag
      (Formula.Implies (race, Formula.Ax (Formula.Not (atom Cache_final_answer))))
  in
  let leaves_a_live_continuation =
    Formula.Ag
      (Formula.Implies
         ( race,
           Formula.Ex
             (Formula.And (atom Cache_recoverable_answer, atom Vote_task_live))
         ))
  in
  let author_cannot_see_the_skew =
    Formula.Ag
      (Formula.Implies
         ( atom Vote_task_dead,
           Formula.Not (Formula.K (Validator.V1, atom Voter_epoch_behind)) ))
  in
  let voter_cannot_see_the_kill =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             ( atom Cache_final_answer,
               Formula.Not (atom Vote_request_in_flight) ),
           Formula.Not (Formula.K (Validator.V0, atom Vote_task_dead)) ))
  in
  {
    name = "one-epoch-ahead-rejection-is-classified-recoverable";
    bucket = Statements.Liveness;
    formula =
      Formula.conj
        [
          never_frozen_final;
          leaves_a_live_continuation;
          author_cannot_see_the_skew;
          voter_cannot_see_the_kill;
        ];
    antecedent = race;
  }

(** S3 - per-author-vote-slot-isolates-committee-authors [fairness].

    The voter keeps one evaluation mutex PER committee author, so a header from
    a slow author holds up only that author's slot.

    (A) Another author can be answered without waiting for the slot to clear:
    AG( evaluating(j,i,h) /\\ ~replied(j,k) -> E[ evaluating(j,i,h) U replied(j,k) ] ).
    The map is keyed by [AuthorityIdentifier] (handler.rs:55-58, preloaded per
    authority at :111-116) and the guard is taken per author at
    handler.rs:510-512 under the verbatim comment "Each committee member has
    it's own lock so different authorities can be voted on in parallel but only
    one vote for an authority can proceed at a time". The until-form is the
    point: k is answered while i's evaluation is still running, not merely at
    some later time once it has finished.

    (B) And no slot is held forever: AG( evaluating(j,i,h) -> AF ~evaluating(j,i,h) ).
    This matters because [vote_inner] genuinely blocks - on
    [notify_read_parent_certificates] (handler.rs:693 ->
    certificate_store.rs [notify_read], which has no internal timeout) and on
    [sync_header_batches] (handler.rs:742). The release is doubly guaranteed: the
    [max_header_delay] timeout at handler.rs:582-586, and the network layer's
    per-request [cancel] oneshot (network/mod.rs:1523, :1550), which drops the
    vote future and with it the guard.

    Mutation pin: {!Vote_cache_retry_model.Single_shared_vote_lock} replaces the
    per-author lookup at handler.rs:510 with a single shared lock. Conjunct A is
    refuted: every path that reaches [replied(j,k)] must first leave
    [evaluating(j,i,h)], which is precisely serialisation. Sibling-repair hunt:
    [PrimaryNetwork::process_vote_request] (network/mod.rs:1517-1554) does spawn
    one task per request, but with the map collapsed all of them contend for the
    SAME mutex, so the spawn is not a repair; [spawn_task] is documented
    non-critical (types/src/task_manager.rs), so a stuck evaluation just holds
    the lock rather than shutting the node down; [requested_parents]
    (handler.rs:897-921) is a different [parking_lot] mutex held only across a
    synchronous filter. Conjunct B is deliberately NOT pinned by this mutation -
    it survives it, because the timeout and the cancel both still fire. R8: the
    deleted keying is a real isolation gate, not a sibling path the code would
    have taken anyway. *)
let s3 =
  let other_author_is_not_serialised =
    Formula.Ag
      (Formula.Implies
         ( Formula.And
             (atom Vote_request_in_flight, Formula.Not (atom Peer_k_answered)),
           Formula.Eu (atom Vote_request_in_flight, atom Peer_k_answered) ))
  in
  let slot_is_always_released =
    Formula.Ag
      (Formula.Implies
         ( atom Vote_request_in_flight,
           Formula.Af (Formula.Not (atom Vote_request_in_flight)) ))
  in
  {
    name = "per-author-vote-slot-isolates-committee-authors";
    bucket = Statements.Fairness;
    formula =
      Formula.conj [ other_author_is_not_serialised; slot_is_always_released ];
    antecedent =
      Formula.And
        (atom Vote_request_in_flight, Formula.Not (atom Peer_k_answered));
  }

(** The family's statements: the re-issue that saves a lost hint, the
    classification that saves a boundary race, and the keying that saves the
    other authors. *)
let all = [ s1; s2; s3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st = Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

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
