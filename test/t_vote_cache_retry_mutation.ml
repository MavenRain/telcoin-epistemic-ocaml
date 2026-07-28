(** Confirm-by-mutation pins for the VOTE_CACHE_RETRY family. Three gate
    deletions, one per statement, each asserted in BOTH directions (the
    statement proves pristine and refutes under the mutation) and each also
    asserted to leave the other two statements alone, so that a pin cannot pass
    because some OTHER statement of the family flipped.

    - {!Vote_cache_retry_model.No_empty_parent_reissue} deletes the
      [if parents.is_empty() { ... }] block at handler.rs:520-534, so an empty
      retry against a cached [MissingParents(M)] takes the wrong-count branch at
      handler.rs:549-562 instead. That branch writes [MissingParents(missing)]
      back into the slot (:551-556) and returns
      [WrongNumberOfParents(|M|, 0)], which message.rs:337-357 makes an
      [Error], network/mod.rs:487-488 makes an [RPCError] and
      certifier.rs:185-190 treats as fatal. No sibling path repairs it: a fresh
      vote task starts from [missing_parents = None] (certifier.rs:133), the
      proposer re-sends the SAME stored header (proposer.rs:802-822) so the
      cache key at handler.rs:577-579 does not move, the handle retries only
      [RecoverableError] (network/mod.rs:474-484), the fast recast at
      handler.rs:494-506 needs a prior vote, and j obtaining the parent by
      itself is irrelevant because the cached-[MissingParents] arm returns
      before [vote_inner] and so before [check_for_missing_parents]
      (handler.rs:879-924) ever runs again. Unlike the replay arm at
      handler.rs:564, this branch WRITES THE SLOT BACK, so the deadlock is
      permanent rather than one-shot.

    - {!Vote_cache_retry_model.No_one_epoch_ahead_arm} deletes the
      [if *theirs == ours + 1] guarded arm at message.rs:331-335, so
      [InvalidEpoch] falls into the generic [Self::Error] arm at :337-357. The
      first boundary-race rejection is then cached as final AND kills the vote
      task on arrival, since the handle loops only on [RecoverableError]
      (network/mod.rs:474-484). No sibling path repairs it: the certifier's own
      loop retries only NON-[RPCError] errors (certifier.rs:191-196) and the
      re-propose re-sends the same header (proposer.rs:802-822). The one genuine
      relief - the replay arm at handler.rs:564 leaving the slot cleared after
      [take()] - is modelled, and the statement is stated over the caching step
      so that it survives it.

    - {!Vote_cache_retry_model.Single_shared_vote_lock} replaces the per-author
      lookup at handler.rs:510 with a single shared lock, so author k can only
      be answered while author i's slot is free. No sibling path repairs it:
      [PrimaryNetwork::process_vote_request] (network/mod.rs:1517-1554) spawns
      one task per request but with the map collapsed they all contend for the
      same mutex; the per-request [cancel] oneshot (network/mod.rs:1523, :1550)
      bounds the HOLD DURATION - which is why it repairs a deletion of the inner
      timeout at handler.rs:582-586 and why this mutation is anchored on the
      keying instead - but supplies no cross-identity concurrency; and
      [requested_parents] (handler.rs:897-921) is a different mutex, held only
      across a synchronous filter. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Vote_cache_retry_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Vote_cache_retry_model.Checker.make (Vote_cache_retry_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Vote_cache_retry_statements.name name))
    Vote_cache_retry_statements.all

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " flips to refuted under the mutation")
            false
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Vote_cache_retry_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Vote_cache_retry_model.Pristine (fun sys ->
          Alcotest.(check bool)
            (name ^ " proves on the pristine model")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Vote_cache_retry_statements.prove sys st)))

(** A statement that must be INSENSITIVE to a mutation: the deletion belongs to
    another gate, so attribution stays clean. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " is untouched by this unrelated deletion")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Vote_cache_retry_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The statements a given deletion must NOT disturb. *)
let insensitive mut names =
  List.map
    (fun n -> Alcotest.test_case (n ^ ":survives") `Quick (survives_under mut n))
    names

(** S1's name. *)
let s1 = "empty-parent-retry-reissues-the-missing-parent-hint"

(** S2's name. *)
let s2 = "one-epoch-ahead-rejection-is-classified-recoverable"

(** S3's name. *)
let s3 = "per-author-vote-slot-isolates-committee-authors"

let () =
  Alcotest.run "vote_cache_retry_mutation"
    [
      ( "empty-parent-reissue",
        pin Vote_cache_retry_model.No_empty_parent_reissue s1
        @ insensitive Vote_cache_retry_model.No_empty_parent_reissue [ s2; s3 ]
      );
      ( "one-epoch-ahead-classification",
        pin Vote_cache_retry_model.No_one_epoch_ahead_arm s2
        @ insensitive Vote_cache_retry_model.No_one_epoch_ahead_arm [ s1; s3 ] );
      ( "per-author-vote-slot",
        pin Vote_cache_retry_model.Single_shared_vote_lock s3
        @ insensitive Vote_cache_retry_model.Single_shared_vote_lock [ s1; s2 ]
      );
    ]
