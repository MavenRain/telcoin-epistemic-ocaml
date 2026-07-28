(** The BATCH-ADMIT family statements, encoded over the {!Batch_admit_model}
    interpreted system. Every mechanism claim was re-verified against
    Telcoin-Association/telcoin-network at git 0c59c15b (working tree) while
    writing this module; file citations are to that checkout.

    {b What was mined.} [BatchValidator::validate_batch]
    (crates/batch-validator/src/validator.rs:39-82) is the only content check a
    peer's batch ever meets, and it meets it on exactly one of the four routes
    into [NodeBatchesCache]. The other three -
    [WorkerRequestHandler::process_gossip]'s prefetch
    (crates/consensus/worker/src/network/handler.rs:181-208),
    [BatchFetcher::fetch_for_primary_inner]
    (crates/consensus/worker/src/batch_fetcher.rs:177-200), and
    [WorkerToPrimary::store_synced_batches] on the certified branch
    (crates/consensus/worker/src/network/primary.rs:106-129) - enforce
    content-ADDRESSING only ([read_and_validate_batches_with_timeout] recomputes
    the digest at handle.rs:754-761 and checks nothing else). So the three
    statements below say what the gate really buys and, deliberately, what it
    does not: the model carries the unvalidated route as a live transition and
    every conjunct is stated to survive it.

    {b Reading guide for the K operands.}

    - S1's positive [K_V1 (no gated admission anywhere)] is knowledge about
      ANOTHER worker's store, not a projection of the knower's own view: the
      operand names [gated-admit_v2], which lives in [V2]'s cache and appears
      in no message [V1] receives ([process_report_batch] answers only the
      requesting stream, handler.rs:246; the only gossip is a digest,
      handle.rs:147-154). It is knowledge because [max_batch_gas] IGNORES its
      epoch argument (crates/types/src/worker/sealed_batch.rs:192-194), so the
      refusal a worker just made is the verdict every honest worker makes on
      the same bytes. It is not rigid: on a clean batch both workers DO admit
      through the gated path, so the operand is false at reachable states, and
      [V1]'s operative view class holds several reachable states - both
      discharged by tests in test/t_batch_admit.ml.
    - S1's [not K_V1 (v2 does not hold b)] is the R5 counterweight and the
      sharp end of the family: knowing the committee-wide GATED verdict is not
      knowing the committee's STORAGE state, because handler.rs:181-208 puts
      the batch in a peer's cache with no validator call at all. The witness
      pair is two reachable states with an identical [V1] view - the fetch-side
      worker has prefetched [b] in one and has an empty slot in the other.
    - S2's [not K_V2 (v1 refused b)] is the silence of a refusal stated as
      ignorance: the error goes back to the author on one stream and nothing
      gossips a negative verdict, so a worker holding a batch it never
      validated cannot tell whether a peer already threw the same bytes away.
    - S3's two [not K_V1] conjuncts are the [#[serde(skip)]] at
      sealed_batch.rs:86 stated as ignorance: [received_at] is written by every
      storing worker (handler.rs:251, batch_fetcher.rs:191, primary.rs:116) and
      read back locally (crates/consensus/executor/src/subscriber.rs:582), yet
      it is excluded from serialization and therefore from every message a peer
      could ever see.

    S2 and S3 each also carry a conjunct that is deliberately NOT a safety
    claim - S2's [EF (holds_v2 /\ carries-blob)] and S3's [EF relay-held_v2] -
    because a family that only asserted the gate would be true by omission. *)

open Batch_admit_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so a statement is never certified on the
          strength of an unreachable antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - gas-ceiling-refusal-is-a-committee-wide-verdict-but-not-a-storage-fact
    [security].

    Trigger: the batch's declared gas limits sum above the ceiling and the
    author's unicast [ReportBatch] to the gate-side worker has resolved
    (quorum_waiter.rs:84-116 -> handle.rs:168-190 -> handler.rs:231-263).

    Conjunct A - [not gated-admit_v1]: the worker refuses. The gate is
    verbatim [if total_possible_gas > max_tx_gas { return
    Err(BatchValidationError::HeaderMaxGasExceedsGasLimit { total_possible_gas,
    gas_limit: max_tx_gas }); }] (validator.rs:177-182), reached from
    [validate_batch] at :77, and [process_report_batch] short-circuits on it
    (handler.rs:244-246) BEFORE the [store.insert::<NodeBatchesCache>] at :252
    and before [report_others_batch] at :257-260.

    Conjunct B - [K_V1 (not gated-admit_v1 /\ not gated-admit_v2)]: the
    refusing worker knows no honest worker admits this batch through the
    content-gated path. That is knowledge of a global fact rather than a local
    one because [pub fn max_batch_gas(_epoch: Epoch) -> u64 { 30_000_000 }]
    (sealed_batch.rs:192-194) discards its epoch argument, making the bound a
    protocol constant instead of a per-node tunable; the operand quantifies
    over the OTHER worker's cache, which [V1] never observes.

    Conjunct C - [not K_V1 (not holds_v2)]: and yet the refusing worker does
    NOT know the batch is absent from its peer's store, because
    [process_gossip] (handler.rs:142-228) fetches by digest alone -
    [request_batches] at :192, [store.insert::<NodeBatchesCache>(digest,
    batch)] at :201-208 - with no [validate_batch] call anywhere on that route,
    and the digest re-check the fetch does make (handle.rs:754-761) is about
    content-addressing, not content.

    Mutation pin: [No_gas_ceiling] deletes validator.rs:177-182, which ADDS the
    transition [leg1 = Unreported -> leg1 = Passed] on an over-ceiling batch,
    making conjunct A false at a reachable trigger state. No sibling path
    repairs it - the decode, byte-size and base-fee steps check other things
    entirely (validator.rs:147-156, :122-141, :188-195) and the builder-side
    cap (crates/batch-builder/src/batch.rs:73-81) constrains honest authors
    only. The trigger stays reachable under the mutation, so the refutation is
    a value flip and not a vacuity. *)
let s_1 =
  let trigger =
    Formula.And (atom Content_over_ceiling, atom Reported_1)
  in
  let refuses = Formula.Not (atom Gated_admit_1) in
  let knows_the_committee_verdict =
    Formula.K
      ( Validator.V1,
        Formula.And
          (Formula.Not (atom Gated_admit_1), Formula.Not (atom Gated_admit_2))
      )
  in
  let does_not_know_the_peer_store =
    Formula.Not (Formula.K (Validator.V1, Formula.Not (atom Holds_2)))
  in
  {
    name = "gas-ceiling-refusal-is-a-committee-verdict-not-a-storage-fact";
    bucket = Statements.Security;
    formula =
      Formula.Ag
        (Formula.Implies
           ( trigger,
             Formula.conj
               [
                 refuses;
                 knows_the_committee_verdict;
                 does_not_know_the_peer_store;
               ] ));
    antecedent = trigger;
  }

(** S2 - blob-rejection-binds-the-validated-path-only [security].

    Conjunct A - [AG (gated-admit_v1 \/ gated-admit_v2 -> not carries-blob)]:
    no worker ever admits a blob-carrying batch through the content-gated path.
    The gate is [if let Some(blob_tx) = transactions.iter().find(|tx|
    tx.is_eip4844()) { return Err(BatchValidationError::InvalidTx4844(..)); }]
    (validator.rs:198-206), reached from [validate_batch] at :73 - before the
    gas check at :77 - and the decode that precedes it does not reject 4844:
    [recover_signed_transaction] is [reth_recover_raw_transaction::<TransactionSigned>(tx)]
    (crates/tn-reth/src/txn_pool.rs:369-373), a plain 2718 decode of the
    consensus envelope, which is well-formed for a blob transaction without a
    sidecar. The transactions being screened are genuinely reachable: the
    worker pool is a stock reth eth pool and TN activates Cancun at genesis, so
    4844 transactions are admitted to pools rather than filtered earlier.

    Conjunct B - [carries-blob -> EF (holds_v2 /\ carries-blob)]: and the
    NETWORK-wide reading of conjunct A is false. A blob-carrying batch does
    reach an honest worker's [NodeBatchesCache], through the digest-only
    prefetch of handler.rs:181-208, whose only checks are the epoch (:201) and
    the digest re-check inside [request_batches] (handle.rs:754-768). Two
    further writers share that property: batch_fetcher.rs:177-200 stores what
    [request_batches] returned with no validator call, and primary.rs:106-111
    runs [validate_batch] only under [if !is_certified]. This conjunct is in
    the statement precisely so that conjunct A cannot be read as more than it
    is.

    Conjunct C - [AG (holds_v2 /\ carries-blob -> not K_V2 (refused_v1))]: the
    worker holding that unvalidated blob-carrying batch cannot learn that its
    peer already refused the same bytes. [process_report_batch] returns the
    error on the requesting stream only (handler.rs:246 via the per-peer
    unicast of handle.rs:168-190), and the sole worker gossip is
    [WorkerGossip::Batch(epoch, batch_hash)] (handle.rs:147-154), which carries
    no verdict.

    Mutation pin: [No_blob_reject] deletes validator.rs:202-204, which ADDS the
    transition [leg = Unreported -> leg = Passed] on a blob-carrying batch and
    makes conjunct A false at a reachable state. No sibling path repairs it -
    the decode accepts consensus 4844, the byte cap does not bite on a small
    envelope, the gas ceiling does not bite on an ordinary [gas_limit], and the
    builder-side skip (batch.rs:88-94) is producer-side only. *)
let s_2 =
  let gated_admission =
    Formula.Or (atom Gated_admit_1, atom Gated_admit_2)
  in
  let gate_holds =
    Formula.Ag
      (Formula.Implies (gated_admission, Formula.Not (atom Content_carries_blob)))
  in
  let bypass_is_real =
    Formula.Implies
      ( atom Content_carries_blob,
        Formula.Ef (Formula.And (atom Holds_2, atom Content_carries_blob)) )
  in
  let holder_cannot_see_the_peer_refusal =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Holds_2, atom Content_carries_blob),
           Formula.Not (Formula.K (Validator.V2, atom Refused_1)) ))
  in
  {
    name = "blob-rejection-binds-the-validated-path-only";
    bucket = Statements.Security;
    formula =
      Formula.conj
        [ gate_holds; bypass_is_real; holder_cannot_see_the_peer_refusal ];
    antecedent = Formula.And (atom Content_carries_blob, atom Reported_1);
  }

(** S3 - relay-preserves-the-author-digest-while-the-receipt-stamp-stays-private
    [safety].

    Conjunct A - [AG (key = digest(stored))]: every copy of the batch in a
    [NodeBatchesCache] still content-addresses its own key, even though every
    storing worker writes a local timestamp into the value first
    (handler.rs:251, batch_fetcher.rs:191, primary.rs:116). That holds because
    [Batch::received_at] carries [#[serde(skip)]] (sealed_batch.rs:86) with the
    comment [// This field changes often so don't serialize (i.e. don't use it
    in the digest)] (:87), and [Batch::digest] hashes [encode(self)]
    (:119-124); [seal_slow] notes the exclusion in so many words at :157-158.
    The receive path is what would notice: [let verified_hash =
    batch.clone().seal_slow().digest(); if digest != verified_hash { return
    Err(BatchValidationError::InvalidDigest); }] (validator.rs:41-45).

    Conjunct B - [clean(b) -> EF relay-held_v2]: and that exclusion is
    load-bearing for relay, not merely tidy. A worker that has stamped its own
    copy can still serve it to a peer whose [request_batches] recomputes
    [batch.digest()] and compares it to the digest it asked for
    (handle.rs:754-761).

    Conjunct C - [AG (gated-admit_v1 /\ holds_v2 -> not K_V1 (received-at_v2 =
    late) /\ not K_V1 (received-at_v2 != late))]: two workers holding the same
    batch under the same key hold different local stamps, and the gate-side
    worker knows neither that its peer's stamp is the later reading nor that it
    is not. The stamp is a real, persisted, locally-read field
    (crates/consensus/executor/src/subscriber.rs:582 reads
    [block.received_at()]), so this is ignorance about a live variable rather
    than about a variable the model invented.

    Mutation pin: [Digest_covers_received_at] deletes the [#[serde(skip)]] at
    sealed_batch.rs:86. It makes conjunct A false at a reachable state (a
    stamped copy no longer hashes to its key) and REMOVES the relay transition
    that conjunct B asserts, because the fetching peer now recomputes a
    different digest and drops the answer as unrequested
    (handle.rs:754-761). No sibling path repairs it: [SealedBatch::split]
    (sealed_batch.rs:51-53), [Batch::seal] (:149-151) and [Batch::seal_slow]
    (:159-162) all route through the one [digest()] helper. The author's own
    copy is never stamped (batch.rs:122-123, worker.rs:359), so fetching from
    the AUTHOR survives the mutation - the trigger stays reachable and the
    refutation is a value flip. *)
let s_3 =
  let key_is_the_content_address = Formula.Ag (atom Key_matches_digest) in
  let relay_actually_works =
    Formula.Implies (atom Content_is_clean, Formula.Ef (atom Relay_held_2))
  in
  let both_hold = Formula.And (atom Gated_admit_1, atom Holds_2) in
  let stamp_stays_private =
    Formula.Ag
      (Formula.Implies
         ( both_hold,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom Tick2_late)),
               Formula.Not
                 (Formula.K (Validator.V1, Formula.Not (atom Tick2_late))) ) ))
  in
  {
    name = "relay-keeps-the-author-digest-while-the-receipt-stamp-stays-private";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [ key_is_the_content_address; relay_actually_works; stamp_stays_private ];
    antecedent = both_hold;
  }

(** The family's statements. *)
let all = [ s_1; s_2; s_3 ]

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
