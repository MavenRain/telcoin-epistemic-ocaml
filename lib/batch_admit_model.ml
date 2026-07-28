(** Finite interpreted system for the BATCH-ADMIT family: the content checks a
    worker runs on a peer's batch before it writes it to [NodeBatchesCache],
    and the digest-only fetch route that reaches the same cache WITHOUT those
    checks.

    Mechanisms modeled, keyed to Telcoin-Association/telcoin-network (git
    0c59c15b, working tree). Every line span below was opened in this checkout
    while writing this module.

    - {b the content-gated admission path.}
      [WorkerRequestHandler::process_report_batch]
      (crates/consensus/worker/src/network/handler.rs:231-263) checks committee
      membership (:237-239), then runs [self.validator.validate_batch(...)?]
      (:244-246) and only afterwards splits, stamps and stores:
      [let (mut batch, digest) = sealed_batch.split(); batch.set_received_at(now());
      store.insert::<NodeBatchesCache>(&digest, &batch)] (:248-254), then
      reports the digest to its primary (:257-260). [BatchValidator::validate_batch]
      (crates/batch-validator/src/validator.rs:39-82) is, in order: the digest
      recomputation (:41-45), worker id (:48-53), epoch (:55-60), byte size
      (:67 -> :122-141), decode (:70 -> :147-156), the EIP-4844 rejection
      (:73 -> :198-206) and the gas ceiling (:77 -> :162-185). Order matters
      here: the blob gate runs BEFORE the gas gate, so deleting one does not
      admit what the other catches.
    - {b the gas ceiling is a protocol constant, not a node tunable.} The gate
      is verbatim [if total_possible_gas > max_tx_gas { return
      Err(BatchValidationError::HeaderMaxGasExceedsGasLimit { .. }); }]
      (validator.rs:177-182) over [max_tx_gas = max_batch_gas(epoch)], and
      [pub fn max_batch_gas(_epoch: Epoch) -> u64 { 30_000_000 }]
      (crates/types/src/worker/sealed_batch.rs:192-194) IGNORES its epoch
      argument. Every honest worker in every epoch therefore returns the same
      verdict on the same bytes, which is what turns one worker's local refusal
      into knowledge of a committee-wide verdict.
    - {b the EIP-4844 rejection.} [validate_no_blob_txs]
      (validator.rs:198-206): [if let Some(blob_tx) = transactions.iter().find(|tx|
      tx.is_eip4844()) { return Err(BatchValidationError::InvalidTx4844(..)); }].
      The producer side has an independent skip at
      crates/batch-builder/src/batch.rs:88-94, but that governs honest authors
      only; the receive-side gate is the one that binds a Byzantine author.
    - {b the digest-only fetch route - the repair path this family refuses to
      omit.} [process_gossip] (handler.rs:142-228) accepts
      [WorkerGossip::Batch(epoch, batch_hash)] - the message [source] is
      DISCARDED at :144 and only the topic (:151-156) and the epoch (:157-161)
      are checked - and when the digest is not already in the local cache
      (:167-170) it calls [self.network_handle.request_batches(&mut missing)]
      (:192) and stores the answer with only an epoch re-check:
      [store.insert::<NodeBatchesCache>(digest, batch)] (:201-208). No
      [validate_batch] anywhere on that path. What [request_batches] enforces
      is content-ADDRESSING only: [read_and_validate_batches_with_timeout]
      recomputes [let batch_digest = batch.digest();] and rejects a batch that
      was not requested (handle.rs:754-761) or is a duplicate (:763-768) -
      nothing about gas, blobs or base fee. Two more writers share that
      property: [BatchFetcher::fetch_for_primary_inner]
      (crates/consensus/worker/src/batch_fetcher.rs:177-200) stamps and inserts
      whatever [request_batches] returned, and
      [WorkerToPrimary::store_synced_batches]
      (crates/consensus/worker/src/network/primary.rs:86-129) runs
      [validate_batch] ONLY under [if !is_certified] (:106-111). So the
      network-wide reading of the blob gate is FALSE and this model says so:
      the bypass is a modeled transition, not an omission.
    - {b the digest excludes the receipt stamp.}
      [Batch::received_at] carries [#[serde(skip)]]
      (sealed_batch.rs:86) with the comment [// This field changes often so
      don't serialize (i.e. don't use it in the digest)] (:87), and
      [Batch::digest] hashes [encode(self)] (:119-124) with the note at :118;
      [seal_slow] routes through it (:159-162). Because of that a relaying
      worker may stamp its own local receipt time (handler.rs:251,
      batch_fetcher.rs:191, primary.rs:116) and still serve the batch under the
      author's digest. The author's own copy is never stamped
      (batch-builder/src/batch.rs:122-123 constructs [received_at: None] and
      worker.rs:359 stores it as built), which is why a fetch served by the
      AUTHOR survives the digest mutation while a fetch served by a RELAYER
      does not. The stamp is genuinely read back, locally:
      crates/consensus/executor/src/subscriber.rs:582
      [block.received_at().map(|t| t.elapsed().as_secs_f64())].
    - {b refusals are unicast and silent.} A batch is reported peer-by-peer:
      [QuorumWaiter::waiter] (crates/consensus/worker/src/quorum_waiter.rs:84-116)
      calls [network.report_batch(bls, sealed_batch.clone())] per peer and
      [WorkerNetworkHandle::report_batch] (handle.rs:168-190) is
      [self.handle.send_request(request, peer_bls)] whose failure surfaces as
      [WorkerResponse::Error] on that one stream. Nothing gossips a NEGATIVE
      verdict: [publish_batch] (handle.rs:147-154) carries a digest and an
      epoch and nothing else, and it is only reached after quorum
      (worker.rs:316-320).

    {b Components.} One batch [b] with a fixed content class; the author's
    unicast report leg to each of the two receiving workers; how the second
    worker came to hold [b] (content-gated admission, digest-only fetch from
    the author, digest-only fetch from the relayer) together with its local
    receipt stamp; and whether a stored copy still content-addresses.

    {b Role mapping.} [V1] is the GATE-SIDE receiving worker: its view is
    exactly its own report leg - nothing, a refusal whose error variant names
    the offending content class, or a pass - and it sees the transaction bytes
    in either decided case. [V2] is the receiving worker that ALSO runs the
    gossip prefetch: its view is its own report leg, its own holding
    (provenance and stamp - it knows which peer served it and what its own
    clock read) and the bytes it holds. Neither view contains the other
    worker's leg, the other worker's store, or the other worker's stamp:
    [process_report_batch] answers only the requesting stream, the gossip
    carries only a digest, and [received_at] never crosses the wire. [V0] is
    the author and [V3]..[V9] are idle; all are non-agents with the blank
    view and neither appears under [K] in any statement of this family.

    {b Deliberate scope.} [V1] is modeled as a report-only receiver and [V2] as
    the receiver that also prefetches, which halves the product without hiding
    anything: the unvalidated route IS in the model, at [V2], and every
    statement below is stated so that it survives that route rather than
    depending on its absence.

    {b Hidden branching.} Three initial states, one per content class, because
    the class is a property of the bytes the author put on the wire and is
    fixed for the run. A receiver that has not been reported to cannot tell the
    three apart. *)

(** The content class of the one batch this family follows. [Clean] passes
    every check in [validate_batch]; [Over_gas] has declared gas limits summing
    above [max_batch_gas] (validator.rs:177-182, sealed_batch.rs:192-194);
    [Has_blob] carries an EIP-4844 envelope (validator.rs:198-206). The
    consensus envelope of a 4844 transaction decodes fine - the recovery
    wrapper is a plain 2718 decode of [TransactionSigned]
    (crates/tn-reth/src/txn_pool.rs:369-373) - so the dedicated gate is the
    only thing that catches it. *)
type content = Clean | Over_gas | Has_blob

(** Total order index for {!content}. *)
let content_index = function Clean -> 0 | Over_gas -> 1 | Has_blob -> 2

(** Total order on {!content}. *)
let content_compare a b = Int.compare (content_index a) (content_index b)

(** The author's unicast report leg to one receiving worker
    (quorum_waiter.rs:84-116 -> handle.rs:168-190 ->
    handler.rs:231-263): [Unreported] means no [ReportBatch] request has been
    delivered to this worker, [Refused] means [validate_batch] returned an
    error that went back on that one stream, [Passed] means it returned [Ok]
    and the worker stamped and stored through the content-gated path. *)
type leg = Unreported | Refused | Passed

(** Total order index for {!leg}. *)
let leg_index = function Unreported -> 0 | Refused -> 1 | Passed -> 2

(** Total order on {!leg}. *)
let leg_compare a b = Int.compare (leg_index a) (leg_index b)

(** A worker's own reading of [now()] at the moment it stamps [received_at]
    (handler.rs:251). Two readings suffice: what matters is that the value is a
    local clock reading which never leaves the node. *)
type tick = Tick_early | Tick_late

(** Total order index for {!tick}. *)
let tick_index = function Tick_early -> 0 | Tick_late -> 1

(** Total order on {!tick}. *)
let tick_compare a b = Int.compare (tick_index a) (tick_index b)

(** How the prefetching worker came to hold [b], with the stamp it wrote.
    [Acq_none] is an empty cache slot; [Acq_gate] is the content-gated
    admission of handler.rs:248-254; [Acq_author] is the gossip-triggered
    digest-only fetch of handler.rs:181-208 served by the author, whose stored
    copy is unstamped (batch.rs:122-123, worker.rs:359); [Acq_relay] is the
    same digest-only fetch served instead by the other receiving worker, whose
    stored copy IS stamped (handler.rs:251). *)
type acq = Acq_none | Acq_gate of tick | Acq_author of tick | Acq_relay of tick

(** Total order on {!acq}; every constructor pairing spelled out. *)
let acq_compare a b =
  match (a, b) with
  | Acq_none, Acq_none -> 0
  | Acq_none, (Acq_gate _ | Acq_author _ | Acq_relay _) -> -1
  | (Acq_gate _ | Acq_author _ | Acq_relay _), Acq_none -> 1
  | Acq_gate t1, Acq_gate t2 -> tick_compare t1 t2
  | Acq_gate _, (Acq_author _ | Acq_relay _) -> -1
  | (Acq_author _ | Acq_relay _), Acq_gate _ -> 1
  | Acq_author t1, Acq_author t2 -> tick_compare t1 t2
  | Acq_author _, Acq_relay _ -> -1
  | Acq_relay _, Acq_author _ -> 1
  | Acq_relay t1, Acq_relay t2 -> tick_compare t1 t2

(** Whether every stored copy of [b] still content-addresses, i.e. the digest
    recomputed over its serialized fields equals the [NodeBatchesCache] key it
    is filed under. [Content_addressed] is what [#[serde(skip)]] on
    [received_at] (sealed_batch.rs:86-88) buys; [Stamp_shifted] is the state a
    stamping store leaves behind once that attribute is gone. *)
type binding = Content_addressed | Stamp_shifted

(** Total order index for {!binding}. *)
let binding_index = function Content_addressed -> 0 | Stamp_shifted -> 1

(** Total order on {!binding}. *)
let binding_compare a b = Int.compare (binding_index a) (binding_index b)

(** The joint global state: the batch's content class, the author's report leg
    to each receiving worker, how the prefetching worker holds [b], and the
    store-key binding. *)
type state = {
  content : content;
  leg1 : leg;
  leg2 : leg;
  acq2 : acq;
  binding : binding;
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = content_compare s1.content s2.content in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = leg_compare s1.leg1 s2.leg1 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = leg_compare s1.leg2 s2.leg2 in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = acq_compare s1.acq2 s2.acq2 in
        if Bool.not (Int.equal c3 0) then c3
        else binding_compare s1.binding s2.binding

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** What a receiving worker's own report leg told it. [Seen_nothing] is a
    worker the author never sent a [ReportBatch] to. [Seen_refused] carries the
    content class because the error variant names it -
    [BatchValidationError::HeaderMaxGasExceedsGasLimit] versus
    [InvalidTx4844] (validator.rs:178-181, :203) - and because the worker
    decoded the transaction bytes to get there. [Seen_passed] likewise carries
    the class the worker saw. *)
type seen =
  | Seen_nothing
  | Seen_refused of content
  | Seen_passed of content

(** Total order on {!seen}; every constructor pairing spelled out. *)
let seen_compare a b =
  match (a, b) with
  | Seen_nothing, Seen_nothing -> 0
  | Seen_nothing, (Seen_refused _ | Seen_passed _) -> -1
  | (Seen_refused _ | Seen_passed _), Seen_nothing -> 1
  | Seen_refused c1, Seen_refused c2 -> content_compare c1 c2
  | Seen_refused _, Seen_passed _ -> -1
  | Seen_passed _, Seen_refused _ -> 1
  | Seen_passed c1, Seen_passed c2 -> content_compare c1 c2

(** Whether a worker can read the batch's transaction bytes at all: it can once
    it has been reported to or has fetched the batch into its own cache, and
    not before. The digest a gossip announcement carries (handle.rs:147-154)
    says nothing about content. *)
type seen_content = Content_hidden | Content_known of content

(** Total order on {!seen_content}; every constructor pairing spelled out. *)
let seen_content_compare a b =
  match (a, b) with
  | Content_hidden, Content_hidden -> 0
  | Content_hidden, Content_known _ -> -1
  | Content_known _, Content_hidden -> 1
  | Content_known c1, Content_known c2 -> content_compare c1 c2

(** A validator's local view. [View_gate_side] is the report-only receiving
    worker: its own leg and nothing else. [View_fetch_side] is the receiving
    worker that also prefetches: its own leg, its own cache slot (provenance
    and stamp - it chose the serving peer and read its own clock) and the bytes
    it can read. [View_blank] is the constant blank view of the author [V0] and
    the idle [V3]..[V9]. NOTHING in either agent view mentions the other's leg,
    cache slot or stamp. *)
type view =
  | View_gate_side of seen
  | View_fetch_side of seen * acq * seen_content
  | View_blank

(** Total order on views: every constructor pairing spelled out, no wildcard
    arm. *)
let view_compare a b =
  match (a, b) with
  | View_blank, View_blank -> 0
  | View_blank, (View_gate_side _ | View_fetch_side _) -> -1
  | (View_gate_side _ | View_fetch_side _), View_blank -> 1
  | View_gate_side s1, View_gate_side s2 -> seen_compare s1 s2
  | View_gate_side _, View_fetch_side _ -> -1
  | View_fetch_side _, View_gate_side _ -> 1
  | View_fetch_side (s1, a1, c1), View_fetch_side (s2, a2, c2) ->
      let c = seen_compare s1 s2 in
      if Bool.not (Int.equal c 0) then c
      else
        let c' = acq_compare a1 a2 in
        if Bool.not (Int.equal c' 0) then c' else seen_content_compare c1 c2

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** What one worker's own report leg shows it, given the batch's class. *)
let seen_of leg content =
  match leg with
  | Unreported -> Seen_nothing
  | Refused -> Seen_refused content
  | Passed -> Seen_passed content

(** Whether the prefetching worker can read the batch bytes: it can once it has
    been reported to, or once it holds the batch in its own cache. *)
let content_seen_by_fetch_side s =
  match s.leg2 with
  | Refused | Passed -> Content_known s.content
  | Unreported -> (
      match s.acq2 with
      | Acq_none -> Content_hidden
      | Acq_gate _ | Acq_author _ | Acq_relay _ -> Content_known s.content)

(** View projection. [V1] and [V2] are the knowledge agents; [V0] (the author)
    and [V3]..[V9] are non-agents with the blank view and never appear under
    [K]. *)
let view v s =
  match v with
  | Validator.V1 -> View_gate_side (seen_of s.leg1 s.content)
  | Validator.V2 ->
      View_fetch_side
        (seen_of s.leg2 s.content, s.acq2, content_seen_by_fetch_side s)
  | Validator.V0 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_blank

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_gas_ceiling
      (** delete the batch-gas bound at
          crates/batch-validator/src/validator.rs:177-182 ([if
          total_possible_gas > max_tx_gas { return Err(...) }]), so
          [validate_batch] returns [Ok] on an over-ceiling batch. This ADDS the
          transitions in which the content-gated admission path stores an
          over-ceiling batch and reports its digest to the primary
          (handler.rs:248-260). No sibling path repairs it: [decode_transactions]
          and [recover_and_validate] (validator.rs:147-156, :209-215) only
          decode and recover a signer, [validate_batch_size_bytes]
          (validator.rs:122-141) bounds BYTES (a single 40M-gas transfer is
          tiny), [validate_basefee] (validator.rs:188-195) compares a batch
          field, [process_report_batch] itself adds only the committee check
          (handler.rs:237-239), and the builder-side cap
          (crates/batch-builder/src/batch.rs:73-81) is producer-side and does
          not constrain a Byzantine author. The blob gate runs earlier
          (validator.rs:73 before :77) but a batch that is merely over the
          ceiling carries no 4844 envelope, so it does not catch this either. *)
  | No_blob_reject
      (** delete the EIP-4844 rejection at
          crates/batch-validator/src/validator.rs:202-204
          ([if let Some(blob_tx) = transactions.iter().find(|tx| tx.is_eip4844())]),
          so [validate_batch] returns [Ok] on a blob-carrying batch. This ADDS
          the transitions in which the content-gated admission path stores a
          blob-carrying batch. No sibling path repairs it: the decode step is
          [recover_signed_transaction] = [reth_recover_raw_transaction::<TransactionSigned>(tx)]
          (crates/tn-reth/src/txn_pool.rs:369-373), a plain 2718 decode of the
          CONSENSUS envelope, which for 4844 is well-formed without a sidecar -
          the existence of the dedicated gate over already-decoded
          [TransactionSigned] values is itself the evidence that decoding does
          not reject them. The byte cap does not repair (a 4844 consensus
          envelope is small), the gas ceiling does not repair (a blob
          transaction's [gas_limit] is ordinary), and the builder-side skip
          (batch.rs:88-94) is producer-side only. *)
  | Digest_covers_received_at
      (** delete the [#[serde(skip)]] attribute on [Batch::received_at]
          (crates/types/src/worker/sealed_batch.rs:86), so [Batch::digest]
          (:119-124) hashes the local receipt stamp too. This REMOVES the
          transition in which a worker that stamped its own copy
          (handler.rs:251) can still serve that copy under the author's digest:
          the fetching peer recomputes [batch.digest()] and rejects the answer
          as an unrequested batch (handle.rs:754-761). It also makes every
          stamped copy stop content-addressing its own store key. No sibling
          path repairs it: [SealedBatch::split] (sealed_batch.rs:51-53),
          [Batch::seal] (:149-151) and [Batch::seal_slow] (:159-162) all route
          through the one [digest()] helper, so there is no cached-digest site
          that re-fixes the key independently, and the stored value is served
          verbatim rather than re-sealed. The author's own copy is never
          stamped (batch.rs:122-123, worker.rs:359), so a fetch served by the
          AUTHOR deliberately survives this mutation - the deletion is targeted
          at relay, not at fetching in general. *)

(** The verdict [validate_batch] (validator.rs:39-82) returns for a batch of
    this content class under [mut]. Exhaustive over both sums. *)
let verdict mut c =
  match mut with
  | Pristine | Digest_covers_received_at -> (
      match c with
      | Clean -> Passed
      | Over_gas -> Refused
      | Has_blob -> Refused)
  | No_gas_ceiling -> (
      match c with
      | Clean -> Passed
      | Over_gas -> Passed
      | Has_blob -> Refused)
  | No_blob_reject -> (
      match c with
      | Clean -> Passed
      | Over_gas -> Refused
      | Has_blob -> Passed)

(** Whether a copy served by a worker that already STAMPED it still satisfies
    the fetcher's digest re-check (handle.rs:754-761). *)
let relay_serves mut =
  match mut with
  | Pristine | No_gas_ceiling | No_blob_reject -> true
  | Digest_covers_received_at -> false

(** The store-key binding after some worker writes [b] and stamps it. *)
let binding_after mut prior =
  match mut with
  | Pristine | No_gas_ceiling | No_blob_reject -> prior
  | Digest_covers_received_at -> Stamp_shifted

(** The two clock readings a stamping worker can produce. *)
let ticks = [ Tick_early; Tick_late ]

(** The author's unicast report leg to the gate-side worker is delivered and
    resolved (quorum_waiter.rs:84-116 -> handler.rs:231-263). A pass stamps and
    stores (handler.rs:251-254); a refusal returns on that stream and writes
    nothing. *)
let step_report_gate_side mut s =
  match s.leg1 with
  | Refused | Passed -> []
  | Unreported -> (
      match verdict mut s.content with
      | Passed ->
          [ { s with leg1 = Passed; binding = binding_after mut s.binding } ]
      | Refused -> [ { s with leg1 = Refused } ]
      | Unreported -> [])

(** The author's unicast report leg to the fetch-side worker is delivered and
    resolved. A pass stores unconditionally (handler.rs:252 has no
    already-present check), so it overwrites any earlier prefetched copy with a
    freshly stamped one; a refusal leaves the cache slot exactly as it was,
    because [process_report_batch] returns at :246 and removes nothing. *)
let step_report_fetch_side mut s =
  match s.leg2 with
  | Refused | Passed -> []
  | Unreported -> (
      match verdict mut s.content with
      | Passed ->
          List.map
            (fun t ->
              {
                s with
                leg2 = Passed;
                acq2 = Acq_gate t;
                binding = binding_after mut s.binding;
              })
            ticks
      | Refused -> [ { s with leg2 = Refused } ]
      | Unreported -> [])

(** The gossip-triggered digest-only prefetch (handler.rs:142-228) served by
    the author. Enabled only while the digest is absent from the local cache,
    which is the real guard at handler.rs:167-170; it is enabled whatever the
    report leg said, which is exactly the bypass - a worker that refused [b]
    through [validate_batch] can still end up storing it here, because this
    path never calls the validator. *)
let step_prefetch_from_author mut s =
  match s.acq2 with
  | Acq_gate _ | Acq_author _ | Acq_relay _ -> []
  | Acq_none ->
      List.map
        (fun t ->
          { s with acq2 = Acq_author t; binding = binding_after mut s.binding })
        ticks

(** The same digest-only prefetch, served instead by the gate-side worker out
    of its own stamped copy. Available only once that worker actually holds
    [b], and only while the served copy still content-addresses. *)
let step_prefetch_from_relay mut s =
  match s.acq2 with
  | Acq_gate _ | Acq_author _ | Acq_relay _ -> []
  | Acq_none -> (
      match s.leg1 with
      | Unreported | Refused -> []
      | Passed -> (
          match relay_serves mut with
          | false -> []
          | true ->
              List.map
                (fun t ->
                  {
                    s with
                    acq2 = Acq_relay t;
                    binding = binding_after mut s.binding;
                  })
                ticks))

(** The transition relation: the two report legs and the prefetch advance
    independently, one per step. *)
let next_with mut s =
  step_report_gate_side mut s
  @ step_report_fetch_side mut s
  @ step_prefetch_from_author mut s
  @ step_prefetch_from_relay mut s

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state for a batch that passes every check. *)
let initial =
  {
    content = Clean;
    leg1 = Unreported;
    leg2 = Unreported;
    acq2 = Acq_none;
    binding = Content_addressed;
  }

(** The initial state for a batch whose declared gas limits sum above
    [max_batch_gas] (sealed_batch.rs:192-194). *)
let initial_over_gas = { initial with content = Over_gas }

(** The initial state for a batch carrying an EIP-4844 envelope. *)
let initial_has_blob = { initial with content = Has_blob }

(** Every initial state: the content class is a property of the bytes the
    author put on the wire, so it branches at the root. *)
let inits = [ initial; initial_over_gas; initial_has_blob ]

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Content_is_clean  (** [b] passes every check in [validate_batch] *)
  | Content_over_ceiling
      (** [b]'s declared gas limits sum above [max_batch_gas]
          (validator.rs:177-182) *)
  | Content_carries_blob
      (** [b] contains an EIP-4844 envelope (validator.rs:198-206) *)
  | Reported_1
      (** the author's unicast [ReportBatch] to the gate-side worker has been
          delivered and resolved *)
  | Reported_2  (** the same, for the fetch-side worker *)
  | Refused_1
      (** [validate_batch] returned an error to the author on the gate-side
          worker's stream *)
  | Refused_2  (** the same, for the fetch-side worker *)
  | Gated_admit_1
      (** the gate-side worker stored [b] through the content-gated path
          (handler.rs:244-254) *)
  | Gated_admit_2  (** the same, for the fetch-side worker *)
  | Holds_2
      (** [b] is in the fetch-side worker's [NodeBatchesCache], by ANY route *)
  | Relay_held_2
      (** the fetch-side worker's copy was served by the stamping gate-side
          worker rather than by the author *)
  | Key_matches_digest
      (** every stored copy's recomputed digest still equals the
          [NodeBatchesCache] key it is filed under *)
  | Tick2_late
      (** the fetch-side worker's [received_at] stamp is the later of the two
          clock readings *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Content_is_clean -> (
      match s.content with Clean -> true | Over_gas | Has_blob -> false)
  | Content_over_ceiling -> (
      match s.content with Over_gas -> true | Clean | Has_blob -> false)
  | Content_carries_blob -> (
      match s.content with Has_blob -> true | Clean | Over_gas -> false)
  | Reported_1 -> (
      match s.leg1 with Unreported -> false | Refused | Passed -> true)
  | Reported_2 -> (
      match s.leg2 with Unreported -> false | Refused | Passed -> true)
  | Refused_1 -> (
      match s.leg1 with Refused -> true | Unreported | Passed -> false)
  | Refused_2 -> (
      match s.leg2 with Refused -> true | Unreported | Passed -> false)
  | Gated_admit_1 -> (
      match s.leg1 with Passed -> true | Unreported | Refused -> false)
  | Gated_admit_2 -> (
      match s.leg2 with Passed -> true | Unreported | Refused -> false)
  | Holds_2 -> (
      match s.acq2 with
      | Acq_none -> false
      | Acq_gate _ | Acq_author _ | Acq_relay _ -> true)
  | Relay_held_2 -> (
      match s.acq2 with
      | Acq_relay _ -> true
      | Acq_none | Acq_gate _ | Acq_author _ -> false)
  | Key_matches_digest -> (
      match s.binding with
      | Content_addressed -> true
      | Stamp_shifted -> false)
  | Tick2_late -> (
      match s.acq2 with
      | Acq_none -> false
      | Acq_gate t | Acq_author t | Acq_relay t -> (
          match t with Tick_late -> true | Tick_early -> false))

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Content_is_clean -> "clean(b)"
  | Content_over_ceiling -> "over-ceiling(b)"
  | Content_carries_blob -> "carries-blob(b)"
  | Reported_1 -> "reported(a->v1,b)"
  | Reported_2 -> "reported(a->v2,b)"
  | Refused_1 -> "refused_v1(b)"
  | Refused_2 -> "refused_v2(b)"
  | Gated_admit_1 -> "gated-admit_v1(b)"
  | Gated_admit_2 -> "gated-admit_v2(b)"
  | Holds_2 -> "holds_v2(b)"
  | Relay_held_2 -> "relay-held_v2(b)"
  | Key_matches_digest -> "key=digest(stored)"
  | Tick2_late -> "received-at_v2=late"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every
    reachable world by test/t_batch_admit_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: one initial state per content class,
    mutation-parameterized transitions, the two-agent view, atom valuation. *)
let spec_of mut = { Checker.init = inits; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
