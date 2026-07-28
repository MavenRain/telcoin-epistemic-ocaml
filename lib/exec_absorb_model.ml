(** EXEC_ABSORB - the executor's error taxonomy for ONE committed consensus
    output: which per-transaction failure is absorbed, and which failure aborts
    the whole output. Everything here is grounded in
    Telcoin-Association/telcoin-network at git HEAD [0c59c15b], read as a
    working tree.

    The mechanism, verbatim from crates/tn-reth/src/lib.rs:763-800:

    - {b recovery phase} (:763-780): every transaction blob of the batch is
      recovered with [reth_recover_raw_transaction::<TransactionSigned>] under
      [par_iter().map(..).collect::<TnRethResult<Vec<_>>>()?] - a collect-or-abort
      over the WHOLE batch, so one undecodable blob aborts the output before any
      transaction executes;
    - {b tolerated arm} (:787-796): [Err(BlockExecutionError::Validation(
      BlockValidationError::InvalidTx {..}))] is logged
      ("allow transaction errors (ie - duplicates) / it's possible that another
      worker's batch included this transaction") and [continue]d, so packing goes
      on and the node still commits a block;
    - {b fatal arm} (:797-798): every other execution error is
      [Err(err) => return Err(err.into())], which propagates through
      crates/engine/src/payload_builder.rs:211-212 and aborts the output BEFORE
      crates/engine/src/payload_builder.rs:189-194 ever calls
      [finish_executing_output]/[finalize_block]. Nothing partial is committed.

    The other two gates the family needs:

    - {b the validation decode gate}, crates/batch-validator/src/validator.rs:69-70
      [let decoded_txs = self.decode_transactions(transactions, digest)?;] ->
      :147-156 [par_iter().map(|tx| Self::recover_and_validate(tx, digest))] ->
      :209-215 [recover_signed_transaction(tx)]. That is literally the same
      helper pair the executor uses: crates/tn-reth/src/txn_pool.rs:363-373
      defines [recover_raw_transaction] and [recover_signed_transaction], both
      wrapping [reth_recover_raw_transaction::<TransactionSigned>]. An honest
      worker refuses to store or report a batch that fails it
      (crates/consensus/worker/src/network/handler.rs:243-260: [validate_batch]
      then [store.insert] then [report_others_batch]), so an undecodable batch
      does not reach consensus.
    - {b the cross-worker duplicate has no upstream filter}: the engine walks the
      output's batches with no seen-set and hands [&batch.transactions] straight
      to the executor (crates/engine/src/payload_builder.rs:137-184, :167-175),
      the batch validator validates each batch in isolation
      (crates/batch-validator/src/validator.rs:39-82), and the pool only evicts
      mined transactions AFTER the output commits
      (crates/tn-reth/src/txn_pool.rs:180-217), which is far too late for two
      batches inside the SAME output. One transaction genuinely lands in two
      pools: [submit_txn_if_mine] shards gossip by sender
      (crates/batch-validator/src/validator.rs:89-106) but an RPC client can post
      the same raw transaction to two validators, and
      crates/tn-reth/src/forward.rs:140-191 deliberately re-offers a transaction
      to the next validator on a [Disposition::TryNext].

    {b Components.}
    - [bytes]: does every transaction blob of the batch recover? The single
      global content fact the decode gate tests.
    - [overlap]: do the two workers' batches in this output share a transaction?
      The single global content fact the tolerated arm absorbs.
    - [cert]: has the batch been admitted by honest workers and reached
      consensus, or was it refused before it could be certified? The family does
      not count votes - it abstracts the single fact that the ONLY route by
      which a peer's batch becomes available for consensus runs
      [validate_batch] first
      (crates/consensus/worker/src/network/handler.rs:243-260), and the library's
      committee is n = 10, f = 3, quorum = 7 (lib/validator.mli), so a certified
      batch carries at least four honest acknowledgements that each ran
      validator.rs:69-70.
    - [t0], [t1]: the executing tips of the two nodes, each advancing
      independently and exactly once per output.

    {b Role mapping.} [Validator.V0] and [Validator.V1] are the two executing
    nodes and the ONLY knowledge agents. [Validator.V2] through [Validator.V9]
    are idle non-agents carrying the constant blank view [View_idle]; they never
    appear under [K].

    {b Why the view projection is what it is.} A node executing a committed
    output holds the batch bytes, sees the output's transactions (it executes
    them) and sees its own resulting tip. It does NOT see any peer's execution
    result: [finish_executing_output] (crates/tn-reth/src/lib.rs:923-980) writes
    to the local database and notifies the LOCAL canonical-state channel, and
    [TNPayload] carries no state root at all
    (crates/tn-reth/src/payload.rs:30-70), so nothing in the execution path
    crosses a node boundary. The peer's tip is therefore the only hidden
    component, which is exactly what makes the knowledge conjuncts of S3
    non-trivial: V0 infers a fact about V1's block from shared content plus
    determinism, never from observation.

    {b Horizon.} The model covers ONE consensus output and terminates when both
    nodes have finished it. The later cross-round channel by which a node learns
    a peer's execution tip - [header.latest_execution_block] in a primary header
    - belongs to the EXEC_TIP family and is deliberately outside this horizon;
    every ignorance conjunct here is scoped to the execution of a single output.

    {b Deliberate omissions and why they cannot repair anything.} Execution-tip
    gossip and voting exist in other crates, but they DETECT a divergence after
    the fact; they cannot un-commit
    crates/tn-reth/src/lib.rs:941-944 ([save_blocks] then [commit]), and TN has
    no reorg path at all (crates/tn-reth/src/txn_pool.rs:135
    [_ => unreachable!("TN reorgs are impossible")]). Modelling them would add
    states and change no verdict. *)

(** Does every transaction blob in the batch recover to a signer under
    [reth_recover_raw_transaction] (crates/tn-reth/src/txn_pool.rs:363-373)? *)
type bytes_kind =
  | Sound  (** every blob recovers: validation and execution both succeed *)
  | Garbage
      (** at least one blob does not recover; the executor's recovery phase is
          a collect-or-abort (crates/tn-reth/src/lib.rs:766-780) *)

(** Total order index for {!bytes_kind}. *)
let bytes_index = function Sound -> 0 | Garbage -> 1

(** Total order on {!bytes_kind}. *)
let bytes_compare a b = Int.compare (bytes_index a) (bytes_index b)

(** Is the batch undecodable? *)
let bytes_is_garbage = function Sound -> false | Garbage -> true

(** Do the two workers' batches in this output share a transaction? Nothing
    upstream deduplicates across batches
    (crates/engine/src/payload_builder.rs:137-184). *)
type overlap =
  | Distinct  (** the two batches carry different transactions *)
  | Duplicated
      (** the two batches carry the same transaction, so the second execution
          attempt is rejected by revm with a nonce-too-low
          [BlockValidationError::InvalidTx] and is skipped
          (crates/tn-reth/src/lib.rs:787-796) *)

(** Total order index for {!overlap}. *)
let overlap_index = function Distinct -> 0 | Duplicated -> 1

(** Total order on {!overlap}. *)
let overlap_compare a b = Int.compare (overlap_index a) (overlap_index b)

(** Does this output contain a cross-worker duplicate? *)
let overlap_is_duplicated = function Distinct -> false | Duplicated -> true

(** Consensus admission status of the batch. *)
type cert =
  | Proposed  (** reported to peers, not yet admitted *)
  | Certified
      (** admitted by a quorum of honest workers and delivered to the executor
          (crates/consensus/worker/src/network/handler.rs:243-260) *)
  | Rejected
      (** [validate_batch] failed on the honest workers, so the batch was never
          stored nor reported and never reaches the executor
          (crates/batch-validator/src/validator.rs:39-82) *)

(** Total order index for {!cert}. *)
let cert_index = function Proposed -> 0 | Certified -> 1 | Rejected -> 2

(** Total order on {!cert}. *)
let cert_compare a b = Int.compare (cert_index a) (cert_index b)

(** Has the batch reached the executor? *)
let cert_is_certified = function
  | Proposed -> false
  | Certified -> true
  | Rejected -> false

(** Was the batch refused before consensus? *)
let cert_is_rejected = function
  | Proposed -> false
  | Certified -> false
  | Rejected -> true

(** One node's tip after it has processed this output. *)
type tip =
  | At_parent  (** the node has not executed this output yet *)
  | At_full
      (** the node committed the block containing BOTH transactions of the
          output *)
  | At_lean
      (** the node committed the block that skipped the duplicated transaction:
          the tolerated arm at crates/tn-reth/src/lib.rs:787-796. This is the
          "engine produces empty block for duplicate batch" outcome the repo's
          own integration test asserts
          (crates/engine/tests/it/main.rs:1109-1122) *)
  | At_partial
      (** MUTANT-ONLY: the node committed a block that silently omits the
          transaction on which a node-local fatal error fired. Unreachable on
          the pristine model, because crates/tn-reth/src/lib.rs:797-798 aborts
          instead *)
  | Halted
      (** the node aborted the output and committed nothing: either the
          recovery-phase collect-or-abort (crates/tn-reth/src/lib.rs:766-780) or
          the fatal arm (:797-798) *)

(** Total order index for {!tip}. *)
let tip_index = function
  | At_parent -> 0
  | At_full -> 1
  | At_lean -> 2
  | At_partial -> 3
  | Halted -> 4

(** Total order on {!tip}. *)
let tip_compare a b = Int.compare (tip_index a) (tip_index b)

(** Has this node not started the output? *)
let tip_is_parent = function
  | At_parent -> true
  | At_full | At_lean | At_partial | Halted -> false

(** Did this node commit the full block? *)
let tip_is_full = function
  | At_full -> true
  | At_parent | At_lean | At_partial | Halted -> false

(** Did this node commit the skip-the-duplicate block? *)
let tip_is_lean = function
  | At_lean -> true
  | At_parent | At_full | At_partial | Halted -> false

(** Did this node commit a silently truncated block? *)
let tip_is_partial = function
  | At_partial -> true
  | At_parent | At_full | At_lean | Halted -> false

(** Did this node abort the output? *)
let tip_is_halted = function
  | Halted -> true
  | At_parent | At_full | At_lean | At_partial -> false

(** Did this node commit SOMETHING for this output? *)
let tip_is_committed = function
  | At_full | At_lean | At_partial -> true
  | At_parent | Halted -> false

(** Did this node commit a block that omits a transaction its peers may hold?
    [At_lean] omits the duplicate (which every node omits, because the rejection
    is a deterministic function of the shared output); [At_partial] omits a
    transaction for a node-LOCAL reason, which is the divergence the fatal arm
    exists to prevent. *)
let tip_omits_a_transaction = function
  | At_lean | At_partial -> true
  | At_parent | At_full | Halted -> false

(** The joint global state: one output's content, its consensus status, and the
    two executing nodes' tips. *)
type state = {
  bytes : bytes_kind;  (** do the batch's transaction blobs recover? *)
  overlap : overlap;  (** do the two batches share a transaction? *)
  cert : cert;  (** has the batch reached the executor? *)
  t0 : tip;  (** the tip of node V0 *)
  t1 : tip;  (** the tip of node V1 *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = bytes_compare s1.bytes s2.bytes in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = overlap_compare s1.overlap s2.overlap in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = cert_compare s1.cert s2.cert in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = tip_compare s1.t0 s2.t0 in
        if Bool.not (Int.equal c3 0) then c3 else tip_compare s1.t1 s2.t1

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    An executing node sees the batch bytes it holds, the output's transaction
    content, the consensus status, and its OWN tip. It does not see the peer's
    tip: nothing in crates/tn-reth/src/lib.rs:923-980 crosses a node boundary
    and [TNPayload] carries no state root to compare against
    (crates/tn-reth/src/payload.rs:30-70). *)
type view =
  | View_node of bytes_kind * overlap * cert * tip
      (** an executing node: shared content, consensus status, own tip *)
  | View_idle  (** the constant blank view of the non-agents V2 and V3 *)

(** Total order on the executing-node view payload. *)
let view_node_compare (b, o, c, t) (b', o', c', t') =
  let cb = bytes_compare b b' in
  if Bool.not (Int.equal cb 0) then cb
  else
    let co = overlap_compare o o' in
    if Bool.not (Int.equal co 0) then co
    else
      let cc = cert_compare c c' in
      if Bool.not (Int.equal cc 0) then cc else tip_compare t t'

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_node _ -> -1
  | View_node _, View_idle -> 1
  | View_node (b0, o0, c0, t), View_node (b1, o1, c1, t') ->
      view_node_compare (b0, o0, c0, t) (b1, o1, c1, t')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 and V1 are the executing nodes and the family's only
    knowledge agents; every other committee member is an idle non-agent with
    the constant blank view and never appears under [K]. *)
let view v s =
  match v with
  | Validator.V0 -> View_node (s.bytes, s.overlap, s.cert, s.t0)
  | Validator.V1 -> View_node (s.bytes, s.overlap, s.cert, s.t1)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine  (** the code as it stands at [0c59c15b] *)
  | Fatal_on_invalid_tx
      (** delete the tolerated arm at crates/tn-reth/src/lib.rs:787-796, moving
          [BlockValidationError::InvalidTx] into the fatal arm at :797-798. That
          REMOVES the [At_parent -> At_lean] transition of a [Duplicated] output
          and replaces it with [At_parent -> Halted], so one cross-worker
          duplicate makes the whole output unexecutable on every honest node at
          once. No sibling path repairs it: there is no deduplication anywhere
          upstream. The engine walks the output's batches with no seen-set and
          passes [&batch.transactions] through unfiltered
          (crates/engine/src/payload_builder.rs:137-184, :167-175); the batch
          validator checks digest, worker id, epoch, size, decode, 4844, gas and
          base fee, each batch in isolation, with no cross-batch and no on-chain
          nonce check (crates/batch-validator/src/validator.rs:39-82); the pool
          evicts mined transactions only on the canonical-state notification
          AFTER the output commits (crates/tn-reth/src/txn_pool.rs:180-217); and
          the sender sharding of [submit_txn_if_mine]
          (crates/batch-validator/src/validator.rs:89-106) governs the gossip
          path only, while crates/tn-reth/src/forward.rs:140-191 deliberately
          re-offers a transaction to the next validator on
          [Disposition::TryNext]. The nearest miss is the batch-stream reader,
          which rejects a repeated batch DIGEST
          (crates/consensus/worker/src/network/handle.rs:763-768
          [if !received_digests.insert(batch_digest)]) - two different batches
          carrying the same transaction have different digests and sail through,
          which is exactly the case the repo's own
          [test_execution_succeeds_with_duplicate_transactions] constructs
          ([assert_eq!] on transactions, [assert_ne!] on the batches,
          crates/engine/tests/it/main.rs:1322-1329). *)
  | No_validation_decode
      (** delete crates/batch-validator/src/validator.rs:70
          [let decoded_txs = self.decode_transactions(transactions, digest)?;]
          (and its uses at :73 and :77). That ADDS the [Proposed -> Certified]
          transition for a [Garbage] batch, so undecodable bytes reach the
          executor and the collect-or-abort at
          crates/tn-reth/src/lib.rs:766-780 aborts the output on EVERY node - a
          uniform chain halt. No sibling path repairs it: the digest check at
          crates/batch-validator/src/validator.rs:42-45 hashes the same opaque
          bytes and says nothing about decodability; [Batch.transactions] is
          [Vec<Vec<u8>>] of opaque blobs
          (crates/types/src/worker/sealed_batch.rs:63-89) and the wire codec
          bounds the frame with [max_batch_size(epoch)] while decoding the
          envelope, not the blobs
          (crates/consensus/worker/src/network/stream_codec.rs:27-40); a peer's
          batch never enters the local pool, whose only external ingress is
          crates/tn-reth/src/txn_pool.rs:242-268; and the engine passes
          [&batch.transactions] straight to the executor
          (crates/engine/src/payload_builder.rs:167-175). *)
  | Commit_partial_block
      (** change the fatal arm at crates/tn-reth/src/lib.rs:797-798 from
          [Err(err) => return Err(err.into())] to a skip. That REPLACES the
          [At_parent -> Halted] transition of a node-local fatal condition with
          [At_parent -> At_partial]: the node commits a block that silently
          omits the transaction its peers included. No sibling path repairs it:
          [TNPayload] carries no state root at all
          (crates/tn-reth/src/payload.rs:30-70 - parent header, beneficiary,
          nonce, batch index, timestamp, batch digest, consensus header digest,
          base fee, gas limit, mix hash, close_epoch, worker id), so
          [builder.finish(&state_provider)] (crates/tn-reth/src/lib.rs:802-803)
          computes a root with nothing to compare it against and
          [finish_executing_output] (crates/tn-reth/src/lib.rs:923-980) writes
          and notifies without comparing anything; the block assembler writes
          [state_root], [gas_used] and [gas_limit] through without comparing
          them to anything (crates/tn-reth/src/evm/block.rs:980-1002); and TN
          has no reorg path to
          undo the commit at crates/tn-reth/src/lib.rs:941-944
          (crates/tn-reth/src/txn_pool.rs:135
          [_ => unreachable!("TN reorgs are impossible")]). *)

(** The consensus verdict a proposed batch receives. Pristine and the two
    execution-side mutations keep the decode gate at
    crates/batch-validator/src/validator.rs:69-70; only
    {!No_validation_decode} lets undecodable bytes through. *)
let certification_verdict mut b =
  match mut with
  | Pristine | Fatal_on_invalid_tx | Commit_partial_block -> (
      match b with Sound -> Certified | Garbage -> Rejected)
  | No_validation_decode -> Certified

(** The tip a node reaches when a NODE-LOCAL fatal condition fires during
    execution - an internal/database error reaching
    crates/tn-reth/src/evm/block.rs:819-831 and hence the fatal arm at
    crates/tn-reth/src/lib.rs:797-798. This branch is per-node precisely because
    the condition is local; content-induced failures (for example the block gas
    budget check at crates/tn-reth/src/evm/block.rs:866-876) are a function of
    the shared output and therefore fire on every node or on none. *)
let local_fault_tip mut =
  match mut with
  | Pristine | Fatal_on_invalid_tx | No_validation_decode -> Halted
  | Commit_partial_block -> At_partial

(** The tip a node reaches when execution runs to completion. It is a function
    of the SHARED output content only, which is the modelled form of "forks are
    impossible" (crates/tn-reth/src/lib.rs:784): every node executes the same
    transactions against the same parent state, so the skip decision is
    node-uniform. *)
let content_tip mut ov =
  match ov with
  | Distinct -> At_full
  | Duplicated -> (
      match mut with
      | Pristine | No_validation_decode | Commit_partial_block -> At_lean
      | Fatal_on_invalid_tx -> Halted)

(** The tips one node may reach from [At_parent] on a certified output. A
    [Garbage] batch aborts in the recovery phase before any transaction runs
    (crates/tn-reth/src/lib.rs:766-780), so it has the single outcome [Halted];
    otherwise the node either hits a node-local fatal condition or runs to
    completion. *)
let execution_tips mut s =
  match s.bytes with
  | Garbage -> [ Halted ]
  | Sound ->
      List.sort_uniq tip_compare [ local_fault_tip mut; content_tip mut s.overlap ]

(** The transition relation: consensus admits or refuses the batch, then the two
    nodes execute the output independently, one node per step. *)
let next_with mut s =
  match s.cert with
  | Proposed -> [ { s with cert = certification_verdict mut s.bytes } ]
  | Rejected -> []
  | Certified ->
      let step0 =
        match s.t0 with
        | At_parent ->
            List.map (fun t -> { s with t0 = t }) (execution_tips mut s)
        | At_full | At_lean | At_partial | Halted -> []
      in
      let step1 =
        match s.t1 with
        | At_parent ->
            List.map (fun t -> { s with t1 = t }) (execution_tips mut s)
        | At_full | At_lean | At_partial | Halted -> []
      in
      step0 @ step1

(** The pristine transition relation. *)
let next = next_with Pristine

(** Initial state: a sound batch of distinct transactions, proposed, nobody
    executed. *)
let initial =
  { bytes = Sound; overlap = Distinct; cert = Proposed; t0 = At_parent; t1 = At_parent }

(** Initial state: a sound batch whose output carries a cross-worker duplicate. *)
let initial_duplicated = { initial with overlap = Duplicated }

(** Initial state: a batch with an undecodable transaction blob, distinct
    transactions otherwise. *)
let initial_garbage = { initial with bytes = Garbage }

(** Initial state: a batch with an undecodable blob AND a cross-worker
    duplicate. *)
let initial_garbage_duplicated =
  { initial with bytes = Garbage; overlap = Duplicated }

(** All four initial states: the content of the output is a global fact fixed
    before consensus, so it is branched at init rather than by a transition. *)
let inits =
  [ initial; initial_duplicated; initial_garbage; initial_garbage_duplicated ]

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Bytes_garbage  (** some transaction blob of the batch does not recover *)
  | Duplicate_in_output
      (** the two workers' batches share a transaction *)
  | Batch_certified  (** the batch reached the executor *)
  | Batch_rejected  (** the batch was refused before consensus *)
  | Node0_unexecuted  (** V0 has not processed this output yet *)
  | Node0_full_block  (** V0 committed the block holding both transactions *)
  | Node0_lean_block  (** V0 committed the skip-the-duplicate block *)
  | Node0_partial_block
      (** V0 committed a silently truncated block (mutant-only) *)
  | Node0_committed  (** V0 committed some block for this output *)
  | Node0_halted  (** V0 aborted the output and committed nothing *)
  | Node1_full_block  (** V1 committed the block holding both transactions *)
  | Node1_halted  (** V1 aborted the output and committed nothing *)
  | Peer_omits_a_transaction
      (** V1 committed a block that omits a transaction: the hidden global fact
          the safety statement's positive knowledge conjunct rules out *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Bytes_garbage -> bytes_is_garbage s.bytes
  | Duplicate_in_output -> overlap_is_duplicated s.overlap
  | Batch_certified -> cert_is_certified s.cert
  | Batch_rejected -> cert_is_rejected s.cert
  | Node0_unexecuted -> tip_is_parent s.t0
  | Node0_full_block -> tip_is_full s.t0
  | Node0_lean_block -> tip_is_lean s.t0
  | Node0_partial_block -> tip_is_partial s.t0
  | Node0_committed -> tip_is_committed s.t0
  | Node0_halted -> tip_is_halted s.t0
  | Node1_full_block -> tip_is_full s.t1
  | Node1_halted -> tip_is_halted s.t1
  | Peer_omits_a_transaction -> tip_omits_a_transaction s.t1

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Bytes_garbage -> "bytes_garbage"
  | Duplicate_in_output -> "duplicate_in_output"
  | Batch_certified -> "batch_certified"
  | Batch_rejected -> "batch_rejected"
  | Node0_unexecuted -> "unexecuted_0"
  | Node0_full_block -> "full_block_0"
  | Node0_lean_block -> "lean_block_0"
  | Node0_partial_block -> "partial_block_0"
  | Node0_committed -> "committed_0"
  | Node0_halted -> "halted_0"
  | Node1_full_block -> "full_block_1"
  | Node1_halted -> "halted_1"
  | Peer_omits_a_transaction -> "peer_omits_a_transaction"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} by
    test/t_exec_absorb_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation. *)
let spec_of mut =
  { Checker.init = inits; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
