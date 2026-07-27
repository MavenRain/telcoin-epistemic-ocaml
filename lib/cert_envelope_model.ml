(** Finite interpreted system for the CERT_ENVELOPE family: what a validator
    learns about a REMOTE node's handling of a batch by virtue of having
    accepted that batch's bytes on its own gated ingress. File citations refer
    to Telcoin-Association/telcoin-network at HEAD 0c59c15b.

    The modeled mechanism. ONE batch behind ONE digest [D], authored by a
    Byzantine committee member. Four components.

    - ENVELOPE: what the author actually put behind [D]. Fixed for the whole run
      because [Batch::digest] hashes the entire serialization
      (crates/types/src/worker/sealed_batch.rs:63-89, :116-124), so the bytes
      cannot change while the digest stays the same. The single init root is
      [Unauthored]; the first transition is the hidden Byzantine choice among
      the four content shapes the validator's gates discriminate.

    - V1: the phase of the GATED ingress. [process_report_batch] runs
      [validate_batch] BEFORE inserting into [NodeBatchesCache]
      (crates/consensus/worker/src/network/handler.rs:231-263, the call at
      :245), so a rejected batch is never stored and the reporter is penalised
      (crates/consensus/worker/src/network/error.rs:76-104).

    - V2: the phase of the UNGATED ingress plus V2's engine. [Holds] abstracts
      the three store routes that never call [validate_batch]: the gossip
      prefetch insert (handler.rs:201-208), the [is_certified] sync store
      (crates/consensus/worker/src/network/primary.rs:104-111) and
      [fetch_for_primary] (crates/consensus/worker/src/batch_fetcher.rs:186-200).
      [validate_batch] has exactly TWO production call sites in the whole tree -
      handler.rs:245 and primary.rs:108 - so V2 genuinely has an unvalidated
      route to possession. [Executed] is a block built for [D]
      (crates/engine/src/payload_builder.rs:139-184); [Halted] is the phase-1
      signer-recovery abort (crates/tn-reth/src/lib.rs:763-780) that propagates
      fatally out of the engine run loop (crates/engine/src/lib.rs:262-266) and
      trips the critical-task shutdown (crates/types/src/task_manager.rs:170-179);
      [Aborted] is the DISJUNCTION OF EVERY OTHER fatal exit of the same [?]
      chain, which is content-independent and is what an earlier revision of this
      model wrongly hardwired away.

    Why [Aborted] exists (R5). [execute_consensus_output] can leave a committed
    batch unexecuted for reasons that have nothing to do with the bytes behind
    [D]: [ConsensusOutputUnevenBatches] (payload_builder.rs:56-76),
    [UnknownAuthority] on the empty-output path (:104-107),
    [NextBlockDigestMissing] (:140-142), any error out of [execute_payload]
    (:167-175), [finish_executing_output] (:189-192) or [finalize_block]
    (:193-194), and inside [build_block_from_batch_payload] the
    [builder_for_next_block] / [apply_pre_execution_changes] failures
    (tn-reth/src/lib.rs:756-761 - both BEFORE recovery phase 1), the non-
    [InvalidTx] execution arm (:797-798) and [builder.finish] (:802-803). Every
    one of them reaches the same [?] at engine/src/lib.rs:264 and the same
    critical-task shutdown. A model with [Halted] as the ONLY failure branch
    would make "a committed batch inevitably becomes a block" true purely by
    omission.

    - CERT: whether consensus committed a certificate carrying [D]. A
      prefetched, never-validated copy already satisfies the primary's payload
      requirement through the local-hit short-circuit in [synchronize]
      (primary.rs:36-53), so commitment does NOT imply anyone validated.

    Role mapping (knowledge agents must have a real, non-constant view; a
    blank-view party may never appear under K):
    - V1 is a knowledge agent: the gated worker. Its view is exactly its own
      worker-task-local state - whether a [ReportBatch] arrived, the verdict,
      and the bytes it validated. It does NOT see [v2] (any remote node's store
      or engine) and does NOT see [cert]. Restricting V1's view is the
      CONSERVATIVE direction: a coarser partition means larger indistinguish-
      ability classes, so every positive [K (V1, _)] is proved under strictly
      LESS information than a real node has, while the ignorance conjuncts rest
      on components no node-level view could contain anyway.
    - V2 is a knowledge agent: the ungated holder/executor. It sees its own
      phase, the bytes it stored, and whether [D] was committed (it must see
      the commit to execute at all, payload_builder.rs:139-184). It does NOT
      see [v1]: the ungated ingresses carry no provenance, a rejection
      elsewhere is a purely local peer penalty (error.rs:76-104), and there is
      no negative cache anywhere.
    - V0 and V3 are idle: the constant blank view, never under K.

    THREE SELF-LOOPS are load-bearing and must not be optimised away; each one
    keeps a real "this may simply never happen" behaviour legal, and dropping
    any of them manufactures liveness (R8).

    - [Pending] in {!cert_moves}: the certificate for [D] may never be committed
      (the author equivocates, or the epoch closes and the cache is cleared,
      handler.rs:194-200). With it, [Af p] at a [Pending] state holds only if
      [p] already holds there.
    - [Idle] in {!v2_moves}, at BOTH [cert] values: V2 may never obtain the
      bytes. Before commitment the gossip prefetch is best-effort and is skipped
      outright when admission declines (handler.rs:167-191). After commitment
      [fetch_for_primary_inner] is an INFINITE retry loop
      (batch_fetcher.rs:154-210) whose exhausted-retries error is deliberately
      swallowed by [if let Ok(..)] at :177 and simply retried, so "the payload
      never arrives" is an infinite behaviour of the real code, not a modelling
      artefact. Delivery therefore may NOT be assumed by any [Af] conjunct.
    - none at [Holds]/[Committed]: once the payload is in hand and the output is
      committed, [execute_consensus_output] runs to a definite verdict, which is
      why possession plus commitment is the honest antecedent for inevitability.

    Reachable set, pristine and under every mutation: 49 states = 1 root + 4
    contents x 2 [v1] values x 6 reachable [(v2, cert)] pairs
    [(Idle,Pending) (Holds,Pending) (Idle,Committed) (Holds,Committed)
    (Executed|Halted,Committed) (Aborted,Committed)]. A mutation flips WHICH
    verdict a content resolves to; it never adds a component value, so the count
    is invariant. *)

(** What the Byzantine author put behind [D]. Content-addressed, hence fixed
    for the run. The four shapes are exactly the ones [validate_batch]
    discriminates (crates/batch-validator/src/validator.rs:39-82). *)
type content =
  | Well_formed  (** passes every gate in [validate_batch] *)
  | Forged_fee
      (** [base_fee_per_gas] differs from the validator's per-epoch snapshot
          (validator.rs:188-195, called at :80) *)
  | Unrecoverable
      (** carries a transaction that fails signer recovery (validator.rs:147-156
          with helper :209-215, called at :70) *)
  | Empty_payload
      (** carries zero transactions (validator.rs:127-141, called at :67) *)

(** The envelope behind the digest. *)
type envelope =
  | Unauthored  (** the pre-authoring root: the author has not chosen yet *)
  | Authored of content  (** the author's committed, immutable choice *)

(** V1's verdict on the gated [ReportBatch] ingress (handler.rs:244-254). *)
type verdict =
  | Accepted  (** [validate_batch] returned [Ok]; the batch was stored *)
  | Rejected  (** [validate_batch] returned [Err]; nothing stored *)

(** V1's phase on the gated ingress. *)
type v1_phase =
  | Unseen  (** no [ReportBatch] for [D] has arrived at V1 *)
  | Resolved of verdict  (** V1 ran the gate and got this verdict *)

(** V2's phase on the ungated ingress and in its engine. *)
type v2_phase =
  | Idle  (** V2 has no bytes for [D] *)
  | Holds  (** V2 stored [D]'s bytes through a route that never validates *)
  | Executed  (** V2's engine built a block for [D] *)
  | Halted  (** V2's engine aborted in signer recovery on [D] *)
  | Aborted
      (** V2's engine failed on [D] for a reason OTHER than signer recovery:
          any of the content-independent fatal exits of the same [?] chain -
          [ConsensusOutputUnevenBatches] (payload_builder.rs:56-76),
          [NextBlockDigestMissing] (:140-142), [execute_payload] (:167-175),
          [finish_executing_output] (:189-192), [finalize_block] (:193-194),
          [builder_for_next_block] / [apply_pre_execution_changes]
          (tn-reth/src/lib.rs:756-761), the non-[InvalidTx] execution arm
          (:797-798) or [builder.finish] (:802-803). Like [Halted] it is
          terminal, because it exits the engine run loop at
          engine/src/lib.rs:264 and trips the critical-task shutdown
          (task_manager.rs:170-179). *)

(** Whether consensus committed a certificate carrying [D]. *)
type cert =
  | Pending  (** not committed; may never be *)
  | Committed  (** committed, so V2's engine is obliged to build for [D] *)

(** Total order index for {!content}. *)
let content_index = function
  | Well_formed -> 0
  | Forged_fee -> 1
  | Unrecoverable -> 2
  | Empty_payload -> 3

(** Total order on {!content}. *)
let content_compare a b = Int.compare (content_index a) (content_index b)

(** Structural equality on {!content} without polymorphic compare. *)
let content_equal a b = Int.equal 0 (content_compare a b)

(** Total order on {!envelope}: [Unauthored] first, then by content. *)
let envelope_compare a b =
  match (a, b) with
  | Unauthored, Unauthored -> 0
  | Unauthored, Authored _ -> -1
  | Authored _, Unauthored -> 1
  | Authored ca, Authored cb -> content_compare ca cb

(** [true] iff the envelope is authored with exactly this content. *)
let envelope_is c e =
  match e with Unauthored -> false | Authored c' -> content_equal c c'

(** Total order index for {!verdict}. *)
let verdict_index = function Accepted -> 0 | Rejected -> 1

(** Total order on {!verdict}. *)
let verdict_compare a b = Int.compare (verdict_index a) (verdict_index b)

(** Total order on {!v1_phase}: [Unseen] first, then by verdict. *)
let v1_compare a b =
  match (a, b) with
  | Unseen, Unseen -> 0
  | Unseen, Resolved _ -> -1
  | Resolved _, Unseen -> 1
  | Resolved va, Resolved vb -> verdict_compare va vb

(** [true] iff V1's gated ingress accepted and stored [D]'s bytes. *)
let v1_is_accepted = function
  | Unseen -> false
  | Resolved Accepted -> true
  | Resolved Rejected -> false

(** [true] iff V1's gated ingress rejected [D]'s bytes. *)
let v1_is_rejected = function
  | Unseen -> false
  | Resolved Accepted -> false
  | Resolved Rejected -> true

(** Total order index for {!v2_phase}. *)
let v2_index = function
  | Idle -> 0
  | Holds -> 1
  | Executed -> 2
  | Halted -> 3
  | Aborted -> 4

(** Total order on {!v2_phase}. *)
let v2_compare a b = Int.compare (v2_index a) (v2_index b)

(** [true] iff V2 has [D]'s bytes in its store (any non-[Idle] phase). The
    engine reads the batch out of the store to build for it, so every failure
    phase implies possession too. *)
let v2_has_bytes = function
  | Idle -> false
  | Holds -> true
  | Executed -> true
  | Halted -> true
  | Aborted -> true

(** [true] iff V2's engine built a block for [D]. *)
let v2_is_executed = function
  | Idle -> false
  | Holds -> false
  | Executed -> true
  | Halted -> false
  | Aborted -> false

(** [true] iff V2's engine aborted in signer recovery on [D]. *)
let v2_is_halted = function
  | Idle -> false
  | Holds -> false
  | Executed -> false
  | Halted -> true
  | Aborted -> false

(** [true] iff V2's engine failed on [D] for a reason other than signer
    recovery (see the {!Aborted} constructor for the exhaustive exit list). *)
let v2_is_aborted = function
  | Idle -> false
  | Holds -> false
  | Executed -> false
  | Halted -> false
  | Aborted -> true

(** Total order index for {!cert}. *)
let cert_index = function Pending -> 0 | Committed -> 1

(** Total order on {!cert}. *)
let cert_compare a b = Int.compare (cert_index a) (cert_index b)

(** [true] iff a certificate carrying [D] has been committed. *)
let cert_is_committed = function Pending -> false | Committed -> true

(** The joint global state: the author's envelope, V1's gated-ingress phase,
    V2's ungated-ingress/engine phase, and the commit status of [D]. *)
type state = { envelope : envelope; v1 : v1_phase; v2 : v2_phase; cert : cert }

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = envelope_compare s1.envelope s2.envelope in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = v1_compare s1.v1 s2.v1 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = v2_compare s1.v2 s2.v2 in
      if Bool.not (Int.equal c2 0) then c2 else cert_compare s1.cert s2.cert

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. V1 sees ONLY its own worker-task-local state:
    whether a [ReportBatch] arrived and, if so, its verdict and the bytes it
    validated - never [v2], never [cert]. V2 sees its own phase, the bytes it
    stored (if any) and the commit status - never [v1], because the ungated
    ingresses carry no provenance and there is no negative cache. *)
type view =
  | View_v1_unseen
      (** V1: no [ReportBatch] has arrived; the author's choice is hidden *)
  | View_v1_seen of verdict * content
      (** V1: its own verdict and the bytes it validated *)
  | View_v2_no_bytes of cert
      (** V2: holds nothing for [D]; sees only [D]'s commit status *)
  | View_v2_bytes of v2_phase * content * cert
      (** V2: its phase, the bytes it stored, and [D]'s commit status *)
  | View_idle  (** the constant blank view of the non-agents V0, V3 *)

(** Total deterministic order over ALL fields of V1's seen view. *)
let view_v1_seen_compare (va, ca) (vb, cb) =
  let c = verdict_compare va vb in
  if Bool.not (Int.equal c 0) then c else content_compare ca cb

(** Total deterministic order over ALL fields of V2's bytes view. *)
let view_v2_bytes_compare (pa, ca, ka) (pb, cb, kb) =
  let c = v2_compare pa pb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = content_compare ca cb in
    if Bool.not (Int.equal c1 0) then c1 else cert_compare ka kb

(** Total order on views: [View_idle] < [View_v1_unseen] < [View_v1_seen] <
    [View_v2_no_bytes] < [View_v2_bytes], with the field-wise order within each
    constructor. Every constructor pair is spelled: no wildcard arm on the
    finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | ( View_idle,
      ( View_v1_unseen | View_v1_seen _ | View_v2_no_bytes _ | View_v2_bytes _ )
    ) ->
      -1
  | ( ( View_v1_unseen | View_v1_seen _ | View_v2_no_bytes _
      | View_v2_bytes _ ),
      View_idle ) ->
      1
  | View_v1_unseen, View_v1_unseen -> 0
  | View_v1_unseen, (View_v1_seen _ | View_v2_no_bytes _ | View_v2_bytes _) -> -1
  | (View_v1_seen _ | View_v2_no_bytes _ | View_v2_bytes _), View_v1_unseen -> 1
  | View_v1_seen (va, ca), View_v1_seen (vb, cb) ->
      view_v1_seen_compare (va, ca) (vb, cb)
  | View_v1_seen _, (View_v2_no_bytes _ | View_v2_bytes _) -> -1
  | (View_v2_no_bytes _ | View_v2_bytes _), View_v1_seen _ -> 1
  | View_v2_no_bytes ka, View_v2_no_bytes kb -> cert_compare ka kb
  | View_v2_no_bytes _, View_v2_bytes _ -> -1
  | View_v2_bytes _, View_v2_no_bytes _ -> 1
  | View_v2_bytes (pa, ca, ka), View_v2_bytes (pb, cb, kb) ->
      view_v2_bytes_compare (pa, ca, ka) (pb, cb, kb)

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 and V2 are the knowledge agents (real, non-constant
    views); V0 and V3 are idle non-agents with the constant blank view and
    never appear under K. The two [Unauthored] arms below are unreachable -
    nothing is reported or stored before the author has chosen the bytes - and
    are spelled only to keep the matches exhaustive. *)
let view v s =
  match v with
  | Validator.V1 -> (
      match s.v1 with
      | Unseen -> View_v1_unseen
      | Resolved verdict -> (
          match s.envelope with
          | Unauthored -> View_v1_unseen
          | Authored c -> View_v1_seen (verdict, c)))
  | Validator.V2 -> (
      match (s.v2, s.envelope) with
      | Idle, (Unauthored | Authored _) -> View_v2_no_bytes s.cert
      | (Holds | Executed | Halted | Aborted), Unauthored ->
          View_v2_no_bytes s.cert
      | ((Holds | Executed | Halted | Aborted) as p), Authored c ->
          View_v2_bytes (p, c, s.cert))
  | Validator.V0
  | Validator.V3
  | Validator.V4
  | Validator.V5
  | Validator.V6
  | Validator.V7
  | Validator.V8
  | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. Each constructor deletes
    exactly one gate of [validate_batch] (validator.rs:39-82) and therefore
    makes exactly one content shape ACCEPTABLE on V1's gated ingress. *)
type mutation =
  | Pristine  (** the real code: all five gates present *)
  | No_basefee_gate
      (** delete the [if base_fee != expected_base_fee] rejection in
          [validate_basefee] (validator.rs:188-195, called at :80). This adds
          the transition (Authored Forged_fee, Unseen, v2, cert) -> (Authored
          Forged_fee, Resolved Accepted, v2, cert) and removes the matching
          [Rejected] edge, so a fee-forged batch enters V1's store. NO SIBLING
          PATH REPAIRS IT: swept every non-test [base_fee_per_gas] use in
          crates/. Execution never re-derives the fee - payload_builder.rs:147
          reads [batch.base_fee_per_gas] verbatim, evm/config.rs:131-138 copies
          it into [BlockEnv.basefee] and evm/block.rs:992 writes it into the
          sealed header, with no comparison anywhere on that chain. The only
          other comparison-shaped uses are the epoch-entry derivation
          (node/manager/node.rs:328-343) and the txpool's [pending_basefee]
          (node/engine/inner.rs:149, start_epoch.rs:414), both AUTHOR-side
          admission control, not a receiver gate. The ungated ingresses run no
          validation at all, and the other four gates in [validate_batch] are
          indifferent to the fee. *)
  | No_recovery_gate
      (** delete the [.collect::<BatchValidationResult<Vec<_>>>()] in
          [decode_transactions] (validator.rs:147-156, called at :70) that turns
          ONE [recover_and_validate] failure (:209-215) into a whole-batch
          rejection - the "drop the bad transaction instead of failing the
          batch" edit. This adds (Authored Unrecoverable, Unseen, v2, cert) ->
          (Authored Unrecoverable, Resolved Accepted, v2, cert), so the [Halted]
          terminal becomes reachable from a V1-accepted state. NO SIBLING PATH
          REPAIRS IT: the engine's tolerance arm is NOT a repair - lib.rs:782-800
          skips only [BlockExecutionError::Validation(InvalidTx)] in phase 2,
          i.e. AFTER recovery succeeded, while phase 1 at :763-780 propagates
          any recovery failure with [?]. No other production code recovers a
          batch's transactions: the only two call sites of
          [reth_recover_raw_transaction::<TransactionSigned>] on batch bytes are
          validator.rs:213 (through txn_pool.rs:369-373) and lib.rs:769.
          Filtering rather than failing leaves every other gate satisfied, and
          the fetch paths verify the digest only (handle.rs:498-523). *)
  | No_empty_batch_gate
      (** delete the [.reduce(|total, size| total + size).ok_or(EmptyBatch)?] in
          [validate_batch_size_bytes] (validator.rs:127-141, called at :67) -
          the "reduce -> zero-seeded sum" edit. This adds (Authored
          Empty_payload, Unseen, v2, cert) -> (Authored Empty_payload, Resolved
          Accepted, v2, cert). NO SIBLING PATH REPAIRS IT:
          [BatchValidationError::EmptyBatch] is constructed at exactly one place
          in the whole tree (validator.rs:132). With a zero total every
          remaining gate passes - [0 <= max_batch_size] (:133-138), decoding
          [[]] is [Ok([])] (:147-156), no blob tx is found (:198-206), total gas
          [0 <= max_batch_gas] (:158-185, whose comment at :167-168 explicitly
          DELEGATES the empty check to [validate_batch_size_bytes]), the fee
          check is untouched (:188-195) and an empty batch's digest is
          self-consistent (:41-45). Downstream, [read_sync_batches] checks only
          digest membership (handle.rs:498-523), [fetch_for_primary] stores
          whatever hashed correctly (batch_fetcher.rs:186-200), and the engine
          builds a block per batch with no emptiness precondition
          (payload_builder.rs:137-184). *)

(** Whether V1's gated ingress accepts this content under a mutation. Pristine
    only [Well_formed] passes all five gates; each mutation additionally accepts
    exactly the content its deleted gate rejected. Every mutation arm is
    spelled - never a wildcard on the finite mutation sum. *)
let accepts mut c =
  match c with
  | Well_formed -> true
  | Forged_fee -> (
      match mut with
      | Pristine -> false
      | No_basefee_gate -> true
      | No_recovery_gate -> false
      | No_empty_batch_gate -> false)
  | Unrecoverable -> (
      match mut with
      | Pristine -> false
      | No_basefee_gate -> false
      | No_recovery_gate -> true
      | No_empty_batch_gate -> false)
  | Empty_payload -> (
      match mut with
      | Pristine -> false
      | No_basefee_gate -> false
      | No_recovery_gate -> false
      | No_empty_batch_gate -> true)

(** V1's enabled moves: the gated ingress resolves once, to the verdict
    {!accepts} dictates for the authored content (handler.rs:244-254). A
    resolved ingress has no further move - the batch is stored or dropped. *)
let v1_moves mut c s =
  match s.v1 with
  | Unseen ->
      [ { s with v1 = Resolved (if accepts mut c then Accepted else Rejected) } ]
  | Resolved (Accepted | Rejected) -> []

(** V2's enabled moves. [Idle -> Holds] is the UNGATED store and is enabled
    before commitment because the gossip prefetch fires on the digest
    announcement ("This allows non-CVVs to pre fetch batches they will soon
    need", handler.rs:188-191). [Idle] also STUTTERS at both [cert] values: the
    prefetch is best-effort and skipped when admission declines
    (handler.rs:167-191), and after commitment [fetch_for_primary_inner] is an
    infinite retry whose exhausted-retries error is swallowed and re-tried
    (batch_fetcher.rs:154-210, the [if let Ok(..)] at :177), so "the payload
    never arrives" is a legal infinite behaviour and no [Af] conjunct may assume
    delivery.

    [Holds -> _] requires [Committed] because the engine only executes the
    batches of a committed [ConsensusOutput] (payload_builder.rs:139-184). Two
    outcomes are then possible and BOTH are modelled:

    - the content-DEPENDENT one - [Halted] exactly for [Unrecoverable] bytes
      (the phase-1 abort of tn-reth/src/lib.rs:763-780, the very predicate
      [validate_batch] re-runs at validator.rs:209-215), [Executed] otherwise;
    - the content-INDEPENDENT [Aborted], always available, standing for every
      other fatal exit of the same [?] chain (see the {!Aborted} constructor).
      It is enabled even for [Unrecoverable] bytes because two of those exits -
      [builder_for_next_block] and [apply_pre_execution_changes],
      tn-reth/src/lib.rs:756-761 - run BEFORE recovery phase 1 and so pre-empt
      the recovery abort.

    There is no stutter at [(Holds, Committed)]: with the payload in hand and
    the output committed, [execute_consensus_output] runs to one of these
    verdicts. *)
let v2_moves c s =
  match (s.v2, s.cert) with
  | Idle, (Pending | Committed) -> [ s; { s with v2 = Holds } ]
  | Holds, Pending -> []
  | Holds, Committed ->
      [
        {
          s with
          v2 =
            (match c with
            | Unrecoverable -> Halted
            | Well_formed | Forged_fee | Empty_payload -> Executed);
        };
        { s with v2 = Aborted };
      ]
  | (Executed | Halted | Aborted), (Pending | Committed) -> []

(** Consensus's move on [D]'s certificate. The [Pending] SELF-LOOP is
    deliberate and load-bearing: it encodes "the certificate for [D] may never
    be committed" (the author equivocates, or the epoch closes and the cache is
    cleared, handler.rs:194-200). It keeps [Af (Atom V2_executed)] FALSE at
    every [Pending] state, so S2's liveness conjunct - asserted only from
    [Committed] - is not manufactured (R8). Commitment is irreversible. *)
let cert_moves s =
  match s.cert with
  | Pending -> [ s; { s with cert = Committed } ]
  | Committed -> []

(** The transition relation under a mutation. From the root the ONLY move is
    the hidden Byzantine authoring choice among the four content shapes;
    thereafter V1's ingress, V2's ingress/engine and consensus advance
    independently, one component per step. Terminal states (authored, resolved,
    executed-or-halted, committed) are stutter-closed by the kernel. *)
let next_with mut s =
  match s.envelope with
  | Unauthored ->
      List.map
        (fun c -> { s with envelope = Authored c })
        [ Well_formed; Forged_fee; Unrecoverable; Empty_payload ]
  | Authored c -> List.concat [ v1_moves mut c s; v2_moves c s; cert_moves s ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The single initial state: nothing authored, nothing reported, nothing
    stored, nothing committed. *)
let initial = { envelope = Unauthored; v1 = Unseen; v2 = Idle; cert = Pending }

(** The atom vocabulary the three CERT_ENVELOPE statements quantify over. *)
type atom =
  | V1_accepted
      (** [v1 = Resolved Accepted]: [validate_batch] returned [Ok] and the batch
          was inserted into [NodeBatchesCache] (handler.rs:244-254) *)
  | V1_rejected
      (** [v1 = Resolved Rejected]: [validate_batch] returned [Err], nothing was
          stored and the reporter was penalised (error.rs:76-104) *)
  | Content_forged_fee
      (** the bytes behind [D] carry [base_fee_per_gas <> f_epoch]
          (validator.rs:188-195) *)
  | Content_unrecoverable
      (** the bytes behind [D] contain a transaction that fails signer recovery
          (validator.rs:147-156, :209-215) *)
  | Content_empty
      (** the bytes behind [D] carry zero transactions (validator.rs:127-141) *)
  | V2_holds
      (** [v2 <> Idle]: the ungated node has [D]'s bytes in [NodeBatchesCache]
          (handler.rs:201-208 / primary.rs:104-111 / batch_fetcher.rs:186-200) *)
  | V2_executed
      (** [v2 = Executed]: the ungated node built a block for [D]
          (payload_builder.rs:139-184) *)
  | V2_halted
      (** [v2 = Halted]: execution aborted in recovery phase 1
          (tn-reth/src/lib.rs:763-780), exiting the engine run loop
          (engine/src/lib.rs:262-266) and tripping the critical-task shutdown
          (task_manager.rs:170-179) *)
  | V2_aborted
      (** [v2 = Aborted]: execution failed loudly on [D] for a
          content-independent reason - any other fatal exit of the same [?]
          chain (payload_builder.rs:56-76, :140-142, :167-175, :189-194;
          tn-reth/src/lib.rs:756-761, :797-798, :802-803) *)
  | V2_payload_empty
      (** V2 holds [D]'s bytes and those bytes carry zero transactions *)
  | Exec_fee_off_epoch
      (** V2's executed block for [D] charges a base fee [<> f_epoch]: the fee
          is copied verbatim from the batch, payload_builder.rs:147 ->
          evm/config.rs:138 -> evm/block.rs:992 *)
  | Committed_cert
      (** [cert = Committed]: consensus committed a certificate carrying [D] *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | V1_accepted -> v1_is_accepted s.v1
  | V1_rejected -> v1_is_rejected s.v1
  | Content_forged_fee -> envelope_is Forged_fee s.envelope
  | Content_unrecoverable -> envelope_is Unrecoverable s.envelope
  | Content_empty -> envelope_is Empty_payload s.envelope
  | V2_holds -> v2_has_bytes s.v2
  | V2_executed -> v2_is_executed s.v2
  | V2_halted -> v2_is_halted s.v2
  | V2_aborted -> v2_is_aborted s.v2
  | V2_payload_empty ->
      v2_has_bytes s.v2 && envelope_is Empty_payload s.envelope
  | Exec_fee_off_epoch ->
      v2_is_executed s.v2 && envelope_is Forged_fee s.envelope
  | Committed_cert -> cert_is_committed s.cert

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | V1_accepted -> "accepted_1(D)"
  | V1_rejected -> "rejected_1(D)"
  | Content_forged_fee -> "content(D)=forged_fee"
  | Content_unrecoverable -> "content(D)=unrecoverable"
  | Content_empty -> "content(D)=empty"
  | V2_holds -> "holds_2(D)"
  | V2_executed -> "executed_2(D)"
  | V2_halted -> "halted_2(D)"
  | V2_aborted -> "aborted_2(D)"
  | V2_payload_empty -> "payload_empty_2(D)"
  | Exec_fee_off_epoch -> "exec_fee_2(D)<>f_epoch"
  | Committed_cert -> "committed(D)"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: single initial state, mutation-
    parameterized transitions, the two-agent view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
