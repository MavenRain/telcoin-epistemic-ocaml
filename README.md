# telcoin-epistemic-ocaml

One hundred and eighty-nine security / safety / liveness / fairness statements
about the
[telcoin-network](https://github.com/Telcoin-Association/telcoin-network)
DAG-BFT protocol, each encoded in a temporal epistemic logic and proved by an
LCF-style kernel wrapping an exact finite-state model checker. What a reader
gets is a machine-checked catalogue of what a telcoin validator **knows** at
each point of a protocol run - not merely what is true, but what is entailed by
the state that validator actually holds - together with 69 executable finite
models of named telcoin subsystems, a negative test per statement that deletes
the exact code gate the claim rests on, and a second, independent foundation of
the checker itself as the internal logic of a presheaf topos.

| | |
|---|---|
| statements | 189 - security 59, safety 63, liveness 38, fairness 29 (pinned in `test/t_all_statements.ml`) |
| models | 69 - one shared `Tn_model` plus 68 isolated family models |
| mutation pins | 189 gate deletions across the 69 models |
| topos layer | all 69 checkers are the presheaf-topos denotation, each differentially gated against the original checker; 57 frames certify as posets, 12 as preorders |
| tests | 217 test executables, 0 failures; `dune build` clean, 0 warnings |
| grounded against | telcoin-network at git `0c59c15b`, plus three uncommitted local files in the authoring tree (see Provenance) |
| license | MIT OR Apache-2.0 |

## Layout

| path | contents |
|---|---|
| `lib/formula.ml{,i}` | the CTLK syntax: atoms are a caller-supplied sum type, so each statement module matches exhaustively over its own vocabulary |
| `lib/system.ml{,i}` | interpreted systems, the exact checker, and the `Theorem.thm` kernel boundary |
| `lib/tn_state.ml`, `lib/tn_model.ml`, `lib/statements.ml` | the original shared model and its seven statements |
| `lib/<family>_model.ml`, `lib/<family>_statements.ml` | 68 isolated family models and the 182 statements over them |
| `lib/all_statements.ml`, `lib/report.ml` | the flat 189-row cross-model report (theorems over different state types cannot share a list) |
| `lib/internal/` | the CTLK checker refounded as the internal logic of a presheaf topos, plus `DESIGN.md`, the normative spec |
| `test/topos_gate.ml`, `test/topos_laws.ml` | the two reusable gate functors every model is put through: the poset certificate plus the `Denote` against `System` differential, and the categorical laws on a real frame |
| `test/` | kernel semantics, per-family proof suites, per-family mutation suites, per-family topos gates, and the two cross-model topos suites |

## The logic

CTLK over Fagin-Halpern-Moses-Vardi interpreted systems: branching temporal
operators (`AG`/`AF`/`AX`/`AU` and their existential duals) plus knowledge
operators - `K_i phi` ("validator i knows phi") holds at a state when `phi` is
true at every reachable global state whose projection onto i's local state
matches, `E_G` (everyone knows), `C_G` (common knowledge, a greatest fixpoint).

Knowledge is grounded. A validator's view is exactly what it possesses - in the
shared model, its DAG, batch store, vote log, committed set and executed prefix
(`lib/tn_state.ml:183-189`); in a family model, that family's local record - and
never other validators' stores, in-flight messages, or the adversary's private
branch. Two consequences shape every statement:

- facts the protocol makes inevitable are knowable by inference (FHMV implicit
  knowledge), so the strictly epistemic content has to live over contingent
  hidden facts: a Byzantine branch, another node's possession inside a delivery
  window, the quorum behind a certificate;
- a positive `K_i` claim is only informative when the operative view class holds
  at least two reachable worlds. A `K` over a singleton class is true for the
  wrong reason. Each family's statement module documents that non-degeneracy
  witness explicitly, and it is a defect class the adversarial review hunted for
  (see [Provenance](#provenance-and-the-adversarial-review)).

The checker is exact on the finite reachable graph: temporal operators by
monotone fixpoint iteration over the powerset lattice, knowledge operators by
partitioning the reachable set on views. The transition relation is made total
by stutter-closing terminal states, so `AF`/`AU` are well defined, and liveness
verdicts therefore encode whatever fairness the model builder baked into `next`.

## The kernel boundary

`Theorem.thm` (`lib/system.mli:59-83`) is the boundary: its only constructors are
`prove` and `prove_nonvacuous`, so possessing a theorem value is possession of a
checked proof. Failure is a typed `proof_error`, either `Refuted of {
failing_inits : int }` or `Vacuous_antecedent`.

Every one of the 189 statements is proved through `prove_nonvacuous`, never
`prove`. The difference matters. `AG (p -> q)` is trivially valid in any model
where `p` is unreachable, and an unreachable antecedent is exactly what a
modelling slip produces: a guard written slightly too tightly, a phase that no
transition ever enters, a Byzantine branch that was never wired up. Such a
statement is green and says nothing. `prove_nonvacuous` takes the antecedent as
a separate argument, checks it is satisfiable somewhere in the reachable set,
and refuses to issue the theorem otherwise. The reachability witness is part of
each statement record, sitting beside its formula, so the guard cannot be
skipped for one statement without deleting a field.

## Why isolated per-family models

Knowledge is not a property of a single run. `K_i phi` at a state quantifies
over the whole set of reachable states sharing i's view, so the verdict depends
on which runs are in the model. Adding an unrelated mechanism to a model adds
runs, splits or merges view classes, and can silently flip a knowledge verdict
in a part of the model that has nothing to do with the addition. One monolithic
model of telcoin-network would cross-perturb: a gate added for the epoch
machinery would change what a worker knows about a batch.

The architecture is therefore one lean model per mechanism family. Each family
is its own `Denote.Make (State) (View)` instance with its own state type, its
own atom vocabulary, its own `make () : (_ Checker.t, Empty_init) result` and
its own `mutation` sum type. Families cannot interfere, mutation pins stay
attributable, and reachable sets stay in the tens of states, where the checker
is exact and the model is small enough to read. The cost is stated plainly in
[Limits and scope](#limits-and-scope): nothing here says anything about the
interaction between two families.

## The family models

Reachable-state counts below are live-measured on the built library at repo
`HEAD`, not copied from the build report. Mutation constructors are the gate
deletions used as pins; `Pristine` is omitted.

### Generation 1 - the shared model

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `tn_model` | one Narwhal/Bullshark anchor window, 10 validators with a uniform-strategy Byzantine coalition (V3/V4/V5), f = 3, 3 rounds: propose -> vote -> certify at 2f+1 = 7 -> deliver -> f+1 = 4-support commit -> deterministic execution. n = 3f+1 is the tight point of the BFT arithmetic: the n-f = 7 honest validators are exactly a quorum, and a conflicting certificate pair needs 4 double-voters where the coalition supplies 3 | 141 | `Drop_batch_gate`, `Weak_quorum`, `No_support_check`, `Unbounded_delay`, `Leader_censors_v2`, `No_vote_once` |

### Generation 2 - twelve isolated families

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `ban_model` | libp2p peer scoring: fatal content-fault charge routing and the committee `TrustBasis` exemption (`peers/peer.rs:209-237`, `peers/manager.rs:424-443`) | 11 | `Charge_relayer`, `No_exemption` |
| `admission_model` | peer-manager admission: three independent directed ban pairs, temp-ban cache, ban-gated dial retry (`peers/manager.rs:396-403`, `peers/behavior.rs:102-105`) | 27 | `No_admission_denial` |
| `gossip_auth_model` | authenticated publishing on the certificate gossip topic (`consensus/primary/src/network/mod.rs:423-428`, `verify_gossip` at `network-libp2p/src/consensus.rs:1491-1514`) | 25 | `Drop_publisher_auth` |
| `exec_tally_model` | a state-sync observer that does not execute, tallying gossiped `ConsensusResult` signatures to f+1 (`executor/src/subscriber.rs:280-325`) | 9 | `Weak_sig_threshold` |
| `identity_model` | the signed peer-record binding of a BLS key to a libp2p `PeerId` (`peers/manager.rs:799-838`) | 13 | `Drop_record_verify` |
| `unres_model` | the unresolved-author gossip reject and its penalty routing (`network-libp2p/src/consensus.rs:1499-1513`, `:2087-2097`) | 10 | `No_author_resolved_guard` |
| `prefetch_model` | worker-batch digest gossip publish (`worker/src/worker.rs:293-320`) and the receiver's content-addressed prefetch (`worker/src/network/handler.rs:188-223`, digest recomputed and re-keyed at `worker/src/network/handle.rs:509,523`) | 5 | `No_content_addressing` |
| `revote_model` | the re-vote discipline for one equivocating slot (`primary/src/network/handler.rs:807-847`, `stores/certificate_store.rs:219-228`) | 8 | `No_cert_evidence_guard` |
| `swap_model` | Bullshark leader swap from committed reputation scores (`consensus/bullshark.rs:81-97`) | 8 | `No_shared_seed` |
| `catchup_model` | ahead-certificate round catch-up; certificate acceptance requires parents in storage (`state_sync/cert_manager.rs:103-120`) | 21 | `Drop_catch_up` |
| `stall_model` | stalled-commit timeout kicking the certificate fetcher, gated on pending targets (`state_sync/gc.rs:42-58`) | 25 | `No_timeout_fetch` |
| `reqres_model` | the state-sync consensus-output pull and its digest gate before caching (`state-sync/src/consensus.rs:42-94`) | 16 | `No_digest_gate` |

### Generation 3 - fourteen isolated families

All fourteen were read in-checkout against telcoin-network `0c59c15b`.

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `epoch_record_model` | holding, and knowing one holds, a super-quorum-certified `EpochRecord` over a three-epoch window (`types/src/primary/epoch.rs:59-89`) | 42 | `No_quorum_count`, `Cert_conjunct_dropped`, `Cursor_starts_at_latest` |
| `epoch_sync_model` | the trustless epoch-record sync loop (`state-sync/src/epoch.rs:46-150`) | 13 | `No_parent_hash_check`, `No_cert_quorum_check`, `Committee_targeted_fetch` |
| `epoch_close_model` | one epoch boundary in two disjoint cones: close it yourself, or adopt someone else's record (`node/manager/node/close_epoch.rs:238-249`, `storage/src/epoch_records.rs:574-576`, `node/manager/node/run_epoch.rs:487-503`) | 51 | `No_cert_quorum_count`, `No_cert_digest_binding`, `No_committee_predial` |
| `epoch_reward_model` | the in-memory per-leader reward counter across the empty-output fast path and a crash-and-rebuild restart (`storage/src/consensus_pack.rs:1284-1291`) | 22 | `Credit_after_skip`, `No_catchup_watermark`, `Skip_batchless_close` |
| `cert_envelope_model` | what accepting a batch's bytes on your own gated ingress tells you about a remote node's handling of it (`batch-validator/src/validator.rs:188-195`) | 49 | `No_basefee_gate`, `No_recovery_gate`, `No_empty_batch_gate` |
| `exec_tip_model` | the pre-vote execution gate binding a header's `latest_execution_block` to the voter's own chain (`primary/src/network/handler.rs:639-650`), against a tip each node writes purely locally (`engine/src/lib.rs:262-271`) | 50 | `No_execution_gate`, `No_engine_spawn` |
| `exex_fanout_model` | the ExEx manager's bounded, non-blocking fan-out pipeline (`exex/src/manager.rs:209-220`) | 25 | `No_canon_gap_marker`, `No_lagged_presend`, `Blocking_send` |
| `exex_life_model` | the ExEx notification surface of one consensus-following host (`executor/src/subscriber.rs:100-129`) | 52 | `No_epoch_window`, `No_committee_gate`, `Spawn_exex_critical` |
| `gossip_reject_model` | how the gossip reject path attributes accountability between relayer and author (`network-libp2p/src/consensus.rs:1491-1514`, `:2087-2097`) | 49 | `No_receive_size_gate`, `No_reject_attribution_split`, `No_committee_exemption` |
| `own_durable_model` | durability of a validator's own certificate record, and who can observe it (the `ProposedCertificates` insert `primary/src/certifier.rs:443-446` ahead of the gossip publish at `:454`, already-certified guard at `:418-430`) | 22 | `No_disk_write`, `No_proposed_cert_guard`, `No_store_before_publish` |
| `pending_gc_model` | the parked-certificate map, its GC release, and the vote round that reads it (`state_sync/cert_manager.rs:103-120`, `state_sync/pending_cert_manager.rs:171-173`) | 48 | `No_gc_release`, `No_parent_check`, `No_pending_filter`, `No_parent_wait` |
| `batch_verdict_model` | the worker's batch-seal quorum wait for one sealed batch (`worker/src/quorum_waiter.rs:130-170`, `worker/src/network/handler.rs:252-254`) | 47 | `No_peer_store_before_ack`, `No_recoverable_class` |
| `verif_prov_model` | the provenance of a certificate's verification mark on the catch-up fetch ingress, versus the evidence it stands for (`types/src/primary/certificate.rs:462-471`, `primary/src/certificate_fetcher.rs:494-505`) | 41 | `No_wire_tag_reset`, `No_leaf_direct_verification`, `No_chunk_abort` |
| `discovery_model` | the kad and peer-exchange discovery surface (`network-libp2p/src/consensus.rs:1993-1999`, `peers/manager.rs:749-755`) | 35 | `No_query_max_fold`, `No_put_freshness_gate`, `Penalize_stale_record`, `Px_binds_identity` |

### Generation 4 - forty-two isolated families

All forty-two were read in-checkout against telcoin-network `0c59c15b`. They are
grouped here by the subsystem they model, which is not always what the family
name suggests: `parent_batch_forward` is a batch of parent certificates on the
proposer's channel and not a worker batch, `pack_replay` is the save-publish-
execute-crash-replay cycle and not an archive family, and the `stream_` prefix
spans two different crates.

**Consensus primary: DAG ordering and certificate and vote ingress.** How a leader is committed and its subdag walked, what the resident DAG keeps and dedups, and every gate a peer's certificate, vote or parent claim passes before it joins that DAG.

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `subdag_leader_walk_model` | one Bullshark commit walk over a four-round window: the f+1 support gate, the linkedness-gated walk-back, and per-leader subdag emission (`consensus/primary/src/consensus/bullshark.rs:194-206`, `consensus/primary/src/consensus/bullshark.rs:290-307`, `consensus/primary/src/consensus/bullshark.rs:217-246`) | 36 | `No_leader_support_gate`, `No_walk_back_inclusion` |
| `dag_retention_model` | one validator's `ConsensusState` dag, which retains committed certificates, and the three gates reading `last_committed` or `committed_round` over it: the walk skip, the leader short-circuit, the always-insert (`consensus/primary/src/consensus/utils.rs:33-44`, `consensus/primary/src/consensus/bullshark.rs:133-138`, `consensus/primary/src/consensus/state.rs:143-148`) | 42 | `No_last_committed_skip`, `No_below_commit_shortcircuit`, `Insert_gated_on_last_committed` |
| `round_weight_cap_model` | one round's parent aggregator: the distinctness guard that discards a repeat origin silently, the weight accumulation, and the 2f+1 threshold gate that reads the capped weight (`consensus/primary/src/aggregators/certificates.rs:82-85`, `consensus/primary/src/aggregators/certificates.rs:87-89`, `consensus/primary/src/aggregators/certificates.rs:91-99`) | 46 | `No_distinct_origin_guard`, `No_quorum_threshold_gate` |
| `parent_batch_forward_model` | the round-`r` parent handoff from the certificate-manager task to the proposer over the bounded `parents` channel, drain-on-quorum then extend-or-replace (`consensus/primary/src/aggregators/certificates.rs:75-102`, `consensus/primary/src/consensus_bus.rs:789`, `consensus/primary/src/proposer.rs:404-407`, `consensus/primary/src/proposer.rs:437-447`) | 42 | `No_drain`, `No_parents_forward`, `No_equal_arm_extend`, `No_equivocation_guard` |
| `cert_bitmap_quorum_model` | the roaring signer bitmap of a certificate, the one aggregate signature it indexes, and the three ingress routes that dispose of a peer-supplied certificate (`types/src/primary/certificate.rs:177-199`, `types/src/primary/certificate.rs:236-246`, `types/src/primary/certificate.rs:284-286`, `types/src/primary/certificate.rs:295-301`, `types/src/primary/certificate.rs:255-266`, `consensus/primary/src/state_sync/cert_validator.rs:303-323`) | 45 | `No_weight_threshold`, `Trust_supplied_signer_set`, `No_genesis_header_equality` |
| `parent_claim_binding_model` | one missing parent digest bound to one proposer on the vote path: the voter's `Entry::Vacant` slot claim (`consensus/primary/src/network/handler.rs:910-921`), its requester-binding retain (`consensus/primary/src/network/handler.rs:936-946`), and the author's declared-parent filter (`consensus/primary/src/certifier.rs:150-151`) | 32 | `No_requester_binding`, `No_vacant_claim`, `No_author_parent_filter`, `No_evaluation_deadline` |
| `vote_cache_retry_model` | the primary's per-author vote response cache and the certifier retry loop that feeds it: one `TokioMutex` per committee author holding that author's last answer (`consensus/primary/src/network/handler.rs:475-600`, `consensus/primary/src/network/handler.rs:55-58`), against `Certifier::request_vote` (`consensus/primary/src/certifier.rs:124-219`) | 44 | `No_empty_parent_reissue`, `No_one_epoch_ahead_arm`, `Single_shared_vote_lock` |
| `fetch_verif_state_model` | bulk certificate fetch of a four-round chain: ingress wire-tag reset, the direct/indirect verification plan, and the one chunk's abort-on-first-failure (`consensus/primary/src/certificate_fetcher.rs:494-505`, `consensus/primary/src/state_sync/cert_validator.rs:303-312`, `consensus/primary/src/state_sync/cert_validator.rs:337-343`) | 41 | `No_periodic_anchor`, `No_wire_state_reset`, `No_chunk_abort` |
| `causal_handoff_model` | the primary's state-sync repair loop: pending-parent index, the arrival `push_front` release and the lowest-key gc drain into the DAG, plus the fetcher's target floor (`consensus/primary/src/state_sync/cert_manager.rs:121-124`, `consensus/primary/src/state_sync/pending_cert_manager.rs:137-156`, `consensus/primary/src/certificate_fetcher.rs:332-348`) | 50 | `Handoff_push_back`, `Release_highest_first`, `Target_retain_default_zero` |

**Worker batches and transaction admission.** The worker's batch lifecycle: what a worker packs into its own batch and how much of it one sender may take, what it accepts from a peer, the quorum it gathers before the pool is updated, and where a non-committee node's transactions go instead.

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `batch_pack_share_model` | one seal of one worker's batch: the over-budget `continue` in the packing loop, the pool's per-sender slot cap, and the synthetic post-seal nonce advance (`batch-builder/src/batch.rs:73-81`, `tn-reth/src/lib.rs:333-337`, `batch-builder/src/batch.rs:128-139`) | 42 | `Break_on_over_budget`, `No_per_sender_slot_cap`, `No_post_seal_nonce_hint` |
| `batch_admit_model` | the four routes into a worker's `NodeBatchesCache`: one content-gated admission through `validate_batch`, three digest-only writers, and the unserialized receipt stamp (`batch-validator/src/validator.rs:39-82`, `consensus/worker/src/network/handler.rs:181-208`, `types/src/worker/sealed_batch.rs:86`) | 36 | `No_gas_ceiling`, `No_blob_reject`, `Digest_covers_received_at` |
| `batch_quorum_tally_model` | one `QuorumWaiter::verify_batch` attempt over a 4-member committee: the whole-committee fan-out, the recoverable versus permanent classification of each reply, and the stake tally (`consensus/worker/src/quorum_waiter.rs:136-137`, `consensus/worker/src/network/message.rs:125-155`, `consensus/worker/src/quorum_waiter.rs:166-170`) | 54 | `No_author_self_credit`, `No_recoverable_class`, `Truncated_fanout` |
| `tx_forward_route_model` | observer-to-committee transaction router: the sender-derived owning slot is contacted first, then every other advertised endpoint, under a per-attempt timeout and a per-transaction budget (`tn-reth/src/forward.rs:218-229`, `tn-reth/src/forward.rs:142-143`, `tn-reth/src/forward.rs:148`) | 46 | `Round_robin_owner`, `No_forward_budget`, `No_transient_fallthrough`, `Timeout_counts_as_delivered` |

**EVM execution semantics and the native precompiles.** Everything inside one block's EVM: the over-estimation gas penalty and the three-way fee split, the system calls that open and close a block, and the two native precompiles.

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `gas_penalty_split_model` | the over-estimation gas penalty's two uniform exemption gates and the three-way redistribution of the gas charge, decided against a batch admitted before its real usage exists (`tn-reth/src/evm/utils.rs:45-84`, `tn-reth/src/evm/handler.rs:78-171`, `batch-validator/src/validator.rs:162-185`) | 27 | `No_small_limit_exemption`, `Refund_aware_penalty`, `Burn_the_penalty` |
| `fee_routing_sink_model` | where a block's fee charge lands: priority tip to the certified author, base fee and over-estimation penalty to a node-local `OnceLock` sink (`tn-reth/src/evm/handler.rs:156`, `consensus/executor/src/subscriber.rs:522-526`, `tn-reth/src/lib.rs:196-210`) | 38 | `Basefee_to_producer`, `Basefee_burned`, `Beneficiary_from_batch_field`, `Mutable_fee_sink` |
| `close_block_syscall_model` | one block on one EVM instance: the pre-block system-call window that zeroes the base fee and disables the nonce check, then swaps them back (`tn-reth/src/evm/mod.rs:164-221`), and the epoch-close guard in `finish` over the `close_epoch` the header carries (`tn-reth/src/evm/block.rs:794`, `tn-reth/src/evm/config.rs:154-167`) | 28 | `No_close_marker_gate`, `No_env_restore`, `Nonzero_basefee_for_syscall` |
| `bls_verify_gate_model` | native BLS12-381 proof-of-possession precompile at 0x..b151: the selector and 150k gas floor, the 48/96 compressed length gate, then `bls_verify_secure` (`tn-reth/src/evm/bls_precompile/mod.rs:93-153`, `types/src/crypto/bls_signature.rs:190-196`) | 49 | `Err_on_failed_verify`, `No_length_gate`, `No_pk_validation` |
| `tel_dispatch_surface_model` | the three gates between an arbitrary call to `0x7e1` and TEL's global state: the short-calldata length check, the fail-closed selector catch-all, and address-pinned storage (`tn-reth/src/evm/tel_precompile/mod.rs:121-123`, `tn-reth/src/evm/tel_precompile/mod.rs:128-164`, `tn-reth/src/evm/tel_precompile/burnable.rs:342-351`) | 33 | `No_short_calldata_guard`, `Open_selector_fallthrough`, `Frame_scoped_storage` |
| `tel_supply_ledger_model` | the TEL precompile's guarded ledger writes - the pending-mint pair, slot 100 `totalSupply` and the precompile's own native balance (`tn-reth/src/evm/tel_precompile/burnable.rs:154-206`, `:220-309`, `:317-377`) | 49 | `No_pending_clear`, `No_recipient_pin`, `No_supply_guard` |

**The engine, the executor and node lifecycle.** The seam from a committed consensus output to an executed block: the order and multiplicity with which outputs reach the EVM, the single execution slot behind the engine's bounded backlog, which execution errors are absorbed and which are fatal, and what a restart re-derives after a crash.

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `output_forward_gate_model` | the epoch manager's live-forwarding loop and its three-arm continuity gate feeding the engine's bounded FIFO backlog, over two consensus outputs and one hidden re-broadcast (`node/src/manager/node/run_epoch.rs:561-619`, `node/src/manager/node/run_epoch.rs:883-891`, `engine/src/lib.rs:120-124`) | 48 | `No_stale_arm`, `No_gap_arm`, `Queue_pop_back` |
| `engine_queue_model` | the tn-engine event loop's bounded backlog and its single execution slot: the ingest gate, the one-at-a-time grant, and grant-by-removal from the queue head (`engine/src/lib.rs:245`, `engine/src/lib.rs:227-230`, `engine/src/lib.rs:124`) | 41 | `No_slot_exclusion`, `No_queue_bound`, `Reexecute_head` |
| `exec_absorb_model` | the executor's error taxonomy for one committed output: the tolerated `InvalidTx` arm absorbs a cross-worker duplicate, every other error abandons the whole output (`tn-reth/src/lib.rs:763-800`, `batch-validator/src/validator.rs:69-70`) | 24 | `Fatal_on_invalid_tx`, `No_validation_decode`, `Commit_partial_block` |
| `pack_replay_model` | one active CVV's save -> publish -> execute cycle through a crash and the restart's replay scan, plus the epoch-close flag no serialized output carries (`consensus/executor/src/subscriber.rs:286`, `state-sync/src/lib.rs:148-182`, `node/src/manager/node/run_epoch.rs:536-539`) | 50 | `No_save_before_publish`, `No_replay_scan`, `No_boundary_recompute` |
| `boot_order_model` | one node's startup sequence from process start through the first epoch iteration: the finalized-marker heal, the recent-blocks priming and the one-time swarm setup (`node/src/manager/node.rs:864`, `node/src/manager/node.rs:906`, `node/src/manager/node/run_epoch.rs:255`) | 38 | `No_marker_heal`, `No_recent_blocks_prime`, `Initial_only_network_gate`, `Rebind_on_replay` |

**Storage backends and the consensus archive.** The layered database and its per-environment writer threads, the ordered certificate tables and the notification that wakes a waiting voter, and the epoch archive packs with their bloom-backed digest indexes, heal paths and import.

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `backend_writer_thread_model` | one `LayeredDatabase`'s background writer thread, the overlap count over its single physical transaction, and the two ways that count stops meaning what its readers think (`storage/src/layered_db.rs:179`, `storage/src/layered_db.rs:155-174`, `storage/src/layered_db.rs:256`) | 36 | `No_end_txn_on_drop`, `No_shutdown_break` |
| `backend_env_split_model` | the per-`TableHint` split of node storage into three physical environments, each with its own writer thread, physical transaction and overlap count, across the epoch boundary's two clear routes (`storage/src/composite_db.rs:39-45`, `storage/src/layered_db.rs:306-315`, `storage/src/redb/database.rs:58-63`) | 34 | `Merge_cache_into_epoch_env`, `No_redb_table_recreate` |
| `store_full_memory_model` | the `LayeredDatabase.full_memory` mode switch: the epoch DB's never-evicted mirror and its startup preload against the cache DB's evicting write buffer and unioning iterator (`storage/src/composite_db.rs:31-37`, `storage/src/layered_db.rs:347-356`, `storage/src/layered_db.rs:427`) | 27 | `No_open_preload`, `No_full_memory_mode_test`, `No_mem_chain_in_iter` |
| `store_key_order_model` | the ordered `CertificateDigestByOrigin` index, the big-endian key encoding that makes its byte order match `Ord`, and the `record_prior_to` probe behind the certificate fetch gate (`types/src/codec.rs:43-49`, `storage/src/stores/certificate_store.rs:411-419`, `consensus/primary/src/certificate_fetcher.rs:232-238`) | 54 | `No_big_endian`, `No_origin_guard` |
| `store_notify_visibility_model` | the seam between a certificate write and the parent-waiters parked on its digest: register then re-read, one notify firing every registered sender, and the mem-layer write that precedes the commit (`storage/src/stores/certificate_store.rs:251-269`, `tn-utils/src/notify_read.rs:38-40`, `storage/src/layered_db.rs:98`) | 36 | `No_post_registration_reread`, `No_notify_fanout`, `No_mem_write_on_insert` |
| `archive_pack_heal_model` | one epoch pack's data file and its three sidecar indexes across a failed append, a crash and a reopen: the write-failure latch, the append-open repair, the read-only agreement gate (`storage/src/archive/pack.rs:165`, `storage/src/consensus_pack.rs:664-728`, `storage/src/consensus_pack.rs:894-902`) | 64 | `No_shrink_clamp`, `No_static_consistency_gate`, `No_write_failure_latch` |
| `archive_hash_index_model` | the linear-hash digest index of one consensus archive pack: the modulus-fixed split rotation, the .odx overflow chain, and the FIFO-bounded clean cache, all served by one blocking thread (`storage/src/archive/digest_index/index.rs:549`, `storage/src/archive/digest_index/bucket_iter.rs:120-126`, `storage/src/consensus_pack.rs:132-193`) | 40 | `No_growth_gate`, `No_cache_eviction_loop`, `No_chain_decrease_guard` |
| `archive_digest_lookup_model` | the archive's by-digest read pipeline: the bloom fast-path negative, the `contains_batch` bounds test, the fetch's digest recheck, and the requester's re-hash of every batch it reads (`storage/src/archive/digest_index/index.rs:775-782`, `storage/src/consensus_pack.rs:1236-1245`, `consensus/worker/src/network/handle.rs:754-761`) | 36 | `No_digest_recheck`, `No_bloom_accrue`, `No_contains_bounds_check` |
| `archive_epoch_import_model` | one pass of `stream_import` over a peer-supplied epoch pack: the already-held short circuit, the v1 declared batch-count cap, the publish-time final-header equality, and the remove+rename install window readers race (`storage/src/consensus.rs:441-541`, `storage/src/consensus_pack.rs:1451-1468`, `storage/src/consensus.rs:509-532`) | 40 | `No_final_header_link`, `No_already_held_shortcircuit`, `No_batch_count_cap` |

**libp2p transport and peer management.** The length-prefixed snappy request and response codec with the penalty it charges the sender, the per-peer inbound stream rate window and its silent drops, and the two ways the peer manager sheds a peer: fairness pruning at heartbeat, and the temporary ban cache.

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `rpc_codec_size_model` | one inbound snappy exchange: the codec's two length gates, the inbound `Io` classifier that splits size refusals from transport flaps, and the trust basis that decides whether a levied penalty reaches the score (`network-libp2p/src/codec.rs:51-54`, `network-libp2p/src/codec.rs:61-67`, `network-libp2p/src/consensus.rs:1279-1314`, `network-libp2p/src/peers/peer.rs:213-233`) | 53 | `No_inbound_catchall_penalty`, `No_inbound_eof_exemption`, `No_trust_exemption`, `No_compressed_length_gate` |
| `stream_inbound_quota_model` | the stream behaviour's per-peer tumbling inbound rate window, its deletion when the last connection closes, and the two silent drops - rate gate and BLS identity gate - a negotiated stream can still hit (`network-libp2p/src/stream/behavior.rs:280-290`, `network-libp2p/src/stream/behavior.rs:258`, `network-libp2p/src/stream/behavior.rs:346-353`, `network-libp2p/src/consensus.rs:1673-1675`) | 37 | `No_per_peer_keying`, `No_window_reset_on_disconnect`, `No_identity_guard` |
| `peer_prune_fairness_model` | one heartbeat connection-limit prune round over five peers: shuffle then stable sort by score and routability, the validator and allowlist exemption filter, then eviction until the excess is spent (`network-libp2p/src/peers/all_peers.rs:965-978`, `network-libp2p/src/peers/manager.rs:575`, `network-libp2p/src/peers/manager.rs:583-594`) | 28 | `No_score_sort`, `No_tie_shuffle`, `No_validator_exemption`, `No_allowlist_exemption` |
| `peer_temp_ban_model` | the temporary-ban cache, the crate's only time-based exclusion: the drain's expiry stop, its one call per heartbeat, and the duplicate re-stamp on insert (`network-libp2p/src/peers/cache.rs:162-165`, `network-libp2p/src/peers/manager.rs:318`, `network-libp2p/src/peers/cache.rs:123-128`) | 26 | `No_expiry_guard`, `No_heartbeat_drain`, `No_reinsert_refresh` |

**Epoch data serving and per-peer admission control.** How a node serves epoch data without letting one peer take the whole node: the global semaphores and per-peer in-flight counters that admit or shed a request, the lifetime of a pending stream slot from acceptance to consumption or timeout, and the capability cache the requesting side keeps about who speaks sync.

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `record_serve_pool_model` | the primary's `EpochRecord` request-response arm: a global 5-permit pool and a 2-per-peer cap in one admission gate (`consensus/primary/src/network/mod.rs:343-363`), the silent shed (`consensus/primary/src/network/mod.rs:1602-1613`), and the dispatch penalty split (`consensus/primary/src/error/network.rs:141-205`) | 52 | `No_per_peer_record_cap`, `No_record_admission_gate`, `No_unaddressed_request_reject` |
| `serve_slot_quota_model` | one serving primary's two admission budgets: a stream semaphore shared by the legacy and sync paths under one union per-peer cap, plus a separate epoch-record pool (`consensus/primary/src/network/mod.rs:1664-1666`, `consensus/primary/src/network/mod.rs:326-341`, `consensus/primary/src/network/mod.rs:351-363`) | 52 | `No_cross_path_count`, `No_per_peer_stream_cap`, `Shared_permit_pool` |
| `stream_slot_tenure_model` | one `(peer, request_digest)` entry of the primary's `pending_epoch_requests` map, from permit-reserving acceptance (`consensus/primary/src/network/mod.rs:1647-1705`) through the consuming stream-open lookup (`consensus/primary/src/network/mod.rs:1843-1845`) to the periodic timeout eviction (`consensus/primary/src/network/mod.rs:1450-1456`) | 39 | `No_stale_prune`, `Rearm_created_at`, `Non_consuming_open` |
| `worker_stream_quota_model` | the worker's batch-stream admission accounting: one global permit pool and a combined per-peer in-flight count summing pending legacy requests, legacy serves and sync streams (`consensus/worker/src/network/mod.rs:41-45`, `consensus/worker/src/network/mod.rs:60-65`, `consensus/worker/src/network/mod.rs:206-216`) | 45 | `No_legacy_per_peer_cap`, `No_serving_guard`, `No_pre_read_sync_shed` |
| `stream_sync_capability_model` | the primary handle's per-peer sync-capability map, the outbound upgrade classification that decides what may write `false` into it, and the epoch-boundary clear that empties it (`consensus/primary/src/network/mod.rs:365-381`, `network-libp2p/src/stream/handler.rs:142-152`, `node/src/manager/node/start_epoch.rs:547-550`) | 34 | `No_io_classification_split`, `No_partial_probe_guard`, `No_epoch_clear` |

## The statements

### Generation 1 - the shared model (`lib/statements.ml`)

Three rounds of propose -> vote (batch-availability gated, vote-once per slot,
synchronizer fetch on vote) -> certify at 2f+1 -> deliver, then the f+1-support
commit rule evaluated by each validator on its own DAG, deterministic execution,
terminal stutter. Genuine branching: the Byzantine validator picks cooperate /
starve-batch / equivocate / silent, the honest leader may crash before proposing
its anchor (the cert-free witness that keeps "knowing a certificate formed"
contingent), and delivery of the anchor to one validator may be delayed a round
(bounded delay - the fairness assumption liveness verdicts are relative to).
Certificates are unforgeable by construction: a certificate value exists only
when the model has assembled quorum votes.

The delay window is real: `EF (v1 holds the anchor and v0 does not know it)` is
satisfiable, and after re-sync the mutual knowledge - in fact common knowledge -
of possession is restored (`test/t_tn_model.ml` probes both).

| # | statement | bucket | telcoin mechanism | pin |
|---|---|---|---|---|
| 1 | stored-cert-implies-known-quorum-and-slot-uniqueness | security | BLS aggregate verification `certificate.rs:225-251`, `is_verified` gate `cert_manager.rs:88-93`, equivocation rejection `state.rs:145-157` | `Weak_quorum` |
| 2 | vote-attests-known-parents-and-payload | security | vote-time parent checks `handler.rs:693-738`, batch sync before vote `header_validator.rs:98-154` | `Drop_batch_gate` |
| 3 | no-conflicting-revote-and-equivocation-detectability | safety | vote-once / `AlreadyVoted` `handler.rs:787-847`; equivocation knowable exactly through local conflicting evidence | `No_vote_once` |
| 4 | commit-implies-known-support-quorum | safety | Bullshark f+1 support count on own DAG `bullshark.rs:192-206`, validity threshold `committee.rs:254-259` | `No_support_check` |
| 5 | rounds-advance-under-known-distinct-quorum | liveness | `enough_parents` gate `proposer.rs:751-766` feeding the round advance `proposer.rs:546-553`, `authorities_seen` dedup `certificates.rs:82-99`, state-sync propagation | `Unbounded_delay` |
| 6 | round-robin-leader-common-knowledge-and-slot-fairness | fairness | deterministic `leader` schedule `leader_schedule.rs:285-304`; causal-closure inclusion (no honest certificate censored) | `Leader_censors_v2` |
| 7 | quorum-ack-implies-honest-batch-availability | security | ack after validate-and-store `handler.rs:231-263`, `validator.rs:39-81`, quorum wait `quorum_waiter.rs:163-190` | `Drop_batch_gate` |

Statement 1's detect-and-halt branch for a delivered conflicting certificate
needs two Byzantine validators and is documented as out of scope at f = 1
(quorum intersection makes the pair unreachable, which is itself the proved
uniqueness invariant). Statement 6's common-knowledge conjunct is knowledge by
shared-config admissibility: every reachable world derives the same anchor slot,
and the perturbed-committee mutation is what would break it.

### Generation 2 - twelve isolated families (14 statements)

| # | family | statement | bucket | what it turns on | pin |
|---|---|---|---|---|---|
| 8 | ban | content-fault-ban-requires-known-author | fairness | a fatal content fault is charged to the author, not the relayer that forwarded it | `Charge_relayer` |
| 9 | ban | committee-exemption-liveness-known-but-unbannable-byzantine | liveness | the committee `TrustBasis` exemption keeps a known-Byzantine committee peer unbannable | `No_exemption` |
| 10 | admission | ban-is-local-enforcement-and-internode-opaque | safety | a ban is banner-local state; no other node can read it off the wire | `No_admission_denial` |
| 11 | admission | established-connection-implies-known-remote-admission | safety | an established connection entails the remote admitted you | `No_admission_denial` |
| 12 | gossip_auth | accepted-gossip-implies-known-committee-publisher | security | signed gossip plus authorized-publisher containment; a phantom outsider's frame is dropped | `Drop_publisher_auth` |
| 13 | exec_tally | consensus-output-gossip-tally-implies-known-honest-save | safety | f+1 distinct verified signers entail an honest node saved the output before signing | `Weak_sig_threshold` |
| 14 | identity | confirmed-identity-implies-known-signed-binding | security | identity is confirmed only through a signature-verified `NodeRecord` | `Drop_record_verify` |
| 15 | unres | unresolved-author-reject-skips-penalty-and-liveness-recovers | liveness | an unattributable frame charges nobody, and the observer recovers | `No_author_resolved_guard` |
| 16 | prefetch | batch-digest-gossip-prefetch-knowledge-via-verified-fetch | liveness | possession by a peer is learned only when a content-addressed fetch lands; a bare digest grants nothing | `No_content_addressing` |
| 17 | revote | revote-only-under-global-cert-ignorance | security | a re-vote on a conflicting slot happens only after the local certificate store is checked | `No_cert_evidence_guard` |
| 18 | swap | leader-swap-schedule-agreement-from-committed-scores | fairness | scores are a pure function of the committed sub-dag, so the same closing sub-dag gives the same swapped schedule | `No_shared_seed` |
| 19 | catchup | ahead-certificate-implies-round-catchup | liveness | a well-signed round-r certificate is transferable evidence of network progress and forces a round jump | `Drop_catch_up` |
| 20 | stall | stalled-commit-timeout-fetch-gated-by-pending-targets | liveness | the commit timeout kicks the fetcher, but a totally starved validator has no targets and stays ignorant | `No_timeout_fetch` |
| 21 | reqres | verified-response-implies-known-responder-possession | security | the digest gate runs before the cache insert, so a cached output entails the responder held it | `No_digest_gate` |

### Generation 3 - fourteen isolated families (42 statements)

| # | family | statement | bucket | what it turns on | pin |
|---|---|---|---|---|---|
| 22 | epoch_record | epoch-cert-implies-known-super-quorum-endorsement | security | the super-quorum count inside `verify_with_cert` | `No_quorum_count` |
| 23 | epoch_record | uncertified-epoch-record-implies-ignorance-until-cert | safety | holding a record is not holding its certificate | `Cert_conjunct_dropped` |
| 24 | epoch_record | restart-rescan-from-zero-recovers-certified-record-gap | liveness | the restart cursor rescans from zero, so a certified-record gap closes | `Cursor_starts_at_latest` |
| 25 | epoch_sync | adopted-record-answers-the-requested-epoch | safety | the parent-hash conjunct is the sole binding of a response to the epoch asked for | `No_parent_hash_check` |
| 26 | epoch_sync | adoption-implies-known-super-quorum-certification | security | adoption is gated on `verify_with_cert`, so 2f+1 signers executed that epoch | `No_cert_quorum_check` |
| 27 | epoch_sync | epoch-record-adoption-is-source-blind | security | the responder identity is discarded at the call site; the source can neither be confirmed nor ruled out | `Committee_targeted_fetch` |
| 28 | epoch_close | certified-epoch-record-implies-known-supermajority-endorsement | security | the `auth_iter < super_quorum()` tail of `verify_with_cert` | `No_cert_quorum_count`, `No_cert_digest_binding` |
| 29 | epoch_close | self-closed-epoch-record-is-never-displaced-and-divergence-stays-hidden | safety | the already-stored early return in `save_record` is idempotent, so your own record survives, and divergence stays invisible | `No_cert_digest_binding` |
| 30 | epoch_close | entry-predial-preserves-record-acquisition | liveness | the committee pre-dial on `connected_peers_count() == 0` keeps record acquisition reachable | `No_committee_predial`, `No_cert_quorum_count` |
| 31 | epoch_reward | blockless-round-credits-its-leader-with-no-block | fairness | the empty-output fast path still credits the round's leader | `Credit_after_skip` |
| 32 | epoch_reward | restart-rebuild-credits-each-committed-round-exactly-once | safety | the catch-up watermark stops a rebuild double-crediting | `No_catchup_watermark` |
| 33 | epoch_reward | batchless-boundary-output-inevitably-seals-the-epoch | liveness | a batchless boundary output still seals the epoch | `Skip_batchless_close` |
| 34 | cert_envelope | accepted-batch-implies-known-uniform-execution-base-fee | security | `validate_basefee` on your own ingress entails the remote's execution base fee | `No_basefee_gate` |
| 35 | cert_envelope | accepted-batch-implies-known-recovery-safe-execution | liveness | the recovery gate entails the remote can execute the payload | `No_recovery_gate` |
| 36 | cert_envelope | accepted-batch-implies-known-nonempty-remote-payload | safety | the empty-batch rejection entails a non-empty remote payload | `No_empty_batch_gate` |
| 37 | exec_tip | vote-implies-own-execution-yet-author-possession-unknown | security | the gate authenticates the claimed value against your own blocks, never the claimant's possession | `No_execution_gate` |
| 38 | exec_tip | certificate-implies-known-honest-execution-quorum | security | a certificate aggregates enough gated votes to entail an honest execution quorum | `No_execution_gate` |
| 39 | exec_tip | parked-vote-request-resolves-and-ahead-claim-stays-opaque | liveness | a parked vote request resolves, and an ahead claim stays opaque | `No_engine_spawn` |
| 40 | exex_fanout | payload-never-delivered-while-a-gap-marker-is-owed | safety | a canonical gap marker is owed before any payload may be delivered | `No_canon_gap_marker`, `No_lagged_presend` |
| 41 | exex_fanout | lagged-marker-is-delivered-and-known-but-its-cause-is-opaque | security | the lagged pre-send makes the marker inevitable, but its cause is unknowable | `No_lagged_presend`, `No_canon_gap_marker` |
| 42 | exex_fanout | stalled-sibling-exex-cannot-starve-the-live-exex | fairness | non-blocking sends stop one stalled ExEx starving another | `Blocking_send` |
| 43 | exex_life | exex-output-window-is-a-lower-bound-that-hides-a-two-epoch-network-lead-until-a-cert-verifies | safety | the output window is a lower bound; the network may be two epochs ahead until a certificate verifies | `No_epoch_window` |
| 44 | exex_life | unknown-committee-blocks-the-exex-certificate-signal-and-leaves-genuineness-unknown | security | an unknown committee blocks the certificate signal, so genuineness stays unknown | `No_committee_gate` |
| 45 | exex_life | isolated-exex-failure-never-halts-the-host-and-is-internode-opaque | liveness | an ExEx failure is isolated from the host and invisible to other nodes | `Spawn_exex_critical` |
| 46 | gossip_reject | oversized-gossip-receipt-implies-known-relayer-deviation | security | the network-wide size bound makes an oversized receipt attributable to the relayer | `No_receive_size_gate` |
| 47 | gossip_reject | unauthorized-author-reject-spares-and-cannot-judge-the-forwarder | fairness | the reject-attribution split spares the forwarder, and cannot judge it either | `No_reject_attribution_split` |
| 48 | gossip_reject | committee-author-charged-under-ignorance-is-never-banned | safety | the committee exemption means a charged committee author is never actually banned | `No_committee_exemption` |
| 49 | own_durable | own-write-persists-yet-author-cannot-observe-durability | liveness | the write persists, but its author has no view of durability | `No_disk_write` |
| 50 | own_durable | durable-own-certificate-record-forbids-signature-equivocation | safety | the proposed-certificate guard forbids signing two variants | `No_proposed_cert_guard` |
| 51 | own_durable | published-own-certificate-implies-known-prior-persist | security | store-before-publish makes publication entail a prior persist | `No_store_before_publish` |
| 52 | pending_gc | gc-horizon-acceptance-forfeits-parent-knowledge | safety | accepting at the GC horizon gives up the parent knowledge the causal-order check would have supplied | `No_parent_check` |
| 53 | pending_gc | pending-certificate-always-released | liveness | every parked certificate is eventually released | `No_gc_release` |
| 54 | pending_gc | vote-round-respects-pending-parent-state | safety | the vote round reads the same pending map, so it never contradicts parent state | `No_pending_filter`, `No_parent_wait` |
| 55 | batch_verdict | anti-quorum-leaves-peer-possession-unknown | safety | an anti-quorum leaves peer possession genuinely open; a `survives_under` row additionally asserts it still proves once the recoverable-error class is deleted | `No_peer_store_before_ack` |
| 56 | batch_verdict | accepted-report-implies-known-peer-possession | safety | the durable peer write precedes the ack, so an accepted report entails possession | `No_peer_store_before_ack` |
| 57 | batch_verdict | quorum-rejected-implies-known-permanent-but-opaque-verdict | security | a quorum rejection is permanent, but its reason is not recoverable | `No_recoverable_class` |
| 58 | verif_prov | fetched-parent-never-stored-before-dependent-signature-check | safety | the wire verification tag is reset on ingress, so nothing is stored on a peer's say-so | `No_wire_tag_reset`, `No_leaf_direct_verification`, `No_chunk_abort` |
| 59 | verif_prov | indirectly-verified-parent-carries-known-but-anonymous-quorum | security | an indirectly verified parent carries a quorum you know exists but cannot name | `No_wire_tag_reset`, `No_leaf_direct_verification`, `No_chunk_abort` |
| 60 | verif_prov | failed-dependent-quarantines-the-pre-marked-batch | safety | a failed dependent quarantines the batch that was marked ahead of it | `No_chunk_abort` |
| 61 | discovery | kad-query-adopts-max-timestamp-record-yet-currency-stays-unknown | security | the strict-max fold picks the freshest response, which is still not known to be current | `No_query_max_fold` |
| 62 | discovery | stale-replay-regression-is-gated-only-by-the-local-kad-store | security | only the local store's freshness gate stops a stale replay, and the replay is unattributable | `No_put_freshness_gate`, `Penalize_stale_record` |
| 63 | discovery | peer-exchange-confers-no-identity-and-no-sybil-knowledge | security | peer exchange binds no identity, so it grants no sybil knowledge | `Px_binds_identity` |

### Generation 4 - forty-two isolated families (126 statements)

| # | family | statement | bucket | what it turns on | pin |
|---|---|---|---|---|---|
| 64 | subdag_leader_walk | supported-leader-commit-implies-known-universal-inclusion | safety | clearing the f+1 support gate forces quorum intersection, so a peer committing the anchor from a lower committed round walks back and pushes L; occurrence known only from the signed record | `No_leader_support_gate`, `No_walk_back_inclusion` |
| 65 | subdag_leader_walk | unlinked-leader-skip-implies-known-global-no-direct-commit | security | an unlinked anchor means at most f supporters exist anywhere, so no node's voting-power sum can ever clear the support gate | `No_leader_support_gate` |
| 66 | subdag_leader_walk | linked-uncommitted-leader-eventually-anchors-its-own-subdag | liveness | the walk-back gives a linked leader a `CommittedSubDag` of its own with `sub_dag_index = leader.nonce()`, not merely its certificates swept into the anchor's closure | `No_walk_back_inclusion` |
| 67 | dag_retention | causal-closure-certificate-sequenced-exactly-once-across-subdags | safety | `already_ordered` is fresh per walk, so the `last_committed` disjunct is the only cross-walk dedup over a dag that still holds everything | `No_last_committed_skip` |
| 68 | dag_retention | committed-leader-round-never-reanchored-for-double-execution | safety | one comparison against `last_round.committed_round` is the whole shield; the late certificate still inserts, the support recount still clears, and the walk root is never deduped | `No_below_commit_shortcircuit` |
| 69 | dag_retention | below-commit-certificate-retained-so-children-stay-insertable | liveness | the insert is unconditional because at insert time nothing tells the node whether a peer built on the certificate; the parent citation arrives strictly later | `Insert_gated_on_last_committed` |
| 70 | round_weight_cap | per-origin-round-weight-cap-is-exactly-one | safety | the origin goes into `authorities_seen` before the `weight +=`, so weight counts identities not messages, and a re-fetch or a second header adds nothing | `No_distinct_origin_guard` |
| 71 | round_weight_cap | round-quorum-emission-implies-known-distinct-supermajority | security | emission entails 2f+1 remote certified rounds only because both gates hold - distinctness makes weight a count of identities, the threshold makes firing mean that count reached 2f+1 | `No_quorum_threshold_gate` |
| 72 | round_weight_cap | equivocating-origin-drop-is-silent-and-unattributable | security | the duplicate is refused before accumulation so it can never be the marginal unit; the drop is a bare `return None` with no log, metric or fault attribution | `No_distinct_origin_guard` |
| 73 | parent_batch_forward | parent-batch-drain-keeps-last-parents-duplicate-free | safety | the quorum emission drains the buffer, so the re-emission the un-reset weight guarantees carries nothing already delivered; the sender never learns whether the batch was taken | `No_drain` |
| 74 | parent_batch_forward | quorum-forward-gives-proposer-trustworthy-parents | liveness | with no catch-up notice due, latched weight leads to non-empty `last_parents`, and non-empty entails 2f+1 distinct origins counted by `authorities_seen` | `No_parents_forward`, `No_equivocation_guard` |
| 75 | parent_batch_forward | late-origin-admissible-and-evicted-only-by-a-future-round-jump | fairness | the `Equal` arm extends rather than replaces, so the late certificate can still reach the header and leaves `last_parents` only there or on a future-round jump | `No_equal_arm_extend` |
| 76 | fetch_verif_state | anchored-round-certificate-carries-known-quorum-its-neighbour-does-not | security | the ingress reset drops the peer's tag and the periodic disjunct runs the anchor's real aggregate check, while the indirect stamp leaves its neighbour unknown either way | `No_periodic_anchor`, `No_wire_state_reset` |
| 77 | fetch_verif_state | fetched-chain-never-runs-two-unchecked-rounds-in-a-row | safety | the multiple-of-interval disjunct selects the round-50 parent for direct verification, so an indirectly stamped round-51 never sits above an indirectly stamped predecessor | `No_periodic_anchor` |
| 78 | fetch_verif_state | failed-anchor-quarantines-the-pre-stamped-chain | safety | chunk error propagation discards the whole response before any write, so members already stamped `VerifiedIndirectly` never reach the store and the leaf's aggregate is never examined | `No_chunk_abort`, `No_periodic_anchor` |
| 79 | causal_handoff | unlocked-parent-precedes-its-dependents-into-consensus | safety | the `push_front` on the arrival path puts the unblocking parent ahead of the dependents it released, so the batch handed to the DAG is topologically sorted | `Handoff_push_back` |
| 80 | causal_handoff | gc-release-drains-the-lowest-blocked-round-first | safety | the drain takes `first_key_value` from the round-keyed blocked-parent index, so a dependent is never released ahead of the parent whose key is still parked | `Release_highest_first` |
| 81 | causal_handoff | every-fetch-target-is-eventually-dropped-by-the-gc-floor | liveness | the target filter defaults an origin with nothing in the reported window to `gc_round` itself, so an unsatisfiable catch-up target is dropped once the horizon passes it | `Target_retain_default_zero` |
| 82 | record_serve_pool | record-serve-pool-exhaustion-needs-three-distinct-requesters | fairness | the per-peer cap of 2 is read and incremented under one `peers.lock()` guard, so an exhausted 5-slot pool needs three distinct keys | `No_per_peer_record_cap` |
| 83 | record_serve_pool | epoch-record-serve-bounded-and-shed-invisible-to-the-shed-requester | security | the shed drops the response channel with no wire rejection, so a shed request and a slow serve look identical to the requester, and only a reply proves admission | `No_record_admission_gate` |
| 84 | record_serve_pool | unaddressed-epoch-record-request-is-charged-only-when-the-pool-had-room | security | the shed returns before `retrieve_epoch_record` runs, so the same `(None, None)` bytes cost a Medium penalty only when a slot was free, and are charged blind | `No_unaddressed_request_reject` |
| 85 | stream_slot_tenure | abandoned-admission-slot-released-without-peer-cooperation | liveness | the 15s cleanup tick evicts on `created_at` age alone, so a permit reserved at acceptance is freed with no peer action, and until the peer acts the responder cannot tell an abandoned reservation from a live one | `No_stale_prune` |
| 86 | stream_slot_tenure | re-request-never-extends-admission-slot-tenure | security | the replacement insert carries the original `created_at` forward, so a repeat RPC swaps the entry without restarting the 30s window | `Rearm_created_at`, `No_stale_prune` |
| 87 | stream_slot_tenure | admitted-stream-request-serves-at-most-once | safety | the stream-open lookup is `remove`, not `get`, so serve and removal are one event and a replay finds `None` and is charged Mild | `Non_consuming_open` |
| 88 | parent_claim_binding | vote-path-certificate-admission-is-bound-to-the-requested-author | security | the retain keeps a ride-along certificate only when `requested_parents` names this header's author, and it runs before any signature check, so a drop teaches the voter nothing | `No_requester_binding` |
| 89 | parent_claim_binding | a-missing-parent-is-claimed-by-exactly-one-proposer | liveness | the `Entry::Vacant` guard silently drops the digest from the later author's missing list, and the resulting blocking `notify_read` ends only at storage or a wall-clock teardown | `No_vacant_claim`, `No_evaluation_deadline` |
| 90 | parent_claim_binding | the-author-serves-only-its-own-declared-parents | security | the author intersects the requested digests with its own header's parents before `read_all`, and the count check turns an undeclared name into an aborted vote request | `No_author_parent_filter` |
| 91 | vote_cache_retry | empty-parent-retry-reissues-the-missing-parent-hint | liveness | the empty-parent arm writes the cache entry back verbatim and re-issues the same hint, so a hint lost to a certifier restart never becomes a fatal wrong-number-of-parents loop | `No_empty_parent_reissue` |
| 92 | vote_cache_retry | one-epoch-ahead-rejection-is-classified-recoverable | liveness | only `theirs == ours + 1` classifies recoverable, so the boundary race never freezes into the final-answer slot; the collapsed `RPCError` still hides which cause killed the task | `No_one_epoch_ahead_arm` |
| 93 | vote_cache_retry | per-author-vote-slot-isolates-committee-authors | fairness | the evaluation mutex is keyed by authority, so a blocking header holds only its own author's slot and a second author is answered while that evaluation still runs | `Single_shared_vote_lock` |
| 94 | worker_stream_quota | per-peer-stream-cap-reserves-capacity-for-every-peer | fairness | `peer_in_flight` sums pending, serving and sync slots for one identity, so both admitters refuse past the per-peer cap and draining the pool takes two distinct peers | `No_legacy_per_peer_cap`, `No_serving_guard` |
| 95 | worker_stream_quota | serving-legacy-stream-stays-charged-to-its-peer | security | the pending removal and the serving-guard increment happen under one lock, so a permit that outlives the pending entry is still charged to the peer holding it | `No_legacy_per_peer_cap`, `No_serving_guard` |
| 96 | worker_stream_quota | sync-shed-conceals-request-and-saturation | security | the shed writes `Deny(AtCapacity)` and closes before the request frame is read, so a denied requester knows its digest set was never decoded, and knows the pool is full only while under its own cap | `No_pre_read_sync_shed` |
| 97 | batch_quorum_tally | quorum-rejection-needs-two-committee-rejecters-one-known-honest | security | the budget `(available_stake + total_stake) - threshold` credits the author's own vote, so one refusal cannot trip the verdict and f = 1 leaves one of the two rejecters honest | `No_author_self_credit`, `No_recoverable_class`, `Truncated_fanout` |
| 98 | batch_quorum_tally | transient-store-fault-never-charges-the-rejection-budget | liveness | only an explicit permanent rejection raises `rejected_stake`; a failed batch-store write answers `RecoverableError` and is retried, lowering availability alone, and the author cannot tell it from fabrication | `No_recoverable_class` |
| 99 | batch_quorum_tally | every-committee-peer-is-offered-the-batch-at-equal-weight | fairness | the fan-out spawns one task per `others_keys_except` key with no await inside the loop, and every ack is worth one unit, so quorum needs two distinct peers | `Truncated_fanout` |
| 100 | output_forward_gate | live-forwarder-skips-stale-redelivery-so-no-output-executes-twice | safety | the `Stale` arm warns and continues before `process_output`, so a re-delivery never reaches the engine, whose whole state cannot see that the skip happened | `No_stale_arm` |
| 101 | output_forward_gate | lagged-output-gap-halts-the-epoch-instead-of-executing-a-hole | safety | the `Gap` arm returns `Err` before `close_epoch` and the leftover drain, so a lagged delivery either stays pending or is answered by that error, never executed over a hole | `No_gap_arm` |
| 102 | output_forward_gate | committed-outputs-execute-in-order-so-one-receipt-certifies-the-prefix | fairness | `pop_front` with one in-flight task serves the bounded backlog in commit order, so the manager's single execution receipt certifies everything it forwarded earlier | `Queue_pop_back` |
| 103 | pack_replay | published-consensus-result-implies-persisted-not-executed | security | `save_consensus` persists before the signature is gossiped, so a received `ConsensusResult` entails a pack entry, carries no execution evidence, and gives its publisher no delivery receipt | `No_save_before_publish` |
| 104 | pack_replay | persisted-unexecuted-output-is-inevitably-executed-after-restart | liveness | the restart scans execution tip to pack tip and re-forwards the gap through `process_output` before live consensus exists, consulting no peer | `No_replay_scan` |
| 105 | pack_replay | replayed-boundary-output-still-closes-the-epoch | liveness | `close_epoch` is never serialized, so the replay path restamps it in `process_output`, and that flag alone gates the `concludeEpoch` system call | `No_boundary_recompute` |
| 106 | gas_penalty_split | well-estimated-transaction-is-never-penalized-under-uniform-thresholds | fairness | gate one reads the declared limit alone, so the admission-time validator already knows a small-limit batch is exempt, and knows nothing past 210,000 | `No_small_limit_exemption` |
| 107 | gas_penalty_split | sstore-refund-never-enlarges-the-over-estimation-penalty | fairness | the penalty denominator is the pre-refund `gas.spent()`, not `gas.spent_sub_refunded()`, so an EVM refund cannot shrink the ratio into the penalty band | `Refund_aware_penalty` |
| 108 | gas_penalty_split | gas-charge-is-exactly-redistributed-never-burned | safety | the confiscated wei is credited to the governance sink rather than burned, and the quadratic's normaliser keeps the penalty within unused gas so `saturating_sub` never clamps | `Burn_the_penalty` |
| 109 | bls_verify_gate | every-verification-failure-mode-costs-the-same-and-returns-a-value | fairness | every admitted call exits through the one `Ok(PrecompileOutput)` at the flat 150k, so the charge separates no verdict; the pre-crypto `Err` rejects are excluded by the guard | `Err_on_failed_verify` |
| 110 | bls_verify_gate | compressed-encoding-is-the-only-accepted-point-form | safety | the 48/96 length test runs before the decoders, so blst cannot deserialize the uncompressed 96/192 form of one point pair into a second accepted encoding | `No_length_gate` |
| 111 | bls_verify_gate | accepted-pop-implies-known-key-possession-yet-exclusivity-unknown | security | the trailing pk-validation flag makes a true verdict entail possession by the signature's producer, while exclusivity of that key stays unknown to the executing node | `No_pk_validation` |
| 112 | close_block_syscall | epoch-transition-is-confined-to-and-published-by-the-marked-block | safety | one `if let Some(..) = self.ctx.close_epoch` guards the whole transition and the assembler writes that context into `extra_data`, so an unmarked header entails no epoch move | `No_close_marker_gate` |
| 113 | close_block_syscall | system-call-window-shuts-before-the-user-transactions-of-the-block | security | the three env swaps are restored before the block's user transactions run on the same EVM, so those still pay base fee and remain nonce-checked | `No_env_restore` |
| 114 | close_block_syscall | epoch-closing-calls-need-the-zeroed-base-fee-admission-window | liveness | the zero-priced system transaction is admitted only by the base-fee swap-in, and a refusing registry halts the block rather than skipping the close | `Nonzero_basefee_for_syscall` |
| 115 | tel_dispatch_surface | unimplemented-selectors-fail-closed-at-the-tel-dispatcher | security | the final match arm returns `Err` rather than an empty `Ok`, and the dispatcher cannot see whether its caller is a `DELEGATECALL` relay that swallows the flag | `Open_selector_fallthrough` |
| 116 | tel_dispatch_surface | short-calldata-guard-is-all-that-stands-between-a-three-byte-call-and-an-executor-panic | liveness | the explicit length check stands in front of the raw `input.data[0..4]` slice, so a 3-byte payload fails its own transaction and the block is still produced | `No_short_calldata_guard` |
| 117 | tel_dispatch_surface | precompile-state-is-address-pinned-under-delegatecall | safety | every `sload`/`sstore` names `TELCOIN_PRECOMPILE_ADDRESS` rather than the executing frame, so a moved supply entails a dispatched burn and does not reveal the call scheme | `Frame_scoped_storage` |
| 118 | fee_routing_sink | block-producer-take-is-tip-only-basefee-and-penalty-go-to-governance | security | the `saturating_sub(basefee)` at `evm/handler.rs:156` credits the producer only the tip, while the base-fee and penalty legs both `incr_balance` the sink | `Basefee_to_producer`, `Basefee_burned` |
| 119 | fee_routing_sink | block-beneficiary-is-the-certified-author-not-the-batch-self-declared-field | security | the payee is a committee lookup keyed by the certificate author, and a failed lookup aborts the output rather than falling back to `Batch.beneficiary` | `Beneficiary_from_batch_field` |
| 120 | fee_routing_sink | fee-sink-is-node-local-immutable-and-peer-opaque-until-tip-comparison | safety | the sink is a once-written `OnceLock` no message carries, so a peer's address stays unknown until the execution-tip comparison, where a match proves agreement without revealing provenance | `Mutable_fee_sink` |
| 121 | tel_supply_ledger | pending-mint-is-credited-at-most-once | safety | the claim credits the recipient and then zeroes the amount slot, so a second claim reloads zero and the indexer infers the disarm from the receipt | `No_pending_clear` |
| 122 | tel_supply_ledger | mint-target-is-pinned-to-governance | security | `mint` calldata supplies only an amount, the recipient being the hardcoded governance safe, so no foreign address's amount slot is ever armed | `No_recipient_pin` |
| 123 | tel_supply_ledger | burn-moves-both-ledger-cells-or-neither | safety | the balance debit precedes the slot-100 `checked_sub`, so only the journal revert keeps both cells in step, and the `Burn` log carries no resulting supply | `No_supply_guard` |
| 124 | batch_pack_share | gas-heavy-predecessor-starves-only-its-own-dependents | fairness | the over-budget arm ends in `continue`, not `break`, so a later sender still packs, while `mark_invalid` drops the skipped sender's own successors and the peer cannot tell | `Break_on_over_budget` |
| 125 | batch_pack_share | per-sender-slot-cap-bounds-a-share-and-makes-occupancy-peer-inferable | security | `max_account_slots = 256` is the only per-identity bound on the batch path, and it is the upper half of a peer's occupancy inference from the batch | `No_per_sender_slot_cap` |
| 126 | batch_pack_share | post-seal-nonce-hint-keeps-a-remainder-pending-without-knowing-it-can-pay | safety | the synthetic nonce advance keeps the remainder pending while its `balance: U256::MAX` leaves the worker unable to tell whether the sender can pay | `No_post_seal_nonce_hint` |
| 127 | tx_forward_route | sender-slot-owns-every-transaction-of-one-account | fairness | routing is a pure function of the sender modulo committee size, and the walked chain puts that slot first; an unadvertised owner is stepped over and the transaction still reaches the rest of the chain | `Round_robin_owner` |
| 128 | tx_forward_route | forward-budget-bounds-one-transaction | safety | the outer timeout wraps the chain inside the per-transaction loop, so 15s over 5s caps elapsed round trips at three and hands the next transaction a fresh budget | `No_forward_budget` |
| 129 | tx_forward_route | endpoint-local-non-verdict-is-neither-a-delivery-nor-an-end-of-chain | security | a transient code keeps the chain moving and an elapsed round trip never records a delivery, so the observer knows some validator holds it but not which | `No_transient_fallthrough`, `Timeout_counts_as_delivered` |
| 130 | cert_bitmap_quorum | direct-verification-implies-known-distinct-triple-signing | security | the bitmap resolves through a monotone cursor into pairwise-distinct keys, the threshold gate forces three of them, and the aggregate verifies against exactly those keys | `No_weight_threshold` |
| 131 | cert_bitmap_quorum | verified-bitmap-is-signature-bound-yet-omission-stays-hidden | security | the aggregate check runs against keys derived from the bitmap, so credited indices are authentic; votes after the first quorum are discarded, so omissions stay unknown | `Trust_supplied_signer_set` |
| 132 | cert_bitmap_quorum | round-zero-certificate-is-admitted-on-header-equality-alone | safety | the round-0 shortcut returns before the threshold and signature gates, and its equality compares only header digest, round, epoch and origin, never the bitmap or the signature | `No_genesis_header_equality` |
| 133 | boot_order | finalized-marker-heal-precedes-every-startup-state-rebuild | safety | the heal runs ahead of the accumulator restore, so the restore's finalized-header-pinned scan range covers the whole epoch instead of ending short | `No_marker_heal` |
| 134 | boot_order | recent-blocks-restore-precedes-the-replay-watermark | safety | the window is primed before the replay derives its watermark from it; on an empty window the default header collapses the watermark to 0 and re-executes | `No_recent_blocks_prime` |
| 135 | boot_order | swarm-listener-binds-exactly-once-even-when-startup-replays-and-closes | liveness | the gate ors `!self.network_initialized` onto `epoch_mode.initial_epoch()`, so a replay-and-close first iteration defers the bind instead of skipping or repeating it | `Initial_only_network_gate`, `Rebind_on_replay` |
| 136 | engine_queue | single-execution-slot-chains-each-output-onto-the-committed-head | safety | the `pending_task.is_none()` conjunct gates the spawn, so the release arm - the only writer of `parent_header` - runs before the next task clones it | `No_slot_exclusion` |
| 137 | engine_queue | engine-backlog-bound-backpressures-upstream-and-reopens | safety | the closed select arm leaves the awaited `to_engine` send blocked rather than buffering, and each slot release reopens the gate, modulo an absorbing engine stop | `No_queue_bound`, `Reexecute_head` |
| 138 | engine_queue | execution-slot-is-a-one-shot-grant-no-output-monopolises-it | fairness | `pop_front` grants by removing, so the backlog strictly shortens and the author-blind scheduler can never re-select the same output | `Reexecute_head` |
| 139 | batch_admit | gas-ceiling-refusal-is-a-committee-verdict-not-a-storage-fact | security | `max_batch_gas` discards its epoch argument, so one worker's local refusal is every honest worker's gated verdict, yet the digest-only prefetch leaves the peer's store unknown | `No_gas_ceiling` |
| 140 | batch_admit | blob-rejection-binds-the-validated-path-only | security | the 4844 check runs on the gated route only, so a blob batch still reaches a peer's cache by digest-only prefetch and no gossip carries the refusal | `No_blob_reject` |
| 141 | batch_admit | relay-keeps-the-author-digest-while-the-receipt-stamp-stays-private | safety | `received_at` is skipped by serialization, so a stamped copy still hashes to the author's digest and relays, while the stamp itself reaches no peer | `Digest_covers_received_at` |
| 142 | serve_slot_quota | record-admission-survives-a-saturated-stream-pool | fairness | `try_admit_epoch_record` reads only the record semaphore and counter, so an exhausted stream pool never fails the record admission, and being served reveals nothing about that pool | `Shared_permit_pool` |
| 143 | serve_slot_quota | stream-slots-are-capped-per-peer-across-both-admission-paths | safety | both stream gates sum legacy pending entries and sync streams before admitting, so no peer exceeds two slots and an exhausted pool needs two holders | `No_cross_path_count` |
| 144 | serve_slot_quota | a-capacity-denial-tells-a-slotless-requester-two-peers-are-served | security | the denial frame is delivered, and a per-peer cap strictly below the pool turns it into an aggregate the requester derives, never a per-peer distribution | `No_per_peer_stream_cap` |
| 145 | exec_absorb | cross-worker-duplicate-transaction-never-halts-execution | liveness | the `InvalidTx` arm logs and continues, so the duplicated transaction is dropped from the block and the node still commits | `Fatal_on_invalid_tx` |
| 146 | exec_absorb | certified-batch-decodes-because-validation-and-execution-share-one-recovery | liveness | worker validation and the executor's collect-or-abort recovery wrap the same reth helper, so consensus never delivers bytes the executor cannot decode | `No_validation_decode` |
| 147 | exec_absorb | block-level-failure-aborts-the-output-so-nodes-halt-rather-than-fork | safety | the fatal arm aborts before anything is persisted, so a full block entails no peer holds a truncated one, while peer progress stays unknown | `Commit_partial_block` |
| 148 | archive_pack_heal | append-open-repair-never-zero-extends-a-pack-whose-batch-index-survived | safety | the shrink-only clamp bounds the repair by the surviving data while the batch index tracks a real length; the dropped output's fate elsewhere stays unknown | `No_shrink_clamp` |
| 149 | archive_pack_heal | read-only-open-enforces-the-three-file-agreement-append-open-only-repairs | safety | `open_static` refuses unless the data length equals both digest indexes and the last position entry; the append repair reconciles only the two digest halves | `No_static_consistency_gate` |
| 150 | archive_pack_heal | published-pack-error-reveals-the-index-gap-not-whether-the-pack-fail-stopped | security | every failing save appends before it indexes, so a collected error entails data past the index; the erased error hides whether the latch fired | `No_write_failure_latch` |
| 151 | archive_digest_lookup | recheck-keeps-a-recycled-offset-from-voiding-the-whole-batch-exchange | liveness | the fetch rechecks the digest before the record leaves, so a recycled offset never turns one unrequested batch into a `ProtocolError` that discards the whole stream | `No_digest_recheck`, `No_bloom_accrue` |
| 152 | archive_digest_lookup | bloom-accrue-is-the-sole-writer-of-the-only-fast-path-negative | safety | `Index::save` sets the bloom bit above the bucket write and nothing clears it, so an indexed key is never short-circuited away by the fast-path negative | `No_bloom_accrue` |
| 153 | archive_digest_lookup | contains-is-an-index-and-bounds-fact-while-only-the-fetch-binds-the-payload | safety | the advertisement gates on `pos < self.data.file_len()` alone and never reads the data file, so only the fetch's recheck binds the answer to the payload | `No_digest_recheck`, `No_contains_bounds_check` |
| 154 | archive_epoch_import | an-epoch-pack-is-published-only-after-its-final-header-matches-the-certified-record | security | the rename runs only after the last streamed header equals the certified record; a stream stopping at the requested final says nothing beyond it | `No_final_header_link` |
| 155 | archive_epoch_import | an-already-held-epoch-is-never-unlinked-for-a-redundant-import | liveness | the already-held short circuit returns before the remove+rename, so a redundant import never opens the window in which readers take no lock | `No_already_held_shortcircuit` |
| 156 | archive_epoch_import | a-streamed-output-declares-its-batch-count-before-any-batch-is-buffered | security | the v1 header arrives first, so the declared digest count is capped before the batch loop inserts anything; the legacy v0 counter only trips after buffering | `No_batch_count_cap` |
| 157 | store_key_order | ordered-scan-lands-on-the-origins-greatest-stored-round | safety | big-endian fixint key encoding makes the byte-ordered walk stop on the origin's highest row, so a lower stored round is never reported over a higher one | `No_big_endian` |
| 158 | store_key_order | origin-guard-makes-the-round-answer-knowledge-of-the-named-authoritys-act | security | the `&name == origin` test admits only the origin's own row, which exists only because `save_cert` keyed it from that authority's certificate; `None` is not silence | `No_origin_guard` |
| 159 | store_key_order | origin-guard-keeps-the-ancestor-fetch-alive-for-a-silent-authority | liveness | with the guard a silent authority's probe answers `None` or a lower round and `unwrap_or(true)` fetches; suppression needs the origin's own stored row | `No_origin_guard` |
| 160 | store_full_memory | restart-preload-is-the-only-recovery-of-round-indexed-visibility | safety | `open_table`'s startup seed alone puts disk contents back on the mem-only index surface, so a post-restart index hit certifies durability to the local reader, not to a peer | `No_open_preload` |
| 161 | store_full_memory | full-memory-layer-is-never-evicted-so-index-and-point-reads-agree | safety | the writer thread gets no mem handle in full-memory mode, so nothing evicts the mirror and the mem-only answer never says absent where `get` says present | `No_full_memory_mode_test`, `No_open_preload` |
| 162 | store_full_memory | cache-iteration-chains-the-unflushed-layer-so-orphan-batches-are-never-lost | liveness | the layered `iter` chains the mem layer, so the boundary scan that clears the table in the same breath still sees a sealed-but-unflushed batch | `No_mem_chain_in_iter` |
| 163 | archive_hash_index | split-rotation-reaches-the-cold-bucket-independent-of-occupancy | fairness | the split target is `buckets() - old_modulus / 2` and the growth trigger reads aggregate `values` only, so being hot buys no extra split | `No_growth_gate` |
| 164 | archive_hash_index | bucket-cache-residency-is-capped-yet-one-hot-bucket-evicts-the-cold-one | fairness | `add_bucket_to_cache` evicts from the front before it inserts, and admits duplicates, so the cap is per insertion and a hot streak evicts the cold bucket | `No_cache_eviction_loop` |
| 165 | archive_hash_index | overflow-chain-decrease-guard-answers-a-corrupt-chain-instead-of-wedging | liveness | the strict-decrease test turns a self-linked overflow record into `Err(FetchError::CrcFailed)`, and neither the parked worker nor the index thread knows the chain is corrupt | `No_chain_decrease_guard` |
| 166 | backend_writer_thread | abandoned-write-txn-still-releases-the-overlapped-physical-commit | liveness | `Drop for TxnGuard` sends `EndTxn` for a transaction abandoned without commit, so the overlap count still drains to the `count <= 1` branch that commits | `No_end_txn_on_drop` |
| 167 | backend_writer_thread | orderly-shutdown-under-an-overlapped-txn-discards-a-barriered-write | safety | `Shutdown => break` exits the loop without `end_txn`, so the physical txn is dropped carrying a committed and barriered write whose author cannot tell either way | `No_shutdown_break` |
| 168 | backend_writer_thread | exported-open-txn-gauge-is-an-exact-census-of-live-logical-txns | security | every `StartTxn` increment is matched by one decrement, so a gauge of one entails a live logical txn and a gauge of zero certifies durability | `No_end_txn_on_drop` |
| 169 | backend_env_split | per-environment-writer-threads-decouple-commit-progress-and-knowledge | fairness | three environments carry three overlap counts, so neither workload's open txn defers the other's queued commit and neither client sees the other environment | `Merge_cache_into_epoch_env` |
| 170 | backend_env_split | table-hint-not-the-api-call-is-the-crash-atomicity-and-knowledge-boundary | safety | `CompositeDbTxMut::commit` is three sequential sends to three threads, so grouping is all-or-nothing within a hint and tears across hints, and the boundary route groups neither | `Merge_cache_into_epoch_env` |
| 171 | backend_env_split | redb-clear-recreates-the-cleared-table-inside-the-same-commit | safety | `delete_table` then `open_table` ride one `self.tx`, so a committed clear keeps the handle the boundary drain's `iter` and `is_empty` depend on | `No_redb_table_recreate` |
| 172 | store_notify_visibility | post-registration-reread-resolves-a-parent-wait-that-began-too-late | liveness | registration and the write share no lock, so the re-read after `register_one` is the only thing that turns a late registration into a resolution | `No_post_registration_reread`, `No_mem_write_on_insert` |
| 173 | store_notify_visibility | one-write-wakes-every-registered-parent-waiter | fairness | `notify` removes the whole registration list and fires every sender, and registration appends without priority, so no peer's vote request outranks another | `No_notify_fanout`, `No_post_registration_reread`, `No_mem_write_on_insert` |
| 174 | store_notify_visibility | certificate-is-store-visible-from-the-instant-its-write-notifies | safety | the notify fires inside `save_cert` before `txn.commit()`, and the mem-first insert with mem-first reads makes the store already answer; whether the answer is durable stays unknown | `No_mem_write_on_insert` |
| 175 | peer_prune_fairness | excess-prune-drops-the-lowest-scored-candidate-first | fairness | the candidate `filter_map` preserves the sorted order and the eviction loop is a plain walk over its output, so the dropped prefix is the lowest-scored one | `No_score_sort` |
| 176 | peer_prune_fairness | tied-candidates-share-the-single-eviction-slot | fairness | the shuffle runs before the stable sort, so tied peers keep the shuffle's residue as their order, and the excess countdown buys exactly one eviction | `No_tie_shuffle` |
| 177 | peer_prune_fairness | recognized-exemption-is-the-only-prune-carve-out | security | the validator and allowlist filter is the only way off the eviction list, so the excess is tolerated not resolved; an unidentified evictee's committee membership stays unknown | `No_validator_exemption`, `No_allowlist_exemption` |
| 178 | peer_temp_ban | temp-ban-exclusion-is-never-served-early | safety | the drain stops at the first entry whose stamp has not aged out, so readmission tells the excluded peer its duration ran or a forgive path fired | `No_expiry_guard`, `No_reinsert_refresh` |
| 179 | peer_temp_ban | temp-ban-exclusion-always-ends-at-a-heartbeat | liveness | the heartbeat's single drain call is the only enactor of expiry, and `contains` reads the map without consulting the clock | `No_heartbeat_drain`, `No_expiry_guard` |
| 180 | peer_temp_ban | temp-ban-reinsertion-restarts-the-uniform-clock | fairness | insert re-stamps a duplicate key and pushes it to the back, so the one duration runs from the last offence and a re-offender cannot jump the release queue | `No_reinsert_refresh`, `No_expiry_guard` |
| 181 | rpc_codec_size | oversize-rpc-charge-is-levied-under-peer-config-ignorance | security | the cap is per-node config, so the catch-all arm charges -5 on the same observation an honest 2 MiB peer produces, and the trust basis exempts committee peers | `No_inbound_catchall_penalty`, `No_trust_exemption` |
| 182 | rpc_codec_size | truncated-body-is-penalty-exempt-while-an-oversize-declaration-is-not | security | the truncation raises `UnexpectedEof`, an alternative of the exemption chain that fires before the trust basis, so griefing is free while `ErrorKind::Other` costs a scored peer -5 | `No_inbound_eof_exemption`, `No_inbound_catchall_penalty` |
| 183 | rpc_codec_size | compressed-body-accumulation-is-bounded-by-the-declared-uncompressed-length | safety | the compressed-length gate runs before the read loop starts, so an inflated declaration costs no buffer; the 8 KiB chunk bounds each read, not the total | `No_compressed_length_gate` |
| 184 | stream_inbound_quota | inbound-rate-window-charges-only-the-opening-peers-own-streams | fairness | the window is taken with `entry(peer)`, so only the opener's own opens drive its count past a bound that is uniform for every peer | `No_per_peer_keying` |
| 185 | stream_inbound_quota | inbound-quota-is-scoped-to-a-connection-episode-not-to-the-peer-identity | fairness | `on_disconnected` removes the whole window entry, so a redial restarts the count at zero and erases the evidence the responder would need to notice | `No_window_reset_on_disconnect` |
| 186 | stream_inbound_quota | a-silently-dropped-inbound-stream-hides-which-gate-killed-it | security | both the rate gate and the identity gate drop the `Stream` without writing a frame, and the one penalty classification is reported metrics-only; an answer proves resolution | `No_identity_guard` |
| 187 | stream_sync_capability | cached-unsyncable-verdict-is-bounded-knowledge-of-the-peers-non-answer | security | only `UpgradeFailed` becomes `Unsupported` while `UpgradeIo` caches `true`, so a `false` slot means non-answer or a post-negotiation cut, and stays silent on advertisement | `No_io_classification_split` |
| 188 | stream_sync_capability | only-a-full-pack-probe-writes-the-negative-capability-entry | safety | the `if last_consensus_number.is_none()` guard keeps a partial `Unsupported` from writing `false`, so a peer that cannot decode the partial variant stays probe-eligible | `No_partial_probe_guard` |
| 189 | stream_sync_capability | epoch-boundary-clear-restores-an-eligibility-the-excluded-peer-cannot-observe | fairness | the map has no TTL, so `clear_sync_capability` at each epoch start is the only route back to eligibility, and the excluded peer is never told | `No_epoch_clear` |

Per-statement grounding - the exact spans, the reading guide for each `K`
operand, the non-degeneracy witness, and what was deliberately not asserted -
lives in the doc comment above each statement in `lib/<family>_statements.ml`.
Those comments are the primary source; this table is an index to them.

## The presheaf-topos internal logic (`lib/internal/`)

`lib/internal/` is a second, independent foundation for the same checker: CTLK
refounded as the internal logic of a genuine presheaf topos. The normative spec
is `lib/internal/DESIGN.md`.

| module | role |
|---|---|
| `frame` | the base category `W = (reach, <=)` with `<=` the reversed reachability order, so presheaf restriction runs past to future and `Sub(1_E)` is the future-closed subsets |
| `sieve` | the subobject classifier `Omega` of `E = [W^op, Set]`, built by hand: `Omega(s)` is the set of sieves on `s`, the future-closed subsets of the cone above `s` |
| `sub` | `Sub(1_E)`, the Heyting algebra of future-closed subsets |
| `basechange` | base change along the transition span and along the view projections, in the Boolean base |
| `fix` | Knaster-Tarski fixpoints over the finite lattice `P(reach)` |
| `knows` | `K_i = f_i^* . Pi_{f_i}`, the lex-idempotent S5 comonad over the discrete base |
| `reflect` | the classical (not-not) reflection bridge from the intuitionistic `Omega` into the Boolean base |
| `denote` | the graded denotation of `Formula.t` and the kernel, exposing the same interface as `System.Make`, so a model re-points at it by changing one line |

Two toposes, one checker. `E = [W^op, Set]` is the intuitionistic home where
`AG` and all invariant content are native subobjects of `1_E`; persistence
points to the future, the opposite of the topos of trees, because the base is
states and invariants must persist forward. `B = Set^|R|` is the Boolean
(not-not) reflection over the discrete set of reachable states, and the whole
modal fragment - `AX`/`EX`/`AG`/`EG`/`AF`/`EF`/`AU`/`EU` and `K_i`/`E_G`/`C_G` -
is computed there. The split is forced rather than decorative: CTLK is a
classical logic, its existential path modalities and its cross-cutting `K_i` are
not intuitionistically internal to `E`, and knowledge in particular breaks
`E`-persistence.

**Every one of the 69 models runs on this layer.** Each `<family>_model.ml`
declares `module Checker = Denote.Make (State) (View)`, so all 189 statements
are proved through the topos denotation rather than through `System.Make`
directly. `System` is retained, and its role grew rather than shrank: it is now
the differential oracle against which each of the 69 denotations is checked.

**The correctness of this layer rests on an executable gate, not on assertion.**
The reduction theorem is

```
is_true (Denote.grade sys phi s) = State_set.mem s (System.sat oracle phi)
```

and it is checked per model, at every reachable state, for every subformula of
every statement and antecedent plus a battery spanning every `Formula.t`
constructor, under the pristine model and every one of its mutations.
`test/t_reduction.ml` is the hand-written instance for the shared model;
`test/topos_gate.ml` packages the same obligation as a functor and each of the
68 `test/t_<family>_topos.ml` suites instantiates it. A family's gate builds
both checkers itself from the raw spec fields, so it can never be handed a
system built by the checker it is auditing.

Generalising the layer from one model to 27, and later to 69, is what made the
gate bite. The
first build reflected only the antecedent of an implication, so `Denote` read
`p -> q` at a world as "if `p` here then `q` at every future world". That
coincides with the classical reading exactly when `q` denotes a future-closed
set. Every atom of the shared model is monotone, so the shared model could not
tell the difference and its gate was green over 141 worlds and seven mutants.
Four family models, whose atoms can go false again because a ban expires or a
pending map is released, exhibited concrete disagreeing worlds. The fix is to
reflect both arguments; `DESIGN.md` sec.4 carries the correction and the
provenance section records the lesson, which is that a differential gate is
only as strong as the diversity of models it runs on.

Three further gates back the reduction up:

| gate | what it establishes |
|---|---|
| `test/t_topos_frames.ml` | `Frame.certify_functorial` over all 69 models, classification pinned in both directions: 57 frames are posets, 12 are preorders because they model mechanisms that undo themselves - a ban expires, a serve pool is released, an admission slot is pruned and re-opened, a stream quota is returned. A preorder is still a thin category, so parallel arrows stay unique and the presheaf topos is intact; the reduction gate is green on all twelve. The test fails if any model changes class |
| `test/t_topos_laws.ml` | the Galois adjunctions, the `K_i` S5 comonad laws, `C_G` convergence, the `AX`/`EX` duality and the `Sub(1_E)` Heyting laws, run on all 69 REAL frames with witnesses drawn from each model's own statements, plus non-degeneracy counters so a frame on which the operators do nothing cannot buy a green verdict |
| `test/t_reflection.ml`, `test/t_categorical.ml` | the synthetic half: a frame with a genuinely sieve-graded `Ag p` (the classical reflection is a no-op on the shared model's seven statements, though it is load-bearing on the families), and each categorical law paired with a deliberately wrong operator that violates it |

## Confirm-by-mutation

A green suite is not evidence. A statement can be green because the mechanism
holds, or because the model never reaches the interesting state, or because a
conjunct quantifies over an empty set, or because the gate it names was never
load-bearing in the model to begin with. Nothing in a passing run distinguishes
these.

Each statement is therefore pinned by a model mutation that deletes exactly the
real code gate the claim rests on, and the pin must flip the proof to `Refuted`
- never to `Vacuous_antecedent`, which would mean the mutation merely broke
reachability. The per-family `test/t_<family>_mutation.ml` suites carry these,
189 gate deletions in all, and several statements additionally carry explicit
`survives_under` rows asserting that a sibling mutation leaves them proved, so
that a refutation is attributable to one gate rather than to general model
damage.

Two disciplines were applied when designing the mutations, both learned from
defects that shipped green in an earlier round:

- a deleted gate must not be silently repaired by a sibling path in the real
  Rust. Each family's build notes record the sweep of alternative write or
  verification paths that was done before the mutation was accepted;
- a positive `K` claim must be pinned by a mutation that changes what is known,
  not merely what is true.

## Provenance and the adversarial review

Every expansion round runs the same pipeline: a read-only multi-lens mining pass
over telcoin-network turns real code into candidate claims carrying the spans
they rest on, a selection stage keeps the ones that survive a grounding and an
encodability check, each family is designed and built independently and verified
green in a private copy of the repo, and only then is it merged. Being green is
never treated as the end of the process, because the defect classes that matter
here are precisely the ones a green suite cannot see.

**The second expansion (42 statements, 14 families).** Mined by a 12-lens
read-only pass over telcoin-network at `0c59c15b`, producing 79 candidates.
Forty-two were selected, three per family; the 37 unchosen candidates were
retained. The 42 then went through an adversarial faithfulness review - 14
per-family auditors plus 4 independent skeptics - aimed at seven defect classes
a green suite structurally cannot catch. It took two attempts: the first run
lost all 14 auditors to a session usage limit and returned an empty finding set,
a vacuous result that reads exactly like a clean review, and only the re-run
produced findings:

| class | defect |
|---|---|
| D1 | `K` operand over-claim (the operand is knower-local, or rigid) |
| D2 | manufactured refutation (the pin flips for an incidental reason) |
| D3 | counterfactual already repaired in the real code |
| D4 | wrong gate arithmetic |
| D5 | degenerate `K` over a singleton view class |
| D6 | vacuous omitted gate |
| D7 | hardwired assumption |

That review raised 37 findings: **15 confirmed, 16 downgraded, 6 refuted**. The
confirmed 15 spanned 10 of the 14 families, and were dominated by D7 (10 of 15),
with D6 twice and D2, D3 and one unclassified finding once each. All 15 were
repaired in a subsequent round by weakening or retargeting conjuncts,
re-anchoring pins to the gate actually being deleted, and enriching models with
the states a hardwired assumption had been standing in for. No statement was
dropped and the bucket distribution did not move; two statements were renamed to
match their weakened claims (`exex_life` S1 gained its
`-until-a-cert-verifies` qualifier, and `discovery` S2 became
`stale-replay-regression-is-gated-only-by-the-local-kad-store`). One pin was
re-anchored outright: `epoch_close` S2 now pins on `No_cert_digest_binding`
rather than the record-idempotence deletion it was originally written against.

The honest reading of that number is that a fully green, fully mutation-pinned
suite still contained 15 real faithfulness defects. The review reduced the
residual risk; it did not eliminate it.

**The third expansion (126 statements, 42 families).** Mined by 21 read-only
slices over the same commit, producing 335 candidate cards spanning 127 family
keys, 70 of which carried at least three cards. The pool's own buckets were
safety 113, security 87, fairness 69, liveness 66. One planned slice,
`liveness-lens`, died twice to a session usage limit and was abandoned rather
than retried, on the grounds that the slices that did run had already produced
66 liveness candidates. Selection was done by three agents on disjoint domains
and then re-checked mechanically rather than taken on their word: 42 unique
family keys, none clashing with an existing module, 126 unique statement names,
no collision with the existing 63, exactly three statements per family.

**Fairness stopped being the thin bucket, and how it did matters.** The shared
model and the first two expansion rounds produced 6 fairness statements between
them; this round took it to
29. Two things did it, and neither was padding. A dedicated cross-cutting
fairness lens was added to the mining pass and contributed 14 of the pool's 69
fairness candidates, against 3 in the entire previous round; the other 55 came
from the ordinary subsystem slices, which finally surfaced mechanisms that are
about allocation rather than validity: per-peer quotas under a global pool,
truncate-by-round collector discipline, fetch fan-out stagger with per-exchange
shuffle, per-author reward attribution at the subdag boundary. And claims were
re-bucketed in both directions where the first reading was wrong, including
moving `per-origin-round-weight-cap-is-exactly-one` out of fairness into safety
on the grounds that it prevents an equivocation-inflated quorum, which is an
invalid state rather than a monopoly. The recurring failure mode, worth stating
because it will recur, is that fairness-looking mechanisms are usually safety
gates that merely happen to treat peers equally.

**The third round's review found one defect, and its result is a lower bound
rather than a clean bill of health.** Thirty-eight agents ran with 0 errors and
all 14 finders returned, so this was not the failure mode that swallowed the
previous round's first review attempt. They raised 48 findings: 18 refuted,
5 downgraded, 1 confirmed, and **24 never adjudicated at all**, because the
verify stage caps at 24. Exactly half the raw findings therefore remain
unexamined, and a second review wave over them is owed.

The one confirmed defect is the class this review exists for: a statement true
only because its model omitted something the real code does, which no mutation
pin can catch. `parent_batch_forward` S3 asserted that a late origin, once in
`last_parents`, stays there until it reaches a header. The model's only
future-round transition was gated on a pending catch-up notice, while the real
code has an ungated path: the quorum-batch forward at
`aggregators/certificates.rs:24-44` is round-generic and runs for every accepted
certificate (`state_sync/cert_manager.rs:205-211`), so a future-round batch takes
the `Ordering::Greater` arm and executes `self.last_parents = parents`
(`proposer.rs:404-407`), a third writer that replaces the vector and drops the
straggler. The fix did not rig the model: an ungated `step_future_batch` was
added so the real drop is representable, the statement was renamed to
`late-origin-admissible-and-evicted-only-by-a-future-round-jump`, and the strong
reading is now asserted to be **refuted** on the pristine model so the weakening
cannot rot back into an unearned claim. What survives is the claim that a late
origin cannot be dropped while the proposer can still collect for that round.
The admissibility conjunct carrying the fairness content is untouched, so the
bucket and the 29 fairness total hold.

**Two qualifiers on all of the above.** First, "grounded against `0c59c15b`"
means grounded against that commit as it stood in a working tree that also
carried uncommitted local edits to `crates/config/src/consensus.rs`,
`crates/config/src/node.rs` and `crates/types/src/primary/mod.rs`, which authors
were instructed to read as they were. That is a state no reader can reproduce
from the hash alone. Second, statement names drift during authoring: 29 of the
42 families renamed statements relative to their selection plan, and the
structured self-reports give no hint of it because they list shipped names,
which look authoritative. Every rename that was checked was a refinement rather
than a substitution, confirmed by verifying that the family's mutation
constructors still match the planned mechanism.

Durable evidence for the second expansion - its candidate pool, selection,
reserve, per-family build reports and full review verdicts - lives in
`~/Documents/telcoin-epistemic-expand-63/` (`STATUS.md`, `CONTRACT.md`,
`pool.json`, `selection.json`, `reserve.json`, `build-report.json`,
`review-findings.json`, `review-verdicts-full.json`). The third expansion is
only partially preserved, in `~/Documents/telcoin-epistemic-expand-189/`
(`STATUS.md`, `CONTRACT.md`, `digest.tsv`, `selection-*.json`, `reserve-*.json`,
`manifest-families.json`): that round's per-family build reports and its 48
review findings were never written to disk, so the 24 unadjudicated findings
survive only as a count in `STATUS.md`, and a second review wave would have to
re-derive them from scratch. Those reports were written before their repair
rounds, so where one disagrees with the source tree on a statement name, a pin
or a reachable-state count, the source tree is authoritative.

## Build and test

Dependencies: OCaml >= 5.1 (the pinned switch is 5.3.0), dune, alcotest, and
`comp_cat`. `comp_cat` is not on opam; it is pinned into the switch from a local
[comp-cat-ocaml](https://github.com/MavenRain/comp-cat-ocaml) checkout.

```sh
eval $(opam env --switch=telcoin-epistemic-ocaml --set-switch)
dune build && dune test
```

or, without switching the ambient environment:

```sh
export PATH="$HOME/.opam/telcoin-epistemic-ocaml/bin:$PATH"
dune build && dune test
```

Dune caches test results, so use `dune test --force` to see every case run. The
current tree builds with 0 errors and 0 warnings, and runs 217 test executables
with 0 failures: 2435 cases across the 215 fast executables, plus 71 cases in
`t_topos_laws` and 7 in `t_reduction`:

| suites | what they cover |
|---|---|
| `t_formula`, `t_kernel`, `t_knowledge` | temporal semantics on toy graphs and knowledge under hidden state, each positive row paired with a negative row (including the muddy-children announcement pair) |
| `t_reduction`, `t_reflection`, `t_categorical` | gates 2-4 of the seven-gate test oracle in `DESIGN.md` sec.6; gate 1, the statements gate, is `t_statements` |
| `t_tn_model`, `t_statements`, `t_tn_mutation` | the shared model, its seven proofs, and its seven pins over six mutations (`Drop_batch_gate` pins two statements) |
| `t_<family>`, `t_<family>_mutation` (68 pairs) | each family's proofs, reachable-set bands and exact counts, plus its pins |
| `t_<family>_topos` (68) | gate 5: per family, the `Denote` against `System` differential at every reachable world under every mutation, the poset certificate on the 56 poset families (the other 12 pin the opposite case, a `preorder-not-poset` assertion that the certificate fails), and the reflection non-vacuity witness |
| `t_topos_frames`, `t_topos_laws` | gates 6 and 7: the frame classification pinned across all 69 models, and the categorical laws run on all 69 real frames with non-degeneracy counters |
| `t_all_statements` | the meta-suite: exactly 189 statements, all proved, names unique, bucket distribution `[59; 63; 38; 29]` |
| `t_probe` | an ad-hoc satisfiability probe kept for model exploration |

Two suites are slow and dominate a full run: `t_reduction` (the shared model's
141 worlds against 259 formulas over seven mutants) takes tens of minutes, and
`t_topos_laws`, which now runs the categorical laws on 69 real frames, took 601
seconds on the reference machine. The 68 per-family topos gates are each under a
tenth of a second, because family frames are small by design.

## Limits and scope

Read this section before quoting anything above.

- **The models are not the system.** Every proof is a statement about a finite
  abstraction - ten validators (f = 3) in the shared model, while each family
  model fixes its own committee: twenty-three keep a four-member one with
  f = 1, four more are stated against the ten-member committee, and the
  remaining forty-one model a mechanism with no committee in it at all, over whatever module-local roster it does
  need (two peer classes, three pack indexes, five peers, ten), a handful of
  rounds, one epoch boundary, one batch, one certificate - not about
  telcoin-network. A proof means the
  modelled mechanism has the stated epistemic property in the modelled runs. It
  says nothing about code paths that were not modelled, and nothing about the
  gap between the model and the code beyond what the cited spans and the
  adversarial review establish.
- **Liveness is relative to baked-in fairness.** The transition relation is
  stutter-closed to make `AF`/`AU` total, so a liveness verdict encodes exactly
  the fairness the model builder wrote into `next`: bounded delivery delay in
  the shared model, a resolving branch in a family model. Change the fairness
  assumption and the liveness statements change with it. Safety and security
  statements hold over all interleavings the model admits, including every
  Byzantine choice it admits.
- **Everything is pinned to a commit, but not only to a commit.** The claims are
  about the mechanism as it stood in the authoring working tree at
  telcoin-network `0c59c15b`, which also carried uncommitted local edits to three
  config and types files (see Provenance), so the hash alone does not reproduce
  that state. Line anchors drift, and gates get moved,
  strengthened or deleted. A statement here is not a standing guarantee about
  the current `main`.
- **Isolation cuts both ways.** Because families are separate models, nothing
  proved here constrains the interaction of two families. An attack that
  composes, say, the discovery surface with the epoch sync loop is out of scope
  by construction, not by having been checked and excluded.
- **No cryptography is modelled.** Certificates, signatures and digests are
  unforgeable by construction: a certificate value exists only where the model
  assembled a quorum. Nothing here bears on the strength of BLS aggregation,
  hash binding or the signing scheme.
- **Knowledge is modelled knowledge.** `K_i` quantifies over the view the model
  gives validator i. Where a node physically holds bytes that would answer a
  question but has not yet run the check, the family modules deliberately do not
  assert ignorance - that would be computation-order ignorance rather than
  partial information - and they say so.
- **A mutation pin is evidence about the model.** It shows the gate is
  load-bearing for the statement in the model, and the sibling-repair sweeps
  argue that no other real code path repairs the deletion. It is not a proof
  that the real system has no such path.
- **The topos layer covers every model, but the gate is not exhaustive.** All 69
  checkers are `Denote.Make`, and each is differentially checked against
  `System` over its own statements plus a constructor-spanning battery, at every
  reachable world, under every mutation. That is a large and diverse sample of
  formulas, not a proof for all formulas: the gate compares the two checkers on
  the formulas it is given. It found a real divergence once, which is the reason
  to state its limits plainly rather than to treat green as equivalence.
- **Small state spaces.** Reachable sets run from 5 to 141 states. That is what
  makes exact checking and hand-reading possible, and it is also the reason no
  claim here scales to real committee sizes, long epoch sequences or realistic
  message multiplicities.

## License

MIT OR Apache-2.0.
