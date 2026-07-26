# telcoin-epistemic-ocaml

Sixty-three security / safety / liveness / fairness statements about the
[telcoin-network](https://github.com/Telcoin-Association/telcoin-network)
DAG-BFT protocol, each encoded in a temporal epistemic logic and proved by an
LCF-style kernel wrapping an exact finite-state model checker. What a reader
gets is a machine-checked catalogue of what a telcoin validator **knows** at
each point of a protocol run - not merely what is true, but what is entailed by
the state that validator actually holds - together with 27 executable finite
models of named telcoin subsystems, a negative test per statement that deletes
the exact code gate the claim rests on, and a second, independent foundation of
the checker itself as the internal logic of a presheaf topos.

| | |
|---|---|
| statements | 63 - security 23, safety 20, liveness 14, fairness 6 (pinned in `test/t_all_statements.ml`) |
| models | 27 - one shared `Tn_model` plus 26 isolated family models |
| mutation pins | 61 gate deletions across the 27 models |
| tests | 63 test executables, 584 cases, 0 failures; `dune build` clean, 0 warnings |
| grounded against | telcoin-network at git `0c59c15b` |
| license | MIT OR Apache-2.0 |

## Layout

| path | contents |
|---|---|
| `lib/formula.ml{,i}` | the CTLK syntax: atoms are a caller-supplied sum type, so each statement module matches exhaustively over its own vocabulary |
| `lib/system.ml{,i}` | interpreted systems, the exact checker, and the `Theorem.thm` kernel boundary |
| `lib/tn_state.ml`, `lib/tn_model.ml`, `lib/statements.ml` | the original shared model and its seven statements |
| `lib/<family>_model.ml`, `lib/<family>_statements.ml` | 26 isolated family models and the 56 statements over them |
| `lib/all_statements.ml`, `lib/report.ml` | the flat 63-row cross-model report (theorems over different state types cannot share a list) |
| `lib/internal/` | the CTLK checker refounded as the internal logic of a presheaf topos, plus `DESIGN.md`, the normative spec |
| `test/` | kernel semantics, per-family suites, per-family mutation suites, the topos gates |

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

Every one of the 63 statements is proved through `prove_nonvacuous`, never
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
is its own `System.Make (State) (View)` instance with its own state type, its
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
| `tn_model` | one Narwhal/Bullshark anchor window, 4 validators, f = 1, 3 rounds: propose -> vote -> certify at 2f+1 -> deliver -> f+1-support commit -> deterministic execution | 141 | `Drop_batch_gate`, `Weak_quorum`, `No_support_check`, `Unbounded_delay`, `Leader_censors_v2`, `No_vote_once` |

### Generation 2 - twelve isolated families

| model | telcoin subsystem | states | mutations |
|---|---|---|---|
| `ban_model` | libp2p peer scoring: fatal content-fault charge routing and the committee `TrustBasis` exemption (`peers/peer.rs:209-237`, `peers/manager.rs:424-443`) | 11 | `Charge_relayer`, `No_exemption` |
| `admission_model` | peer-manager admission: three independent directed ban pairs, temp-ban cache, ban-gated dial retry (`peers/manager.rs:396-403`, `peers/behavior.rs:102-105`) | 27 | `No_admission_denial` |
| `gossip_auth_model` | authenticated publishing on the certificate gossip topic (`primary/src/network/mod.rs:423-428`, `verify_gossip` at `network-libp2p/src/consensus.rs:1491-1514`) | 25 | `Drop_publisher_auth` |
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
| `denote` | the graded denotation of `Formula.t` and the kernel, exposing the same interface as `System.Make` |

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

`Tn_model.Checker` is `Denote.Make (Tn_state) (Tn_state.Local)`
(`lib/tn_model.ml:533`), so the original seven statements are proved through the
topos denotation. The 26 family models remain on `System.Make`, which is also
retained as the differential oracle.

**The correctness of this layer rests on an executable gate, not on assertion.**
The reduction theorem is

```
is_true (Denote.grade sys phi s) = State_set.mem s (System.sat oracle phi)
```

and `test/t_reduction.ml` checks exactly that, at every reachable state, for
every subformula of all seven statements and their antecedents plus a hand
battery spanning every `Formula.t` constructor, over the pristine model and all
six mutants. The pen-and-paper argument in `DESIGN.md` sec.4 is not treated as
sufficient: the executable gate is what actually catches a wrong persistence
direction or a mis-seeded fixpoint. Two further gates back it up:
`test/t_reflection.ml` supplies a synthetic frame with a genuinely sieve-graded
`Ag p`, because the classical reflection is a no-op on the seven statements and
would otherwise be green by vacuity; `test/t_categorical.ml` asserts the
categorical laws positively and pairs each with a deliberately wrong operator
that violates the same law.

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
61 gate deletions in all, and several statements additionally carry explicit
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

The 42 second-expansion statements were mined by a 12-lens read-only pass over
telcoin-network at `0c59c15b`, producing 79 candidates. Forty-two were selected,
three per family; the 37 unchosen candidates were retained. Each family was then
designed and built independently, verified green in a private copy of the repo,
and only then merged.

Being green was not treated as the end of the process. The 42 went through an
adversarial faithfulness review - 14 per-family auditors plus 4 independent
skeptics - aimed at seven defect classes a green suite structurally cannot
catch:

| class | defect |
|---|---|
| D1 | `K` operand over-claim (the operand is knower-local, or rigid) |
| D2 | manufactured refutation (the pin flips for an incidental reason) |
| D3 | counterfactual already repaired in the real code |
| D4 | wrong gate arithmetic |
| D5 | degenerate `K` over a singleton view class |
| D6 | vacuous omitted gate |
| D7 | hardwired assumption |

The review raised 37 findings: **15 confirmed, 16 downgraded, 6 refuted**. The
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

**The fairness ceiling.** Only 3 of the 79 mined candidates were fairness
claims, and the selection took all three. The 6-of-63 fairness figure is
therefore the ceiling of this mining pass, not the result of a preference for
the other buckets, and it was not padded out.

Durable evidence for all of this - the candidate pool, the selection, the
reserve, the per-family build report and the full review verdicts - lives in
`~/Documents/telcoin-epistemic-expand-63/` (`STATUS.md`, `CONTRACT.md`,
`pool.json`, `selection.json`, `reserve.json`, `build-report.json`,
`review-verdicts-full.json`). Note that `build-report.json` was written before
the repair round, so where it disagrees with the source tree on a statement
name, a pin or a reachable-state count, the source tree is authoritative.

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
current tree builds with 0 errors and 0 warnings, and runs 63 test executables /
584 cases with 0 failures:

| suites | what they cover |
|---|---|
| `t_formula`, `t_kernel`, `t_knowledge` | temporal semantics on toy graphs and knowledge under hidden state, each positive row paired with a negative row (including the muddy-children announcement pair) |
| `t_reduction`, `t_reflection`, `t_categorical` | gates 2-4 of the four-gate test oracle in `DESIGN.md` sec.6; gate 1, the statements gate, is `t_statements` |
| `t_tn_model`, `t_statements`, `t_tn_mutation` | the shared model, its seven proofs, and its seven pins over six mutations (`Drop_batch_gate` pins two statements) |
| `t_<family>`, `t_<family>_mutation` (26 pairs) | each family's proofs, reachable-set bands and exact counts, plus its pins |
| `t_all_statements` | the meta-suite: exactly 63 statements, all proved, names unique, bucket distribution `[23; 20; 14; 6]` |
| `t_probe` | an ad-hoc satisfiability probe kept for model exploration |

## Limits and scope

Read this section before quoting anything above.

- **The models are not the system.** Every proof is a statement about a finite
  abstraction - 4 validators, f = 1, a handful of rounds, one epoch boundary,
  one batch, one certificate - not about telcoin-network. A proof means the
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
- **Everything is pinned to a commit.** The claims are about the mechanism as it
  stood at telcoin-network `0c59c15b`. Line anchors drift, and gates get moved,
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
- **The topos layer covers one model.** The reduction gate compares `Denote`
  against `System` over the shared model's formulas and mutants. The 26 family
  models run on `System.Make` directly.
- **Small state spaces.** Reachable sets run from 5 to 141 states. That is what
  makes exact checking and hand-reading possible, and it is also the reason no
  claim here scales to real committee sizes, long epoch sequences or realistic
  message multiplicities.

## License

MIT OR Apache-2.0.
