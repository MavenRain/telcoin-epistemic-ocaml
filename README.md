# telcoin-epistemic-ocaml

Seven security / liveness / fairness / safety statements about the
[telcoin-network](https://github.com/Telcoin-Association/telcoin-network)
DAG-BFT protocol, each encoded in a temporal epistemic logic and proved by an
LCF-style kernel wrapping an exact finite-state model checker.

The statements were mined from the telcoin-network sources and adversarially
verified twice before encoding: once against the code (does the cited
mechanism really enforce the claim, including restarts, GC, and Byzantine
peers?) and once against the finite-model semantics (is each knowledge
operator grounded in state the validator actually holds, and non-vacuous
under the model's observability?). Six of seven were weakened by that review
into the forms proved here; the availability statement survived as mined.

## The logic

CTLK over Fagin-Halpern-Moses-Vardi interpreted systems: branching temporal
operators (`AG`/`AF`/`AX`/`AU` and existential duals) plus knowledge
operators - `K_i phi` ("validator i knows phi") holds when `phi` is true at
every reachable global state whose projection onto i's local state matches,
`E_G` (everyone knows), `C_G` (common knowledge, a greatest fixpoint).
Knowledge is grounded: a validator's view is exactly its DAG, batch store,
vote log, and committed set - never other validators' stores, in-flight
messages, or the adversary's private branch.

`Theorem.t` is the kernel boundary (`lib/system.ml`): the only constructors
are `prove` and `prove_nonvacuous`, so possessing a theorem value is
possession of a checked proof. `prove_nonvacuous` additionally refuses any
implication whose antecedent is unreachable, so no statement is certified
vacuously.

## The model

A 4-validator, f = 1 abstraction of one Narwhal/Bullshark anchor window
(`lib/tn_state.ml`, `lib/tn_model.ml`): three rounds of propose → vote
(batch-availability gated, vote-once per slot, synchronizer fetch on vote) →
certify (2f+1) → deliver, then the f+1-support commit rule evaluated by each
validator on its own DAG, deterministic execution, terminal stutter.
Genuine branching: the Byzantine validator picks cooperate / starve-batch /
equivocate / silent, the honest leader may crash before proposing its anchor
(the cert-free witness that keeps "knowing a certificate formed" contingent),
and delivery of the anchor to one validator may be delayed a round (bounded
delay - the fairness assumption liveness verdicts are relative to).
Certificates are unforgeable by construction: a certificate value exists only
when the model has assembled quorum votes.

Facts the protocol makes inevitable are knowable by inference (FHMV implicit
knowledge), so the strictly epistemic content lives over contingent hidden
facts: the Byzantine branch (S3), other validators' possession inside the
delay window (S5), the availability quorum behind a certificate (S1, S7).
The delay window is real: `EF (v1 holds the anchor and v0 does not know it)`
is satisfiable, and after re-sync the mutual knowledge - in fact common
knowledge - of possession is restored (`test/t_tn_model.ml` probes both).

## The seven statements (`lib/statements.ml`)

| # | statement | bucket | telcoin mechanism |
|---|-----------|--------|-------------------|
| 1 | stored-cert-implies-known-quorum-and-slot-uniqueness | security | BLS aggregate verification `certificate.rs:225-251`, `is_verified` gate `cert_manager.rs:88-93`, equivocation rejection `state.rs:145-157` |
| 2 | vote-attests-known-parents-and-payload | security | vote_inner parent checks `handler.rs:693-738`, batch sync-before-vote `header_validator.rs:98-154` |
| 3 | no-conflicting-revote-and-equivocation-detectability | safety | vote-once / AlreadyVoted `handler.rs:787-847`; equivocation knowable exactly through local conflicting evidence |
| 4 | commit-implies-known-support-quorum | safety | Bullshark f+1 support count on own DAG `bullshark.rs:192-206`, `committee.rs:254-259` |
| 5 | rounds-advance-under-known-distinct-quorum | liveness | enough_parents gate `proposer.rs:546-553`, authorities_seen dedup `certificates.rs:82-99`, state-sync propagation |
| 6 | round-robin-leader-common-knowledge-and-slot-fairness | fairness | deterministic next_leader `leader_schedule.rs:285-304`; causal-closure inclusion (no honest certificate censored) |
| 7 | quorum-ack-implies-honest-batch-availability | security | ack-after-validate-and-store `handler.rs:231-263`, `validator.rs:39-81`, `quorum_waiter.rs:163-190` |

Statement 1's detect-and-halt branch for a delivered conflicting certificate
needs two Byzantine validators and is documented as out of scope at f = 1
(quorum intersection makes the pair unreachable, which is itself the proved
uniqueness invariant). Statement 6's common-knowledge conjunct is knowledge
by shared-config admissibility: every reachable world derives the same
anchor slot, and the perturbed-committee mutation is what would break it.

## Confirm-by-mutation

Every statement is pinned by a model mutation deleting exactly the gate it
depends on (`test/t_tn_mutation.ml`): weak quorum → S1, dropped batch gate →
S2/S7, dropped vote-once → S3, dropped support check → S4, unbounded delay
(delivery and synchronizer fetch both removed) → S5, leader censorship → S6.
Each flips its statement to refuted while the pristine model proves all
seven - no statement is green for lack of teeth.

## Build

```sh
eval $(opam env --switch=telcoin-epistemic-ocaml --set-switch)
dune build && dune test
```

62 tests: kernel temporal/knowledge semantics (muddy-children announcement
pair, livelock honesty, vacuity guard), model sanity, the seven proofs, and
the mutation pins.

## License

MIT OR Apache-2.0.
