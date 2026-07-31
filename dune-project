(lang dune 3.0)
(name telcoin_epistemic)
(generate_opam_files true)

(license "MIT OR Apache-2.0")
(authors "Onyeka (Oni/MavenRain) Obi")
(maintainers "Onyeka (Oni/MavenRain) Obi")
(source
 (github MavenRain/telcoin-epistemic-ocaml))

(package
 (name telcoin_epistemic)
 (allow_empty)
 (synopsis
  "One hundred and eighty-nine temporal-epistemic (CTLK) statements about telcoin-network, proved on 69 finite interpreted-system models")
 (description
  "One hundred and eighty-nine security / safety / liveness / fairness statements (59 / 63 / 38 / 29) about the telcoin-network DAG-BFT protocol (Narwhal/Bullshark-derived: worker batches, primary headers, 2f+1 certificates, leader commit rule, deterministic execution, epoch records, and the execution/ExEx and libp2p layers), each encoded in a temporal epistemic logic (CTLK over Fagin-Halpern-Moses-Vardi interpreted systems: branching temporal operators plus K_i grounded in per-validator local-state indistinguishability) and proved by an LCF-style kernel over an exact finite-state model checker, which lib/internal refounds as the internal logic of a presheaf topos: E = [W^op, Set] over the finite reachability preorder with persistence pointing to the future, its Boolean not-not reflection B in which the whole modal fragment computes, and K_i as the lex idempotent S5 comonad f_i^* . Pi_{f_i} over the discrete base, with an executable differential gate pinning is_true (grade phi s) = (s in sat phi) over every subformula, every world and every mutant, run for all sixty-nine models and not only the shared one. Fifty-seven of the sixty-nine frames certify as posets and twelve are only preorders, because they model mechanisms that undo themselves (a ban expires, a serve pool releases, a vote slot is returned, a capability cache is cleared at the epoch boundary), which costs the denotation nothing: a preorder is still a thin category, so presheaf restriction stays path-independent and antisymmetry would buy only skeletality. Seven statements live on a shared 10-validator, f=3 abstraction with genuine Byzantine branching (a three-member coalition that equivocates and withholds votes) and partial observability (each validator sees only its own DAG view, votes, batches and committed prefix); a first expansion adds fourteen statements over twelve lean isolated family models, a second adds forty-two over fourteen more, and a third adds one hundred and twenty-six over forty-two more, each family carrying its own model of 5 to 64 reachable states, because knowledge quantifies over sets of runs and one monolithic model would cross-perturb the families. Liveness statements hold under bounded-delay fairness baked into the models; safety and security statements hold over all interleavings including Byzantine choices. Every statement is proved through prove_nonvacuous, which refuses an unreachable antecedent, and pinned by confirm-by-mutation: a mutated model with exactly one real code gate deleted flips the proof to refuted, one hundred and eighty-nine such gate deletions in all, a few of them load-bearing for more than one statement. Fairness is no longer the thin bucket it was: the shared model and the first two expansions carried only six fairness claims between them, because mechanisms that look like fairness kept resolving into safety gates that merely happen to treat peers equally, and a dedicated cross-cutting fairness lens in the third round, together with honest re-bucketing in both directions, carried the bucket from six to twenty-nine. The honest caveat is now about what fairness means here rather than how little of it there is: a per-claimant cap on a shared pool, a grant that cannot be held, uniform cost across the outcomes an adversary chooses between, and reach that does not depend on load, each proved on a finite model, and none of them an economic or long-run fairness notion.")
 (depends
  (ocaml
   (>= 5.1))
  dune
  alcotest
  comp_cat))
