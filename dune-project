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
  "Sixty-three temporal-epistemic (CTLK) statements about telcoin-network, proved on 27 finite interpreted-system models")
 (description
  "Sixty-three security / safety / liveness / fairness statements (23 / 20 / 14 / 6) about the telcoin-network DAG-BFT protocol (Narwhal/Bullshark-derived: worker batches, primary headers, 2f+1 certificates, leader commit rule, deterministic execution, epoch records, and the execution/ExEx and libp2p layers), each encoded in a temporal epistemic logic (CTLK over Fagin-Halpern-Moses-Vardi interpreted systems: branching temporal operators plus K_i grounded in per-validator local-state indistinguishability) and proved by an LCF-style kernel over an exact finite-state model checker, which lib/internal refounds as the internal logic of a presheaf topos: E = [W^op, Set] over the reachability poset with persistence pointing to the future, its Boolean not-not reflection B in which the whole modal fragment computes, and K_i as the lex idempotent S5 comonad f_i^* . Pi_{f_i} over the discrete base, with an executable differential gate pinning is_true (grade phi s) = (s in sat phi) over every subformula, every world and pristine plus six mutants. Seven statements live on a shared 4-validator, f=1 abstraction with genuine Byzantine branching (equivocation, vote withholding) and partial observability (each validator sees only its own DAG view, votes, batches and committed prefix); a first expansion adds fourteen statements over twelve lean isolated family models and a second adds forty-two over fourteen more, each family carrying its own model of 5 to 52 reachable states, because knowledge quantifies over sets of runs and one monolithic model would cross-perturb the families. Liveness statements hold under bounded-delay fairness baked into the models; safety and security statements hold over all interleavings including Byzantine choices. Every statement is proved through prove_nonvacuous, which refuses an unreachable antecedent, and pinned by confirm-by-mutation: a mutated model with exactly one real code gate deleted flips the proof to refuted. The fairness bucket is small by supply rather than by choice, and the honest caveat is that only three of the seventy-nine mined candidates were fairness claims and all three were taken.")
 (depends
  (ocaml
   (>= 5.1))
  dune
  alcotest
  comp_cat))
