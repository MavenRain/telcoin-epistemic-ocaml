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
  "Temporal-epistemic (CTLK) statements about telcoin-network, proved on a finite interpreted-system model")
 (description
  "Seven security / liveness / fairness / safety statements about the telcoin-network DAG-BFT protocol (Narwhal/Bullshark-derived: worker batches, primary headers, 2f+1 certificates, leader commit rule, deterministic execution), each encoded in a temporal epistemic logic (CTLK over Fagin-Halpern-Moses-Vardi interpreted systems: branching temporal operators plus K_i grounded in per-validator local-state indistinguishability) and proved by an LCF-style kernel wrapping an exact finite-state model checker. The model is a 4-validator, f=1 abstraction with genuine Byzantine branching (equivocation, vote withholding) and partial observability (each validator sees only its own DAG view, votes, batches and committed prefix). Liveness statements hold under bounded-delay fairness baked into the model; safety and security statements hold over all interleavings including Byzantine choices. Every statement is pinned by confirm-by-mutation negative tests: a mutated model (gate deleted) flips the proof to refuted.")
 (depends
  (ocaml
   (>= 5.1))
  dune
  alcotest
  comp_cat))
