# CTLK as the internal logic of a presheaf topos

**Normative build spec (v1.0)** for the `lib/internal/` refactor of
`telcoin-epistemic-ocaml`. It refounds the CTLK model checker (`lib/system.ml`)
as the internal logic of a genuine presheaf topos, leveraging
`comp-cat-ocaml`, exactly mirroring how `comp-cat-ocaml/lib/temporal/DESIGN.md`
refounded Lamport TLA as the internal logic of the topos of trees.

Repo: `~/Documents/telcoin-epistemic-ocaml`; own opam switch
`telcoin-epistemic-ocaml` (OCaml 5.3.0, dune, alcotest). Build with
`dunecho build` / `dunecho test`. License dual MIT OR Apache (inherit).

This spec is the OUTPUT of an 8-agent adversarial design workshop (2 independent
reviewers on the two riskiest pillars). Every claim below survived a refutation
pass; the `## Provenance` at the end records what the workshop corrected.

---

## 0. What we build and why (read before coding)

The current checker (`system.ml`) already computes, without saying so, in the
internal logic of a topos: `sat` maps each `Formula.t` to a `State_set.t` (a
subobject of the reachable-state object), boolean connectives are subobject-
lattice ops, `K_i` is base change along the view projection, `AX`/`EX` are base
change along the transition span, and `AG`/`AF`/`C_G` are μ/ν fixpoints
(`system.ml:98-136`). We make that structure the DEFINITION.

### 0.1 The four load-bearing facts

1. **Two toposes, one checker.** The refoundation lives in two related toposes:
   - **`E = [W^op, Set]`**, the genuine *intuitionistic* presheaf topos over the
     reachability poset `W` (§1). This is the "internal logic of a topos" home.
     `AG` and all invariant content are NATIVE subobjects of `1_E` here.
   - **`B = Set^{|R|} = [R_disc^op, Set]`**, the *Boolean* topos over the
     discrete set of reachable states (`Sub(1_B) = P(reach)`, `Ω_B = 2`). The
     full modal fragment (temporal `AX/EX/AG/EG/AF/EF/AU/EU` AND epistemic
     `K_i/E_G/C_G`) is computed here (§2, §3). `B` is the classical (¬¬-)
     reflection of `E`; the passage `E → B` is the classical-reflection bridge.

   This split is forced, not cosmetic: CTLK is a *classical* logic; its
   existential-path modalities (`EX/EF/EG`) and its cross-cutting epistemic `K_i`
   are NOT intuitionistically internal to `E` (workshop P2/P3, both P3 reviewers
   independently). Knowledge in particular breaks `E`-persistence (§3.5c).

2. **Persistence points to the FUTURE** (opposite of the topos of trees).
   `W = (reach, ⊑)` with `⊑ =` reversed reachability (a `W`-arrow `t→s` iff
   `s →* t`), so `[W^op,Set]` restriction runs past→future and `Sub(1_E) =`
   future-closed (⊑-up-closed) subsets of `reach`. This makes
   `AG φ = {s | ∀ t reachable from s, t ∈ ⟦φ⟧}` a native subobject of `1_E`.
   The topos of trees is the OPPOSITE (truth decays forward, `Sub(1)` past-closed,
   `Ω(n)={0..n}`) because its base is time-DEPTH; our base is STATES and
   invariants must persist forward. Getting this backwards silently breaks the
   reduction (workshop P1, HIGH).

3. **The reduction is (almost) definitional and must be tested executably.**
   `is_true : Ω → bool` (`is_true v ⟺ v = ⊤`) is a bounded-lattice + normal-modal
   HOMOMORPHISM: it commutes with `meet/join`, `pre_all/pre_some`, `knows`,
   `everyone`, and finite μ/ν iteration — failing to commute ONLY at Heyting
   `imp`/`neg` on graded (non-two-valued) arguments. The classical reflection
   (§4) repairs exactly those two nodes. Hence by induction
   `is_true (grade φ s) = (s ∈ sat φ)` (the current `system.ml` sat), giving
   `valid_E ⟺ valid_checker` and `satisfiable_E ⟺ satisfiable`. **Therefore S1–S7
   re-verify and every confirm-by-mutation pin still flips.** This is proven
   operator-by-operator in §4, and PINNED by an executable differential test
   `is_true ∘ grade = sat` over pristine + all 6 model mutants (§6).

4. **Reflection is vacuous on S1–S7, so it needs a synthetic witness.** Every
   `Implies`-antecedent and `Not`-argument across S1–S7 is a crisp Boolean of
   atoms, and every atom is monotone/two-valued, so `classical` is a no-op on all
   seven statements (workshop P4 both, P6 HIGH). The reflection code path is
   therefore exercised NOT by S1–S7 but by a hand-built modal-under-¬/→ probe
   (`Not (Ag p)`, `Implies (Af p, q)`) whose graded value is a proper sieve —
   without it the reflection is green-by-vacuity.

---

## 1. `W` and the presheaf topos `E = [W^op, Set]`  (module `frame`, `sieve`, `sub`)

**Base category `W`.** Objects = `reach` (`system.ml:27-46`). Order `s ≤ t` iff
`s →* t` under `step spec` (successors, terminals self-looped, `system.ml:24-25`).
This is a genuine finite PARTIAL order for this model: phases strictly advance
(`phase_index`, `tn_state.ml:155-164`), per-validator locals only grow
(`tn_state.ml:183`; `label` monotone `tn_model.ml:447-499`), the only cycle is
the `Done` self-loop on a single state (`tn_model.ml:400`). `W := (reach, ⊑)` is
this order REVERSED. Finite (`≤ |reach|²` arrows). The **one-step span** is kept
as separate structure (never recovered from `⊑`): `N = {(s,s') | s' ∈ step s}`,
`π₁,π₂ : N → reach` — it powers `AX/EX` (§2). (In this model `→` happens to equal
the Hasse relation since sibling successors are incomparable, but carry `N`
independently for robustness.)

**Object presentation** (branching analogue of `temporal/trees.ml:5`):
```
type 'x obj = { sections : state -> 'x list;
                restrict : state -> state -> 'x -> 'x }   (* along s ⊑ s' *)
```
`restrict s s'` is defined on one-step edges and extended along ⊑-paths by
composition; path-independence holds (poset ⇒ all parallel arrows equal) and is
checked by a finite `commutes ~upto` certificate (`trees.ml:13` analogue).
Terminal `1`: `sections s = [()]`.

**Sieve-Ω** (built BY HAND — comp-cat's `omega_via_ran`/`power`/`exists` are
`Err.Unsupported`, `subobject.ml:310/275/288`). For `s`, let `↑s = {t | s ⊑ t}`
(future cone, finite). `Ω(s) := { future-closed subsets of ↑s }` (= sieves on `s`
in `W`). Restriction along `s ⊑ s'`: `σ ↦ σ ∩ ↑s'`. `truth s () = ↑s` (the ⊤
sieve). This is the branching generalization of `temporal/omega_val.ml`'s linear
validity-depth chain (there `↑n = {n,n+1,…}` and a sieve is a truncation depth).
Ops on `Ω` (Alexandrov/Heyting, `omega_val.ml`-analogue): `meet = ∩`, `join = ∪`,
`imp σ τ = {t ∈ ↑s | ∀u ⊒ t, u∈σ ⟹ u∈τ}`, `neg σ = imp σ ∅`, `is_true σ = (σ = ↑s)`.

**`Sub(1_E)` and connectives** (`sub.ml`, `trees_omega.ml:25` analogue).
`Sub(1_E) =` future-closed subsets of `reach`, ordered by `⊆`, a finite Heyting
algebra. `⊤ = reach`, `⊥ = ∅`, `∧ = ∩`, `∨ = ∪` (pointwise; the only presheaf
cover is maximal, so `∨/∃` are pointwise union — NO reflection, matches
`system.ml:104-105`). `A → B = {s | ∀ t ⊒ s, t∈A ⟹ t∈B}` (Alexandrov
future-hereditary); `¬A = {s | ↑s ∩ A = ∅}`. `character S s () = S ∩ ↑s`;
`s ∈ S ⟺ character S s () = ↑s`. All 18 atoms denote genuine up-sets
(`label` monotone). NOTE: general formulas do NOT all live in `Sub(1_E)` (e.g.
`Not At_done` is past-closed); those are computed in `B` (§2) — only `AG` and
invariant content are read natively in `Sub(1_E)`.

---

## 2. Temporal modalities  (modules `basechange`, `fix`)

Computed in the **Boolean base `B` = `P(reach)`** (workshop P2: the modal fragment
is valued in the discrete/underlying-set object, NOT the graded `Sub(1_E)`; so
the topos-of-trees "guarded ν vs inductive μ" contractiveness discipline does NOT
transfer — over `B` there is no `later`-contractivity and the fixpoints are the
plain finite-lattice ones the checker already uses).

Base change along the transition span `N` (`basechange.ml`):
`pre_all Z = {s | ∀ s'∈step s, s'∈Z} = ∀_{π₁}(π₂* Z)` (`system.ml:57-61`);
`pre_some Z = {s | ∃ s'∈step s, s'∈Z} = ∃_{π₁}(π₂* Z)` (`system.ml:62-65`).
So `AX = pre_all`, `EX = pre_some`. `EX/EF/EG` are the POSSIBILITY (∃-base-change)
modality — categorically distinct from the base-logic `∃`, NOT intuitionistic □.

Fixpoints (`fix.ml`, Knaster–Tarski over the finite `P(reach)` lattice; matches
`system.ml:110-133` seeds EXACTLY):
```
AG p = νZ. p ∧ pre_all Z      (seed ⊤ = reach)      EG p = νZ. p ∧ pre_some Z  (⊤)
AF p = μZ. p ∨ pre_all Z      (seed ⊥ = ∅)          EF p = μZ. p ∨ pre_some Z  (⊥)
AU(p,q) = μZ. q ∨ (p ∧ pre_all Z)   (⊥)      EU(p,q) = μZ. q ∨ (p ∧ pre_some Z)  (⊥)
```
`AF/EF/AU/EU` are the UNGUARDED μ (seed ∅). Keeping them unguarded is a hard
constraint from the reduction (§4): a "later-guarded ◇" would ⊤-collapse
(`temporal/DESIGN.md §0.1.2`). `AG` additionally has a native `Sub(1_E)` reading
(future-closed) — the DESIGN may expose that for invariants, but the executable
path computes all eight uniformly in `B`.

Left-totality precondition: the μ-semantics rely on `step` being left-total
(guaranteed by the terminal self-loop totalization, `system.ml:24-25`).

---

## 3. Epistemic modalities  (module `knows`)

Computed in `B` as the S5 comonad of an essential geometric morphism over the
DISCRETE base (workshop P3, both reviewers — the ordered-`W` geometric morphism
computes a right Kan extension that is NOT `knows`, and `K_i` breaks
`E`-persistence, so it must live in `B`).

For validator `i`: `f_i : reach → V_i`, `f_i(s) = local_of s i`
(`tn_model.ml:535`; `Checker = System.Make(Tn_state)(Tn_state.Local)`). `~_i =`
kernel of `f_i` (an equivalence relation). The three base-change adjoints along
`f_i` on `(P(reach),⊆) ⇄ (P(V_i),⊆)`:
```
f_i*  (preimage)        : P(V_i)→P(reach)   f_i* T = {s | f_i s ∈ T}
Σ_{f_i} ⊣ f_i* (image)  : P(reach)→P(V_i)   Σ S = f_i(S)
f_i* ⊣ Π_{f_i} (∀-image): P(reach)→P(V_i)   Π S = {u | f_i⁻¹ u ⊆ S}
```
**`K_i := f_i* ∘ Π_{f_i}`**, i.e. `K_i S = {s | ~_i-class of s ⊆ S}`. This is the
necessity comonad `h* ∘ h_*` of the essential geometric morphism
`h : B → Set^{|V_i|}` induced by `f_i`. **`K_i = knows` VERBATIM**
(`system.ml:69-87` builds the same fibre partition via `View_map` and keeps `s`
iff its class ⊆ `S`; the `~none:false` guard at `:84` is dead). Properties (each
pinnable by mutation, §6): lex, factive (`Kφ⊆φ`, counit), idempotent (`KK=K`),
Euclidean (S5) — a lex idempotent S5 comonad, the correct categorical status of
knowledge.

`E_G φ = ⋀_{i∈G} K_i φ` (`everyone`, `system.ml:89-92`);
`C_G φ = νZ. E_G(φ ∧ Z)` (`common`, gfp seeded ⊤, converges in `≤ |reach|`
iterations, `system.ml:94-96`).

**Orthogonality (the honest account).** `~_i` cuts across temporal depth, so for a
persistent `S`, `K_i S` need not be persistent: `K_i` is NOT an endofunctor of
`Sub(1_E)`; it is a genuine operator on `B = P(reach)`. It is reconciled with `E`
only through the classical reflection (§4), not by re-persisting. No S1–S7
statement reads `K` outside a temporal wrapper, so this discrete-base reading is
the canonical one.

---

## 4. Classical reflection + reduction theorem  (module `reflect`, `denote`)

**Bridge** (`reflect.ml`, `temporal_eval.ml:29-30` analogue):
`classical v = if is_true v then ⊤ else ⊥`, applied to the Ω-VALUE of the
argument during per-world graded evaluation, RECURSIVELY, at every `Not` node and
every `Implies`-antecedent (structural, like `temporal_eval` `V_neg`/`V_impl`).
NOT `¬¬` (which reflects the wrong way). NOT a subobject-level operator (that is a
no-op on persistent atoms and would leave `¬/→` hereditary).

**Graded evaluator `grade : Formula.t → state → Ω`** (`denote.ml`, bottom-up):
`Atom a` → `character ⟦a⟧`; `And/Or` → `Ω.meet/join`, no reflection;
`Not φ` → `neg (classical (grade φ s))`; `Implies(φ,ψ)` → `imp (classical (grade φ s)) (grade ψ s)`;
`AX..EU` → §2 in `B`, no reflection; `K/Everyone/Common` → §3 in `B`, no reflection.

**Reduction theorem.** By §0.1.3, `is_true (grade φ s) = (s ∈ sat φ)` for all `φ,s`
(induction over `Formula.t`; `is_true` is a homomorphism except at `imp/neg`,
where `classical` restores it via the top/bot laws `imp(⊤,T)=T`, `imp(⊥,T)=⊤`,
`neg(⊤)=⊥`, `neg(⊥)=⊤`). Define `valid_E φ := is_true (grade φ w0)` at the single
initial world `w0 = initial` (`tn_model.ml:533`), `= (w0 ∈ sat φ) = valid sys φ`
(`system.ml:145`). Hence `prove`/`prove_nonvacuous` (`denote.ml`) return `Ok`
exactly when the current kernel does: **S1–S7 re-verify unchanged, and each stays
refuted under its model mutation.**

Where reflection is load-bearing vs no-op: on S1–S7 it is a NO-OP (all
antecedents/¬-args crisp two-valued), so it is exercised only by the synthetic
probe (§0.1.4, §6).

---

## 5. comp-cat reuse map + dune wiring  (workshop P5)

telcoin-epistemic-ocaml does NOT currently depend on `comp_cat` (deps: ocaml,
dune, alcotest). Wire it:
- `opam pin add comp_cat ~/Documents/comp-cat-ocaml --yes` into the
  `telcoin-epistemic-ocaml` switch (or a dune-workspace spanning both repos —
  pin chosen for a clean reusable dep).
- `lib/dune`: add `(libraries comp_cat)`. `comp_cat` is wrapped, so reference
  `Comp_cat.Res`, `Comp_cat.Err`, `Comp_cat.Finset`, etc.
- `lib/internal/` joins the existing flat `telcoin_epistemic` library via the
  repo layout (no nested library). Verify no basename collisions with existing
  `lib/*.ml` (frame/sieve/sub/basechange/fix/knows/reflect/denote are all new).

**Consumed from comp_cat (all exist, none are sentinels):** `Comp_cat.Res` /
`Comp_cat.Err` (the no-exceptions monad, mirrors the temporal core); `Comp_cat.Finset`
plumbing (`finset.ml`) if a concrete FinSet carrier is wanted for the reflection
target; the topos-of-trees modules (`temporal/omega_val`, `trees_omega`, `later`)
as the STRUCTURAL TEMPLATE to mirror.

**NOT consumed (Err.Unsupported):** `Subobject.omega_via_ran` (`:310`),
`Subobject.power` (`:275`), `Subobject.exists` (`:288`), mirrored in `Topos`.
**NOT consumed (unexercised / FinSet-only):** `Subobject.for_all`/`name` (need a
concrete exponential), `Subobject.and_/or_/imply/not_/character` (only the FinSet
2-valued classifier `Ch7_toposes.subobject_classifier` exists; no presheaf
grounding). => The sieve-Ω, `Sub(1_E)` lattice, base-change trio, fixpoint engine,
`K_i` comonad, and reflection are ALL built BY HAND in `lib/internal/`, exactly as
`lib/temporal/` hand-built the topos of trees. This is the ratified "bespoke
layer" decision: comp_cat is leveraged as framework + template, not as a
black-box internal-logic engine (its presheaf internal logic is unimplemented).

**Bespoke modules (build order, each ends green):**
1. `frame.ml/.mli` — `W`: states, `leq`, one-step span `succ`, view fibres.
2. `sieve.ml/.mli` — sieve-graded `Ω` (`meet/join/imp/neg/is_true`).
3. `sub.ml/.mli` — `Sub(1_E)` Heyting lattice (`top/bot/of_pred/meet/join/imp/neg/equal/character`).
4. `basechange.ml/.mli` — `reindex (f*)`, `exists_`, `forall_`, `pre_all/pre_some`.
5. `fix.ml/.mli` — Knaster–Tarski `lfp (seed ⊥)` / `gfp (seed ⊤)`.
6. `knows.ml/.mli` — `K_i = f_i* ∘ forall_`, `everyone`, `common`.
7. `reflect.ml/.mli` — `classical` reflection.
8. `denote.ml/.mli` — `grade`, `sat`, `valid`, `satisfiable`, `prove`,
   `prove_nonvacuous` over `Formula.t`; the new LCF boundary (keep `Theorem.t`).

Then re-point `Tn_model.Checker` (or `Statements.prove`) at `denote` — preferably
via a functor over a `CHECKER` signature so `t_statements.ml`/`t_tn_mutation.ml`
are unchanged. `system.ml` may be retained as the reduction ORACLE (the
differential test compares `denote` against it) or deleted after the differential
gate is green; keep it for the test.

---

## 6. Conventions, tests, confirm-by-mutation  (workshop P6)

Conventions (enforced; the review agent checks each): no exceptions (`Res.t`/`Err.t`
for partial ops; total ops return values directly); no two-arm `match` on
`option`/`result` (combinators); no `_ ->` catch-all on any finite sum
(`Formula.t`, `Ω`, phase/round/etc. matched exhaustively); every `.mli` value
carries a doc comment naming its topos/FHMV/TLA source; `List`/`Array`
combinators over hand recursion; flat namespace, globally-unique basenames; dual
license inherited.

**Test oracle (four gates, all must be green):**
1. **Statements gate.** `Statements.prove_all` over the new `denote`: all 7 return
   `Ok` (`prove_nonvacuous`), and each flips to `Error (Refuted _)` under its
   paired `tn_model` mutation. 7 pins over 6 mutations — `Drop_batch_gate` pins
   two (S2 payload-availability and S7 honest-holders); the other five map
   `Weak_quorum→S1/S4`, `No_support_check→S4`, `Unbounded_delay→S5`,
   `Leader_censors_v2→S6`, `No_vote_once→S3` (verify the exact pairing against
   the existing `t_tn_mutation.ml`).
2. **Executable reduction gate (the D3 guardrail).** For every subformula of every
   `Si` and a spanning battery of hand formulas, assert
   `is_true (grade sys f s) = State_set.mem s (System.sat sys f)` at ALL reachable
   `s`, over pristine + all 6 mutants. This is what actually catches a wrong
   persistence direction (§0.1.2) or a mis-seeded fixpoint; the operator-by-
   operator §4 argument is not enough on its own (workshop P6 HIGH).
3. **Reflection non-vacuity probe.** Since `classical` is a no-op on S1–S7, add a
   modal-under-¬/→ probe whose antecedent is genuinely sieve-graded
   (`Not (Ag p)`, `Implies (Af p, q)` on a small synthetic frame) and assert:
   (a) the reflected `grade` equals the classical `sat`; (b) DELETING `classical`
   from `reflect.ml` FLIPS this probe (proving the reflection path is live) while
   leaving S1–S7 green (proving vacuity on them).
4. **Categorical-law pins** (confirm-by-mutation, each mutation flips one paired
   negative test then is restored): adjunction unit/counit `f* ⊣ forall_` and
   `exists_ ⊣ f*` (Galois: `exists_ f A ⊆ B ⟺ A ⊆ reindex f B`, dually forall);
   `K_i` factivity (`K S ⊆ S`), idempotence (`K K S = K S`), Euclidean; `C_G` gfp
   convergence bound (`≤ |reach|`); the μ-vs-ν seed correctness (seed `AF` at ⊤
   instead of ∅ ⇒ `AF` collapses to ⊤, a paired test must catch it).

Gotcha (from the temporal build): first cold `dunecho test` may time out on
alcotest warmup; run `./_build/default/test/t_NAME.exe` directly, or re-run.

---

## Provenance (what the adversarial workshop corrected in the first draft)

- **Persistence direction** was self-contradictory; fixed to FUTURE-closed
  (`W` = reversed reachability), opposite the topos of trees (P1 HIGH).
- "**Every formula is a subobject of `1`**" was false (`Not At_done` is
  past-closed); only `AG`/invariants are native to `Sub(1_E)`, general formulas
  live in `B = P(reach)` (P1 HIGH).
- **`K_i` as a geometric morphism over ordered `W`** was WRONG (yields a right
  Kan extension ≠ `knows`, and breaks persistence); corrected to the discrete-base
  essential-geometric-morphism comonad `f_i* ∘ Π_{f_i}` = `knows` verbatim (P3
  HIGH ×2, both reviewers independently).
- **"Guarded ν vs inductive μ" discipline** does NOT transfer from trees; the
  modal fragment is valued in the Boolean `B`, fixpoints are the plain
  finite-lattice ones (P2 HIGH).
- **Reflection is vacuous on S1–S7** (all antecedents crisp) — needs a synthetic
  probe or it is green-by-vacuity (P4/P6 HIGH).
- **The reduction needs an EXECUTABLE differential gate** (`is_true ∘ grade =
  sat`), not just an operator-by-operator argument (P6 HIGH).
