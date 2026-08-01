# Comparison: `openai/ten-proofs` `QuantumParallelRepetition.lean` vs `MIPStarRE`

Date: 2026-08-01
External repo: <https://github.com/openai/ten-proofs> (Apache-2.0), commit fetched
via `git clone --depth 1` on 2026-08-01.
File under comparison: `QuantumParallelRepetition.lean` (result #6 of the
*Ten advances in mathematics and theoretical computer science* release).

## 1. Verdict

**Same field, adjacent problems, no shared code.** The two developments live in
the same mathematical universe — two-player one-round nonlocal games with
finite-dimensional entangled strategies — and both are "soundness against
entangled provers" theorems. But they prove different theorems by disjoint
techniques, and neither is a component of the other. The only genuine code
overlap is the bottom ~200 lines of shared quantum boilerplate (density
matrices, POVMs, PSD trace pairings, Kronecker products), which both projects
re-derived independently on top of Mathlib.

## 2. The two problems

| | `ten-proofs` #6 | `MIPStarRE` |
|---|---|---|
| Statement | Exponential parallel repetition for arbitrary finite two-player quantum games | Quantum soundness of the classical low individual degree test |
| Source | OpenAI, *Ten advances…* (2026) | arXiv:2009.12982 (Ji–Natarajan–Vidick–Wright–Yuen) |
| Top decl | `QuantumParallelRepetition.distributionUniformExponential` | `MIPStarRE.LDT.Test.mainFormal` |

Their headline statement (`QuantumParallelRepetition.lean:70953`):

```
∃ c : ℝ, 0 < c ∧ ∀ (G : Game X Y A B), Nonempty A → Nonempty B →
  0 < 1 - entangledValue G → ∀ n, 0 < n →
    repeatedEntangledValue G n ≤
      Real.exp (-(c * ((1 - entangledValue G) ^ 13 /
        ((1 - entangledValue G) + Real.log (card A * card B)))) * n)
```

i.e. `val*(Gⁿ) ≤ exp(−c · (1−val*)¹³ / ((1−val*) + log|A||B|) · n)`.

Ours (`MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`): from a projective
bipartite strategy passing the LDT with error `eps`, produce global
low-individual-degree polynomial measurements `G_A`, `G_B` consistent with the
strategy's point measurements up to `mainFormalError params k eps`.

### Why they are *related*

- Both are about **entangled strategies breaking a classical soundness
  argument**. Classical parallel repetition (Raz) and classical low-degree
  testing both proceed by conditioning on / rounding one player's information;
  entanglement kills that step in both cases. Both papers are the story of
  repairing exactly that step.
- Both feed the same complexity-theoretic program around `MIP* = RE`: parallel
  repetition is the standard **gap-amplification** tool for interactive proofs,
  the LDT is the **PCP/gap-creation** tool used inside `MIP* = RE`.
- The literature overlaps: *Parallel repetition of entangled games* is already
  cited in `blueprint/src/references.bib:10` and `references/ldt-paper/wright.bib:250`.

### Why they are *not the same problem*

- Neither theorem is used to prove the other. `MIP* = RE` deliberately avoids
  parallel repetition (it uses answer reduction / introspection) precisely
  because quantum parallel repetition was open; conversely the parallel
  repetition proof never touches low-degree tests.
- Techniques are disjoint. Theirs is **information-theoretic**: KL divergence,
  Pinsker, chain rules, coordinate conditioning, postselection/filtering,
  purified histories, then rounding an `n`-fold strategy down to a single-copy
  strategy. Ours is **operator-algebraic**: approximate representation theory,
  self-consistency, state-dependent distances `≈_δ`, Naimark dilation /
  projectivization, hypercube-graph expansion, orthonormalization, pasting.
- Grep evidence of the disjointness:

  | concept | `QuantumParallelRepetition.lean` | `MIPStarRE/` |
  |---|---:|---:|
  | Pinsker / entropy / divergence | present (`namespace Pinsker`, 10226–10613) | 0 |
  | purification | 644 | 0 |
  | Naimark | 0 | 353 |
  | orthonormalization | 0 | 443 |
  | consistency | 0 | 2229 |
  | polynomial / low degree | 0 | pervasive |
  | Kronecker `⊗ₖ` | 369 | 207 |
  | `PosSemidef` | present | 237 |

## 3. Code comparison — the shared base layer

This is where the two developments actually touch.

### 3.1 States

Theirs (`QuantumParallelRepetition.lean:88`):

```lean
structure DensityMatrix (d : Type*) [Fintype d] where
  matrix : Matrix d d ℂ
  positive : matrix.PosSemidef
  trace_one : Matrix.trace matrix = 1
```

Ours (`MIPStarRE/LDT/Basic/QuantumState.lean:25`):

```lean
abbrev Op (d : Type*) := Matrix d d ℂ            -- Quantum/FiniteMatrix/Basic.lean:79

structure QuantumState (ι : Type*) [Fintype ι] [DecidableEq ι] where
  density : Op ι := 0
  density_psd : 0 ≤ density := by positivity

def QuantumState.IsNormalized (ψ : QuantumState ι) : Prop :=
  MIPStarRE.Quantum.normalizedTrace ψ.density = 1
```

Three deliberate divergences:

1. **Positivity encoding.** They use the `Matrix.PosSemidef` predicate; we use
   the Loewner order `0 ≤ A` from `MatrixOrder`/`StarOrderedRing`. Ours
   composes with `positivity`, `Finset.sum_nonneg`, and ordered-algebra lemmas
   directly; theirs needs `Matrix.nonneg_iff_posSemidef` bridging wherever an
   order argument appears (we hit the same bridge, e.g.
   `Quantum/FiniteMatrix/TracePairing.lean:180-202`).
2. **Trace convention.** They use the raw trace with `tr ρ = 1` baked into the
   structure. We use the **normalized** trace `τ(A) = tr(A)/dim`, so a pure
   state is `dim · |ψ⟩⟨ψ|` (`pureDensity`), and normalization is a separate
   `Prop` rather than a field. This is not gratuitous: the LDT paper works with
   normalized traces on matrix algebras, and keeping `IsNormalized` detached
   lets un-normalized sub-states appear in intermediate steps.
3. **Defaults.** Our structure carries `:= 0` / `by positivity` autoparams; we
   deliberately withhold an `Inhabited` instance so the zero matrix cannot
   silently trivialize downstream statements.

### 3.2 Measurements

Theirs (`:93`) has one notion, the complete POVM:

```lean
structure POVM (ι d : Type*) [Fintype ι] [Fintype d] [DecidableEq d] where
  effect : ι → Matrix d d ℂ
  positive : ∀ i, (effect i).PosSemidef
  complete : (∑ i : ι, effect i) = 1
```

Ours (`MIPStarRE/Quantum/Measurement.lean:33,46`) makes the *sub*-measurement
primitive and derives the complete case:

```lean
structure Submeasurement (α : Type*) [Fintype α] (d : Type*) … where
  effect : α → Op d
  pos : ∀ a, 0 ≤ effect a
  sum_le_one : ∑ a, effect a ≤ 1

structure Measurement (α : Type*) … extends Submeasurement α d where
  sum_eq_one : ∑ a, effect a = 1
```

That inversion is forced by the mathematics: the LDT argument constantly
truncates, restricts, and projectivizes measurements, so `∑ ≤ 1` is the
invariant that survives. Parallel repetition never needs it. We also carry
`postprocess` (fiberwise relabeling with a `Finset.sum_fiberwise` proof) as
first-class API; they inline the equivalent when needed.

### 3.3 Strategies

Structurally the closest pair in the two repos.

Theirs (`:101`):

```lean
structure Strategy … (_G : Game X Y A B) where
  Alice : Type
  Bob : Type
  state : DensityMatrix (Alice × Bob)
  aliceMeasurement : X → POVM A Alice
  bobMeasurement : Y → POVM B Bob
```

Ours (`MIPStarRE/LDT/Test/StrategyCore.lean:774`):

```lean
structure ProjStrat (params : Parameters) [FieldModel params.q]
    (ιA : Type*) … (ιB : Type*) … where
  state : QuantumState (ιA × ιB)
  isNormalized : state.IsNormalized
  pointMeasurementA : IdxProjMeas (Point params) (Fq params) ιA
  axisParallelMeasurementA : IdxProjMeas (AxisParallelLine params) … ιA
  axisParallelReparamInvariantA : …
  diagonalMeasurementA : … (and the B-side mirror)
```

Same skeleton — bipartite state on a product index, question-indexed
measurement families per player. Differences: they existentially quantify the
local dimensions *inside* the structure (`Alice Bob : Type` as fields), we take
`ιA ιB` as parameters; their answer type is abstract `A`/`B`, ours is the
concrete LDT question/answer geometry (points, axis-parallel lines, diagonal
lines) with **reparametrization-covariance side conditions** as structure
fields; and their measurements are POVMs whereas `ProjStrat` demands projective
ones, since making measurements projective is a named chapter of our proof
(`LDT/MakingMeasurementsProjective/`).

Their joint effect is an explicit Kronecker product
`(aliceMeasurement x).effect a ⊗ₖ (bobMeasurement y).effect b` (`:129`). We use
`LDT/Basic/TensorPlacement.lean` to lift A-side and B-side operators into the
single ambient index, which gives the commuting-operator calculus the paper's
proofs are written in.

### 3.4 A genuine near-duplicate

The clearest instance of independent convergence:

`QuantumParallelRepetition.lean:113`

```lean
theorem trace_mul_posSemidef_nonneg {R E : Matrix d d ℂ}
    (hR : R.PosSemidef) (hE : E.PosSemidef) : 0 ≤ (Matrix.trace (R * E)).re := by
  obtain ⟨K, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  …
```

`MIPStarRE/Quantum/FiniteMatrix/TracePairing.lean:180`

```lean
theorem trace_mul_nonneg_of_nonneg {A B : Op d} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ Complex.re (Matrix.trace (A * B)) := by
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB
  …
```

Same lemma, same proof: factor one operand as `K⋆K`, cyclically move it to
conjugate the other operand, conclude from `Complex.nonneg_iff` on the trace of
a PSD matrix. Neither was copied from the other — this is simply the shortest
route through current Mathlib. Both projects then use it for the same purpose:
"outcome probabilities are nonnegative" there, weak-duality positivity here.

The same pattern repeats one level up: their `outcomeProbability_normalized`
and `winProbability_le_one` (`:161,187`) are the analogue of our
`bipartiteConsError_uniform_le_one` — both are "POVM completeness forces the
total mass to 1, hence every masked sub-sum is ≤ 1".

## 4. Engineering comparison

| | `QuantumParallelRepetition.lean` | `MIPStarRE/` |
|---|---:|---:|
| Lean / Mathlib | v4.32.0 | v4.31.0 |
| Files | 1 | 337 |
| Lines | 70,980 | 126,131 |
| Avg lines/file | 70,980 | 374 (1000-line CI guard) |
| `theorem`/`lemma` | 1,660 | 2,105 |
| `def`/`abbrev` | 805 | 1,030 |
| `structure` | 14 | 148 |
| Declaration docstrings `/--` | **0** | 3,471 |
| Module docstrings `/-!` | **0** | 477 |
| Line comments | **0** | — |
| `sorry` | 0 | 0 |
| Custom `axiom` | 0 | 0 |
| Imports | `import Mathlib` | per-file minimal imports |

Other structural differences:

- **Provenance.** Every statement of ours carries a paper-origin reference
  (`references/ldt-paper/<file>.tex:<line>`) enforced by
  `scripts/check_statement_paper_origin.py`, plus dated `audits/` and
  `docs/paper-gaps/` notes where the Lean statement deviates from the printed
  one (e.g. the corrected `k ≥ 400·m·d` bound in `MainFormal.lean`). Their file
  carries no provenance at all — traceability lives entirely in
  `formalization.yaml` and the external PDF.
- **Blueprint.** We maintain a `leanblueprint` dependency graph with
  `\lean{}`/`\leanok` cross-references and CI sync guards
  (`scripts/blueprint_lean_sync.py`, `lake exe checkdecls`). They have none;
  the 71k-line file is the only artifact.
- **Independent checking — a real convergence.** Both projects use the official
  [`leanprover/comparator`](https://github.com/leanprover/comparator) to check
  that the *statement* is what it claims to be. Theirs:
  `ComparatorChallenges/G_QuantumParallelRepetition.json`, pinning
  `permitted_axioms: [propext, Quot.sound, Classical.choice]` and
  `enable_nanoda: true`. Ours: `scripts/comparator/` regenerates a
  self-contained `Challenge.lean` for the kernel closure of `mainFormal`'s
  statement, checked byte-for-byte against
  `scripts/comparator/expected/Challenge.lean.expected` in CI, and consumed by
  the companion `LionSR/LDT-comparator` repo. Same trust model, arrived at
  independently.
- **Process.** `formalization.yaml` records their proof as ~1 week of agent
  wall-time (Astra / Codex) with `review.status: agent-reviewed`. Ours is a
  long-running human-supervised PR pipeline with per-PR CI, statement-integrity
  guards, and proof-debt audits.

## 5. Things worth stealing / worth noting

Points in their favour:

- The **top-level statement surface is tiny** — two theorems, both
  `∃ c > 0, ∀ G n, …`, with no auxiliary error parameters exposed. That is very
  easy for a reader to audit. Our `mainFormal` exposes `mainFormalError` plus
  hypotheses (`400 * params.m * params.d ≤ k`, `0 < k`), which is faithful to
  the paper but a larger surface to trust. Worth keeping the comparator
  challenge as the mitigation it already is.
- Their `formalization.yaml` is a clean machine-readable manifest (main results,
  declaration names, sorry counts, permitted axioms, comparator config, cost).
  We have all of this information spread across `README.md`, badges, and
  `audits/`; a single manifest file would be cheap and useful.

Points in ours:

- 0 docstrings vs 3,471. A 71k-line uncommented file with no blueprint is
  essentially unreviewable by a human except through the comparator; our
  paper-origin + blueprint discipline is the thing that makes statement drift
  detectable at all.
- Their `Game`/`Strategy` layer would need substantial rework to support
  sub-measurements, projectivization, or reparametrization covariance — none of
  which their theorem needs, all of which ours does. There is no shortcut to be
  had by importing their base layer.

## 6. Bottom line

No code to reuse in either direction, and no duplicated effort to worry about.
The overlap is confined to the ~200 lines of Mathlib-adjacent quantum
boilerplate that any formalization of nonlocal games has to write, and even
there the two projects made different, individually well-motivated modelling
choices (PSD predicate vs Loewner order; raw vs normalized trace; POVM vs
submeasurement primitive). The one process idea genuinely shared — verifying the
statement with `leanprover/comparator` under a pinned axiom list — both projects
adopted independently, which is a decent signal that it is the right thing to do.
