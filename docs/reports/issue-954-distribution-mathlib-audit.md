# Issue #954: Mathlib probability API audit for `Distribution`

Audit date: 2026-04-30

Audited branch/base: `gpt55/issue-954-distribution-mathlib-session40` at
`53443203` (`origin/main` when the worktree was created)

## Verdict

Mathlib already has the right *mathematical* APIs for finite/discrete
probability distributions:

- `PMF` in `Mathlib.Probability.ProbabilityMassFunction.Basic`;
- `PMF.ofFinset`, `PMF.ofFintype`, `PMF.normalize`, `PMF.map`, and `PMF.bind`
  in `Mathlib.Probability.ProbabilityMassFunction.Constructions` and
  `Monad`;
- `PMF.uniformOfFinset` and `PMF.uniformOfFintype` in
  `Mathlib.Probability.Distributions.Uniform`;
- `PMF.toMeasure`, `PMF.toMeasure.isProbabilityMeasure`, and
  `PMF.integral_eq_sum` / `PMF.integral_eq_tsum` for expectations;
- measure-level finite sums/integrals such as
  `MeasureTheory.integral_fintype`, `MeasureTheory.integral_finset`,
  `MeasureTheory.lintegral_fintype`, and `MeasureTheory.lintegral_finset`.

However, the current LDT `Distribution` should **not** be replaced wholesale
now.  The replacement is mathematically feasible but high-blast-radius and
low-reward during active proof work: `avgOver` and `uniformDistribution` occur
thousands of times across more than one hundred LDT files, the project relies
on real-valued (`Error = ℝ`) weights for `ring`/`linarith`/`field_simp` proofs,
and several current distributions are intentionally only finite weighted
measures or subprobability-like objects rather than bundled probability laws.

Recommended action for #954: close the issue with this audit as the decision
record, keep the local `Distribution` representation for now, and open smaller
follow-up PRs for optional adapters to Mathlib `PMF`/`Measure` where they are
useful.

## What Mathlib provides

### `PMF`: discrete probability mass functions

`PMF` is defined as a function `α → ℝ≥0∞` whose infinite sum is `1`:

```lean
def PMF (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // HasSum f 1 }
```

Relevant declarations found in the checkout:

| Declaration | Import/module | Why it matters |
| --- | --- | --- |
| `PMF`, `PMF.support`, `PMF.tsum_coe` | `Mathlib.Probability.ProbabilityMassFunction.Basic` | Bundled discrete probability law and support-as-nonzero-set API. |
| `PMF.toMeasure` | `Mathlib.Probability.ProbabilityMassFunction.Basic` | Converts a `PMF` to a `Measure`. |
| `PMF.toMeasure.isProbabilityMeasure` | `Mathlib.Probability.ProbabilityMassFunction.Basic` | The associated measure is a probability measure. |
| `MeasureTheory.Measure.toPMF` | `Mathlib.Probability.ProbabilityMassFunction.Basic` | Converts countable probability measures with measurable singletons back to `PMF`. |
| `PMF.ofFinset` | `Mathlib.Probability.ProbabilityMassFunction.Constructions` | Builds a `PMF` from a finitely supported weight function and a `Finset` support. |
| `PMF.ofFintype` | `Mathlib.Probability.ProbabilityMassFunction.Constructions` | Builds a `PMF` from weights on a finite type. |
| `PMF.normalize` | `Mathlib.Probability.ProbabilityMassFunction.Constructions` | Normalizes a nonzero finite/countable mass function. |
| `PMF.map`, `PMF.bind` | `Mathlib.Probability.ProbabilityMassFunction.Constructions` / `Monad` | Push-forward and monadic sampling. |
| `PMF.uniformOfFinset`, `PMF.uniformOfFintype` | `Mathlib.Probability.Distributions.Uniform` | Uniform finite distributions. |
| `PMF.integral_eq_sum`, `PMF.integral_eq_tsum` | `Mathlib.Probability.ProbabilityMassFunction.Integrals` | Expectations as finite or countable weighted sums. |

Mathlib also has `PMF.binomial` and Bernoulli APIs, and this repository already
uses them in `MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean`.

### Measure-level finite and discrete APIs

Mathlib's measure layer supplies:

- `MeasureTheory.Measure.count` and count/Dirac decomposition lemmas such as
  `MeasureTheory.Measure.sum_smul_dirac`;
- finite/countable Lebesgue integral lemmas
  `MeasureTheory.lintegral_count`, `MeasureTheory.lintegral_finset`, and
  `MeasureTheory.lintegral_fintype`;
- Bochner integral lemmas `MeasureTheory.integral_finset`,
  `MeasureTheory.integral_fintype`, and `MeasureTheory.integral_countable`;
- `ProbabilityTheory.cond` and `ProbabilityTheory.uniformOn` for normalized
  restrictions of measures (`uniformOn` is measure-valued, not a `PMF`).

These are more general than the LDT finite-sum wrappers, but they bring the
usual measure-theory side conditions: `MeasurableSpace`,
`MeasurableSingletonClass`, integrability hypotheses, and `ℝ≥0∞` weights.

## Current LDT API

The local API is in `MIPStarRE/LDT/Basic/Distribution.lean`.

```lean
structure Distribution (α : Type*) where
  support : Finset α := ∅
  weight : α → Error := fun _ => 0
  nonnegative : ∀ a, 0 ≤ weight a := by intro _; positivity
  outsideSupport : ∀ a, a ∉ support → weight a = 0 := by intro _ _; rfl
```

Here `Error` is `ℝ` (`MIPStarRE/LDT/Basic/ParametersBase.lean:18`).
Probability is a predicate, not part of the structure:

```lean
def Distribution.IsProbability (𝒟 : Distribution α) : Prop :=
  𝒟.totalWeight = 1

abbrev ProbabilityDistribution (α : Type*) :=
  {𝒟 : Distribution α // 𝒟.IsProbability}
```

The main consumers are:

```lean
def avgOver (𝒟 : Distribution α) (f : α → Error) : Error :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a * f a

noncomputable def averageOperatorOverDistribution
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op ι :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a • f a

noncomputable def uniformDistribution (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] : Distribution α := ...
```

This file already contains project-local finite-sum adapters such as
`Distribution.sum_univ_eq_sum_support`,
`Distribution.weight_sum_univ_eq_totalWeight`, `avgOver_eq_sum_univ`, and
`averageOperatorOverDistribution_eq_sum_univ`.  Those are wrappers around
Mathlib's `Finset` API, not replacements for Mathlib probability theory.

## Can `avgOver` be expressed as a Mathlib expectation?

Yes, for a genuine probability distribution.  A plausible adapter is:

```lean
noncomputable def Distribution.toPMF (𝒟 : Distribution α)
    (h𝒟 : 𝒟.IsProbability) : PMF α :=
  PMF.ofFinset
    (fun a => ENNReal.ofReal (𝒟.weight a))
    𝒟.support
    -- sum proof from `h𝒟` using `ENNReal.ofReal_sum_of_nonneg`
    -- outside-support proof from `𝒟.outsideSupport`
```

Then, when the ambient type is finite and the needed measurable-space
instances are available, the intended bridge is:

```lean
avgOver 𝒟 f = ∫ a, f a ∂((𝒟.toPMF h𝒟).toMeasure)
```

The proof would use:

- `PMF.integral_eq_sum` to rewrite the Bochner integral as
  `∑ a, (p a).toReal • f a`;
- `ENNReal.toReal_ofReal (𝒟.nonnegative a)` to return from `ℝ≥0∞` weights to
  `Error = ℝ` weights;
- `avgOver_eq_sum_univ` / `Distribution.sum_univ_eq_sum_support` to move
  between the explicit support and the ambient finite type.

For non-probability weights, `avgOver` is not an expectation.  It is a finite
weighted sum.  It can still be represented by a finite measure, but then the
replacement target is `Measure α`, not `PMF α`, and downstream statements would
need finite-measure rather than probability-measure hypotheses.

For operator-valued averages, a Bochner integral expression is also plausible
for finite index types, but it is not obviously a simplification.  Current proofs
use finite sums and real scalar multiplication directly for positivity/order
arguments on `Quantum.Op`; rewriting them through Bochner integrals would add
normed-space, completeness, measurability, and integrability obligations without
removing the matrix-order proof work.

## Downstream blast radius

A focused grep over `MIPStarRE` found:

| Term | Occurrences | Files |
| --- | ---: | ---: |
| `avgOver` | 2,178 | 102 |
| `uniformDistribution` | 2,334 | 100 |
| either `avgOver` or `uniformDistribution` | — | 123 |
| `averageOperatorOverDistribution` | 116 | 15 |
| `Distribution` | — | 61 |
| `ProbabilityDistribution` | 12 | 3 |
| `totalVariationDistance` | 19 | 4 |

The heaviest files for `avgOver`/`uniformDistribution` are:

| Occurrences | File |
| ---: | --- |
| 334 | `MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean` |
| 332 | `MIPStarRE/LDT/MainInductionStep/Theorems.lean` |
| 277 | `MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean` |
| 230 | `MIPStarRE/LDT/GlobalVariance/Theorems/Results.lean` |
| 212 | `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/AdjacentStages.lean` |
| 151 | `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds.lean` |
| 149 | `MIPStarRE/LDT/Test/MainTheorem.lean` |
| 139 | `MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation.lean` |
| 113 | `MIPStarRE/LDT/Pasting/BridgeLemmas/OverAllOutcomes.lean` |
| 105 | `MIPStarRE/LDT/Pasting/SwitcherooCompletion.lean` |

Representative downstream shapes:

- `MIPStarRE/LDT/Test/Defs.lean` defines core relations such as `consError`,
  `sddError`, `sddErrorOp`, `sscError`, `subMeasMassError`,
  `bipartiteConsError`, and `bipartiteSSCError` as `avgOver 𝒟 ...`.
- `MIPStarRE/LDT/Preliminaries/Defs.lean` stores `Distribution Question` in
  proposition structures such as `BipartiteSDDRel`, `ConsAgreement`,
  `ConsSubMeasStmt`, `SwitchSandwichStmt`, and `CompTransferStmt`.
- `MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean` has many concrete
  paper averages, often over `uniformDistribution (FullSliceQuestion params)`
  or `uniformDistribution (EvaluatedSliceQuestion params)`.
- `MIPStarRE/LDT/SelfImprovement/Defs.lean`,
  `MIPStarRE/LDT/GlobalVariance/Defs/Core.lean`, and
  `MIPStarRE/LDT/GlobalVariance/Defs/Families.lean` use
  `averageOperatorOverDistribution` to build submeasurements and averaged
  operators.
- `MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation.lean` and
  `MIPStarRE/LDT/Pasting/Core.lean` use `totalVariationDistance` in explicit
  real finite-sum estimates.

The local distribution definitions are also more varied than a simple uniform
`Fintype` law:

- `distinctTupleDistribution` in `MIPStarRE/LDT/Pasting/Defs/Tuples.lean` is
  uniform on the finite set of injective tuples.  It has a proved mass bound
  `≤ 1`; for edge cases with empty support it is not a probability law.
- `surfaceVsPointDistribution` in `MIPStarRE/LDT/Test/SurfaceVsPoint.lean` is
  uniform on a filtered support of genuine 2-dimensional framed incident pairs;
  the docstring explicitly notes empty-support edge cases when `params.m < 2`.
- `axisParallelLineQuestionDistribution` in
  `MIPStarRE/LDT/GlobalVariance/Defs/Core.lean` is uniform on an incident-pair
  support defined by a predicate.
- `pointPairSharedDiagonalLineDistribution` in
  `MIPStarRE/LDT/CommutativityPoints/Defs.lean` is a push-forward-style finite
  distribution with image support but a denominator from the source sample
  space.
- `rerandomizeCoord` in
  `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Core.lean` has non-uniform weights
  counting triples `(u, i, x)` mapping to the same edge pair.

## Key blockers to a wholesale replacement

1. **Real weights vs. `ℝ≥0∞` weights.**
   The LDT code uses `Error = ℝ` and proves many bounds by real arithmetic.
   `PMF` and `Measure` store masses in `ℝ≥0∞`, so every migrated proof would
   accumulate coercions, `toReal`, `ofReal`, finiteness, and nonnegativity
   obligations.

2. **Probability is not always bundled.**
   `Distribution` can represent finite weighted sums before a normalization
   proof exists, or edge cases whose support is empty.  `PMF` requires total mass
   exactly `1`; `Measure` can represent subprobability/finite measures, but then
   it no longer gives the small `PMF` API directly.

3. **Explicit `Finset` support is part of the proof style.**
   Many lemmas reason by `Finset.sum_congr`, support membership, filtered
   supports, and supportwise inequalities.  `PMF.support` is a `Set` of nonzero
   masses, not a stored `Finset`; `PMF.ofFinset` records enough information to
   recover support facts, but the proof surface changes substantially.

4. **Measure-theory side conditions would spread through foundational files.**
   The current `MIPStarRE/LDT/Basic/Distribution.lean` imports only
   `ParametersBase` and `Quantum.FiniteMatrix`.  Importing
   `ProbabilityMassFunction.Integrals` would pull in Bochner integration and
   measure-theory infrastructure at a low level, while downstream LDT finite
   types currently do not need explicit `MeasurableSpace` assumptions.

5. **Operator averages are not made easier by integrals.**
   `averageOperatorOverDistribution` is used to build PSD operator averages and
   submeasurements.  The current finite-sum form works with `Finset.sum_nonneg`,
   real scalar multiplication, and matrix-order lemmas.  A Bochner integral route
   would add analytic typeclass obligations and likely require new matrix-order
   bridge lemmas.

6. **No direct replacement for the local TV-distance formula was found.**
   Mathlib has signed/vector-measure total variation machinery, but not a
   ready-made finite-probability `totalVariationDistance` API matching the local
   real formula
   `1 / 2 * ∑ a ∈ μ.support ∪ ν.support, |μ.weight a - ν.weight a|`.

## Recommended migration plan

Do not migrate the existing codebase in one PR.  If Mathlib integration is
wanted, do it by small adapters that do not change current statement shapes.

1. **Add an optional adapter file, not a foundational import.**
   Create something like `MIPStarRE/LDT/Basic/DistributionPMF.lean` importing
   `MIPStarRE.LDT.Basic.Distribution` and Mathlib `PMF` APIs.  Do not import it
   from `Distribution.lean` or the main LDT barrel until it has users.

2. **Start with probability-only scalar adapters.**
   Prove `Distribution.toPMF` for `𝒟.IsProbability`, plus
   `avgOver_eq_integral_toPMF` for finite ambient types.  This would validate
   the bridge while preserving all existing `avgOver` statements.

3. **Bridge uniform distributions.**
   Prove that `uniformDistribution α` maps to `PMF.uniformOfFintype α`, and use
   this only in new scalar-probability lemmas where Mathlib expectation theorems
   are valuable.

4. **Handle subprobability/empty-support laws separately.**
   For `distinctTupleDistribution`, `surfaceVsPointDistribution`, and similar
   filtered supports, add measure-level finite-measure adapters only when a proof
   genuinely needs measure theory.  Do not force them into `PMF` unless the
   nonempty/normalization hypotheses are already available.

5. **Leave operator averages as finite sums unless a specific theorem needs an
   integral statement.**
   Any future Bochner bridge for `Quantum.Op` should be a dedicated theorem with
   explicit typeclass assumptions, not a replacement for the core definition.

## Follow-up issues opened from this audit

- #964: add `Distribution.toPMF` and `avgOver_eq_integral_toPMF` in a new
  optional file, with no downstream migration.
- #966: prove `uniformDistribution` corresponds to `PMF.uniformOfFintype` and
  document the exact `toReal` simplification for uniform weights.
- #967: add a measure-valued adapter for finite nonnegative `Distribution`s that
  are not known to have mass `1`.

A later TV-distance scout may also be useful: check whether the signed-measure
`totalVariation` API can recover the local finite `totalVariationDistance`
formula without making the pasting proofs harder.

## Validation for this PR

This PR is docs-only.  Validate with:

```text
git diff --check -- docs/reports/issue-954-distribution-mathlib-audit.md
```

No Lean files are changed; no `lake env lean` target is required for this audit.
