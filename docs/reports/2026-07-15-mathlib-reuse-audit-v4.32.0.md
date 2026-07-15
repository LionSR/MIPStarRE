# Mathlib reuse audit for MIPStarRE on v4.32.0

Audit date: 2026-07-15

## Purpose and baseline

This is a project-wide audit of tracked Lean sources for local infrastructure that can be replaced by, or simplified through, existing Mathlib APIs. It is broader than the earlier v4.31-to-v4.32 delta review: long-standing Mathlib declarations were included.

Audited checkout:

- Lean: `v4.32.0`
- Mathlib tag: `v4.32.0`
- Mathlib commit: `81a5d257c8e410db227a6665ed08f64fea08e997`
- Git branch: `chore/bump-toolchain-v4.32.0`
- Tracked Lean sources: 339
- Local `theorem`/`lemma`/`def`/`abbrev` declarations inventoried: 3,589

The working tree already contained modifications, including two tracked Lean files. The audit inspected the current working-tree statements but did not edit Lean files or pre-existing untracked files.

## Method

The audit used four complementary checks:

1. Inventory every tracked local declaration and identify generic helpers, wrappers, finite-sum algebra, scalar bounds, matrix utilities, PMF utilities, and paper-facing aliases.
2. Search the checked-out Mathlib declaration database by exact name, related name, and type/conclusion shape.
3. Inspect exact local and Mathlib source statements, including module placement and proof assumptions.
4. Count downstream usages and compile-check the strongest proposed replacements in isolated temporary Lean files.

A candidate is called an **exact replacement** only when its mathematical statement agrees after definitional unfolding or a routine representation conversion. A merely related theorem is recorded as a close API, not as a replacement.

## Phase plan

### Phase 1 — Lean/Mathlib v4.32.0 upgrade

The current upgrade work on `chore/bump-toolchain-v4.32.0` is Phase 1. Its purpose is to establish the v4.32.0 toolchain and Mathlib baseline before reuse refactors. This report does not assert that an upgrade PR is currently open.

Reuse batches below should be based on the completed Phase 1 baseline so that changes are not mixed with toolchain-manifest churn.

### Phase 2 and later — focused reuse PRs

Apply only the high-confidence replacements in small subsystem-specific batches. Retained candidates should not be repeatedly proposed without a new Mathlib API or a change in project representation.

## Accepted replacements

### 1. Hermitian-part construction

Local declarations in `MIPStarRE/Quantum/FiniteMatrix/TracePairing.lean`:

```lean
noncomputable def tracePairingHermitianPart (Z : Op d) : Op d :=
  (1 / 2 : ℝ) • (Z + Zᴴ)

theorem tracePairingHermitianPart_isHermitian ...
```

Exact Mathlib replacement:

```lean
(↑((selfAdjointPart ℝ) Z) : Op d)
```

Relevant Mathlib declarations:

- `selfAdjointPart`
- `selfAdjointPart_apply_coe`

Module:

```lean
import Mathlib.Algebra.Star.Module
```

`selfAdjointPart_apply_coe` gives `⅟2 • (Z + star Z)`; for complex matrices, `star Z = Zᴴ`, and over `ℝ`, `⅟2 = 1 / 2`. The equality was compile-checked. Hermiticity is supplied by:

```lean
(selfAdjointPart ℝ Z).property.isHermitian
```

Usages are confined to `TracePairing.lean`. Recommended action: direct replacement and deletion of the local construction/theorem. Risk: low. Confidence: very high.

### 2. Hermitian sandwich positivity

Local declaration in `MIPStarRE/Quantum/FiniteMatrix/Order.lean`:

```lean
theorem sandwich_nonneg {M P : Op d}
    (hP : 0 ≤ P) (hMH : Mᴴ = M) :
    0 ≤ M * P * M
```

Exact Mathlib replacement:

```lean
IsSelfAdjoint.conjugate_nonneg
```

Module:

```lean
import Mathlib.Algebra.Order.Star.Basic
```

The only representation change is `hMH : Mᴴ = M` versus `IsSelfAdjoint M`. The replacement is more general and was compile-checked. The local theorem has approximately 19 occurrences across 10 files. Recommended action: direct use of Mathlib. Risk: medium because call sites pass raw Hermiticity equalities. Confidence and value: very high/high.

### 3. Hermitian sandwich monotonicity

Local declaration:

```lean
theorem sandwich_mono {M P Q : Op d}
    (hMH : Mᴴ = M) (hPQ : P ≤ Q) :
    M * P * M ≤ M * Q * M
```

Exact Mathlib replacement:

```lean
IsSelfAdjoint.conjugate_le_conjugate
```

Module:

```lean
import Mathlib.Algebra.Order.Star.Basic
```

This is an exact semantic replacement after converting Hermiticity to `IsSelfAdjoint`. It was compile-checked. The local theorem has approximately 47 occurrences across 24 files. Recommended action: direct use of Mathlib in the same PR as `sandwich_nonneg`. Risk: medium-high from rewrite surface, not from semantics. Confidence and value: very high/high.

### 4. Scalar PMF weighted sum as an integral

Local declaration in `MIPStarRE/LDT/Basic/PMFAverages.lean`:

```lean
theorem PMF.realWeightedSum_eq_integral ... :
    PMF.realWeightedSum p f = ∫ a, f a ∂p.toMeasure
```

Mathlib replacement:

```lean
PMF.integral_eq_sum
```

Module:

```lean
import Mathlib.Probability.ProbabilityMassFunction.Integrals
```

After unfolding `PMF.realWeightedSum`, the local theorem is the symmetric orientation of `PMF.integral_eq_sum`. It has no downstream usages. Recommended action: delete and use the Mathlib theorem directly. Risk and value: negligible/low.

### 5. Unused `PMF.realWeightedSum` linearity wrappers

The following declarations in `PMFAverages.lean` have no downstream references:

```lean
PMF.realWeightedSum_zero
PMF.realWeightedSum_add
PMF.realWeightedSum_sub
PMF.realWeightedSum_smul
PMF.realWeightedSum_sum
PMF.realWeightedSum_finset_sum
```

Their bodies are exact applications of generic Mathlib linear-map laws to `PMF.realWeightedSumLinearMap`:

```lean
map_zero
map_add
map_sub
LinearMap.map_smul
map_sum
```

Recommended action: delete if these were not intentionally added as public convenience API. This is dead-wrapper cleanup rather than a mathematical representation change. Risk: low; value: low-medium.

## Compatibility migration

### `IsProj` to `IsStarProjection`

Local declaration in `MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean`:

```lean
structure IsProj (P : Op d) : Prop where
  isHermitian : P.IsHermitian
  idempotent : P * P = P
```

Exact Mathlib concept:

```lean
IsStarProjection P
```

Relevant declarations:

- `IsStarProjection`
- `IsStarProjection.isSelfAdjoint`
- `IsStarProjection.isIdempotentElem`
- `isStarProjection_iff'`
- `IsStarProjection.nonneg`

Modules:

```lean
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Order.Star.Basic
```

The predicates are mathematically identical. The compatibility differences are field names and construction syntax. The local API has approximately 81 occurrences across 15 files, but only about five direct structure literals.

Recommended staged migration:

1. Replace the local structure with a paper-facing compatibility abbreviation:

   ```lean
   abbrev IsProj (P : Op d) : Prop := IsStarProjection P
   ```

2. Temporarily provide selector compatibility lemmas for `isHermitian` and `idempotent`.
3. Convert the small number of structure literals to `IsStarProjection.mk` or `isStarProjection_iff'`.
4. Delete `IsProj.isStarProjection`, `IsProj.of_isStarProjection`, and the local `IsProj.nonneg`; use `IsStarProjection.nonneg`.

Risk: high because this is a foundational API migration. Confidence and long-term value: very high/very high. Keep it separate from the sandwich and PMF batches.

## Retained candidates

### Project `Distribution` versus `PMF`

Keep the local explicit-support representation. Mathlib provides `PMF`, `PMF.ofFinset`, `PMF.map`, `PMF.bind`, uniform PMFs, `PMF.toMeasure`, and `PMF.integral_eq_sum`, but they are not source-compatible replacements.

Exact reasons to retain:

- local weights are real-valued and used directly by `ring`, `linarith`, and matrix-order proofs;
- `Distribution` permits unnormalized and subprobability-like weights;
- empty-support edge cases are meaningful in the development;
- an explicit `Finset` support is part of many proof statements;
- `PMF` requires total mass one and uses `ℝ≥0∞` weights;
- a measure-based replacement would introduce measurable-space, integrability, and coercion obligations.

The existing `Distribution.toPMF` and integral/finite-sum bridge theorems are the correct selective reuse pattern. This agrees with `docs/reports/issue-954-distribution-mathlib-audit.md`.

### `PMF.realWeightedSum` and `PMF.realWeightedSumLinearMap`

Keep the core definitions:

```lean
PMF.realWeightedSum p f := ∑ a, (p a).toReal • f a
PMF.realWeightedSumLinearMap p : (α → M) →ₗ[ℝ] M
```

`PMF.integral_eq_sum` only applies in a complete normed real vector space with measurable-space assumptions. The local weighted sum works under the more algebraic assumptions `[AddCommMonoid M] [Module ℝ M]`. The finite `map`/`bind` formulas therefore remain justified.

### PMF total variation

Keep `PMF.totalVariationDistance` and its finite comparison lemmas. No PMF-level Mathlib total-variation distance matching

```lean
(1 / 2) * ∑ a, |(p a).toReal - (q a).toReal|
```

was found. Signed/vector-measure total variation is not source-compatible.

### `Matrix.trace_reindex`

Keep:

```lean
Matrix.trace (Matrix.reindex e e M) = Matrix.trace M
```

No exact v4.32.0 theorem was found. `Matrix.reindex_apply` and `Equiv.sum_comp` prove it, but do not replace the named result. This is a reasonable future Mathlib contribution in `Mathlib.LinearAlgebra.Matrix.Trace`.

### `Matrix.submatrixLinearMap`

Keep the bundled linear map for arbitrary row/column functions. Mathlib supplies `Matrix.submatrix` and many associated lemmas, but no matching arbitrary-index-function linear map was found. There is one external project use.

### Kronecker subtraction

Keep `kronecker_sub_left` and `kronecker_sub_right`. Mathlib provides `Matrix.kroneckerMapBilinear`, addition, and scalar-multiplication lemmas, but no exact subtraction rewrites. Their proofs may be simplified via `LinearMap.map_sub`; their rewrite-oriented statements remain useful.

### Kronecker positivity and reindex positivity

Keep `kronecker_nonneg` and `reindex_nonneg` as compatibility adapters.

Closest APIs:

- `Matrix.PosSemidef.kronecker` in `Mathlib.Analysis.Matrix.Order`;
- `Matrix.posSemidef_submatrix_equiv` in `Mathlib.LinearAlgebra.Matrix.PosDef`;
- `Matrix.nonneg_iff_posSemidef` in `Mathlib.Analysis.Matrix.Order`.

The local theorems bridge Mathlib's `PosSemidef` language to matrix order, install finite instances where needed, and expose source-compatible conclusions. They are not independent reimplementations.

### Block-diagonal API

Keep:

```lean
Matrix.blockDiagonal_eq_sum_kronecker_diagonal
Matrix.blockDiagonalLinearMap
Matrix.blockDiagonal_nonneg
Matrix.blockDiagonal_nonneg_iff
```

Mathlib has `Matrix.blockDiagonalAddMonoidHom`, `Matrix.blockDiagonal_smul`, multiplication, subtraction, and trace lemmas, but no arbitrary-scalar linear map or block-diagonal PSD theorem/iff matching the local statements.

### Normalized matrix trace

Keep `normalizedTrace` and its algebraic API. Mathlib's declaration with the same simple name is field-theoretic and unrelated. No finite-matrix normalized trace matching `trace A / card d` was found. This local definition has approximately 242 occurrences across 21 files.

### Closed PSD cone and matrix trace bounds

Keep:

```lean
norm_apply_le_trace_re_of_nonneg
norm_le_trace_re_of_nonneg
isClosed_op_nonnegative
opNonnegativeProperCone
sq_le_self
```

No exact matrix trace-bound or contraction-square theorem was found. `CStarAlgebra.isClosed_nonneg` is only superficially similar: the project's matrix topology/norm instance is not automatically a `NonUnitalCStarAlgebra (Matrix ι ι ℂ)`, while the local closedness theorem is stated without a finite-index assumption. Do not substitute the C-star theorem without changing the ambient structure.

### Real trace pairing and complementary slackness

Except for the Hermitian-part construction, keep the trace-pairing layer:

```lean
realTracePairingCLM
tracePairingMatrixOfRealCLM
realTracePairingCLM_tracePairingMatrixOfRealCLM
trace_mul_nonneg_of_nonneg
nonneg_of_trace_mul_nonneg_of_isHermitian
trace_mul_nonneg_forall_nonneg_iff_of_isHermitian
mul_eq_zero_of_nonneg_of_trace_mul_eq_zero
```

Mathlib has `Matrix.traceLinearMap`, `Complex.reCLM`, PSD trace nonnegativity, and conjugation lemmas, but no matching real-dual representation or complementary-slackness product-zero theorem.

### Finite Hilbert-space utilities

Keep:

```lean
LinearIsometry.ofFinrankLE
Matrix.toEuclideanLin_conjTranspose_mul_self
Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows
Matrix.exists_mul_conjTranspose_eq_one_of_card_le
```

Mathlib provides the component orthonormal-basis, adjoint, and matrix-linear-map APIs, but no direct finrank-inequality isometric embedding or rectangular coisometry existence theorem was found. `LinearIsometry.ofFinrankLE` is a plausible future Mathlib contribution.

### Projector spectral/range API

After the `IsProj` migration, retain the explicit projector spectral decomposition, trace-rank theorem, `ProjectorRangeONB`, and subprojector API. Mathlib's `Matrix.IsHermitian.spectral_theorem`, eigenvalue sum, rank/cardinality, and `Matrix.vecMulVec` results are the ingredients, not replacements for the packaged statements.

### Square-root and `rpow` helpers

Keep `sqrt_add_le_add_sqrt` and `sqrt_add3_le_add3_sqrt`; no exact theorem was found. The specialized `sqrt_rpow_one_div`, `rpow_one_four_eq_sqrt_sqrt`, and `rpow_one_eight_eq_sqrt_sqrt_sqrt` proofs may be shortened with `Real.rpow_div_two_eq_sqrt`, `Real.sqrt_eq_rpow`, and `Real.rpow_mul`, but this is proof simplification only.

### Polynomial aliases and wrappers

Keep `polyFunc` as paper-facing notation for `MvPolynomial.restrictDegree`, and keep the individual-degree and Schwartz-Zippel wrappers. They already delegate to:

- `MvPolynomial.restrictDegree`;
- `MvPolynomial.mem_restrictDegree`;
- `MvPolynomial.degreeOf_le_iff`;
- `MvPolynomial.schwartz_zippel_totalDegree`.

No exact theorem replacing `totalDegree_le_mul_of_degreeOf_le` was found.

## Reviewable PR batches and dependencies

### Batch A — self-adjoint part

Scope: `Quantum/FiniteMatrix/TracePairing.lean` only.

- use `selfAdjointPart ℝ`;
- delete the local Hermitian-part definition/theorem.

Risk: low. Independent. Recommended first reuse PR after Phase 1.

### Batch B — sandwich order API

Scope: `Quantum/FiniteMatrix/Order.lean` and its sandwich consumers.

- use `IsSelfAdjoint.conjugate_nonneg`;
- use `IsSelfAdjoint.conjugate_le_conjugate`;
- remove the local wrappers.

Risk: medium. Independent of Batch A. Prefer before the projection migration so downstream code consistently uses Mathlib star-order vocabulary.

### Batch C — projection compatibility migration

Scope: `Quantum/FiniteMatrix/NormalizedTrace.lean`, `Quantum/ProjectorONB.lean`, and approximately 13 LDT consumers.

- alias `IsProj` to `IsStarProjection`;
- add temporary selector compatibility lemmas;
- update direct constructors;
- remove conversion and positivity wrappers.

Risk: high. Do not combine with PMF or toolchain changes. Prefer after Batch B.

### Batch D — PMF dead-wrapper cleanup

Scope: `LDT/Basic/PMFAverages.lean`.

- delete unused linearity wrappers where generic linear-map laws suffice;
- delete `realWeightedSum_eq_integral` in favor of `PMF.integral_eq_sum`.

Risk: low. Independent and may run in parallel with B/C.

### Batch E — proof simplifications only

Scope: square-root/`rpow` helpers and optionally Kronecker subtraction proofs.

- preserve theorem names and statements;
- use existing Mathlib algebra internally.

Risk and value: low. Optional after functional reuse work.

Do not combine a wholesale `Distribution` migration, block-diagonal generalization, or trace-pairing theorem redesign with these reuse batches.

## Validation evidence

The audit verified the local Mathlib checkout is exactly tag `v4.32.0` at commit `81a5d257c8e410db227a6665ed08f64fea08e997`.

Isolated Lean checks successfully compiled for:

- `IsSelfAdjoint.conjugate_nonneg` as the sandwich positivity replacement;
- `IsSelfAdjoint.conjugate_le_conjugate` as the sandwich monotonicity replacement;
- `Matrix.PosSemidef.kronecker` plus `Matrix.nonneg_iff_posSemidef` for local Kronecker positivity;
- `Matrix.posSemidef_submatrix_equiv` for positive reindexing;
- equality of the local Hermitian-part formula with coerced `selfAdjointPart ℝ`;
- Hermiticity obtained from `(selfAdjointPart ℝ Z).property`.

A direct attempt to use `CStarAlgebra.isClosed_nonneg` for arbitrary matrices failed because the required matrix C-star-algebra instance is not available in the project's ambient structure. This validates retaining `isClosed_op_nonnegative` rather than treating the similarly named Mathlib theorem as an exact replacement.

## Re-audit triggers

Revisit retained candidates when any of the following occurs:

- Mathlib adds `Matrix.trace_reindex`, block-diagonal PSD lemmas, or matrix-order Kronecker/reindex lemmas;
- Mathlib adds a PMF finite real-expectation or PMF total-variation API;
- the project changes its matrix norm/topology to a bundled C-star-algebra representation;
- the project adopts `IsStarProjection` directly and removes the paper-facing `IsProj` name;
- a concrete proof needs measure-theoretic expectations rather than finite algebraic sums.

Future audits should update this report's candidate status and retained reasons instead of recreating the same replacement proposals from scratch.
