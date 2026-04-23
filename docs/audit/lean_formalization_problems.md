# Lean Formalization Audit: Paper Mismatches and Placeholder Definitions

Date: 2026-04-04

Scope audited:

- Paper: `references/ldt-paper/preliminaries.tex`, `commutativity-G.tex`, `orthonormalization.tex`, `self_improvement.tex`, `ld-pasting.tex`, `expansion.tex`, `inductive_step.tex`
- Lean: all files under `MIPStarRE/LDT/`
- Existing scouting notes: `docs/scouting/gap_*.md`

High-level result:

- I did **not** find any remaining literal `MISMATCH(...)` comments under `MIPStarRE/LDT/`.
- I did find multiple **active faithfulness problems**: fake placeholder definitions, weakened theorem types, missing hypotheses, a remaining operator/tensor-model mismatch, stale `TODO` markers for known model drift, and several unused definitions.

## Critical and medium issues

### 1. Fake square-root operator in the global-variance matrix layer

- Lean location: `MIPStarRE/LDT/GlobalVariance/MatrixRealization.lean:33-40`
- Severity: **critical**

Lean code:

```lean
/--
The concrete stand-in for `(G_g)^{1/2}`. The source uses the square root; this
placeholder omits it and reuses `G_g` itself.
-/
noncomputable def matrixPolynomialWeightSqrtOperator ...
  matrixPolynomialWeightOperator params model g
```

What the paper says:

- `references/ldt-paper/expansion.tex:276`, `:295`, `:328`, `:334-335` use the actual weight `(G_g)^{1/2}` throughout the local/global variance arguments.
- Replacing `(G_g)^{1/2}` by `G_g` changes the operator being compared and changes the squared norm identity.

Why this is a problem:

- This is an explicit placeholder, not a faithful formalization of the paper’s weighted operator.

### 2. The matrix global-variance model collapses tensor placement to same-space multiplication

- Lean location: `MIPStarRE/LDT/GlobalVariance/MatrixRealization.lean:17-25`, `:48-53`, `:105-119`
- Severity: **critical**

Lean code:

```lean
structure MatrixVarianceTransferRealization (params : Parameters) where
  space : FiniteHilbertSpace
  state : PositiveMatrixState space
  ...

noncomputable def matrixWeightedPointConditionedOperatorAtPolynomial ...
  matrixPointConditionedOutcomeOperatorAtPolynomial params model g u *
    matrixPolynomialWeightSqrtOperator params model g
```

What the paper says:

- `references/ldt-paper/expansion.tex:276`, `:295`, `:328`, `:334-335` use operators of the form
  `A^u_{g(u)} \otimes (G_g)^{1/2}` acting on the bipartite state `|ψ⟩`.

Why this is a problem:

- The Lean matrix realization uses one ambient matrix algebra and multiplies the two factors instead of placing them on separate tensor factors.
- This is an operator-placement mismatch, not just a proof gap.

### 3. `generalizeB`, `localVarianceOfPoints`, and `globalVarianceOfPoints` are stated for an arbitrary `ψbi`

- Lean location: `MIPStarRE/LDT/GlobalVariance/Theorems.lean:21-34`, `:37-56`, `:59-83`, `:117-123`, `:155-162`, `:206-213`
- Severity: **critical**

Lean code:

```lean
structure GeneralizeBStatement (params : Parameters)
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Prop where
```

and similarly for `LocalVarianceOfPointsStatement` and `GlobalVarianceOfPointsStatement`.

What the paper says:

- `references/ldt-paper/expansion.tex:271-335` fixes a single good strategy `(\psi, A, B, L)` and states these bounds for that strategy’s state.

Why this is a problem:

- The Lean theorem types disconnect the variance bounds from `strategy.state`.
- That is a real statement mismatch: the paper proves a fact about the strategy’s actual bipartite state, not an arbitrary external `ψbi`.

### 4. Polynomial and line answers in the global-variance layer are raw functions, not low-degree objects

- Lean location: `MIPStarRE/LDT/GlobalVariance/Defs.lean:25-31`
- Severity: **medium**

Lean code:

```lean
/-- TODO(degree): polynomial answers should be degree-bounded objects rather than raw functions. -/
abbrev DegreeBoundedPolynomialAnswer (params : Parameters) :=
  Point params → Fq params

/-- TODO(degree): line answers should be degree-bounded objects rather than raw functions. -/
abbrev DegreeBoundedLineAnswer (params : Parameters) :=
  Fq params → Fq params
```

What the paper says:

- The paper quantifies over genuine low-degree polynomial objects, e.g. `g ∈ polyfunc{m}{q}{d}` and line restrictions `g|_ℓ`; see `references/ldt-paper/expansion.tex:273-279`, `:292-330`.

Why this is a problem:

- These Lean abbreviations forget the degree constraints entirely.
- That drops a real hypothesis from the mathematical objects being formalized.

### 5. `interpolateCompletedSlices` — definition faithful, degree bound proven

- Lean location: `MIPStarRE/LDT/Pasting/Defs/Interpolation.lean`
- Severity: **low** (was **critical**; definition now faithful and the
  `lowIndividualDegree` proof is complete)

The definition uses proper Lagrange interpolation via Mathlib's
`Lagrange.basis`, embedded into `MvPolynomial` at the last coordinate,
and restricts the sum to a chosen `(d+1)`-sized support witness
`σ ⊆ gHatTupleSupport gs` (packaged by `InterpolationSupportWitness`).
The `lowIndividualDegree` proof is fully discharged: for the first `m`
coordinates the bound follows from `degreeOf_mul_le` plus the fact that
`Li.eval₂ C (X (lastCoord))` has degree `0` in those coordinates; for
the last coordinate the bound follows from
`natDegree_lagrangeBasis_le_card_sub_one` together with
`σ.card = d + 1`, avoiding the cancellation argument entirely.

What the paper says:

- `references/ldt-paper/ld-pasting.tex:241-245`, `:478-482`, `:1240-1247` uses actual interpolation from compatible slice polynomials to the unique ambient degree-`d` polynomial.

Remaining gaps:

- **Interpolation correctness (downstream)**: the definition gives the
  correct degree bound unconditionally, but to prove the paper's
  restriction property (that `restrictAtHeight` of the result agrees
  with each slice on `σ`) one needs `Set.InjOn (decodeScalar ∘ xs) ↑σ`
  and `σ ⊆ gHatTupleSupport gs`. The latter is now threaded explicitly
  into `interpolateCompletedSlicesFromSupport` and, in the default
  interpolation path, is supplied by
  `InterpolationSupportWitness.subset_support`; the former holds when
  `xs` is drawn from `distinctTupleDistribution`, but is a proof
  obligation at each downstream call site, not in the definition itself.

### 6. `laplacianDifferenceForm` is definitionally equal to `laplacian`, so `laplacianRewrite` is vacuous

- Lean location: `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean:204-208`, `MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems.lean:104-108`
- Severity: **critical**

Lean code:

```lean
/-- The edge-difference form of the Laplacian from `prop:laplacian-rewrite`.
Definitionally equal to `laplacian` since both represent `(1/M)I - K`. -/
noncomputable def laplacianDifferenceForm (params : Parameters) :=
  laplacian params

theorem laplacianRewrite (params : Parameters) :
    laplacian params = laplacianDifferenceForm params := by
  rfl
```

What the paper says:

- `references/ldt-paper/expansion.tex:29-44` proves the nontrivial identity
  `L = (1/2) E_{(u,v)~C} (|u⟩-|v⟩)(⟨u|-⟨v|)`.

Why this is a problem:

- The Lean “rewrite” theorem does not state or prove the paper’s rewrite formula.
- It replaces the proposition by a definitional equality placeholder.

### 7. Historical note (resolved by PRs #527, #542, and #576): Fourier orthonormality was hard-coded instead of derived from `fourierBasisState`

- Historical Lean location: `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean:517-520`, `:539-543`, `:567-569`
- Historical severity: **critical**

**Update (2026-04-23): resolved on current `main`.** The live Chapter 5 code no longer
hard-codes `fourierBasisInnerProduct := if α = β then 1 else 0`, and the orphan
`EigenvectorsStatement` wrapper is gone. Instead, `Defs/Fourier.lean` computes the
inner product from the actual Fourier basis via `fourierBasisState_inner_product` and
exposes the paper-facing spectral facts as standalone lemmas
`eigenvectors_orthonormality`, `eigenvectors_card`, and `eigenvectors`.

Historical Lean code:

```lean
def fourierBasisInnerProduct (params : Parameters)
    (α β : Point params) : Error :=
  if α = β then 1 else 0

theorem eigenvectors (params : Parameters) :
    EigenvectorsStatement params where
  orthonormality _ _ := rfl
```

What the paper says:

- `references/ldt-paper/expansion.tex:50-72` computes
  `⟨φ_α | φ_β⟩ = 1` if `α = β` and `0` otherwise from the explicit Fourier basis vector formula, using `prop:fourier-fact-vector`.

Why this was a problem:

- The old Lean orthonormality statement was satisfied by definition rather than by the actual vector formula.
- The old API hid that scaffolding behind a theorem-shaped wrapper.

### 8. Historical note (resolved by PRs #527 and #542): `globalRewrite` packaged an existential and used `default` as witness

- Historical Lean location: `MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems.lean:26-30`, `:139-153`
- Historical severity: **medium**

**Update (2026-04-23): resolved on current `main`.** `globalRewrite` still packages the
paper's displayed decomposition as an existential `∃ decomp`, but the witness is now the
canonical centered-family decomposition `canonicalGlobalVarianceDecomposition params A`,
and `globalVarianceTraceWitness` consumes `decomp.orthogonalComponent` rather than
ignoring the decomposition. The live `GlobalVarianceDecomposition` records
`averageComponent`, the centered residual family `u ↦ A u - A_avg`,
`orthogonal_sum_zero`, and the pointwise decomposition `A u = A_avg + A_⊥^u`.

Historical Lean code:

```lean
structure GlobalRewriteStatement ... where
  decomposition :
    ∃ decomp : GlobalVarianceDecomposition params A,
      globalVariance params A ψ = globalVarianceTraceForm params A ψ decomp

lemma globalRewrite ...
  exact ⟨default, by ...⟩
```

What the paper says:

- `references/ldt-paper/expansion.tex:259-264` uses the explicit decomposition
  `A_comb = |φ_0⟩ ⊗ A_0 + |φ_⊥⟩ ⊗ A_⊥`
  and then identifies the global variance with the orthogonal component.

Why this was a problem:

- The old Lean statement was materially weaker than the paper: it only asked for existence of some decomposition.
- The old implementation then used `default`, so the proof object did not carry the paper’s actual decomposition.

### 9. `AlmostProjMeasStatement` does not encode the paper’s almost-projectivity claim

- Lean location: `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean:98-112`, `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean:248-258`
- Severity: **critical**

Lean code:

```lean
structure AlmostProjMeasStatement ... where
  strongSelfConsistency : ...
  selfDistance :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily A.toSubMeas)
      (2 * ζ)
```

What the paper says:

- `references/ldt-paper/orthonormalization.tex:403-406` derives
  `∑_a ⟨ψ| (A_a - A_a^2) ⊗ I |ψ⟩ ≤ 2ζ`,
  which is the actual “almost projective” content used in the next truncation step.

Why this is a problem:

- `SDDRel ... A ... A ...` is trivial: it compares a family with itself.
- So the Lean statement does not capture the paper’s quantity at all.

### 10. `SpectralTruncationStatement` forgets the actual output of the truncation lemma

- Lean location: `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean:115-120`, `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean:264-274`
- Severity: **medium**

Lean code:

```lean
structure SpectralTruncationStatement ... where
  matrixWitness :
    Nonempty (MatrixSpectralTruncationMeasurementWitness (Outcome := Outcome) ζ)
```

What the paper says:

- `references/ldt-paper/orthonormalization.tex:414-422` proves existence of projectors `R_a` with
  `A_a ⊗ I ≈_{2√ζ} R_a ⊗ I`
  and
  `R := ∑_a R_a ≤ (1 + 2√ζ) I`.

Why this is a problem:

- The Lean statement only stores a witness type.
- It omits the actual mathematical content of the paper’s lemma.

### 11. [resolved] The restricted diagonal strategy now uses a measurement-valued encoding

- Lean location: `MIPStarRE/LDT/MainInductionStep/Defs.lean:28-58`, `:281-320`
- Status: **resolved in #593**

Lean code:

```lean
structure RestrictedSymStrat ... where
  ...
  diagonalMeasurement :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι
```

Resolution:

- `restrictDiagonalMeasurement` now postprocesses the ambient diagonal measurement to its base-point value and re-embeds it into the honest slice answer space, so the restricted diagonal branch is packaged as a genuine projective measurement.
- This removes the earlier completeness loss that motivated the old audit warning.

### 12. [resolved] The diagonal branch in `restrictedProbabilities` now uses the paper's `m/(m+1)` and `(m+1)/m` factors

- Lean location: `MIPStarRE/LDT/MainInductionStep/Defs.lean:429-438`, `MIPStarRE/LDT/MainInductionStep/Statements.lean:148-191`, `MIPStarRE/LDT/MainInductionStep/Theorems.lean:1039-1120`
- Status: **resolved in #593**

Lean code:

```lean
averageRestrictedDiagonalError params profile ≤
  sliceConditioningLoss params * gamma
```

Resolution:

- `references/ldt-paper/inductive_step.tex:374-388` and `blueprint/src/chapter/ch10_induction.tex:27-38` use the same conditioning loss `((m+1)/m)` for the axis-parallel and diagonal branches.
- The Lean statement now packages the diagonal average bound with that same constant and no longer routes it through a separate diagonal-only surrogate API.

### 13. The global-variance layer still carries stale mismatch TODOs

- Lean location: `MIPStarRE/LDT/GlobalVariance/Defs.lean:25-31`
- Severity: **medium**

Lean code:

```lean
/-- TODO(degree): polynomial answers should be degree-bounded objects rather than raw functions. -/
/-- TODO(degree): line answers should be degree-bounded objects rather than raw functions. -/
```

What the paper says:

- The paper never uses arbitrary functions here; it uses low-degree polynomial objects and their line restrictions.

Why this is a problem:

- These TODOs are not stale editorial notes; they identify a still-live model mismatch.

### 14. [resolved] The stale diagonal-branch mismatch TODOs were cleared from the induction-step layer

- Lean location: `MIPStarRE/LDT/MainInductionStep/Defs.lean`, `Statements.lean`, `Theorems.lean`
- Status: **resolved in #593**

Resolution:

- The old closed-issue TODO comments were removed once the diagonal branch was upgraded to a projective-measurement encoding and `RestrictedProbabilitiesStatement` was aligned with the paper's shared `((m + 1) / m)` conditioning loss.
- The remaining MainInductionStep commentary now explains the current encoding instead of pointing to a closed issue.

### 15. The expansion layer still carries a stale normalization-convention TODO

- Lean location: `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean:458-465`
- Severity: **low**

Lean code:

```lean
-- TODO(#136): document/verify the `1 / |U|` normalization convention against
-- Section 7 (`lem:global-rewrite`) to avoid silent constant-factor drift.
```

What the paper says:

- `references/ldt-paper/expansion.tex:259-264` uses an explicit `1/M` normalization in the global-variance rewrite.

Why this is a problem:

- The code itself admits the constant factor has not been fully verified against the paper.
- This is a stale unresolved faithfulness note in a theorem-critical definition.

## Dead code

I searched `MIPStarRE/LDT` for definitions whose names appear only at their definition site and never in any theorem statement or proof. These are dead in the current development.

| Lean location | Lean code | What the paper says | Severity |
| --- | --- | --- | --- |
| `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean:106-111` | `matrixAveragedSandwichedPolynomialOutcomeOperator` | Corresponds to the paper’s averaged `H_h = E_u A^u_{h(u)} T_h A^u_{h(u)}` from `references/ldt-paper/self_improvement.tex:203-205`, but no theorem uses it. | low |
| `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean:186-191` | `matrixHelperBoundednessGap` | Corresponds to the helper boundedness quantity from `references/ldt-paper/self_improvement.tex:51-58`, but it is not referenced by any theorem. | low |
| `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean:194-199` | `matrixProjectiveResidualGap` | Corresponds to the projective-output boundedness quantity used after self-improvement/pasting, but no theorem uses it. | low |
| `MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean:297-298` | `orthonormalizationCompletionError` | Intended to encode the completion-to-measurement loss from the orthonormalization wrapper, but it is never referenced anywhere. | low |
| `MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean:310-311` | `spectralTruncationError` | Intended to encode the `√ζ` truncation loss from `references/ldt-paper/orthonormalization.tex:447-529`, but the theorem layer never uses it. | low |

## Category summary

- Placeholder / fake definitions:
  - `matrixPolynomialWeightSqrtOperator`
  - ~~`interpolateCompletedSlices`~~ (resolved: definition faithful and degree bound proven; see §5)
  - `laplacianDifferenceForm`
  - ~~`fourierBasisInnerProduct`~~ (resolved: now derived from the actual Fourier basis inner product; see §7)
- Wrong or weakened theorem statements:
  - `generalizeB` / `localVarianceOfPoints` / `globalVarianceOfPoints`
  - ~~`globalRewrite`~~ (resolved: canonical decomposition witness is operational; see §8)
  - `AlmostProjMeasStatement` / `consistencyToAlmostProjective`
  - `SpectralTruncationStatement` / `spectralTruncateAlmostProjective`
  - `RestrictedProbabilitiesStatement`
- Missing hypotheses / dropped structure:
  - raw-function “degree-bounded” answer types
  - restricted diagonal measurement completeness
- Operator-placement / tensor-factor problems:
  - single-space matrix model in `GlobalVariance/MatrixRealization`
- Stale mismatch comments:
  - no literal `MISMATCH` markers remain under `MIPStarRE/LDT`
  - active `TODO` mismatch markers remain in `GlobalVariance`, `MainInductionStep`, and `ExpansionHypercubeGraph`
