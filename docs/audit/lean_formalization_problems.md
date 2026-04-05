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

### 5. `interpolateCompletedSlices` is still fake interpolation

- Lean location: `MIPStarRE/LDT/Pasting/Defs.lean:216-237`
- Severity: **critical**

Lean code:

```lean
-- Multiply by the Lagrange basis coefficient for height xᵢ
-- Note: honest Lagrange interpolation requires Field (ZMod q), which
-- holds only for prime q. For prime-power q, use GaloisField via
-- PrimePowerFieldSpec. For now, use Lagrange basis coefficient = 1
-- as a structural placeholder; the degree bound is sorry'd regardless.
slicePoly
```

What the paper says:

- `references/ldt-paper/ld-pasting.tex:241-245`, `:478-482`, `:1240-1247` uses actual interpolation from compatible slice polynomials to the unique ambient degree-`d` polynomial.

Why this is a problem:

- The current Lean definition does not perform interpolation at all; it just sums lifted slice polynomials with coefficient `1`.
- This is a fake definition of a core construction.

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

### 7. Fourier orthonormality is hard-coded instead of derived from `fourierBasisState`

- Lean location: `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean:517-520`, `:539-543`, `:567-569`
- Severity: **critical**

Lean code:

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

Why this is a problem:

- The Lean orthonormality statement is satisfied by definition rather than by the actual vector formula.
- This is a placeholder definition masquerading as a proved theorem.

### 8. `globalRewrite` is weakened to existential packaging and uses `default` as witness

- Lean location: `MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems.lean:26-30`, `:139-153`
- Severity: **medium**

Lean code:

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

Why this is a problem:

- The Lean statement is materially weaker than the paper: it only asks for existence of some decomposition.
- The implementation then uses `default`, so the proof object does not carry the paper’s actual decomposition.

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

### 11. The restricted diagonal strategy is modeled as a submeasurement, not a measurement

- Lean location: `MIPStarRE/LDT/MainInductionStep/Defs.lean:30-46`, `:177-186`
- Severity: **critical**

Lean code:

```lean
structure RestrictedSymStrat ... where
  ...
  diagonalMeasurement :
    IdxProjSubMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι

TODO(#195): This currently drops ambient outcomes whose restriction is not
represented in `DiagonalLinePolynomial params`, so it only produces a
submeasurement.
```

What the paper says:

- `references/ldt-paper/inductive_step.tex:374-412` treats the restricted diagonal-line branch as a genuine restricted test, exactly parallel to the axis-parallel branch.
- The blueprint says the same in `blueprint/src/chapter/ch10_induction.tex:23-37`.

Why this is a problem:

- The Lean model drops outcomes and loses completeness on the diagonal branch.
- This is the root cause of the later wrong loss factors.

### 12. The diagonal branch in `restrictedProbabilities` uses `1 / q` and `q` instead of `m/(m+1)` and `(m+1)/m`

- Lean location: `MIPStarRE/LDT/MainInductionStep/Defs.lean:337-353`, `MIPStarRE/LDT/MainInductionStep/Statements.lean:101-125`, `MIPStarRE/LDT/MainInductionStep/Theorems.lean:81-99`
- Severity: **critical**

Lean code:

```lean
noncomputable def sliceDiagonalDirectionWeight (params : Parameters) : Error :=
  1 / (params.q : Error)

noncomputable def sliceDiagonalConditioningLoss (params : Parameters) : Error :=
  (params.q : Error)
```

and

```lean
avgOver ... (fun x => sliceDiagonalDirectionWeight params * profile.diagonal x) ≤ gamma ∧
averageRestrictedDiagonalError params profile
  ≤ sliceDiagonalConditioningLoss params * gamma
```

What the paper says:

- `references/ldt-paper/inductive_step.tex:374-388` states
  `E_x γ_x ≤ ((m+1)/m) γ`,
  exactly parallel to the axis-parallel branch.
- The blueprint matches this at `blueprint/src/chapter/ch10_induction.tex:23-33`.

Why this is a problem:

- The Lean statement has a different theorem type from the paper and blueprint.
- This is not just weaker bookkeeping; it is a different quantitative claim.

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

### 14. The induction-step files still carry stale mismatch TODOs for the diagonal branch

- Lean location: `MIPStarRE/LDT/MainInductionStep/Defs.lean:35-39`, `:179-183`, `:341-350`; `MIPStarRE/LDT/MainInductionStep/Statements.lean:103-107`; `MIPStarRE/LDT/MainInductionStep/Theorems.lean:93-97`
- Severity: **medium**

Lean code:

```lean
TODO(#195): The paper's restricted strategy treats the diagonal branch as a
genuine projective measurement ...

TODO(#195): The paper/blueprint statement uses the same `((m + 1) / m)` loss ...
```

What the paper says:

- `references/ldt-paper/inductive_step.tex:374-412` and `blueprint/src/chapter/ch10_induction.tex:23-37` do not introduce a special `q`-dependent diagonal loss.

Why this is a problem:

- These comments correctly record an unfixed theorem-faithfulness bug.
- They should be treated as active audit findings, not harmless TODO noise.

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
  - `interpolateCompletedSlices`
  - `laplacianDifferenceForm`
  - `fourierBasisInnerProduct`
- Wrong or weakened theorem statements:
  - `generalizeB` / `localVarianceOfPoints` / `globalVarianceOfPoints`
  - `globalRewrite`
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
