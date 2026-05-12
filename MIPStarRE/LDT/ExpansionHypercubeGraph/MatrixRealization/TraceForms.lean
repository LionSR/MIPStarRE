import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization.Core

/-!
# Section 7 — Matrix variance trace forms

This file contains the matrix-level variance quantities and trace-form rewrite
statements used after the Fourier spectral-gap material in `MatrixRealization.Core`.

## References

- `blueprint/src/chapter/ch05_expansion.tex`
- `references/ldt-paper/expansion.tex`
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- The quadratic form `τ(ρ (X-Y)^*(X-Y))`. -/
noncomputable def matrixSquaredDifferenceExpectation {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H) (X Y : MatrixOperator H) : Error :=
  Complex.re (matrixExpectation ρ (((X - Y)ᴴ) * (X - Y)))

/-- The actual local variance, averaged over the hypercube edge set.
This matches the Section 7.1 rerandomization distribution on ordered edges. -/
noncomputable def matrixLocalVariance (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (2 : Error)) *
    avgOver (matrixHypercubeEdgeDistribution params) (fun uv =>
      matrixSquaredDifferenceExpectation model.state
        (model.family uv.1) (model.family uv.2))

/-- The actual global variance, averaged over two independent points. -/
noncomputable def matrixGlobalVariance (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (2 : Error)) *
    avgOver (independentPointPair params) (fun uv =>
      matrixSquaredDifferenceExpectation model.state
        (model.family uv.1) (model.family uv.2))

/-- The actual average operator `E_u A^u`. -/
noncomputable def matrixAveragePointOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : MatrixOperator model.space :=
  matrixAverageOperator model.family

/-- The matrix-level combined column operator used for the trace rewrites.
Its `u`-th block is `(A^u)ᴴ`, so that the trace witnesses match the
quadratic forms `τ(ρ · (A^u - A^v)ᴴ (A^u - A^v))` for arbitrary families. -/
noncomputable def matrixCombinedOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    RectangularMatrixOperator model.space
      (tensorHilbertSpace (pointHilbertSpace params) model.space) :=
  fun ui j => star (model.family ui.1 j ui.2)

/-- Bridge for the column-operator view used in the quadratic-form witnesses. -/
noncomputable def matrixCombinedColumnOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    RectangularMatrixOperator model.space
      (tensorHilbertSpace (pointHilbertSpace params) model.space) :=
  matrixCombinedOperator params model

/-- Paper origin: `references/ldt-paper/expansion.tex:145-154`
(`\label{lem:local-rewrite}`); trace witness for the local-variance
rewrite, matrix realization. -/
noncomputable def matrixLocalVarianceTraceWitness (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixOperator model.space :=
  (matrixCombinedColumnOperator params model)ᴴ *
    (matrixTensorOperator (matrixLaplacianOperator params) model.state.matrix *
      matrixCombinedColumnOperator params model)

/-- The actual trace form for the local variance. -/
noncomputable def matrixLocalVarianceTraceForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  Complex.re (MIPStarRE.Quantum.normalizedTrace (matrixLocalVarianceTraceWitness params model))

/-- Paper origin: `references/ldt-paper/expansion.tex:179-190`
(`\label{lem:global-rewrite}`); trace witness for the global-variance
rewrite, matrix realization. -/
noncomputable def matrixGlobalVarianceTraceWitness (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixOperator model.space :=
  (matrixCombinedColumnOperator params model)ᴴ *
    (matrixTensorOperator (orthogonalModeProjectorMatrix params) model.state.matrix *
      matrixCombinedColumnOperator params model)

/-- The actual trace form for the global variance.

The `1 / hypercubeVertexCount` factor (= `1 / M` where `M = q^m`) matches the paper's
`lem:global-rewrite`: the global variance equals
  `(1/M) · Tr(⟨φ⊥| ⊗ A⊥ · (I ⊗ |ψ⟩⟨ψ|) · |φ⊥⟩ ⊗ A⊥)`,
which in turn equals `(1/2) · E_{u,v} ⟨ψ| (Aᵘ − Aᵛ)² ⊗ I |ψ⟩`. -/
noncomputable def matrixGlobalVarianceTraceForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (hypercubeVertexCount params : Error)) *
    Complex.re (MIPStarRE.Quantum.normalizedTrace
      (matrixGlobalVarianceTraceWitness params model))

/-- Kronecker product is monotone in the left factor against a PSD right factor. -/
lemma matrixTensorOperator_mono_left {H K : FiniteHilbertSpace}
    {A₁ A₂ : MatrixOperator H} {B : MatrixOperator K} (hA : A₁ ≤ A₂) (hB : 0 ≤ B) :
    matrixTensorOperator A₁ B ≤ matrixTensorOperator A₂ B := by
  simpa [matrixTensorOperator] using MIPStarRE.Quantum.kronecker_mono_left hA hB

set_option linter.flexible false in
/-- Adjoint sandwiching is monotone in the middle factor. -/
lemma conjTranspose_mul_mul_mono {H K : FiniteHilbertSpace}
    (M : RectangularMatrixOperator H K) {A B : MatrixOperator K} (hAB : A ≤ B) :
    Mᴴ * (A * M) ≤ Mᴴ * (B * M) := by
  have hpsd : 0 ≤ Mᴴ * (B - A) * M := by
    exact
      (Matrix.PosSemidef.conjTranspose_mul_mul_same
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)) M).nonneg
  have hrewrite : Mᴴ * (B - A) * M = Mᴴ * (B * M) - Mᴴ * (A * M) := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, sub_eq_add_neg, mul_add, add_mul]
    congr 1 <;> (rw [Finset.sum_comm]; simp [mul_assoc])
  rw [hrewrite] at hpsd
  exact sub_nonneg.mp hpsd

/-- Monotonicity of `Re τ` with respect to the matrix order. -/
lemma normalizedTrace_re_mono {H : FiniteHilbertSpace}
    {A B : MatrixOperator H} (hAB : A ≤ B) :
    Complex.re (MIPStarRE.Quantum.normalizedTrace A) ≤
      Complex.re (MIPStarRE.Quantum.normalizedTrace B) := by
  let ψ : QuantumState H.carrier := { density := 1 }
  simpa [ψ, ev] using (ev_mono ψ A B hAB)

/-- Paper origin: `references/ldt-paper/expansion.tex:145-178`
(`\label{lem:local-rewrite}`); matrix realization of `LocalRewriteStatement`.

Matrix-level rewrite package for the local variance. -/
structure MatrixLocalRewriteStatement (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Prop where
  traceFormula :
    matrixLocalVariance params model = matrixLocalVarianceTraceForm params model

/-- Paper origin: `references/ldt-paper/expansion.tex:179-269`
(`\label{lem:global-rewrite}`); matrix realization of `GlobalRewriteStatement`.

Matrix-level rewrite package for the global variance. -/
structure MatrixGlobalRewriteStatement (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Prop where
  traceFormula :
    matrixGlobalVariance params model = matrixGlobalVarianceTraceForm params model

end MIPStarRE.LDT.ExpansionHypercubeGraph
