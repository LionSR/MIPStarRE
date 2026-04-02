import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization

/-!
# Section 7 — Theorems

Output structures and theorem statements for the expansion / variance lemmas.
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Output package for `lem:local-rewrite`. -/
structure LocalRewriteStatement (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Prop where
  traceFormula :
    localVariance params A ψ = localVarianceTraceForm params A ψ

/-- Output package for `lem:global-rewrite`. -/
structure GlobalRewriteStatement (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Prop where
  decomposition :
    ∃ decomp : GlobalVarianceDecomposition params A,
      globalVariance params A ψ = globalVarianceTraceForm params A ψ decomp

private def ambientHilbertSpaceOf (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    FiniteHilbertSpace where
  carrier := ι
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

private def abstractMatrixModel (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) [Nonempty ι] :
    MatrixOperatorFamilyRealization params where
  space := ambientHilbertSpaceOf ι
  state :=
    { matrix := ψ.density
      positive := ψ.density_psd }
  family := A

private lemma localVariance_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    localVariance params A ψ = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  have hzero : ∀ uv : Point params × Point params,
      ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2) = 0 := by
    intro uv
    simp [pointDifferenceSquaredOperator, ev, MIPStarRE.Quantum.normalizedTrace]
  unfold localVariance
  rw [avgOver_congr _ _ (fun _ => 0) hzero, avgOver_zero]
  ring

private lemma globalVariance_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    globalVariance params A ψ = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  have hzero : ∀ uv : Point params × Point params,
      ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2) = 0 := by
    intro uv
    simp [pointDifferenceSquaredOperator, ev, MIPStarRE.Quantum.normalizedTrace]
  unfold globalVariance
  rw [avgOver_congr _ _ (fun _ => 0) hzero, avgOver_zero]
  ring

private lemma localVarianceTraceForm_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    localVarianceTraceForm params A ψ = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  simp [localVarianceTraceForm, localVarianceTraceWitness, MIPStarRE.Quantum.normalizedTrace]

private lemma globalVarianceTraceForm_eq_zero_of_isEmpty (hι : ¬ Nonempty ι)
    (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι)
    (decomp : GlobalVarianceDecomposition params A) :
    globalVarianceTraceForm params A ψ decomp = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  simp [globalVarianceTraceForm, globalVarianceTraceWitness, MIPStarRE.Quantum.normalizedTrace]

/-- The concrete matrix-level counterpart of `lem:local-to-global`. -/
lemma matrixLocalToGlobal (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVariance params model ≤ (params.m : Error) * matrixLocalVariance params model := by
  sorry

/-- The concrete matrix-level counterpart of `lem:local-rewrite`. -/
lemma matrixLocalRewrite (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixLocalRewriteStatement params model := by
  sorry

/-- The concrete matrix-level counterpart of `lem:global-rewrite`. -/
lemma matrixGlobalRewrite (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixGlobalRewriteStatement params model := by
  sorry

/-- `prop:laplacian-rewrite`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
theorem laplacianRewrite (params : Parameters) :
    laplacian params = laplacianDifferenceForm params := by
  rfl

/-- `lem:local-to-global`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
lemma localToGlobal (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    globalVariance params A ψ ≤ (params.m : Error) * localVariance params A ψ := by
  by_cases hι : Nonempty ι
  · letI := hι
    simpa [abstractMatrixModel] using
      (matrixLocalToGlobal params (abstractMatrixModel params A ψ))
  · rw [globalVariance_eq_zero_of_isEmpty hι params A ψ,
      localVariance_eq_zero_of_isEmpty hι params A ψ]
    positivity

/-- `lem:local-rewrite`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
lemma localRewrite (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    LocalRewriteStatement params A ψ := by
  by_cases hι : Nonempty ι
  · letI := hι
    refine ⟨?_⟩
    simpa [abstractMatrixModel] using
      (matrixLocalRewrite params (abstractMatrixModel params A ψ)).traceFormula
  · refine ⟨?_⟩
    rw [localVariance_eq_zero_of_isEmpty hι params A ψ,
      localVarianceTraceForm_eq_zero_of_isEmpty hι params A ψ]

/-- `lem:global-rewrite`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
lemma globalRewrite (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    GlobalRewriteStatement params A ψ := by
  by_cases hι : Nonempty ι
  · letI := hι
    refine ⟨default, ?_⟩
    simpa [abstractMatrixModel] using
      (matrixGlobalRewrite params (abstractMatrixModel params A ψ)).traceFormula
  · refine ⟨default, ?_⟩
    rw [globalVariance_eq_zero_of_isEmpty hι params A ψ,
      globalVarianceTraceForm_eq_zero_of_isEmpty hι params A ψ default]

end MIPStarRE.LDT.ExpansionHypercubeGraph
