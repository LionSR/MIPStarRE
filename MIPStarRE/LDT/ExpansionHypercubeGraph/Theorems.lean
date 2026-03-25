import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization

/-!
# Section 7 — Theorems

Output structures and theorem statements for the expansion / variance lemmas.
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- Output package for `lem:local-rewrite`. -/
structure LocalRewriteStatement (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Prop where
  differenceFormula :
    localVariance params A ψ = localVarianceDifferenceForm params A ψ
  traceFormula :
    localVariance params A ψ = localVarianceTraceForm params A ψ

/-- Output package for `lem:global-rewrite`. -/
structure GlobalRewriteStatement (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Prop where
  differenceFormula :
    globalVariance params A ψ = globalVarianceDifferenceForm params A ψ
  decomposition :
    ∃ decomp : GlobalVarianceDecomposition params A,
      globalVariance params A ψ = globalVarianceTraceForm params A ψ decomp

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
  sorry

/-- `lem:local-to-global`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
lemma localToGlobal (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) :
    globalVariance params A ψ ≤ (params.m : Error) * localVariance params A ψ := by
  sorry

/-- `lem:local-rewrite`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
lemma localRewrite (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) :
    LocalRewriteStatement params A ψ := by
  sorry

/-- `lem:global-rewrite`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
lemma globalRewrite (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) :
    GlobalRewriteStatement params A ψ := by
  sorry

end MIPStarRE.LDT.ExpansionHypercubeGraph
