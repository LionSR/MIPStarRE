import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.StrongDuality.Separation

/-!
# Section 9 -- Canonical SDP strong duality

This compatibility module preserves the historical import path for the canonical
finite-dimensional matrix SDP strong-duality development.  The feasibility and
compactness preliminaries live in
`Canonical.StrongDuality.Basic`; the separation and zero-gap argument lives in
`Canonical.StrongDuality.Separation`.  The short objective-bound lemmas below
remain here because they are useful consequences of the same canonical SDP
interface.

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology

/-- The canonical objective block operator is positive semidefinite. -/
theorem matrixSdpCanonicalObjectiveOperator_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    0 ≤ matrixSdpCanonicalObjectiveOperator params model := by
  rw [matrixSdpCanonicalObjectiveOperator]
  refine matrixSdpCanonicalBlockDiagonal_nonneg params model
    (matrixSdpCanonicalObjectiveBlockFamily params model) ?_
  intro b
  cases b with
  | none => simp [matrixSdpCanonicalObjectiveBlockFamily]
  | some g => exact matrixAveragedPointOperator_nonneg params model g

/-- The canonical objective has nonnegative trace pairing with every feasible
canonical primal matrix. -/
theorem matrixSdpCanonicalObjective_trace_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    0 ≤ Complex.re (Matrix.trace
      (matrixSdpCanonicalObjectiveOperator params model * X)) :=
  MIPStarRE.Quantum.trace_mul_nonneg_of_nonneg
    (matrixSdpCanonicalObjectiveOperator_nonneg params model) hX.nonnegative

/-- Every feasible canonical primal objective is bounded above by the explicit
strict-dual objective. -/
theorem matrixSdpCanonicalObjective_trace_le_strictDualObjective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
      matrixSdpDualObjective model (matrixSdpStrictDualWitness model) :=
  matrixSdpCanonicalWeakDuality params model X hX
    (matrixSdpStrictDualWitness model)
    (matrixSdpCanonicalStrictDualConstraint_nonneg params model)

/-- The explicit strict-primal canonical objective is bounded above by every
paper-form dual-feasible objective. -/
theorem matrixSdpCanonicalStrictPrimalObjective_le_dualObjective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalPrimalBlockMatrix params model
            (matrixSdpStrictPrimalSubmeasurement params model))) ≤
      matrixSdpDualObjective model Z :=
  matrixSdpCanonicalWeakDuality params model
    (matrixSdpCanonicalPrimalBlockMatrix params model
      (matrixSdpStrictPrimalSubmeasurement params model))
    (matrixSdpCanonicalStrictPrimalBlockMatrix_feasible params model) Z
    (matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible params model Z hdual)

end MIPStarRE.LDT.SelfImprovement
