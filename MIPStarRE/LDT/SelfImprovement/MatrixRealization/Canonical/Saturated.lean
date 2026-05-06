import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.Witness

/-!
# Section 9 — Saturated canonical SDP witnesses

This module contains the zero-slack variant of the canonical SDP output used in
the self-improvement argument.  The canonical block SDP supplies a feasible
matrix `X`; when its slack diagonal block is zero, the extracted polynomial
blocks form a complete measurement without using the auxiliary dominance
condition \(I \le Z\).

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- Vanishing of the slack diagonal block saturates the extracted paper
primal submeasurement.

This is the paper-faithful replacement for deriving saturation from an
auxiliary lower bound on the dual variable: if the canonical optimal solution
is supplied with zero slack block, then the extracted family satisfies
`∑_g T_g = I` directly. -/
theorem matrixSdpPrimalTotalEqOne_extracted_of_canonicalSlackBlock_eq_zero
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (hSlack : matrixSdpCanonicalDiagonalBlock params model X none = 0) :
    ∑ g : Polynomial params,
        (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX).effect g =
      1 := by
  refine matrixSdpPrimalTotalEqOne_of_canonicalSlackOperator_eq_zero
    params model (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) ?_
  rw [matrixSdpCanonicalSlackOperator_extractedPrimalSubmeasurement]
  exact hSlack

/-- Package a paper-form optimal witness from canonical complementary
slackness and an explicitly saturated slack block.

The hypotheses are precisely the canonical SDP data needed after the
block-diagonal reduction: dual feasibility, equality of the primal and dual
objectives, canonical complementary slackness, and zero slack block
`I - ∑_g T_g = 0`.  No dominance condition on the dual variable is used. -/
theorem matrixSdpOptimalWitness_of_canonicalSaturatedComplementarySlackness
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g)
    (hstrong :
      matrixSdpPrimalObjective params model T = matrixSdpDualObjective model Z)
    (hcanonical :
      matrixSdpCanonicalPrimalBlockMatrix params model T *
          (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (hSlack : matrixSdpCanonicalSlackOperator params model T = 0) :
    MatrixSdpOptimalWitness params model T Z where
  primalTotalEqOne :=
    matrixSdpPrimalTotalEqOne_of_canonicalSlackOperator_eq_zero params model T hSlack
  dualFeasible := hdual
  strongDuality := hstrong
  complementarySlackness :=
    matrixSdpComplementarySlacknessDefect_of_canonical params model T Z hcanonical

/-- Package a paper-form optimal witness from an arbitrary feasible canonical
matrix with zero slack block.

The extracted polynomial diagonal blocks form the paper primal measurement.
The zero slack block supplies normalization; the canonical objective and
complementary-slackness equations are transported to the extracted
submeasurement. -/
theorem matrixSdpOptimalWitness_of_canonicalFeasibleSaturatedComplementarySlackness
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) =
        matrixSdpDualObjective model Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (hSlack : matrixSdpCanonicalDiagonalBlock params model X none = 0) :
    MatrixSdpOptimalWitness params model
      (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) Z := by
  refine matrixSdpOptimalWitness_of_canonicalSaturatedComplementarySlackness
    params model (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) Z
    hdual ?_ ?_ ?_
  · calc
      matrixSdpPrimalObjective params model
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX)
          = Complex.re (Matrix.trace
              (matrixSdpCanonicalObjectiveOperator params model * X)) := by
              exact (matrixSdpCanonicalObjective_trace_extractedPrimalSubmeasurement
                params model X hX).symm
      _ = matrixSdpDualObjective model Z := hstrong
  · exact matrixSdpCanonicalPrimalBlockMatrix_extracted_mul_dualSlack_of_canonical
      params model X hX Z hcanonical
  · rw [matrixSdpCanonicalSlackOperator_extractedPrimalSubmeasurement]
    exact hSlack

/-- Package the canonical block-SDP conclusions as the matrix-level statement
with an explicitly saturated slack block.

This is the statement form of
`matrixSdpOptimalWitness_of_canonicalSaturatedComplementarySlackness`.
It records the paper-form strong-duality output without adding the auxiliary
dominance condition used by the reduced abstract helper interface. -/
theorem matrixSdpStatementWithSlackness_of_canonicalSaturatedComplementarySlackness
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g)
    (hstrong :
      matrixSdpPrimalObjective params model T = matrixSdpDualObjective model Z)
    (hcanonical :
      matrixSdpCanonicalPrimalBlockMatrix params model T *
          (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (hSlack : matrixSdpCanonicalSlackOperator params model T = 0) :
    MatrixSdpStatementWithSlackness params model where
  witness :=
    ⟨T, Z,
      matrixSdpOptimalWitness_of_canonicalSaturatedComplementarySlackness
        params model T Z hdual hstrong hcanonical hSlack⟩

/-- Package the canonical block-SDP conclusions as the matrix-level statement
with zero slack block.

For a feasible canonical primal matrix `X`, the hypothesis
`X_none,none = 0` is exactly the saturated form of the paper's final slack
block assertion.  The theorem extracts the polynomial diagonal blocks and
records the resulting complete primal measurement and complementary-slackness
equations. -/
theorem matrixSdpStatementWithSlackness_of_canonicalFeasibleSaturatedComplementarySlackness
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) =
        matrixSdpDualObjective model Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (hSlack : matrixSdpCanonicalDiagonalBlock params model X none = 0) :
    MatrixSdpStatementWithSlackness params model where
  witness :=
    ⟨matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX, Z,
      matrixSdpOptimalWitness_of_canonicalFeasibleSaturatedComplementarySlackness
        params model X hX Z hdual hstrong hcanonical hSlack⟩

end MIPStarRE.LDT.SelfImprovement
