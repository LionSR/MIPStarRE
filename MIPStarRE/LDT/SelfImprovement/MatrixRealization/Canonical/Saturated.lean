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

/-- Move the canonical primal slack block into the distinguished polynomial block.

Paper origin: `references/ldt-paper/self_improvement.tex:177-190`.  The paper
passes from an optimal canonical block matrix to a saturated paper primal
measurement.  This block family implements the source-faithful completion step:
the `none` block is set to zero, and its positive mass is added to the fixed
polynomial block `sdpDistinguishedPolynomial params`.  This avoids the auxiliary
route which proves saturation from an additional bound `I ≤ Z`. -/
noncomputable def matrixSdpCanonicalSaturateSlackBlockFamily
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space
  | none => 0
  | some g =>
      matrixSdpCanonicalDiagonalBlock params model X (some g) +
        if g = sdpDistinguishedPolynomial params then
          matrixSdpCanonicalDiagonalBlock params model X none
        else 0

@[simp] theorem matrixSdpCanonicalSaturateSlackBlockFamily_none
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalSaturateSlackBlockFamily params model X none = 0 :=
  rfl

@[simp] theorem matrixSdpCanonicalSaturateSlackBlockFamily_some
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (g : Polynomial params) :
    matrixSdpCanonicalSaturateSlackBlockFamily params model X (some g) =
      matrixSdpCanonicalDiagonalBlock params model X (some g) +
        if g = sdpDistinguishedPolynomial params then
          matrixSdpCanonicalDiagonalBlock params model X none
        else 0 :=
  rfl

/-- The saturated canonical matrix obtained by completing the slack at the
distinguished polynomial block.

This is a source-faithful replacement for the Lean-only saturation route through
`I ≤ Z`: it changes only the primal matrix, setting the extra canonical slack
block to zero and adding that block to `sdpDistinguishedPolynomial params`. -/
noncomputable def matrixSdpCanonicalSaturateSlackBlockMatrix
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  matrixSdpCanonicalBlockDiagonal params model
    (matrixSdpCanonicalSaturateSlackBlockFamily params model X)

/-- The saturated canonical matrix has zero extra slack block. -/
@[simp] theorem matrixSdpCanonicalDiagonalBlock_saturateSlackBlockMatrix_none
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalSaturateSlackBlockMatrix params model X) none =
      0 := by
  simp [matrixSdpCanonicalSaturateSlackBlockMatrix]

/-- The polynomial blocks of the saturated canonical matrix agree with the
original diagonal blocks, except that the distinguished polynomial receives the
old `none` slack block. -/
@[simp] theorem matrixSdpCanonicalDiagonalBlock_saturateSlackBlockMatrix_some
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (g : Polynomial params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalSaturateSlackBlockMatrix params model X) (some g) =
      matrixSdpCanonicalDiagonalBlock params model X (some g) +
        if g = sdpDistinguishedPolynomial params then
          matrixSdpCanonicalDiagonalBlock params model X none
        else 0 := by
  simp [matrixSdpCanonicalSaturateSlackBlockMatrix]

/-- Feasibility is preserved by moving the `none` slack block into
`sdpDistinguishedPolynomial params`.

The proof uses only positivity of principal diagonal blocks of the original
feasible canonical matrix and the canonical equality constraint.  It is the
source-faithful saturation step corresponding to
`references/ldt-paper/self_improvement.tex:182-190`, avoiding any use of an
auxiliary dominance hypothesis `I ≤ Z`. -/
theorem matrixSdpCanonicalSaturateSlackBlockMatrix_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    MatrixSdpCanonicalPrimalFeasible params model
      (matrixSdpCanonicalSaturateSlackBlockMatrix params model X) where
  nonnegative := by
    rw [matrixSdpCanonicalSaturateSlackBlockMatrix]
    refine matrixSdpCanonicalBlockDiagonal_nonneg params model
      (matrixSdpCanonicalSaturateSlackBlockFamily params model X) ?_
    intro b
    cases b with
    | none =>
        simp
    | some g =>
        have hsome :
            0 ≤ matrixSdpCanonicalDiagonalBlock params model X (some g) :=
          matrixSdpCanonicalDiagonalBlock_nonneg params model hX.nonnegative (some g)
        by_cases hg : g = sdpDistinguishedPolynomial params
        · have hnone :
              0 ≤ matrixSdpCanonicalDiagonalBlock params model X none :=
            matrixSdpCanonicalDiagonalBlock_nonneg params model hX.nonnegative none
          simpa [hg] using add_nonneg hsome hnone
        · simpa [hg] using hsome
  constraintEqOne := by
    classical
    have hconstraint :
        matrixSdpCanonicalDiagonalBlock params model X none +
            ∑ g : Polynomial params,
              matrixSdpCanonicalDiagonalBlock params model X (some g) =
          1 := by
      simpa [matrixSdpCanonicalConstraintOperator, Fintype.sum_option] using
        hX.constraintEqOne
    rw [matrixSdpCanonicalSaturateSlackBlockMatrix,
      matrixSdpCanonicalConstraintOperator_blockDiagonal]
    rw [Fintype.sum_option]
    simp only [matrixSdpCanonicalSaturateSlackBlockFamily_none,
      matrixSdpCanonicalSaturateSlackBlockFamily_some, zero_add]
    rw [Finset.sum_add_distrib]
    have hsingle :
        (∑ g : Polynomial params,
            (if g = sdpDistinguishedPolynomial params then
              matrixSdpCanonicalDiagonalBlock params model X none
            else 0)) =
          matrixSdpCanonicalDiagonalBlock params model X none := by
      rw [Finset.sum_eq_single (sdpDistinguishedPolynomial params)]
      · simp
      · intro g _ hg
        simp [hg]
      · intro hnot
        simp at hnot
    rw [hsingle]
    simpa [add_comm, add_left_comm, add_assoc] using hconstraint

/-- Exact objective formula for source-faithful slack saturation.

After the `none` block is moved to `sdpDistinguishedPolynomial params`, the
canonical objective increases by the trace pairing of the old slack block with
the averaged point operator for that distinguished polynomial.  The `none` block
itself has objective coefficient zero, which is why this completion is the
paper-faithful alternative to deriving saturation through an auxiliary `I ≤ Z`
hypothesis. -/
theorem matrixSdpCanonicalObjective_trace_saturateSlackBlockMatrix
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalSaturateSlackBlockMatrix params model X)) =
      Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) +
        Complex.re (Matrix.trace
          (matrixAveragedPointOperator params model
              (sdpDistinguishedPolynomial params) *
            matrixSdpCanonicalDiagonalBlock params model X none)) := by
  classical
  rw [matrixSdpCanonicalObjectiveOperator,
    matrixSdpCanonicalSaturateSlackBlockMatrix]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul_left]
  simp only [Complex.re_sum, Fintype.sum_option,
    matrixSdpCanonicalObjectiveBlockFamily_none,
    matrixSdpCanonicalSaturateSlackBlockFamily_none, zero_mul, Matrix.trace_zero,
    zero_add, matrixSdpCanonicalObjectiveBlockFamily_some,
    matrixSdpCanonicalSaturateSlackBlockFamily_some]
  calc
    ∑ g : Polynomial params,
        Complex.re (Matrix.trace
          (matrixAveragedPointOperator params model g *
            (matrixSdpCanonicalDiagonalBlock params model X (some g) +
              if g = sdpDistinguishedPolynomial params then
                matrixSdpCanonicalDiagonalBlock params model X none
              else 0))) =
        ∑ g : Polynomial params,
          (Complex.re (Matrix.trace
              (matrixAveragedPointOperator params model g *
                matrixSdpCanonicalDiagonalBlock params model X (some g))) +
            Complex.re (Matrix.trace
              (matrixAveragedPointOperator params model g *
                (if g = sdpDistinguishedPolynomial params then
                  matrixSdpCanonicalDiagonalBlock params model X none
                else 0)))) := by
          refine Finset.sum_congr rfl ?_
          intro g _
          rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    _ = (∑ g : Polynomial params,
          Complex.re (Matrix.trace
            (matrixAveragedPointOperator params model g *
              matrixSdpCanonicalDiagonalBlock params model X (some g)))) +
        ∑ g : Polynomial params,
          Complex.re (Matrix.trace
            (matrixAveragedPointOperator params model g *
              (if g = sdpDistinguishedPolynomial params then
                matrixSdpCanonicalDiagonalBlock params model X none
              else 0))) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ g : Polynomial params,
          Complex.re (Matrix.trace
            (matrixAveragedPointOperator params model g *
              matrixSdpCanonicalDiagonalBlock params model X (some g)))) +
        Complex.re (Matrix.trace
          (matrixAveragedPointOperator params model
              (sdpDistinguishedPolynomial params) *
            matrixSdpCanonicalDiagonalBlock params model X none)) := by
          congr 1
          rw [Finset.sum_eq_single (sdpDistinguishedPolynomial params)]
          · simp
          · intro g _ hg
            simp [hg]
          · intro hnot
            simp at hnot

/-- Saturating the canonical slack block cannot decrease the canonical primal
objective.

The added objective term is nonnegative because the distinguished averaged point
operator is positive semidefinite and the original `none` block is a positive
principal block of the feasible canonical matrix. -/
theorem matrixSdpCanonicalObjective_trace_le_saturateSlackBlockMatrix
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
      Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalSaturateSlackBlockMatrix params model X)) := by
  rw [matrixSdpCanonicalObjective_trace_saturateSlackBlockMatrix]
  exact le_add_of_nonneg_right
    (MIPStarRE.Quantum.trace_mul_nonneg_of_nonneg
      (matrixAveragedPointOperator_nonneg params model
        (sdpDistinguishedPolynomial params))
      (matrixSdpCanonicalDiagonalBlock_nonneg params model hX.nonnegative none))

/-- Objective equality survives source-faithful slack saturation.

If a feasible canonical primal matrix and a dual-feasible `Z` have equal
objective values, then the saturated matrix obtained by moving the slack block
to `sdpDistinguishedPolynomial params` has the same objective value.  The proof
combines objective monotonicity of the completion with canonical weak duality;
it does not use the auxiliary dominance condition `I ≤ Z`. -/
theorem matrixSdpCanonicalSaturateSlackBlockMatrix_strongDuality
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
        matrixSdpDualObjective model Z) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalSaturateSlackBlockMatrix params model X)) =
      matrixSdpDualObjective model Z := by
  let Xsat := matrixSdpCanonicalSaturateSlackBlockMatrix params model X
  have hXsat : MatrixSdpCanonicalPrimalFeasible params model Xsat :=
    matrixSdpCanonicalSaturateSlackBlockMatrix_feasible params model X hX
  have hsat_le_dual :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * Xsat)) ≤
        matrixSdpDualObjective model Z :=
    matrixSdpCanonicalWeakDuality params model Xsat hXsat Z
      (matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible params model Z hdual)
  have hdual_le_sat :
      matrixSdpDualObjective model Z ≤
        Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * Xsat)) := by
    rw [← hstrong]
    exact matrixSdpCanonicalObjective_trace_le_saturateSlackBlockMatrix
      params model X hX
  exact le_antisymm hsat_le_dual hdual_le_sat

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
dominance condition used by one internal saturation route. -/
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
