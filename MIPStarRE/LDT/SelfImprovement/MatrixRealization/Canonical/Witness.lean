import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical

/-!
# Section 9 — Canonical matrix SDP witnesses

This module contains the optimal-witness packages extracted from the canonical
matrix SDP.  The preceding canonical module proves the block-diagonal algebra,
including the dual slack identities and saturation of the slack block under
the retained dominance hypothesis \(I \le Z\).  This file records the
paper-form optimal pair, the dominance-carrying successor package, and the
measurement witnesses used by the self-improvement bridge.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix

/-- Paper origin: `references/ldt-paper/self_improvement.tex:82-88`
(`\label{lem:sdp}`, `\label{eq:slater}`);
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex` (SDP gap).

Matrix-level witness for an optimal SDP pair. -/
structure MatrixSdpOptimalWitness (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  primalTotalEqOne :
    ∑ g : Polynomial params, T.effect g = 1
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g
  strongDuality :
    matrixSdpPrimalObjective params model T = matrixSdpDualObjective model Z
  complementarySlackness :
    ∀ g : Polynomial params,
      matrixSdpComplementarySlacknessDefect params model T Z g = 0

/-- Matrix-level optimal SDP witness together with the dominance condition
required by the reduced abstract helper interface.

Paper-gap note: `docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

The paper's dual SDP feasibility gives \(Z \ge A_g\).  The current reduced
abstract interface also asks for \(I \le Z\), because boundedness is expressed
against this dual operator.  This successor package records that extra
dominance for the same optimal dual witness, without changing the matrix
strong-duality statement below. -/
structure MatrixSdpOptimalWitnessWithDominance (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  toMatrixSdpOptimalWitness :
    MatrixSdpOptimalWitness params model T Z
  dualDominatesIdentity : (1 : MatrixOperator model.space) ≤ Z

/-- Package a paper-form optimal witness from the canonical block SDP
conclusions.

The hypotheses are the canonical pieces supplied by the finite-dimensional SDP
argument: paper dual feasibility, equality of the paper primal and dual
objectives, canonical complementary slackness, and the dominance condition
`I ≤ Z`.  The preceding saturation lemma supplies the missing primal
normalization, while the polynomial-block projection of canonical
complementary slackness supplies the defect equations
`T_g (Z - A_g) = 0`. -/
theorem matrixSdpOptimalWitnessWithDominance_of_canonicalComplementarySlackness
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
    (hOneLe : (1 : MatrixOperator model.space) ≤ Z) :
    MatrixSdpOptimalWitnessWithDominance params model T Z where
  toMatrixSdpOptimalWitness :=
    { primalTotalEqOne :=
        matrixSdpPrimalTotalEqOne_of_canonicalComplementarySlackness_of_one_le
          params model T Z hcanonical hOneLe
      dualFeasible := hdual
      strongDuality := hstrong
      complementarySlackness :=
        matrixSdpComplementarySlacknessDefect_of_canonical params model T Z hcanonical }
  dualDominatesIdentity := hOneLe

/-- Package an optimal paper-form witness directly from an arbitrary feasible
canonical primal matrix.

The theorem combines the two block-diagonal reductions: the extracted paper
submeasurement has the same objective as the canonical matrix, and canonical
complementary slackness is preserved when one replaces the canonical matrix by
the block-diagonal matrix determined by its diagonal blocks. -/
theorem matrixSdpOptimalWitnessWithDominance_of_canonicalFeasibleComplementarySlackness
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
    (hOneLe : (1 : MatrixOperator model.space) ≤ Z) :
    MatrixSdpOptimalWitnessWithDominance params model
      (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) Z := by
  refine matrixSdpOptimalWitnessWithDominance_of_canonicalComplementarySlackness
    params model (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) Z
    hdual ?_ ?_ hOneLe
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

/-- Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`), with complementary slackness from
`eq:complementary-slackness` at line 179; matrix realization of
`SdpStatementWithSlackness`.

Matrix-level statement of the strong-duality output for the SDP.

This is the concrete matrix analogue of `SdpStatementWithSlackness`: it does
not assert that the currently formalized reduced `sdp` witness is optimal.
Instead it records the kind of optimal witness obtained from the paper's
Slater/strong-duality argument.

Grounded by: #1230. -/
structure MatrixSdpStatementWithSlackness (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) : Prop where
  witness :
    ∃ T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∃ Z : MatrixOperator model.space,
        MatrixSdpOptimalWitness params model T Z

/-- Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`), with complementary slackness from
`eq:complementary-slackness` at line 179; matrix realization of
`SdpStatementWithSlackness` enriched with the `I ≤ Z` dominance step
(`references/ldt-paper/self_improvement.tex:200-201`,
`eq:Z-greater-than-A`).

Matrix-level strong-duality statement with the additional dominance
condition needed by the reduced abstract helper interface.

This is the matrix-side target for the downstream bridge into
`SelfImprovementHelperConclusionWithSlackness`: it keeps the same optimal pair
and complementary-slackness data as `MatrixSdpStatementWithSlackness`, and also
records \(I \le Z\) for the selected dual witness. -/
structure MatrixSdpStatementWithSlacknessAndDominance (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) : Prop where
  witness :
    ∃ T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∃ Z : MatrixOperator model.space,
        MatrixSdpOptimalWitnessWithDominance params model T Z

/-- Package the canonical block-SDP conclusions as the matrix-level statement
with the dominance hypothesis retained.

This is the statement form of
`matrixSdpOptimalWitnessWithDominance_of_canonicalComplementarySlackness`: the
canonical complementary-slackness equation supplies the primal normalization and
the defect-zero equations, while the remaining hypotheses record paper dual
feasibility, equality of the paper primal and dual objectives, and \(I \le Z\). -/
theorem matrixSdpStatementWithSlacknessAndDominance_of_canonicalComplementarySlackness
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
    (hOneLe : (1 : MatrixOperator model.space) ≤ Z) :
    MatrixSdpStatementWithSlacknessAndDominance params model where
  witness :=
    ⟨T, Z,
      matrixSdpOptimalWitnessWithDominance_of_canonicalComplementarySlackness
        params model T Z hdual hstrong hcanonical hOneLe⟩

/-- Package a matrix SDP statement with dominance from an arbitrary feasible
canonical primal matrix satisfying objective equality and complementary
slackness.

This statement-level theorem is the paper-facing block-diagonal reduction:
given the output of canonical strong duality, it extracts the paper primal
submeasurement and records the complete matrix-level slackness package needed
by the downstream self-improvement bridge. -/
theorem matrixSdpStatementWithSlacknessAndDominance_of_canonicalFeasibleComplementarySlackness
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
    (hOneLe : (1 : MatrixOperator model.space) ≤ Z) :
    MatrixSdpStatementWithSlacknessAndDominance params model where
  witness :=
    ⟨matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX, Z,
      matrixSdpOptimalWitnessWithDominance_of_canonicalFeasibleComplementarySlackness
        params model X hX Z hdual hstrong hcanonical hOneLe⟩

/-- The concrete complementary-slackness equation `T_g Z = T_g A_g`. -/
def matrixSdpComplementarySlacknessEquation (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : Prop :=
  T.effect g * Z = T.effect g * matrixAveragedPointOperator params model g

namespace MatrixSdpOptimalWitness

/-- The dual operator in an optimal matrix SDP witness is positive
semidefinite.  This follows from dual feasibility, because the averaged point
operators are positive. -/
theorem dualPositive {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) :
    0 ≤ Z :=
  matrixSdpDualPositive_of_dualFeasible params model Z h.dualFeasible

/-- An optimal matrix SDP witness whose primal total is the identity determines
a complete matrix measurement. -/
noncomputable def primalMeasurement {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) :
    MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne T.effect T.pos h.primalTotalEqOne

@[simp] theorem primalMeasurement_effect {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) (g : Polynomial params) :
    h.primalMeasurement.effect g = T.effect g :=
  rfl

/-- The defect-zero form of complementary slackness is the equation
`T_g Z = T_g A_g`. -/
theorem complementarySlacknessEquation {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) (g : Polynomial params) :
    matrixSdpComplementarySlacknessEquation params model T Z g := by
  have hzero :
      T.effect g * Z - T.effect g * matrixAveragedPointOperator params model g = 0 := by
    simpa [matrixSdpComplementarySlacknessDefect, matrixSdpDualSlackOperator,
      Matrix.mul_sub] using h.complementarySlackness g
  exact sub_eq_zero.mp hzero

end MatrixSdpOptimalWitness

namespace MatrixSdpStatementWithSlacknessAndDominance

/-- Forget the additional dominance condition and recover the matrix-level
strong-duality statement with complementary slackness. -/
theorem toMatrixSdpStatementWithSlackness {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (h : MatrixSdpStatementWithSlacknessAndDominance params model) :
    MatrixSdpStatementWithSlackness params model := by
  obtain ⟨T, Z, hopt⟩ := h.witness
  exact ⟨T, Z, hopt.toMatrixSdpOptimalWitness⟩

/-- A matrix strong-duality statement with dominance gives a complete primal
measurement, a dual operator satisfying \(I \le Z\), dual feasibility, equality
of objective values, and the complementary-slackness equations
`T_g Z = T_g A_g`. -/
theorem exists_measurement_witness {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (h : MatrixSdpStatementWithSlacknessAndDominance params model) :
    ∃ T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∃ Z : MatrixOperator model.space,
        0 ≤ Z ∧
        (1 : MatrixOperator model.space) ≤ Z ∧
        (∀ g : Polynomial params, 0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpPrimalObjective params model T.toSubmeasurement =
          matrixSdpDualObjective model Z ∧
        ∀ g : Polynomial params,
          T.effect g * Z = T.effect g * matrixAveragedPointOperator params model g := by
  obtain ⟨Tsub, Z, hopt⟩ := h.witness
  refine ⟨hopt.toMatrixSdpOptimalWitness.primalMeasurement, Z,
    hopt.toMatrixSdpOptimalWitness.dualPositive, hopt.dualDominatesIdentity,
    hopt.toMatrixSdpOptimalWitness.dualFeasible, ?_, ?_⟩
  · simpa [MatrixSdpOptimalWitness.primalMeasurement] using
      hopt.toMatrixSdpOptimalWitness.strongDuality
  · intro g
    simpa using hopt.toMatrixSdpOptimalWitness.complementarySlacknessEquation g

end MatrixSdpStatementWithSlacknessAndDominance

/-- Canonical block-SDP conclusions give the displayed paper-form measurement
and dual witness.

This is the measurement-level form of
`matrixSdpStatementWithSlacknessAndDominance_of_canonicalFeasibleComplementarySlackness`.
From an arbitrary feasible canonical primal matrix satisfying objective equality
and canonical complementary slackness, together with dual feasibility and
\(I \le Z\), it extracts a complete paper primal measurement and records the
dual feasibility, objective equality, and equations \(T_g Z = T_g A_g\). -/
theorem matrixSdpMeasurementWitness_of_canonicalFeasibleComplementarySlackness
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
    (hOneLe : (1 : MatrixOperator model.space) ≤ Z) :
    ∃ T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      0 ≤ Z ∧
      (1 : MatrixOperator model.space) ≤ Z ∧
      (∀ g : Polynomial params, 0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
      matrixSdpPrimalObjective params model T.toSubmeasurement =
        matrixSdpDualObjective model Z ∧
      ∀ g : Polynomial params,
        T.effect g * Z = T.effect g * matrixAveragedPointOperator params model g := by
  let Tsub := matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX
  let hopt :
      MatrixSdpOptimalWitnessWithDominance params model Tsub Z :=
    matrixSdpOptimalWitnessWithDominance_of_canonicalFeasibleComplementarySlackness
      params model X hX Z hdual hstrong hcanonical hOneLe
  refine ⟨hopt.toMatrixSdpOptimalWitness.primalMeasurement,
    hopt.toMatrixSdpOptimalWitness.dualPositive, hopt.dualDominatesIdentity,
    hopt.toMatrixSdpOptimalWitness.dualFeasible, ?_, ?_⟩
  · simpa [MatrixSdpOptimalWitness.primalMeasurement] using
      hopt.toMatrixSdpOptimalWitness.strongDuality
  · intro g
    simpa using hopt.toMatrixSdpOptimalWitness.complementarySlacknessEquation g

namespace MatrixSdpStatementWithSlackness

/-- A matrix strong-duality statement gives a complete primal measurement, a
dual operator, dual feasibility, equality of objective values, and the
complementary-slackness equations in the displayed `T_g Z = T_g A_g` form. -/
theorem exists_measurement_witness {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (h : MatrixSdpStatementWithSlackness params model) :
    ∃ T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∃ Z : MatrixOperator model.space,
        0 ≤ Z ∧
        (∀ g : Polynomial params, 0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpPrimalObjective params model T.toSubmeasurement =
          matrixSdpDualObjective model Z ∧
        ∀ g : Polynomial params,
          T.effect g * Z = T.effect g * matrixAveragedPointOperator params model g := by
  obtain ⟨Tsub, Z, hopt⟩ := h.witness
  refine ⟨hopt.primalMeasurement, Z, hopt.dualPositive, hopt.dualFeasible, ?_, ?_⟩
  · simpa [MatrixSdpOptimalWitness.primalMeasurement] using hopt.strongDuality
  · intro g
    simpa using hopt.complementarySlacknessEquation g

end MatrixSdpStatementWithSlackness

end MIPStarRE.LDT.SelfImprovement
