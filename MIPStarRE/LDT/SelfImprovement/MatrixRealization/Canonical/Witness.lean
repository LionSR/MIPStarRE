import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical

/-!
# Section 9 — Canonical matrix SDP witnesses

This module contains the optimal-witness structures extracted from the canonical
matrix SDP.  The preceding canonical module proves the block-diagonal algebra,
including the dual slack identities and saturation of the slack block.  This
file records the paper-form optimal pair and the measurement witnesses used by
the self-improvement comparison.

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
      T.effect g * Z = T.effect g * matrixAveragedPointOperator params model g

/-- Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`), with complementary slackness from
`eq:complementary-slackness` at line 179; matrix realization of
`SdpStatementWithSlackness`.

Matrix-level statement of the strong-duality output for the SDP.

This is the concrete matrix analogue of `SdpStatementWithSlackness`: it does
not assert that the explicit strict feasible witnesses are optimal.  Instead it
records the kind of optimal witness obtained from the paper's
Slater/strong-duality argument.  The feasible primal variables in the canonical
SDP remain submeasurements; this statement stores the selected saturated
optimal witness as a complete matrix measurement.

Grounded by: #1230. -/
structure MatrixSdpStatementWithSlackness (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) : Prop where
  witness :
    ∃ T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∃ Z : MatrixOperator model.space,
        MatrixSdpOptimalWitness params model T.toSubmeasurement Z

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

/-- The stored complementary-slackness equation, expressed through the named
matrix-level predicate. -/
theorem complementarySlacknessEquation {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) (g : Polynomial params) :
    matrixSdpComplementarySlacknessEquation params model T Z g := by
  exact h.complementarySlackness g

end MatrixSdpOptimalWitness

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
  obtain ⟨T, Z, hopt⟩ := h.witness
  refine ⟨T, Z, hopt.dualPositive, hopt.dualFeasible, hopt.strongDuality, ?_⟩
  intro g
  exact hopt.complementarySlacknessEquation g

end MatrixSdpStatementWithSlackness

end MIPStarRE.LDT.SelfImprovement
