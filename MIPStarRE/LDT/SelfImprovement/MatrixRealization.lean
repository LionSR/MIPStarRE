import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization
import MIPStarRE.LDT.SelfImprovement.Defs

/-!
# Section 9 — Matrix realization

Concrete finite-dimensional matrix realizations of the self-improvement SDP data.

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- A concrete finite-dimensional matrix realization of the SDP data. -/
structure MatrixSdpRealization (params : Parameters) [FieldModel params.q] where
  space : FiniteHilbertSpace
  state : PositiveMatrixState space
  pointMeasurement : Point params → MatrixSubmeasurement (Fq params) space

/-- The paper's strict-feasibility weight for the matrix SDP primal witness. -/
noncomputable def matrixSdpStrictPrimalWeight (params : Parameters)
    [FieldModel params.q] : Error :=
  sdpStrictPrimalWeight params

/-- The matrix-level strict-feasible primal witness
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`. -/
noncomputable def matrixSdpStrictPrimalSubmeasurement (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space where
  effect := (sdpStrictPrimalSubMeas (ι := model.space.carrier) params).outcome
  pos := (sdpStrictPrimalSubMeas (ι := model.space.carrier) params).outcome_pos
  sum_le_one := by
    simpa [(sdpStrictPrimalSubMeas (ι := model.space.carrier) params).sum_eq_total] using
      (sdpStrictPrimalSubMeas (ι := model.space.carrier) params).total_le_one

/-- The matrix-level strict-feasible primal witness has total mass
`(1/2) I`. -/
theorem matrixSdpStrictPrimalSubmeasurement_sum_effect (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∑ g : Polynomial params,
        (matrixSdpStrictPrimalSubmeasurement params model).effect g =
      ((1 / 2 : Error) • (1 : MatrixOperator model.space)) := by
  calc
    ∑ g : Polynomial params,
        (matrixSdpStrictPrimalSubmeasurement params model).effect g =
        (sdpStrictPrimalSubMeas (ι := model.space.carrier) params).total := by
          simpa [matrixSdpStrictPrimalSubmeasurement] using
            (sdpStrictPrimalSubMeas (ι := model.space.carrier) params).sum_eq_total
    _ = ((1 / 2 : Error) • (1 : MatrixOperator model.space)) :=
        sdpStrictPrimalSubMeas_total (ι := model.space.carrier) params

/-- The paper's matrix-level strict-feasible dual witness `Z = 2I`. -/
noncomputable def matrixSdpStrictDualWitness {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params) : MatrixOperator model.space :=
  (2 : Error) • (1 : MatrixOperator model.space)

/-- The matrix-level strict-feasible dual witness is positive semidefinite. -/
theorem matrixSdpStrictDualWitness_nonneg {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    0 ≤ matrixSdpStrictDualWitness model := by
  unfold matrixSdpStrictDualWitness
  exact smul_nonneg (by norm_num)
    (op_one_nonneg (d := model.space.carrier))

/-- The matrix-level strict-feasible dual witness dominates the identity. -/
theorem one_le_matrixSdpStrictDualWitness {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    (1 : MatrixOperator model.space) ≤ matrixSdpStrictDualWitness model := by
  calc
    (1 : MatrixOperator model.space) =
        (1 : Error) • (1 : MatrixOperator model.space) := by simp
    _ ≤ (2 : Error) • (1 : MatrixOperator model.space) :=
        smul_le_smul_of_nonneg_right
          (show (1 : Error) ≤ 2 by norm_num)
          (op_one_nonneg (d := model.space.carrier))

/-- The concrete operator `A^u_{g(u)}` entering the SDP average. -/
def matrixAveragedPointOperatorContribution (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) (u : Point params) : MatrixOperator model.space :=
  (model.pointMeasurement u).effect (g u)

/-- The concrete averaged operator `A_g = E_u A^u_{g(u)}`. -/
noncomputable def matrixAveragedPointOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (matrixAveragedPointOperatorContribution params model g)

/-- The concrete matrix average agrees with the paper-local uniform operator
average used elsewhere in the formalization. -/
theorem matrixAveragedPointOperator_eq_averageOperatorOverDistribution (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    matrixAveragedPointOperator params model g =
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (matrixAveragedPointOperatorContribution params model g) := by
  rfl

/-- The averaged point operator `A_g` is bounded by the identity. -/
theorem matrixAveragedPointOperator_le_one (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    matrixAveragedPointOperator params model g ≤ 1 := by
  let A : SubMeas Unit model.space.carrier :=
    averageUnitSubMeas (ι := model.space.carrier)
      (matrixAveragedPointOperatorContribution params model g)
      (fun u => by
        exact (model.pointMeasurement u).pos (g u))
      (fun u => by
        calc
          (model.pointMeasurement u).effect (g u)
              ≤ ∑ a : Fq params, (model.pointMeasurement u).effect a :=
                Finset.single_le_sum
                  (fun a _ => (model.pointMeasurement u).pos a)
                  (Finset.mem_univ (g u))
          _ ≤ 1 := (model.pointMeasurement u).sum_le_one)
  simpa [A, matrixAveragedPointOperator_eq_averageOperatorOverDistribution,
    matrixAveragedPointOperatorContribution, averageUnitSubMeas_outcome] using
      A.outcome_le_one ()

/-- The concrete primal contribution `T_g A_g`. -/
noncomputable def matrixSdpPrimalContributionOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  (T.effect g) * matrixAveragedPointOperator params model g

/-- The concrete primal objective `Σ_g Re Tr(T_g A_g)`. -/
noncomputable def matrixSdpPrimalObjective (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) : Error :=
  Complex.re (Matrix.trace (∑ g : Polynomial params,
    matrixSdpPrimalContributionOperator params model T g))

/-- The concrete dual objective `Re Tr(Z)`. -/
noncomputable def matrixSdpDualObjective {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) : Error :=
  Complex.re (Matrix.trace Z)

/-- The concrete dual slack operator `Z - A_g`. -/
noncomputable def matrixSdpDualSlackOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  Z - matrixAveragedPointOperator params model g

/-- The matrix-level strict-feasible dual witness `2I` dominates every averaged
point operator. -/
theorem matrixSdpStrictDualWitness_dualFeasible (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model (matrixSdpStrictDualWitness model) g := by
  intro g
  exact sub_nonneg.mpr
    (le_trans (matrixAveragedPointOperator_le_one params model g)
      (one_le_matrixSdpStrictDualWitness model))

/-- Matrix-level record of the explicit feasible bounds used in the SDP argument.

The uniform primal family has total `(1/2)I`, while the dual witness `2I` is
positive semidefinite, dominates the identity, and is dual feasible.  These are
the non-strict matrix inequalities currently recorded in Lean; the structure is
not an optimality statement and does not include complementary slackness. -/
structure MatrixSdpFeasibleBounds (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  primalTotalHalf :
    ∑ g : Polynomial params, T.effect g =
      ((1 / 2 : Error) • (1 : MatrixOperator model.space))
  dualPositive : 0 ≤ Z
  dualDominatesIdentity : (1 : MatrixOperator model.space) ≤ Z
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g

/-- The canonical explicit matrix feasible bounds used in the SDP argument. -/
theorem matrixSdpFeasibleBounds_canonical (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSdpFeasibleBounds params model
      (matrixSdpStrictPrimalSubmeasurement params model)
      (matrixSdpStrictDualWitness model) where
  primalTotalHalf := matrixSdpStrictPrimalSubmeasurement_sum_effect params model
  dualPositive := matrixSdpStrictDualWitness_nonneg model
  dualDominatesIdentity := one_le_matrixSdpStrictDualWitness model
  dualFeasible := matrixSdpStrictDualWitness_dualFeasible params model

/-- The concrete complementary-slackness defect `T_g (Z - A_g)`. -/
noncomputable def matrixSdpComplementarySlacknessDefect (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  (T.effect g) * matrixSdpDualSlackOperator params model Z g

/-- Matrix-level witness for an optimal SDP pair. -/
structure MatrixSdpOptimalWitness (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  primalTotalEqOne :
    ∑ g : Polynomial params, T.effect g = 1
  dualPositive : 0 ≤ Z
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g
  strongDuality :
    matrixSdpPrimalObjective params model T = matrixSdpDualObjective model Z
  complementarySlackness :
    ∀ g : Polynomial params,
      matrixSdpComplementarySlacknessDefect params model T Z g = 0

/-- Matrix-level statement of the strong-duality output for the SDP.

This is the concrete matrix analogue of `SdpStatementWithSlackness`: it does
not assert that the currently formalized reduced `sdp` witness is optimal.
Instead it records the kind of optimal witness obtained from the paper's
Slater/strong-duality argument. -/
structure MatrixSdpStatementWithSlackness (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) : Prop where
  witness :
    ∃ T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∃ Z : MatrixOperator model.space,
        MatrixSdpOptimalWitness params model T Z

/-- The concrete complementary-slackness equation `T_g Z = T_g A_g`. -/
def matrixSdpComplementarySlacknessEquation (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : Prop :=
  T.effect g * Z = T.effect g * matrixAveragedPointOperator params model g

namespace MatrixSdpOptimalWitness

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

/-- A raw point-indexed matrix outcome family used in the matrix `add-in-u` transfer. -/
abbrev MatrixIndexedPointOutcomeFamily (params : Parameters) [FieldModel params.q]
    (Outcome : Type*) (H : FiniteHilbertSpace) :=
  Point params → Outcome → MatrixOperator H

/-- The concrete sandwiched operator `A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def matrixSandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) (h : Polynomial params) : MatrixOperator model.space :=
  let Au := matrixAveragedPointOperatorContribution params model h u
  Au * (T.effect h) * Au

/-- The averaged concrete sandwiched operator `E_u A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def matrixAveragedSandwichedPolynomialOutcomeOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (h : Polynomial params) : MatrixOperator model.space :=
  matrixAverageOperator (fun u : Point params =>
    matrixSandwichedPolynomialOutcomeOperatorAt params model T u h)

/-- The matrix left-hand operator in `add-in-u`. -/
noncomputable def matrixAddInULeftOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MatrixOperator model.space :=
  ∑ ah ∈ addInUSelectionPairs params S u,
    (M u ah.1) * (H.effect ah.2)

/-- The matrix right-hand operator in `add-in-u`. -/
noncomputable def matrixAddInURightOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MatrixOperator model.space :=
  ∑ ah ∈ addInUSelectionPairs params S u,
    let Au := matrixAveragedPointOperatorContribution params model ah.2 u
    Au * (M u ah.1) * Au * (T.effect ah.2)

private noncomputable def matrixAddInUPointAverage (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (f : Point params → MatrixOperator model.space) : Error :=
  finiteAverage (fun u : Point params => Complex.re (matrixExpectation model.state (f u)))

/-- The matrix left-hand expectation in `add-in-u`. -/
noncomputable def matrixAddInULeftQuantity {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome) : Error :=
  matrixAddInUPointAverage params model (matrixAddInULeftOperatorAtPoint params model M H S)

/-- The matrix right-hand expectation in `add-in-u`. -/
noncomputable def matrixAddInURightQuantity {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome) : Error :=
  matrixAddInUPointAverage params model (matrixAddInURightOperatorAtPoint params model M T S)

/-- The concrete evaluated polynomial family `H_[h(u)=a]`. -/
noncomputable def matrixPolynomialEvaluationOutcomeOperatorAtPoint (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) (a : Fq params) : MatrixOperator model.space :=
  let evalFamily :=
    MIPStarRE.Quantum.Submeasurement.postprocess (M := H) (fun h => h u)
  evalFamily.effect a

/-- The concrete matched operator `Σ_a A^u_a H_[h(u)=a]`. -/
noncomputable def matrixHelperAgreementOperatorAtPoint (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) : MatrixOperator model.space :=
  ∑ a : Fq params,
    (model.pointMeasurement u).effect a *
      matrixPolynomialEvaluationOutcomeOperatorAtPoint params model H u a

/-- The concrete averaged matched operator `E_u Σ_a A^u_a H_[h(u)=a]`. -/
noncomputable def matrixHelperAgreementAverageOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixOperator model.space :=
  matrixAverageOperator (fun u : Point params =>
    matrixHelperAgreementOperatorAtPoint params model H u)

/-- The concrete helper boundedness gap `Re τ(ρ (Z - E_u Σ_a A^u_a H_[h(u)=a]))`. -/
noncomputable def matrixHelperBoundednessGap (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Error :=
  Complex.re (matrixExpectation model.state
    (Z - matrixHelperAgreementAverageOperator params model H))

/-- The concrete projective residual gap `Re τ(ρ (Z (I - Σ_h H_h)))`. -/
noncomputable def matrixProjectiveResidualGap (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Error :=
  let total := MIPStarRE.Quantum.Submeasurement.total H
  Complex.re (matrixExpectation model.state (Z * (1 - total)))

/-- Matrix-level version of the `add-in-u` transfer inequality. -/
structure MatrixAddInUTransferStatement {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (eps delta : Error) : Prop where
  transfer :
    ∀ S : AddInUSelection params Outcome,
      |matrixAddInULeftQuantity params model M H S -
          matrixAddInURightQuantity params model M T S| ≤
        addInUError params eps delta

end MIPStarRE.LDT.SelfImprovement
