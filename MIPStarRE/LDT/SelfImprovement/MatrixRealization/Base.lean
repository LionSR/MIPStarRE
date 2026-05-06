import MIPStarRE.Quantum.FiniteMatrix
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

/-- The concrete averaged operator `A_g = E_u A^u_{g(u)}`.

This is defined through the project-wide distributional average
`averageOperatorOverDistribution` so that the submeasurement averaging lemmas
apply directly.  The operator is used only in this matrix realization layer. -/
noncomputable def matrixAveragedPointOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (matrixAveragedPointOperatorContribution params model g)

/-- The averaged point operator `A_g` is bounded by the identity. -/
theorem matrixAveragedPointOperator_le_one (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    matrixAveragedPointOperator params model g ≤ 1 := by
  let A : SubMeas Unit model.space.carrier :=
    averageUnitSubMeas (ι := model.space.carrier)
      (matrixAveragedPointOperatorContribution params model g)
      (fun u => (model.pointMeasurement u).pos (g u))
      (fun u => by
        calc
          (model.pointMeasurement u).effect (g u)
              ≤ ∑ a : Fq params, (model.pointMeasurement u).effect a :=
                Finset.single_le_sum
                  (fun a _ => (model.pointMeasurement u).pos a)
                  (Finset.mem_univ (g u))
          _ ≤ 1 := (model.pointMeasurement u).sum_le_one)
  simpa [A, matrixAveragedPointOperator, matrixAveragedPointOperatorContribution,
    averageUnitSubMeas_outcome] using
      A.outcome_le_one ()

/-- The averaged point operator `A_g` is positive semidefinite. -/
theorem matrixAveragedPointOperator_nonneg (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    0 ≤ matrixAveragedPointOperator params model g := by
  unfold matrixAveragedPointOperator averageOperatorOverDistribution
  exact Finset.sum_nonneg fun u _ =>
    smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
      ((model.pointMeasurement u).pos (g u))

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

/-- Dual feasibility already implies that the dual operator is positive
semidefinite, since every averaged point operator `A_g` is positive. -/
theorem matrixSdpDualPositive_of_dualFeasible (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    0 ≤ Z := by
  -- Any polynomial would suffice here; the distinguished one is only a
  -- convenient fixed element of the finite polynomial type.
  let g0 : Polynomial params := sdpDistinguishedPolynomial params
  have hAg_nonneg : 0 ≤ matrixAveragedPointOperator params model g0 :=
    matrixAveragedPointOperator_nonneg params model g0
  have hAg_le_Z : matrixAveragedPointOperator params model g0 ≤ Z :=
    sub_nonneg.mp (by simpa [matrixSdpDualSlackOperator] using hdual g0)
  exact hAg_nonneg.trans hAg_le_Z

/-- Matrix-level record of the explicit feasible bounds used in the SDP argument.

The uniform primal family has total `(1/2)I`, while the dual witness `2I`
dominates the identity and is dual feasible. Positivity of the dual witness is
derivable from dual feasibility and the positivity of the averaged point
operators. These are the non-strict matrix inequalities currently recorded in
Lean; the structure is not an optimality statement and does not include
complementary slackness. -/
structure MatrixSdpFeasibleBounds (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  primalTotalHalf :
    ∑ g : Polynomial params, T.effect g =
      ((1 / 2 : Error) • (1 : MatrixOperator model.space))
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
  dualDominatesIdentity := one_le_matrixSdpStrictDualWitness model
  dualFeasible := matrixSdpStrictDualWitness_dualFeasible params model


end MIPStarRE.LDT.SelfImprovement
