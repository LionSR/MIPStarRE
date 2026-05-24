import MIPStarRE.LDT.Test.StrategyBiProjRoleAverage.Core

/-!
# Role-Register Averaging: Goodness Bound

This module packages the branch equalities into the three-times-error goodness
bound for the role-register symmetric strategy.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat

/-- The axis-parallel role-average branch of a two-space projective strategy is
nonnegative. -/
theorem axisParallelRoleAverage_nonneg
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) :
    0 ≤ strategy.axisParallelRoleAverage := by
  unfold ProjStrat.axisParallelRoleAverage
  apply div_nonneg
  · have hline : 0 ≤ strategy.axisParallelLineLeftPointRightFailureProbability := by
      unfold ProjStrat.axisParallelLineLeftPointRightFailureProbability
      exact bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params))
        (axisParallelLineAnswerFamilyA strategy)
        (axisParallelPointAnswerFamilyB strategy)
    have hpoint : 0 ≤ strategy.axisParallelPointLeftLineRightFailureProbability := by
      unfold ProjStrat.axisParallelPointLeftLineRightFailureProbability
      exact bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamilyA strategy)
        (axisParallelLineAnswerFamilyB strategy)
    linarith
  · norm_num

/-- The point-agreement branch of a two-space projective strategy is
nonnegative. -/
theorem pointAgreementFailureProbability_nonneg
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) :
    0 ≤ strategy.pointAgreementFailureProbability := by
  unfold ProjStrat.pointAgreementFailureProbability
  exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)

/-- The diagonal role-average branch of a two-space projective strategy is
nonnegative. -/
theorem diagonalRoleAverage_nonneg
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) :
    0 ≤ strategy.diagonalRoleAverage := by
  unfold ProjStrat.diagonalRoleAverage
  apply div_nonneg
  · unfold ProjStrat.diagonalLineLeftPointRightFailureProbability
    unfold ProjStrat.diagonalPointLeftLineRightFailureProbability
    have hline :
        0 ≤ (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            bipartiteConsError strategy.state
              (uniformDistribution (RestrictedDiagonalSample params j))
              (diagonalLineAnswerFamilyA strategy j)
              (diagonalPointAnswerFamilyB strategy j) := by
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro j _
        exact bipartiteConsError_nonneg strategy.state
          (uniformDistribution (RestrictedDiagonalSample params j))
          (diagonalLineAnswerFamilyA strategy j)
          (diagonalPointAnswerFamilyB strategy j)
    have hpoint :
        0 ≤ (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            bipartiteConsError strategy.state
              (uniformDistribution (RestrictedDiagonalSample params j))
              (diagonalPointAnswerFamilyA strategy j)
              (diagonalLineAnswerFamilyB strategy j) := by
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro j _
        exact bipartiteConsError_nonneg strategy.state
          (uniformDistribution (RestrictedDiagonalSample params j))
          (diagonalPointAnswerFamilyA strategy j)
          (diagonalLineAnswerFamilyB strategy j)
    linarith
  · norm_num

/-- The heterogeneous role-register symmetrization of a two-space projective
strategy is `(3ε, 3ε, 3ε)`-good whenever the original strategy passes the full
low individual degree test with error `ε`. -/
theorem roleRegisterSymmStrategy_is_good_three_mul
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    {strategy : ProjStrat params ιA ιB} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.roleRegisterSymmStrategy).IsGood (3 * eps) (3 * eps) (3 * eps) := by
  have haxis_nonneg : 0 ≤ strategy.axisParallelRoleAverage :=
    axisParallelRoleAverage_nonneg strategy
  have hpoint_nonneg : 0 ≤ strategy.pointAgreementFailureProbability :=
    pointAgreementFailureProbability_nonneg strategy
  have hdiag_nonneg : 0 ≤ strategy.diagonalRoleAverage :=
    diagonalRoleAverage_nonneg strategy
  have hmain :
      (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
        strategy.diagonalRoleAverage) / 3 ≤ eps := by
    simpa [ProjStrat.lowIndividualDegreeFailureProbability] using
      hpass.soundnessHypothesis
  have haxis : strategy.axisParallelRoleAverage ≤ 3 * eps :=
    (MIPStarRE.LDT.three_summand_bounds_of_average_le
      haxis_nonneg hpoint_nonneg hdiag_nonneg hmain).1
  have hpoint : strategy.pointAgreementFailureProbability ≤ 3 * eps :=
    (MIPStarRE.LDT.three_summand_bounds_of_average_le
      haxis_nonneg hpoint_nonneg hdiag_nonneg hmain).2.1
  have hdiag : strategy.diagonalRoleAverage ≤ 3 * eps :=
    (MIPStarRE.LDT.three_summand_bounds_of_average_le
      haxis_nonneg hpoint_nonneg hdiag_nonneg hmain).2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [roleRegisterSymmStrategy_axisParallel_eq_roleAverage strategy]
    exact haxis
  · rw [roleRegisterSymmStrategy_selfConsistency_eq_pointAgreement strategy]
    exact hpoint
  · rw [roleRegisterSymmStrategy_diagonal_eq_roleAverage strategy]
    exact hdiag


end ProjStrat

end MIPStarRE.LDT
