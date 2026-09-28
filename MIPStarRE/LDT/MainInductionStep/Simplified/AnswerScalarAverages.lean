import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerSliceDilation
import MIPStarRE.LDT.MainInductionStep.Simplified.ScalarAverages

/-!
# Averaged errors for answer-valued successors

The answer-valued restriction profile obeys the same three average bounds
as the ordinary successor profile. The scalar estimates therefore have
identical proofs.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement
open scoped BigOperators

/-- The mean recursive point-consistency error of answer-valued slices. -/
noncomputable def answerSuccessorAverageInductionError
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : AnswerSymStrat params.next ι}
    {eps delta gamma : Error}
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData
      params strategy eps delta gamma) : Error :=
  avgOver (uniformDistribution (Fq params))
    (fun x => simplifiedMainInductionError params
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x))

/-- The dilation error on a restricted answer-valued slice. -/
noncomputable def answerSuccessorSliceDilationError
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : AnswerSymStrat params.next ι}
    {eps delta gamma : Error}
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData
      params strategy eps delta gamma) (x : Fq params) : Error :=
  selfImprovementDilationError params
    (restrictionPkg.profile.axisParallel x)
    (restrictionPkg.profile.selfConsistency x)

/-- The mean local dilation error of answer-valued slices. -/
noncomputable def answerSuccessorAverageDilationError
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : AnswerSymStrat params.next ι}
    {eps delta gamma : Error}
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData
      params strategy eps delta gamma) : Error :=
  avgOver (uniformDistribution (Fq params))
    (answerSuccessorSliceDilationError params restrictionPkg)

/-- The restriction profile has nonnegative errors because each profile
entry bounds a nonnegative failure probability. -/
theorem answerSuccessorRestrictionProfile_nonneg
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params.next ι)
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) (x : Fq params) :
    0 ≤ profile.axisParallel x ∧
      0 ≤ profile.selfConsistency x ∧
      0 ≤ profile.diagonal x := by
  let restricted := xRestrictedAnswerSymStratOfAnswer params strategy x
  have hgood := profile.restrictedGood x
  have haxis : 0 ≤ restricted.axisParallelFailureProbability := by
    exact bipartiteConsError_nonneg restricted.state
      (uniformDistribution (AxisParallelTestSample params))
      (AnswerSymStrat.axisParallelPointAnswerFamily restricted)
      (AnswerSymStrat.axisParallelLineAnswerFamily restricted)
  have hself : 0 ≤ restricted.selfConsistencyFailureProbability := by
    exact bipartiteSSCError_nonneg restricted.state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas restricted.pointMeasurement)
  have hdiag : 0 ≤ restricted.diagonalFailureProbability :=
    answer_diagonalFailureProbability_nonneg params restricted
  exact ⟨haxis.trans hgood.axisParallelTest,
    hself.trans hgood.selfConsistencyTest,
    hdiag.trans hgood.diagonalLineTest⟩

/-- The averaged recursive error is bounded by the positive-degree
coefficient times the conditioning factor and ambient fractional-power sum. -/
theorem answerSuccessorAverageInductionError_le
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData params strategy eps delta gamma)
    (hd : 0 < params.d)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) (hgamma : 0 ≤ gamma) :
    answerSuccessorAverageInductionError params restrictionPkg ≤
      1000 * (params.d : Error) ^ (2 : ℕ) *
        (params.m : Error) ^ (4 : ℕ) *
        sliceConditioningLoss params *
        simplifiedPositiveErrorSum params eps delta gamma := by
  let 𝒟 := uniformDistribution (Fq params)
  let c := sliceConditioningLoss params
  have hc : 1 ≤ c := one_le_sliceConditioningLoss params
  have haxis := average_fractional_power_le_loss
    restrictionPkg.profile.axisParallel 32 (by norm_num)
    eps c
    (fun x => (answerSuccessorRestrictionProfile_nonneg params strategy restrictionPkg.profile x).1)
    heps hc (by simpa [𝒟, c, averageAnswerSuccessorRestrictedAxisParallelError] using
      restrictionPkg.axisAverageBound)
  have hself := average_fractional_power_le_loss
    restrictionPkg.profile.selfConsistency 32 (by norm_num)
    delta 1
    (fun x =>
      (answerSuccessorRestrictionProfile_nonneg params strategy
        restrictionPkg.profile x).2.1)
    hdelta le_rfl (by simpa [𝒟, averageAnswerSuccessorRestrictedSelfConsistencyError] using
      restrictionPkg.selfAverageBound)
  have hdiag := average_fractional_power_le_loss
    restrictionPkg.profile.diagonal 8 (by norm_num)
    gamma c
    (fun x =>
      (answerSuccessorRestrictionProfile_nonneg params strategy
        restrictionPkg.profile x).2.2)
    hgamma hc (by simpa [𝒟, c, averageAnswerSuccessorRestrictedDiagonalError] using
      restrictionPkg.diagonalAverageBound)
  have hratio : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  have hdeltaPow : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
    Real.rpow_nonneg hdelta _
  have hratioPow :
      0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
        (1 / (32 : Error)) := Real.rpow_nonneg hratio _
  have hself' :
      avgOver 𝒟
          (fun x => Real.rpow (restrictionPkg.profile.selfConsistency x)
            (1 / (32 : Error))) ≤
        c * Real.rpow delta (1 / (32 : Error)) := by
    exact hself.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hc) hdeltaPow])
  have hratio' :
      Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (32 : Error)) ≤
        c * Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (32 : Error)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hratioPow]
  have hsum :
      avgOver 𝒟 (fun x => simplifiedPositiveErrorSum params
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)) ≤
      c * simplifiedPositiveErrorSum params eps delta gamma := by
    simp only [simplifiedPositiveErrorSum, avgOver_add]
    rw [avgOver_uniform_const]
    nlinarith [haxis, hself', hratio', hdiag]
  have hcoef :
      0 ≤ 1000 * (params.d : Error) ^ (2 : ℕ) *
        (params.m : Error) ^ (4 : ℕ) := by positivity
  calc
    answerSuccessorAverageInductionError params restrictionPkg =
        (1000 * (params.d : Error) ^ (2 : ℕ) *
          (params.m : Error) ^ (4 : ℕ)) *
        avgOver 𝒟 (fun x => simplifiedPositiveErrorSum params
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)) := by
      simp [answerSuccessorAverageInductionError, simplifiedMainInductionError,
        simplifiedPositiveDegreeError, simplifiedPositiveErrorSum,
        Nat.ne_of_gt hd, avgOver_const_mul, 𝒟]
    _ ≤ (1000 * (params.d : Error) ^ (2 : ℕ) *
          (params.m : Error) ^ (4 : ℕ)) *
        (c * simplifiedPositiveErrorSum params eps delta gamma) :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = _ := by ring

/-- The mean dilation error is at most `200(m+1)` times the three
ambient square-root terms. -/
theorem answerSuccessorAverageDilationError_le
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData params strategy eps delta gamma)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    answerSuccessorAverageDilationError params restrictionPkg ≤
      200 * ((params.m + 1 : ℕ) : Error) *
        (Real.rpow eps (1 / (2 : Error)) +
          Real.rpow delta (1 / (2 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error))
            (1 / (2 : Error))) := by
  let 𝒟 := uniformDistribution (Fq params)
  let c := sliceConditioningLoss params
  have hc : 1 ≤ c := one_le_sliceConditioningLoss params
  have haxis := average_fractional_power_le_loss
    restrictionPkg.profile.axisParallel 2 (by norm_num)
    eps c
    (fun x => (answerSuccessorRestrictionProfile_nonneg params strategy restrictionPkg.profile x).1)
    heps hc (by simpa [𝒟, c, averageAnswerSuccessorRestrictedAxisParallelError] using
      restrictionPkg.axisAverageBound)
  have hself := average_fractional_power_le_loss
    restrictionPkg.profile.selfConsistency 2 (by norm_num)
    delta 1
    (fun x =>
      (answerSuccessorRestrictionProfile_nonneg params strategy
        restrictionPkg.profile x).2.1)
    hdelta le_rfl (by simpa [𝒟, averageAnswerSuccessorRestrictedSelfConsistencyError] using
      restrictionPkg.selfAverageBound)
  have hratio : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  have hdeltaPow : 0 ≤ Real.rpow delta (1 / (2 : Error)) :=
    Real.rpow_nonneg hdelta _
  have hratioPow :
      0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
        (1 / (2 : Error)) := Real.rpow_nonneg hratio _
  have hself' :
      avgOver 𝒟
          (fun x => Real.rpow (restrictionPkg.profile.selfConsistency x)
            (1 / (2 : Error))) ≤
        c * Real.rpow delta (1 / (2 : Error)) := by
    exact hself.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hc) hdeltaPow])
  have hratio' :
      Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (2 : Error)) ≤
        c * Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (2 : Error)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hratioPow]
  have hsum :
      avgOver 𝒟 (fun x =>
        Real.rpow (restrictionPkg.profile.axisParallel x) (1 / (2 : Error)) +
          Real.rpow (restrictionPkg.profile.selfConsistency x)
            (1 / (2 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error))
            (1 / (2 : Error))) ≤
      c * (Real.rpow eps (1 / (2 : Error)) +
        Real.rpow delta (1 / (2 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (2 : Error))) := by
    simp only [avgOver_add]
    rw [avgOver_uniform_const]
    nlinarith [haxis, hself', hratio']
  have hm : (0 : Error) < (params.m : Error) := by
    exact_mod_cast params.hm
  have hmc : (params.m : Error) * c = ((params.m + 1 : ℕ) : Error) := by
    dsimp [c, sliceConditioningLoss]
    field_simp
  calc
    answerSuccessorAverageDilationError params restrictionPkg =
        200 * (params.m : Error) *
          avgOver 𝒟 (fun x =>
            Real.rpow (restrictionPkg.profile.axisParallel x) (1 / (2 : Error)) +
              Real.rpow (restrictionPkg.profile.selfConsistency x)
                (1 / (2 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error))
                (1 / (2 : Error))) := by
      change avgOver 𝒟 (fun x => 200 * (params.m : Error) *
          (Real.rpow (restrictionPkg.profile.axisParallel x) (1 / (2 : Error)) +
            Real.rpow (restrictionPkg.profile.selfConsistency x)
              (1 / (2 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error))
              (1 / (2 : Error)))) = _
      exact avgOver_const_mul 𝒟 (200 * (params.m : Error)) _
    _ ≤ 200 * (params.m : Error) *
          (c * (Real.rpow eps (1 / (2 : Error)) +
            Real.rpow delta (1 / (2 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error))
              (1 / (2 : Error)))) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 200 * ((params.m : Error) * c) *
          (Real.rpow eps (1 / (2 : Error)) +
            Real.rpow delta (1 / (2 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error))
              (1 / (2 : Error))) := by ring
    _ = _ := by rw [hmc]

/-- Every local dilation error is nonnegative, hence so is its average. -/
theorem answerSuccessorAverageDilationError_nonneg
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData params strategy eps delta gamma) :
    0 ≤ answerSuccessorAverageDilationError params restrictionPkg := by
  unfold answerSuccessorAverageDilationError
  apply avgOver_nonneg
  intro x
  obtain ⟨haxis, hself, _⟩ :=
    answerSuccessorRestrictionProfile_nonneg params strategy restrictionPkg.profile x
  unfold answerSuccessorSliceDilationError
    MIPStarRE.LDT.SelfImprovement.selfImprovementDilationError
  have hratio : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  exact mul_nonneg (by positivity)
    (add_nonneg
      (add_nonneg (Real.rpow_nonneg haxis _) (Real.rpow_nonneg hself _))
      (Real.rpow_nonneg hratio _))


end MIPStarRE.LDT.MainInductionStep
