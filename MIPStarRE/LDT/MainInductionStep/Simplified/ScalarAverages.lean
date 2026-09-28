import MIPStarRE.LDT.MainInductionStep.Simplified.Family
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Averaging

/-!
# Averaged errors in the simplified induction

The restricted-probabilities lemma bounds the mean slice test errors.
Concavity of fractional powers converts those bounds into the mean
recursive and dilation errors used in the successor step.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:374-412`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement
open scoped BigOperators

/-- Jensen's inequality followed by the conditioning-loss estimate for a
fractional power. -/
theorem average_fractional_power_le_loss
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) (n : ℕ) (hn : 1 ≤ n)
    (x c : Error)
    (hf : ∀ a, 0 ≤ f a)
    (hx : 0 ≤ x) (hc : 1 ≤ c)
    (havg : avgOver (uniformDistribution α) f ≤ c * x) :
    avgOver (uniformDistribution α)
        (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
      c * Real.rpow x (1 / (n : Error)) := by
  have hnreal : (1 : Error) ≤ (n : Error) := by exact_mod_cast hn
  have hp0 : 0 ≤ (1 / (n : Error)) := by positivity
  have hp1 : (1 / (n : Error)) ≤ 1 := by
    exact (div_le_iff₀ (by positivity : (0 : Error) < n)).2 (by linarith)
  have hcx : 0 ≤ c * x := mul_nonneg (by linarith) hx
  have hcPow : Real.rpow c (1 / (n : Error)) ≤ c := by
    simpa using Real.rpow_le_rpow_of_exponent_le hc hp1
  calc
    avgOver (uniformDistribution α)
        (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
        Real.rpow (avgOver (uniformDistribution α) f)
          (1 / (n : Error)) :=
      avgOver_uniform_rpow_one_div_le_rpow_avg f n hn hf
    _ ≤ Real.rpow (c * x) (1 / (n : Error)) := by
      exact Real.rpow_le_rpow
        (avgOver_nonneg (uniformDistribution α) f hf) havg hp0
    _ = Real.rpow c (1 / (n : Error)) *
        Real.rpow x (1 / (n : Error)) :=
      Real.mul_rpow (by linarith) hx
    _ ≤ c * Real.rpow x (1 / (n : Error)) := by
      exact mul_le_mul_of_nonneg_right hcPow (Real.rpow_nonneg hx _)

/-- The four fractional-power terms in the positive-degree induction error. -/
noncomputable def simplifiedPositiveErrorSum
    (params : Parameters) (eps delta gamma : Error) : Error :=
  Real.rpow eps (1 / (32 : Error)) +
    Real.rpow delta (1 / (32 : Error)) +
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) +
    Real.rpow gamma (1 / (8 : Error))

/-- The restriction profile has nonnegative errors because each profile
entry bounds a nonnegative failure probability. -/
theorem answerRestrictionProfile_nonneg
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (profile : AnswerRestrictedFailureProfile params strategy) (x : Fq params) :
    0 ≤ profile.axisParallel x ∧
      0 ≤ profile.selfConsistency x ∧
      0 ≤ profile.diagonal x := by
  let restricted := xRestrictedAnswerSymStrat params strategy x
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

/-- The slice conditioning factor `(m+1)/m` is at least one. -/
theorem one_le_sliceConditioningLoss (params : Parameters) :
    (1 : Error) ≤ sliceConditioningLoss params := by
  unfold sliceConditioningLoss
  have hm : (0 : Error) < (params.m : Error) := by
    exact_mod_cast params.hm
  apply (one_le_div₀ hm).2
  exact_mod_cast Nat.le_succ params.m

/-- The averaged recursive error is bounded by the positive-degree
coefficient times the conditioning factor and ambient fractional-power sum. -/
theorem simplifiedAverageInductionError_le
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hd : 0 < params.d)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) (hgamma : 0 ≤ gamma) :
    simplifiedAverageInductionError params restrictionPkg ≤
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
    (fun x => (answerRestrictionProfile_nonneg params strategy restrictionPkg.profile x).1)
    heps hc (by simpa [𝒟, c, averageAnswerRestrictedAxisParallelError] using
      restrictionPkg.axisAverageBound)
  have hself := average_fractional_power_le_loss
    restrictionPkg.profile.selfConsistency 32 (by norm_num)
    delta 1
    (fun x => (answerRestrictionProfile_nonneg params strategy restrictionPkg.profile x).2.1)
    hdelta le_rfl (by simpa [𝒟, averageAnswerRestrictedSelfConsistencyError] using
      restrictionPkg.selfAverageBound)
  have hdiag := average_fractional_power_le_loss
    restrictionPkg.profile.diagonal 8 (by norm_num)
    gamma c
    (fun x => (answerRestrictionProfile_nonneg params strategy restrictionPkg.profile x).2.2)
    hgamma hc (by simpa [𝒟, c, averageAnswerRestrictedDiagonalError] using
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
    simplifiedAverageInductionError params restrictionPkg =
        (1000 * (params.d : Error) ^ (2 : ℕ) *
          (params.m : Error) ^ (4 : ℕ)) *
        avgOver 𝒟 (fun x => simplifiedPositiveErrorSum params
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)) := by
      simp [simplifiedAverageInductionError, simplifiedMainInductionError,
        simplifiedPositiveDegreeError, simplifiedPositiveErrorSum,
        Nat.ne_of_gt hd, avgOver_const_mul, 𝒟]
    _ ≤ (1000 * (params.d : Error) ^ (2 : ℕ) *
          (params.m : Error) ^ (4 : ℕ)) *
        (c * simplifiedPositiveErrorSum params eps delta gamma) :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = _ := by ring

/-- The mean dilation error is at most `200(m+1)` times the three
ambient square-root terms. -/
theorem simplifiedAverageDilationError_le
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    simplifiedAverageDilationError params restrictionPkg ≤
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
    (fun x => (answerRestrictionProfile_nonneg params strategy restrictionPkg.profile x).1)
    heps hc (by simpa [𝒟, c, averageAnswerRestrictedAxisParallelError] using
      restrictionPkg.axisAverageBound)
  have hself := average_fractional_power_le_loss
    restrictionPkg.profile.selfConsistency 2 (by norm_num)
    delta 1
    (fun x => (answerRestrictionProfile_nonneg params strategy restrictionPkg.profile x).2.1)
    hdelta le_rfl (by simpa [𝒟, averageAnswerRestrictedSelfConsistencyError] using
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
    simplifiedAverageDilationError params restrictionPkg =
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
theorem simplifiedAverageDilationError_nonneg
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma) :
    0 ≤ simplifiedAverageDilationError params restrictionPkg := by
  unfold simplifiedAverageDilationError
  apply avgOver_nonneg
  intro x
  obtain ⟨haxis, hself, _⟩ :=
    answerRestrictionProfile_nonneg params strategy restrictionPkg.profile x
  unfold simplifiedSliceDilationError
    MIPStarRE.LDT.SelfImprovement.selfImprovementDilationError
  have hratio : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  exact mul_nonneg (by positivity)
    (add_nonneg
      (add_nonneg (Real.rpow_nonneg haxis _) (Real.rpow_nonneg hself _))
      (Real.rpow_nonneg hratio _))

end MIPStarRE.LDT.MainInductionStep
