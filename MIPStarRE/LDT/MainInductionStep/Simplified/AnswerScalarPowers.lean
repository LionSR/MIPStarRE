import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerScalarAverages
import MIPStarRE.LDT.MainInductionStep.Simplified.ScalarPowers

/-!
# Power bounds for answer-valued successor errors

The averaged answer-valued dilation error is absorbed into the same
positive-degree power sum as the ordinary successor error.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement

/-- The averaged dilation error is bounded by a quarter-power sum in
the small-error regime. -/
theorem answerSuccessorAverageDilationError_le_quarter
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData params strategy eps delta gamma)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hratio1 : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    answerSuccessorAverageDilationError params restrictionPkg ≤
      200 * ((params.m + 1 : ℕ) : Error) *
        (Real.rpow eps (1 / (4 : Error)) +
          Real.rpow delta (1 / (4 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error))
            (1 / (4 : Error))) := by
  have hratio0 : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  have hroot := answerSuccessorAverageDilationError_le params strategy eps delta gamma
    restrictionPkg heps0 hdelta0
  have heps := half_power_le_quarter_power eps heps0 heps1
  have hdelta := half_power_le_quarter_power delta hdelta0 hdelta1
  have hratio := half_power_le_quarter_power _ hratio0 hratio1
  have hcoef : 0 ≤ 200 * ((params.m + 1 : ℕ) : Error) := by positivity
  exact hroot.trans (mul_le_mul_of_nonneg_left (by linarith) hcoef)

/-- The averaged dilation error also fits directly below the positive-degree
induction sum. -/
theorem answerSuccessorAverageDilationError_le_positive_sum
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData params strategy eps delta gamma)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hgamma0 : 0 ≤ gamma)
    (hratio1 : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    answerSuccessorAverageDilationError params restrictionPkg ≤
      200 * ((params.m + 1 : ℕ) : Error) *
        simplifiedPositiveErrorSum params eps delta gamma := by
  have hratio0 : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  have hroot := answerSuccessorAverageDilationError_le params strategy eps delta gamma
    restrictionPkg heps0 hdelta0
  have heps : Real.rpow eps (1 / (2 : Error)) ≤
      Real.rpow eps (1 / (32 : Error)) :=
    Real.rpow_le_rpow_of_exponent_ge' heps0 heps1
      (by norm_num) (by norm_num)
  have hdelta : Real.rpow delta (1 / (2 : Error)) ≤
      Real.rpow delta (1 / (32 : Error)) :=
    Real.rpow_le_rpow_of_exponent_ge' hdelta0 hdelta1
      (by norm_num) (by norm_num)
  have hratio : Real.rpow ((params.d : Error) / (params.q : Error))
      (1 / (2 : Error)) ≤
      Real.rpow ((params.d : Error) / (params.q : Error))
        (1 / (32 : Error)) :=
    Real.rpow_le_rpow_of_exponent_ge' hratio0 hratio1
      (by norm_num) (by norm_num)
  have hinner :
      Real.rpow eps (1 / (2 : Error)) +
        Real.rpow delta (1 / (2 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (2 : Error)) ≤
      simplifiedPositiveErrorSum params eps delta gamma := by
    change eps ^ (1 / (2 : Error)) ≤ eps ^ (1 / (32 : Error)) at heps
    change delta ^ (1 / (2 : Error)) ≤ delta ^ (1 / (32 : Error)) at hdelta
    change (((params.d : Error) / (params.q : Error)) ^ (1 / (2 : Error))) ≤
      ((params.d : Error) / (params.q : Error)) ^ (1 / (32 : Error)) at hratio
    dsimp [simplifiedPositiveErrorSum]
    have hgamma := Real.rpow_nonneg hgamma0 (1 / (8 : Error))
    linarith
  exact hroot.trans
    (mul_le_mul_of_nonneg_left hinner (by positivity))


end MIPStarRE.LDT.MainInductionStep
