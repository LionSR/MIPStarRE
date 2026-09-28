import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerScalarPowers
import MIPStarRE.LDT.MainInductionStep.Simplified.ScalarSuccessor

/-!
# Scalar absorption for the answer-valued successor

The answer-valued restriction profile obeys the same recurrence as the
ordinary profile, with the attempt count chosen internally.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.Pasting

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The error returned by internally parametrized simplified pasting is
at most the positive-degree main-induction error in dimension `m+1`. -/
theorem answerSuccessorPastingError_le_inductionError
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData params strategy eps delta gamma)
    (hd : 0 < params.d)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hgamma0 : 0 ≤ gamma)
    (hratio1 : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    simplifiedPastingPaperError params
        (simplifiedInductionAttemptCount params) eps delta gamma
        (answerSuccessorAverageInductionError params restrictionPkg +
          answerSuccessorAverageDilationError params restrictionPkg)
        (answerSuccessorAverageDilationError params restrictionPkg) ≤
      simplifiedMainInductionError params.next eps delta gamma := by
  let σ := answerSuccessorAverageInductionError params restrictionPkg
  let ζ := answerSuccessorAverageDilationError params restrictionPkg
  let s := pastingEighthSum params eps delta gamma ζ
  let S := simplifiedPositiveErrorSum params eps delta gamma
  have hM : (1 : Error) ≤ (params.m : Error) := by exact_mod_cast params.hm
  have hD : (1 : Error) ≤ (params.d : Error) := by exact_mod_cast hd
  have hS : 0 ≤ S := by
    dsimp [S, simplifiedPositiveErrorSum]
    positivity
  have hσ : σ ≤
      1000 * (params.d : Error) ^ (2 : ℕ) *
        (params.m : Error) ^ (4 : ℕ) *
        ((((params.m : Error) + 1) / (params.m : Error))) * S := by
    simpa [σ, S, sliceConditioningLoss, Nat.cast_add] using
      answerSuccessorAverageInductionError_le params strategy eps delta gamma
        restrictionPkg hd heps0 hdelta0 hgamma0
  have hζ : ζ ≤ 200 * ((params.m : Error) + 1) * S := by
    simpa [ζ, S, Nat.cast_add] using
      answerSuccessorAverageDilationError_le_positive_sum
        params strategy eps delta gamma restrictionPkg
        heps0 heps1 hdelta0 hdelta1 hgamma0 hratio1
  have hquarter := answerSuccessorAverageDilationError_le_quarter
    params strategy eps delta gamma restrictionPkg
    heps0 heps1 hdelta0 hdelta1 hratio1
  have hζ0 : 0 ≤ ζ := answerSuccessorAverageDilationError_nonneg
    params strategy eps delta gamma restrictionPkg
  have hs : s ≤
      4 * Real.rpow ((params.m : Error) + 1) (1 / (8 : Error)) * S := by
    simpa [s, S, Nat.cast_add] using
      pastingEighthSum_le_positive_sum params eps delta gamma ζ
        heps0 heps1 hdelta0 hdelta1 hgamma0 hζ0 hratio1
        (by simpa [ζ] using hquarter)
  have hbound := simplified_successor_coefficient_absorption
    (params.m : Error) (params.d : Error) S σ ζ s
    hM hD hS hσ hζ hs
  rw [simplifiedPastingPaperError_induction_eq
    params eps delta gamma (σ + ζ) ζ hd]
  change simplifiedInductionPaperError params eps delta gamma (σ + ζ) ζ ≤
    simplifiedMainInductionError params.next eps delta gamma
  simpa [simplifiedInductionPaperError, simplifiedMainInductionError,
    simplifiedPositiveDegreeError, simplifiedPositiveErrorSum,
    S, s, σ, ζ, Parameters.next, Nat.ne_of_gt hd,
    Nat.cast_add, add_assoc, add_comm, add_left_comm] using hbound

end MIPStarRE.LDT.MainInductionStep
