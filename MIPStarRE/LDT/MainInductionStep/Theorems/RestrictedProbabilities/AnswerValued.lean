import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.Core

/-!
# Section 6 -- Answer-Valued Restricted Probability Statement

This module contains the answer-valued form of the restricted-probability
bookkeeping for the main induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The answer-valued slice has the same axis-parallel failure probability as the
legacy restricted slice. -/
lemma answerRestricted_axisParallelFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability =
      (xRestrictedStrategy params strategy x).axisParallelFailureProbability := by
  rfl

/-- The answer-valued slice has the same self-consistency failure probability as
the legacy restricted slice. -/
lemma answerRestricted_selfConsistencyFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability =
      (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability := by
  rfl

/-- The answer-valued slice has the same verifier-visible diagonal failure
probability as the legacy restricted slice after evaluating line answers at the
base point. -/
lemma answerRestricted_diagonalFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability =
      (xRestrictedStrategy params strategy x).diagonalFailureProbability := by
  unfold AnswerSymStrat.diagonalFailureProbability RestrictedSymStrat.diagonalFailureProbability
  apply congrArg (fun s => (1 / (params.m : Error)) * s)
  refine Finset.sum_congr rfl ?_
  intro j _hj
  apply congrArg
  funext s
  let ℓ : DiagonalLine params :=
    { base := s.1, direction := extendRestrictedDirection j s.2 }
  change
    postprocess ((restrictDiagonalAnswerMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord) =
      postprocess ((restrictDiagonalMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLinePolynomial params => f zeroCoord)
  rw [restrictDiagonalAnswerMeasurement_postprocess_zero,
    restrictDiagonalMeasurement_postprocess_zero]

/-- The weighted average of the answer-valued restricted axis-parallel slice errors
is bounded by the ambient axis-parallel test error. -/
lemma answer_weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerRestricted_axisParallelFailureProbability_eq]
    _ ≤ eps := weighted_axisParallel_bound params strategy eps delta gamma hgood

/-- The weighted average of the answer-valued restricted diagonal slice errors is
bounded by the ambient diagonal-line test error. -/
lemma answer_weighted_diagonal_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerRestricted_diagonalFailureProbability_eq]
    _ ≤ gamma := weighted_diagonal_bound params strategy eps delta gamma hgood

/-- Data answer-valued weighted restricted axis/diagonal bounds into the public
answer-valued restricted-probabilities statement. -/
lemma AnswerRestrictedProbabilitiesStatement.ofWeightedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma) :
    AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile : AnswerRestrictedFailureProfile params strategy :=
    { axisParallel := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability
      selfConsistency := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability
      diagonal := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability
      restrictedGood := by
        intro x
        exact ⟨le_rfl, le_rfl, le_rfl⟩ }
  have haxis_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageAnswerRestrictedAxisParallelError params profile ≤ eps := by
    simpa [profile, averageAnswerRestrictedAxisParallelError, avgOver_const_mul] using
      haxisWeightedBound
  have hdiag_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageAnswerRestrictedDiagonalError params profile ≤ gamma := by
    simpa [profile, averageAnswerRestrictedDiagonalError, avgOver_const_mul] using
      hdiagonalWeightedBound
  refine ⟨profile, ?_⟩
  refine ⟨weighted_bound_to_average params haxis_weighted_avg, ?_, ?_⟩
  · calc
      averageAnswerRestrictedSelfConsistencyError params profile
        = avgOver (uniformDistribution (Fq params))
            (fun x =>
              (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            simp [profile,
              answerRestricted_selfConsistencyFailureProbability_eq]
      _ = strategy.selfConsistencyFailureProbability := by
            exact selfConsistencyRestrictedAverage_eq params strategy
      _ ≤ delta := hgood.selfConsistencyTest
  · exact weighted_bound_to_average params hdiag_weighted_avg

/-- Answer-valued version of `lem:restricted-probabilities`. -/
lemma answerRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  exact AnswerRestrictedProbabilitiesStatement.ofWeightedBounds
    params strategy eps delta gamma hgood
    (answer_weighted_axisParallel_bound params strategy eps delta gamma hgood)
    (answer_weighted_diagonal_bound params strategy eps delta gamma hgood)

end MIPStarRE.LDT.MainInductionStep
