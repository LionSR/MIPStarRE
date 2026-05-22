import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.Core
import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementAssembly.AnswerSlice
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds

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

universe uF uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

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

/-! ### Answer-valued successor restrictions

The preceding lemmas start from an ordinary successor strategy and build the
answer-valued slice profile used in the current Section 6 successor route.  For
the simultaneous answer-valued induction theorem, the successor strategy itself
has answer-valued diagonal measurements.  The next definitions and lemmas
record the corresponding restricted-probability theorem without replacing that
diagonal measurement by an ordinary low-degree realization.
-/

/-- Slice-wise error profile obtained by restricting an answer-valued successor
strategy.

This is the answer-valued analogue of `AnswerRestrictedFailureProfile`, but
with source strategy `AnswerSymStrat params.next ι` and slices
`xRestrictedAnswerSymStratOfAnswer`. -/
structure AnswerSuccessorRestrictedFailureProfile (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι) : Type where
  /-- The axis-parallel failure bound attached to each slice height. -/
  axisParallel : Fq params → Error
  /-- The self-consistency failure bound attached to each slice height. -/
  selfConsistency : Fq params → Error
  /-- The diagonal-line failure bound attached to each slice height. -/
  diagonal : Fq params → Error
  /-- Each answer-valued slice is good with the recorded parameters. -/
  restrictedGood :
    ∀ x,
      (xRestrictedAnswerSymStratOfAnswer params strategy x).IsGood
        (axisParallel x)
        (selfConsistency x)
        (diagonal x)

/-- Average restricted axis-parallel error over answer-valued successor slices. -/
noncomputable def averageAnswerSuccessorRestrictedAxisParallelError
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next ι}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.axisParallel

/-- Average restricted self-consistency error over answer-valued successor slices. -/
noncomputable def averageAnswerSuccessorRestrictedSelfConsistencyError
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next ι}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.selfConsistency

/-- Average restricted diagonal-line error over answer-valued successor slices. -/
noncomputable def averageAnswerSuccessorRestrictedDiagonalError
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next ι}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.diagonal

/-- Restricted-probabilities statement for an answer-valued successor strategy.

This is a Lean-only statement needed for the simultaneous answer-valued
induction route.  It has the same three averaged conclusions as the restricted
probabilities lemma (`\label{lem:restricted-probabilities}`), with
`xRestrictedAnswerSymStratOfAnswer` as the slice strategy. -/
structure AnswerSuccessorRestrictedProbabilitiesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error) : Prop where
  /-- There is a slice-wise answer-valued error profile realizing the three
  averaged restricted bounds. -/
  profileExists :
    ∃ profile : AnswerSuccessorRestrictedFailureProfile params strategy,
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
          sliceConditioningLoss params * eps ∧
        averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta ∧
        averageAnswerSuccessorRestrictedDiagonalError params profile ≤
          sliceConditioningLoss params * gamma

private lemma answerCarrier_axisParallelFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι) :
    (answerSelfImprovementCarrier params.next strategy).axisParallelFailureProbability =
      strategy.axisParallelFailureProbability := by
  rfl

private lemma answerCarrier_selfConsistencyFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι) :
    (answerSelfImprovementCarrier params.next strategy).selfConsistencyFailureProbability =
      strategy.selfConsistencyFailureProbability := by
  rfl

private lemma answerSuccessorRestricted_axisParallelFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability =
      (xRestrictedAnswerSymStrat params
        (answerSelfImprovementCarrier params.next strategy) x).axisParallelFailureProbability := by
  rfl

private lemma answerSuccessorRestricted_selfConsistencyFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).selfConsistencyFailureProbability =
      AnswerSymStrat.selfConsistencyFailureProbability
        (xRestrictedAnswerSymStrat params
          (answerSelfImprovementCarrier params.next strategy) x) := by
  rfl

/-- The weighted average of the answer-valued successor restricted
axis-parallel slice errors is bounded by the ambient answer-valued
axis-parallel test error. -/
lemma answerSuccessor_weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability)
      ≤ eps := by
  let carrier := answerSelfImprovementCarrier params.next strategy
  have hcarrier_good :
      carrier.IsGood eps delta carrier.diagonalFailureProbability := by
    refine ⟨?_, ?_, le_rfl⟩
    · simpa [carrier, answerCarrier_axisParallelFailureProbability_eq] using
        hgood.axisParallelTest
    · simpa [carrier, answerCarrier_selfConsistencyFailureProbability_eq] using
        hgood.selfConsistencyTest
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params carrier x).axisParallelFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerSuccessorRestricted_axisParallelFailureProbability_eq]
    _ ≤ eps :=
        answer_weighted_axisParallel_bound params carrier eps delta
          carrier.diagonalFailureProbability hcarrier_good

/-- Averaging the self-consistency defect over answer-valued successor
restrictions recovers the ambient answer-valued self-consistency defect. -/
lemma answerSuccessor_selfConsistencyRestrictedAverage_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          (xRestrictedAnswerSymStratOfAnswer params strategy x).selfConsistencyFailureProbability) =
      strategy.selfConsistencyFailureProbability := by
  let carrier := answerSelfImprovementCarrier params.next strategy
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          (xRestrictedAnswerSymStratOfAnswer params strategy x).selfConsistencyFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x =>
            (xRestrictedAnswerSymStrat params carrier x).selfConsistencyFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerSuccessorRestricted_selfConsistencyFailureProbability_eq]
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => (xRestrictedStrategy params carrier x).selfConsistencyFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerRestricted_selfConsistencyFailureProbability_eq]
    _ = carrier.selfConsistencyFailureProbability :=
        selfConsistencyRestrictedAverage_eq params carrier
    _ = strategy.selfConsistencyFailureProbability :=
        answerCarrier_selfConsistencyFailureProbability_eq params strategy

private def answerPointAppendProdEquiv (params : Parameters) [FieldModel params.q]
    (β : Type*) :
    Fq params × (Point params × β) ≃ Point params.next × β where
  toFun := fun xb => (appendPoint params xb.2.1 xb.1, xb.2.2)
  invFun := fun ub => (pointHeight params ub.1, (truncatePoint params ub.1, ub.2))
  left_inv := by
    rintro ⟨x, u, b⟩
    simp [truncatePoint_appendPoint, pointHeight_appendPoint]
  right_inv := by
    rintro ⟨u, b⟩
    exact Prod.ext ((CommutativityPoints.pointNextEquiv params).left_inv u) rfl

private lemma answerSuccessorRestrictedDiagonalSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (j : Fin params.m)
    (s : RestrictedDiagonalSample params j) :
    qBipartiteConsDefect strategy.state
      (AnswerSymStrat.diagonalPointAnswerFamily
        (xRestrictedAnswerSymStratOfAnswer params strategy x) j s)
      (AnswerSymStrat.diagonalLineAnswerFamily
        (xRestrictedAnswerSymStratOfAnswer params strategy x) j s) =
    qBipartiteConsDefect strategy.state
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2))
      (AnswerSymStrat.diagonalLineAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2)) := by
  have hdir :
      appendPoint params (extendRestrictedDirection j s.2) zeroCoord =
        extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 := by
    funext k
    by_cases hkm : k.1 < params.m
    · by_cases hk : k.1 ≤ j.1
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
        rfl
    · have hnotle : ¬ k.1 ≤ j.1 := by
          intro hk
          exact hkm (lt_of_le_of_lt hk j.2)
      simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hnotle]
      rfl
  have hline :
      DiagonalLine.appendAtHeight params
          { base := s.1, direction := extendRestrictedDirection j s.2 } x =
        ({ base := appendPoint params s.1 x,
           direction :=
             extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 } :
          DiagonalLine params.next) := by
    simp [DiagonalLine.appendAtHeight, hdir]
  simp [AnswerSymStrat.diagonalPointAnswerFamily,
    AnswerSymStrat.diagonalLineAnswerFamily, xRestrictedAnswerSymStratOfAnswer,
    restrictAnswerDiagonalAnswerMeasurement]
  simp [hline]
  rfl

private noncomputable def answerSuccessorDiagonalSliceIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (j : Fin params.m) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (RestrictedDiagonalSample params j))
    (AnswerSymStrat.diagonalPointAnswerFamily
      (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
    (AnswerSymStrat.diagonalLineAnswerFamily
      (xRestrictedAnswerSymStratOfAnswer params strategy x) j)

private noncomputable def answerSuccessorDiagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (j : Fin params.next.m) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (RestrictedDiagonalSample params.next j))
    (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
    (AnswerSymStrat.diagonalLineAnswerFamily strategy j)

private lemma answerSuccessorDiagonalIndexError_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (j : Fin params.next.m) :
    0 ≤ answerSuccessorDiagonalIndexError params strategy j := by
  unfold answerSuccessorDiagonalIndexError
  exact bipartiteConsError_nonneg strategy.state
    (uniformDistribution (RestrictedDiagonalSample params.next j))
    (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
    (AnswerSymStrat.diagonalLineAnswerFamily strategy j)

private lemma answerSuccessorDiagonalSliceIndexErrorAverage_eq_diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (j : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j) =
      answerSuccessorDiagonalIndexError params strategy (embedCoord params j) := by
  let g : RestrictedDiagonalSample params.next (embedCoord params j) → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (embedCoord params j) s)
      (AnswerSymStrat.diagonalLineAnswerFamily strategy (embedCoord params j) s)
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (RestrictedDiagonalSample params j))
            (fun s => g (appendPoint params s.1 x, s.2))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold answerSuccessorDiagonalSliceIndexError bipartiteConsError
              refine avgOver_congr _ _ _ ?_
              intro s
              simpa [g] using
                answerSuccessorRestrictedDiagonalSampleError_eq params strategy x j s
    _ = avgOver (uniformDistribution (Fq params × RestrictedDiagonalSample params j))
          (fun xs => g (appendPoint params xs.2.1 xs.1, xs.2.2)) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params)
                (β := RestrictedDiagonalSample params j)
                (f := fun x s => g (appendPoint params s.1 x, s.2))).symm
    _ = avgOver
          (uniformDistribution (RestrictedDiagonalSample params.next (embedCoord params j)))
          g := by
            simpa using
              (MIPStarRE.LDT.avgOver_uniform_equiv
                (e := answerPointAppendProdEquiv params (Fin (j.val + 1) → Fq params))
                (f := fun xs : Fq params × RestrictedDiagonalSample params j =>
                  g ((answerPointAppendProdEquiv params
                    (Fin (j.val + 1) → Fq params)) xs)))
    _ = answerSuccessorDiagonalIndexError params strategy (embedCoord params j) := by
            rfl

private lemma answerSuccessorDiagonalFailure_eq_average_indexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι) :
    avgOver (uniformDistribution (Fin params.next.m))
      (answerSuccessorDiagonalIndexError params strategy) =
      strategy.diagonalFailureProbability := by
  unfold answerSuccessorDiagonalIndexError AnswerSymStrat.diagonalFailureProbability
  calc
    avgOver (uniformDistribution (Fin params.next.m))
        (fun j =>
          bipartiteConsError strategy.state
            (uniformDistribution (RestrictedDiagonalSample params.next j))
            (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
            (AnswerSymStrat.diagonalLineAnswerFamily strategy j))
      = ∑ j : Fin params.next.m,
          (1 / (params.next.m : Error)) *
            bipartiteConsError strategy.state
              (uniformDistribution (RestrictedDiagonalSample params.next j))
              (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
              (AnswerSymStrat.diagonalLineAnswerFamily strategy j) := by
                simp [avgOver, uniformDistribution, Fintype.card_fin]
    _ = (1 / (params.next.m : Error)) *
          ∑ j : Fin params.next.m,
            bipartiteConsError strategy.state
              (uniformDistribution (RestrictedDiagonalSample params.next j))
              (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
              (AnswerSymStrat.diagonalLineAnswerFamily strategy j) := by
                symm
                rw [Finset.mul_sum]
    _ = strategy.diagonalFailureProbability := by
          rfl

private lemma answerSuccessorAverageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun j => answerSuccessorDiagonalIndexError params strategy (embedCoord params j)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun j => answerSuccessorDiagonalSliceIndexError params strategy x j)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold AnswerSymStrat.diagonalFailureProbability
                answerSuccessorDiagonalSliceIndexError
              calc
                (1 / (params.m : Error)) *
                    ∑ j : Fin params.m,
                      bipartiteConsError strategy.state
                        (uniformDistribution (RestrictedDiagonalSample params j))
                        (AnswerSymStrat.diagonalPointAnswerFamily
                          (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
                        (AnswerSymStrat.diagonalLineAnswerFamily
                          (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
                  = ∑ j : Fin params.m,
                      (1 / (params.m : Error)) *
                        bipartiteConsError strategy.state
                          (uniformDistribution (RestrictedDiagonalSample params j))
                          (AnswerSymStrat.diagonalPointAnswerFamily
                            (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
                          (AnswerSymStrat.diagonalLineAnswerFamily
                            (xRestrictedAnswerSymStratOfAnswer params strategy x) j) := by
                              rw [Finset.mul_sum]
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun j => answerSuccessorDiagonalSliceIndexError params strategy x j) := by
                              simp [avgOver, uniformDistribution, Fintype.card_fin,
                                answerSuccessorDiagonalSliceIndexError]
    _ = avgOver (uniformDistribution (Fq params × Fin params.m))
          (fun xj => answerSuccessorDiagonalSliceIndexError params strategy xj.1 xj.2) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params) (β := Fin params.m)
                (f := fun x j =>
                  answerSuccessorDiagonalSliceIndexError params strategy x j)).symm
    _ = avgOver (uniformDistribution (Fin params.m × Fq params))
          (fun jx => answerSuccessorDiagonalSliceIndexError params strategy jx.2 jx.1) := by
            simpa using
              (MIPStarRE.LDT.avgOver_uniform_equiv
                (e := Equiv.prodComm (Fq params) (Fin params.m))
                (f := fun xj : Fq params × Fin params.m =>
                  answerSuccessorDiagonalSliceIndexError params strategy xj.1 xj.2))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => avgOver (uniformDistribution (Fq params))
            (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j)) := by
            simpa using
              (avgOver_uniform_prod (α := Fin params.m) (β := Fq params)
                (f := fun j x =>
                  answerSuccessorDiagonalSliceIndexError params strategy x j))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => answerSuccessorDiagonalIndexError params strategy (embedCoord params j)) := by
            refine avgOver_congr _ _ _ ?_
            intro j
            exact answerSuccessorDiagonalSliceIndexErrorAverage_eq_diagonalIndexError
              params strategy j

/-- The weighted average of the answer-valued successor restricted diagonal
slice errors is bounded by the ambient answer-valued diagonal-line test error. -/
lemma answerSuccessor_weighted_diagonal_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      ≤ gamma := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fq params))
            (fun x =>
              AnswerSymStrat.diagonalFailureProbability
                (xRestrictedAnswerSymStratOfAnswer params strategy x)) := by
              rw [avgOver_const_mul]
    _ = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fin params.m))
            (fun j => answerSuccessorDiagonalIndexError params strategy (embedCoord params j)) := by
              rw [answerSuccessorAverageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
                params strategy]
    _ ≤ avgOver (uniformDistribution (Fin params.next.m))
          (answerSuccessorDiagonalIndexError params strategy) :=
        weighted_embedded_average_le_full_average params
          (f := answerSuccessorDiagonalIndexError params strategy)
          (hf := answerSuccessorDiagonalIndexError_nonneg params strategy)
    _ = strategy.diagonalFailureProbability :=
        answerSuccessorDiagonalFailure_eq_average_indexError params strategy
    _ ≤ gamma := hgood.diagonalLineTest

/-- Package the weighted answer-valued successor restricted-probability bounds
into the averaged statement. -/
lemma AnswerSuccessorRestrictedProbabilitiesStatement.ofWeightedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability)
        ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
        ≤ gamma) :
    AnswerSuccessorRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile : AnswerSuccessorRestrictedFailureProfile params strategy :=
    { axisParallel := fun x =>
        (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability
      selfConsistency := fun x =>
        (xRestrictedAnswerSymStratOfAnswer params strategy x).selfConsistencyFailureProbability
      diagonal := fun x =>
        (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability
      restrictedGood := by
        intro x
        exact ⟨le_rfl, le_rfl, le_rfl⟩ }
  have haxis_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageAnswerSuccessorRestrictedAxisParallelError params profile ≤ eps := by
    simpa [profile, averageAnswerSuccessorRestrictedAxisParallelError, avgOver_const_mul] using
      haxisWeightedBound
  have hdiag_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageAnswerSuccessorRestrictedDiagonalError params profile ≤ gamma := by
    simpa [profile, averageAnswerSuccessorRestrictedDiagonalError, avgOver_const_mul] using
      hdiagonalWeightedBound
  refine ⟨profile, ?_⟩
  refine ⟨weighted_bound_to_average params haxis_weighted_avg, ?_, ?_⟩
  · calc
      averageAnswerSuccessorRestrictedSelfConsistencyError params profile
        = avgOver (uniformDistribution (Fq params))
            (fun x =>
              AnswerSymStrat.selfConsistencyFailureProbability
                (xRestrictedAnswerSymStratOfAnswer params strategy x)) := by
            rfl
      _ = strategy.selfConsistencyFailureProbability := by
            exact answerSuccessor_selfConsistencyRestrictedAverage_eq params strategy
      _ ≤ delta := hgood.selfConsistencyTest
  · exact weighted_bound_to_average params hdiag_weighted_avg

/-- Answer-valued restricted-probabilities theorem for an answer-valued
successor strategy.

This is the restricted-probability input needed by a simultaneous
answer-valued proof of the main induction theorem.  It is a construction from
the answer-valued successor strategy's own goodness hypotheses, not an
additional theorem assumption. -/
lemma answerSuccessorRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    AnswerSuccessorRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  exact AnswerSuccessorRestrictedProbabilitiesStatement.ofWeightedBounds
    params strategy eps delta gamma hgood
    (answerSuccessor_weighted_axisParallel_bound params strategy eps delta gamma hgood)
    (answerSuccessor_weighted_diagonal_bound params strategy eps delta gamma hgood)

/-- Recursive predecessor conclusions for the answer-valued successor slices.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`, in the
answer-valued successor interface used by the simultaneous induction route.

This theorem is the formal content of the recursive call: from the
answer-valued restricted-probabilities theorem and the predecessor
answer-valued induction hypothesis, it obtains the main-induction conclusion
for every restricted slice.  The hypotheses `k ≥ 1` and
`400 * params.m * params.d ≤ k` are derived here from the nontrivial
successor branch, rather than being stored in a source theorem statement. -/
theorem answerSuccessorRestrictedSliceConclusions
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ profile : AnswerSuccessorRestrictedFailureProfile params strategy,
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
          sliceConditioningLoss params * eps ∧
        averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta ∧
        averageAnswerSuccessorRestrictedDiagonalError params profile ≤
          sliceConditioningLoss params * gamma ∧
        ∀ x,
          AnswerMainInductionConclusion params
            (xRestrictedAnswerSymStratOfAnswer params strategy x)
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)
            k := by
  classical
  let hrestricted :=
    answerSuccessorRestrictedProbabilities params strategy eps delta gamma hgood
  rcases hrestricted.profileExists with
    ⟨profile, haxisAverage, hselfAverage, hdiagonalAverage⟩
  have hk_pos : 1 ≤ k :=
    one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  have hk_pred : 400 * params.m * params.d ≤ k :=
    mainInductionSuccessorBound_pred params hk_next
  refine ⟨profile, haxisAverage, hselfAverage, hdiagonalAverage, ?_⟩
  intro x
  exact
    hinduction ι (xRestrictedAnswerSymStratOfAnswer params strategy x)
      (profile.axisParallel x)
      (profile.selfConsistency x)
      (profile.diagonal x)
      k (profile.restrictedGood x) hk_pos hk_pred

end MIPStarRE.LDT.MainInductionStep
