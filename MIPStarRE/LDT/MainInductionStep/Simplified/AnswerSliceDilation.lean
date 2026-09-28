import MIPStarRE.LDT.MainInductionStep.Simplified.SliceDilation
import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.AnswerValued

/-!
# Common-ancilla dilation of answer-valued successor slices

The answer-valued restriction theorem supplies good strategies on each
slice. The predecessor induction hypothesis supplies their polynomial
measurements. Dilation places the improved slice measurements on one
common enlarged local register.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:441-454`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement

universe uι uF

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The restricted profile and its three average bounds for an answer-valued
successor strategy. -/
structure SimplifiedAnswerSuccessorRestrictionData
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error) where
  /-- Slice-wise failure bounds. -/
  profile : AnswerSuccessorRestrictedFailureProfile params strategy
  /-- Averaged axis-parallel bound. -/
  axisAverageBound :
    averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
      sliceConditioningLoss params * eps
  /-- Averaged self-consistency bound. -/
  selfAverageBound :
    averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta
  /-- Averaged diagonal-line bound. -/
  diagonalAverageBound :
    averageAnswerSuccessorRestrictedDiagonalError params profile ≤
      sliceConditioningLoss params * gamma

/-- Package the established answer-valued restricted-probabilities theorem. -/
noncomputable def SimplifiedAnswerSuccessorRestrictionData.ofRestrictedProbabilities
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SimplifiedAnswerSuccessorRestrictionData params strategy eps delta gamma := by
  classical
  let h := (answerSuccessorRestrictedProbabilities
    params strategy eps delta gamma hgood).profileExists
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2.1, (Classical.choose_spec h).2.2⟩

/-- Recursive polynomial measurements for the answer-valued restricted slices. -/
structure SimplifiedAnswerSuccessorPerSliceData
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData
      params strategy eps delta gamma) where
  /-- Polynomial measurement on each restricted slice. -/
  sliceMeasurement : Fq params → Measurement (Polynomial params) ι
  /-- Recursive point consistency. -/
  pointConsistency : ∀ x,
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas
        (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
      (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
      (simplifiedMainInductionError params
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x))

/-- Apply the predecessor theorem to each answer-valued restricted slice. -/
noncomputable def SimplifiedAnswerSuccessorPerSliceData.ofInductionHypothesis
    (params : Parameters) [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData
      params strategy eps delta gamma)
    (hinduction : SimplifiedAnswerInductionHypothesis.{uF, uι} params) :
    SimplifiedAnswerSuccessorPerSliceData params strategy eps delta gamma
      restrictionPkg := by
  classical
  let output : ∀ x, SimplifiedAnswerInductionConclusion params
      (xRestrictedAnswerSymStratOfAnswer params strategy x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x) := by
    intro x
    exact hinduction ι (xRestrictedAnswerSymStratOfAnswer params strategy x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (restrictionPkg.profile.restrictedGood x)
  refine {
    sliceMeasurement := fun x => Classical.choose (output x)
    pointConsistency := ?_ }
  intro x
  exact Classical.choose_spec (output x)

/-- Common-ancilla self-improvement outputs for answer-valued slices. -/
structure SimplifiedAnswerSuccessorDilationData
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData
      params strategy eps delta gamma)
    (inductionPkg : SimplifiedAnswerSuccessorPerSliceData
      params strategy eps delta gamma restrictionPkg) where
  /-- Projective polynomial submeasurement on each slice. -/
  sliceMeasurement : Fq params →
    ProjSubMeas (Polynomial params) (ι × Option (Polynomial params))
  /-- Positive dual witness on each slice. -/
  sliceWitness : Fq params →
    MIPStarRE.Quantum.Op (ι × Option (Polynomial params))
  /-- The complete dilation conclusion on each slice. -/
  conclusion : ∀ x,
    DilationSelfImprovementConclusion params
      (answerSelfImprovementCarrier params
        (xRestrictedAnswerSymStratOfAnswer params strategy x))
      (sliceMeasurement x) (sliceWitness x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (simplifiedMainInductionError params
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x))

/-- Improve every answer-valued restricted slice on the common register. -/
noncomputable def SimplifiedAnswerSuccessorDilationData.ofInductionData
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData
      params strategy eps delta gamma)
    (inductionPkg : SimplifiedAnswerSuccessorPerSliceData
      params strategy eps delta gamma restrictionPkg) :
    SimplifiedAnswerSuccessorDilationData params strategy eps delta gamma
      restrictionPkg inductionPkg := by
  classical
  let output : ∀ x,
      ∃ H : ProjSubMeas (Polynomial params)
          (ι × Option (Polynomial params)),
        ∃ Z : MIPStarRE.Quantum.Op (ι × Option (Polynomial params)),
          DilationSelfImprovementConclusion params
            (answerSelfImprovementCarrier params
              (xRestrictedAnswerSymStratOfAnswer params strategy x)) H Z
            (restrictionPkg.profile.axisParallel x)
            (restrictionPkg.profile.selfConsistency x)
            (simplifiedMainInductionError params
              (restrictionPkg.profile.axisParallel x)
              (restrictionPkg.profile.selfConsistency x)
              (restrictionPkg.profile.diagonal x)) := by
    intro x
    let answerSlice := xRestrictedAnswerSymStratOfAnswer params strategy x
    let carrier := answerSelfImprovementCarrier params answerSlice
    have haxis : carrier.axisParallelFailureProbability ≤
        restrictionPkg.profile.axisParallel x := by
      have hfail : carrier.axisParallelFailureProbability =
          answerSlice.axisParallelFailureProbability := by
        unfold SymStrat.axisParallelFailureProbability
          AnswerSymStrat.axisParallelFailureProbability
          axisParallelPointAnswerFamily AnswerSymStrat.axisParallelPointAnswerFamily
          axisParallelLineAnswerFamily AnswerSymStrat.axisParallelLineAnswerFamily
        simp [carrier, answerSelfImprovementCarrier]
      simpa [hfail, answerSlice] using
        (restrictionPkg.profile.restrictedGood x).axisParallelTest
    have hself : carrier.selfConsistencyFailureProbability ≤
        restrictionPkg.profile.selfConsistency x := by
      have hfail : carrier.selfConsistencyFailureProbability =
          answerSlice.selfConsistencyFailureProbability := by
        unfold SymStrat.selfConsistencyFailureProbability
          AnswerSymStrat.selfConsistencyFailureProbability
        simp [carrier, answerSelfImprovementCarrier]
      simpa [hfail, answerSlice] using
        (restrictionPkg.profile.restrictedGood x).selfConsistencyTest
    have hcons : ConsRel carrier.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas carrier.pointMeasurement)
        (polynomialEvaluationFamily params
          (inductionPkg.sliceMeasurement x).toSubMeas)
        (simplifiedMainInductionError params
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)) := by
      simpa [carrier, answerSelfImprovementCarrier, answerSlice] using
        inductionPkg.pointConsistency x
    exact selfImprovementWithDilation_of_axisParallel_selfConsistency
      params carrier
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (simplifiedMainInductionError params
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x))
      haxis hself (inductionPkg.sliceMeasurement x) hcons
  refine {
    sliceMeasurement := fun x => Classical.choose (output x)
    sliceWitness := fun x => Classical.choose (Classical.choose_spec (output x))
    conclusion := ?_ }
  intro x
  exact Classical.choose_spec (Classical.choose_spec (output x))

end MIPStarRE.LDT.MainInductionStep
