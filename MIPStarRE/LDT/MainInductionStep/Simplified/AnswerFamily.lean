import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerScalarAverages
import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.Basic

/-!
# Family assumptions from answer-valued successor slices

The common-ancilla slice measurements satisfy completeness, point
consistency, strong self-consistency, and boundedness for simplified
pasting.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The concrete family of projective dilations and dual witnesses. -/
noncomputable def SimplifiedAnswerSuccessorDilationData.toIdxPolyFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      SimplifiedAnswerSuccessorPerSliceData params strategy eps delta gamma restrictionPkg)
    (data : SimplifiedAnswerSuccessorDilationData params strategy eps delta gamma
      restrictionPkg inductionPkg) :
    IdxPolyFamily params (ι × Option (Polynomial params)) where
  meas := data.sliceMeasurement
  witness := data.sliceWitness
  dominationTarget := fun x g =>
    IdxPolyFamily.averagedSlicePointEvaluationOperator
      (extendSymStrat params.next
      (answerSelfImprovementCarrier params.next strategy) (Polynomial params)) x g

/-- The dilated slices satisfy all four assumptions of simplified pasting,
with completeness error equal to the two averaged slice errors. -/
theorem SimplifiedAnswerSuccessorDilationData.pastingInputs
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      SimplifiedAnswerSuccessorPerSliceData params strategy eps delta gamma restrictionPkg)
    (data : SimplifiedAnswerSuccessorDilationData params strategy eps delta gamma
      restrictionPkg inductionPkg) :
    let extended := extendSymStrat params.next
      (answerSelfImprovementCarrier params.next strategy) (Polynomial params)
    let family := data.toIdxPolyFamily params strategy eps delta gamma
      restrictionPkg inductionPkg
    family.Complete extended.state
      (answerSuccessorAverageInductionError params restrictionPkg +
        answerSuccessorAverageDilationError params restrictionPkg) ∧
    family.ConsistentWithPoints extended
      (answerSuccessorAverageDilationError params restrictionPkg) ∧
    family.StronglySelfConsistent extended.state
      (answerSuccessorAverageDilationError params restrictionPkg) ∧
    IdxPolyFamily.SliceBoundednessInput extended family
      (answerSuccessorAverageDilationError params restrictionPkg) := by
  classical
  let extended := extendSymStrat params.next
      (answerSelfImprovementCarrier params.next strategy) (Polynomial params)
  let family := data.toIdxPolyFamily params strategy eps delta gamma
    restrictionPkg inductionPkg
  let σ : Fq params → Error := fun x => simplifiedMainInductionError params
    (restrictionPkg.profile.axisParallel x)
    (restrictionPkg.profile.selfConsistency x)
    (restrictionPkg.profile.diagonal x)
  let ζ : Fq params → Error := answerSuccessorSliceDilationError params restrictionPkg
  have hcomplete : ∀ x,
      CompletenessAtLeast extended.state
        ((family.meas x).toSubMeas.liftLeft) ((1 - σ x) - ζ x) := by
    intro x
    simpa [extended, family, σ, ζ, SimplifiedAnswerSuccessorDilationData.toIdxPolyFamily,
      answerSuccessorSliceDilationError, answerRestrictedCarrier,
      answerSelfImprovementCarrier, extendSymStrat] using
      (data.conclusion x).completeness
  have hpoint : ∀ x,
      ConsRel extended.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (xRestrictedAnswerSymStrat params extended x).pointMeasurement)
        (polynomialEvaluationFamily params (family.meas x).toSubMeas)
        (ζ x) := by
    intro x
    have hstate :
        (extendSymStrat params (answerSelfImprovementCarrier params
          (xRestrictedAnswerSymStratOfAnswer params strategy x))
          (Polynomial params)).state = extended.state := by
      simp [extended, extendSymStrat,
        answerSelfImprovementCarrier]
    have hpointEq :
        IdxProjMeas.toIdxSubMeas
          (extendSymStrat params (answerSelfImprovementCarrier params
          (xRestrictedAnswerSymStratOfAnswer params strategy x))
            (Polynomial params)).pointMeasurement =
        IdxProjMeas.toIdxSubMeas
          (xRestrictedAnswerSymStrat params extended x).pointMeasurement := by
      funext u
      rfl
    have h := (data.conclusion x).pointConsistency
    rw [hstate, hpointEq] at h
    simpa [family, ζ, SimplifiedAnswerSuccessorDilationData.toIdxPolyFamily,
      answerSuccessorSliceDilationError] using h
  have hself : ∀ x,
      SDDRel extended.state (uniformDistribution Unit)
        (constSubMeasFamily
          (leftPlacedSubMeas (ιB := ι × Option (Polynomial params))
            (family.meas x).toSubMeas))
        (constSubMeasFamily
          (rightPlacedSubMeas (ιA := ι × Option (Polynomial params))
            (family.meas x).toSubMeas))
        (ζ x) := by
    intro x
    have hstate :
        (extendSymStrat params (answerSelfImprovementCarrier params
          (xRestrictedAnswerSymStratOfAnswer params strategy x))
          (Polynomial params)).state = extended.state := by
      simp [extended, extendSymStrat,
        answerSelfImprovementCarrier]
    have hleft :
        IdxSubMeas.liftLeft
          (constSubMeasFamily (data.sliceMeasurement x).toSubMeas) =
        constSubMeasFamily
          (leftPlacedSubMeas (ιB := ι × Option (Polynomial params))
            (data.sliceMeasurement x).toSubMeas) := rfl
    have hright :
        IdxSubMeas.liftRight
          (constSubMeasFamily (data.sliceMeasurement x).toSubMeas) =
        constSubMeasFamily
          (rightPlacedSubMeas (ιA := ι × Option (Polynomial params))
            (data.sliceMeasurement x).toSubMeas) := rfl
    have h := (data.conclusion x).strongSelfConsistency
    rw [hstate, hleft, hright] at h
    simpa [family, ζ, SimplifiedAnswerSuccessorDilationData.toIdxPolyFamily,
      answerSuccessorSliceDilationError] using h
  have hresidual : ∀ x,
      tensorFailureExpectation extended.state
        (family.witness x) (family.meas x).toSubMeas ≤ ζ x := by
    intro x
    simpa [extended, family, ζ, SimplifiedAnswerSuccessorDilationData.toIdxPolyFamily,
      answerSuccessorSliceDilationError, answerRestrictedCarrier,
      answerSelfImprovementCarrier, extendSymStrat, tensorFailureExpectation,
      leftTensor_mul_rightTensor_eq_opTensor] using (data.conclusion x).residual
  have hdom : ∀ x : Fq params, ∀ g : Polynomial params,
      IdxPolyFamily.averagedSlicePointEvaluationOperator extended x g ≤
        family.witness x := by
    intro x g
    have heq : IdxPolyFamily.averagedSlicePointEvaluationOperator extended x g =
        averagedPointOperator params
          (extendSymStrat params
            (answerSelfImprovementCarrier params
          (xRestrictedAnswerSymStratOfAnswer params strategy x)) (Polynomial params)) g := by
      unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
        averagedPointOperator
      apply averageOperatorOverDistribution_congr
      intro u
      rfl
    rw [heq]
    exact (data.conclusion x).witness_domination g
  have hcomplete' := idxPolyFamily_complete_of_slice_bounds
    params extended.state family σ ζ hcomplete
  have hpoint' : family.ConsistentWithPoints extended
      (avgOver (uniformDistribution (Fq params)) ζ) := by
    refine ⟨⟨?_⟩⟩
    rw [family_answerRestrictedPointConsistencyError_eq_avg params extended family]
    exact avgOver_mono (uniformDistribution (Fq params)) _ _
      (fun x => (hpoint x).offDiagonalBound)
  have hself' := idxPolyFamily_stronglySelfConsistent_of_slice_bounds
    params extended.state family ζ
    (avgOver (uniformDistribution (Fq params)) ζ) hself le_rfl
  have hbound' := idxPolyFamily_sliceBoundednessInput_of_slice_bounds
    params extended family ζ
    (avgOver (uniformDistribution (Fq params)) ζ) hresidual le_rfl hdom
  simpa [answerSuccessorAverageInductionError, answerSuccessorAverageDilationError,
    σ, ζ, extended, family] using
    (show family.Complete extended.state
        (avgOver (uniformDistribution (Fq params)) σ +
          avgOver (uniformDistribution (Fq params)) ζ) ∧
      family.ConsistentWithPoints extended
        (avgOver (uniformDistribution (Fq params)) ζ) ∧
      family.StronglySelfConsistent extended.state
        (avgOver (uniformDistribution (Fq params)) ζ) ∧
      IdxPolyFamily.SliceBoundednessInput extended family
        (avgOver (uniformDistribution (Fq params)) ζ) from
      ⟨hcomplete', hpoint', hself', hbound'⟩)

end MIPStarRE.LDT.MainInductionStep
