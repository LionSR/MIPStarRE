import MIPStarRE.LDT.MainInductionStep.Simplified.SliceDilation
import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.Basic

/-!
# Pasting inputs from the dilated slice family

The slice outputs share one enlarged local register. Averaging their
individual bounds yields the four family assumptions used by simplified
pasting, with the actual averaged errors retained for scalar bookkeeping.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:461-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The average recursive point-consistency error of the restricted slices. -/
noncomputable def simplifiedAverageInductionError
    (params : Parameters) [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error}
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma) : Error :=
  avgOver (uniformDistribution (Fq params))
    (fun x => simplifiedMainInductionError params
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x))

/-- The average local self-improvement error of the restricted slices. -/
noncomputable def simplifiedAverageDilationError
    (params : Parameters) [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error}
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma) : Error :=
  avgOver (uniformDistribution (Fq params))
    (simplifiedSliceDilationError params restrictionPkg)

/-- The concrete family of projective dilations and dual witnesses. -/
noncomputable def SimplifiedSliceDilationData.toIdxPolyFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      SimplifiedAnswerPerSliceData params strategy eps delta gamma restrictionPkg)
    (data : SimplifiedSliceDilationData params strategy eps delta gamma
      restrictionPkg inductionPkg) :
    IdxPolyFamily params (ι × Option (Polynomial params)) where
  meas := data.sliceMeasurement
  witness := data.sliceWitness
  dominationTarget := fun x g =>
    IdxPolyFamily.averagedSlicePointEvaluationOperator
      (extendSymStrat params.next strategy (Polynomial params)) x g

/-- The dilated slices satisfy all four assumptions of simplified pasting,
with completeness error equal to the two averaged slice errors. -/
theorem SimplifiedSliceDilationData.pastingInputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      SimplifiedAnswerPerSliceData params strategy eps delta gamma restrictionPkg)
    (data : SimplifiedSliceDilationData params strategy eps delta gamma
      restrictionPkg inductionPkg) :
    let extended := extendSymStrat params.next strategy (Polynomial params)
    let family := data.toIdxPolyFamily params strategy eps delta gamma
      restrictionPkg inductionPkg
    family.Complete extended.state
      (simplifiedAverageInductionError params restrictionPkg +
        simplifiedAverageDilationError params restrictionPkg) ∧
    family.ConsistentWithPoints extended
      (simplifiedAverageDilationError params restrictionPkg) ∧
    family.StronglySelfConsistent extended.state
      (simplifiedAverageDilationError params restrictionPkg) ∧
    IdxPolyFamily.SliceBoundednessInput extended family
      (simplifiedAverageDilationError params restrictionPkg) := by
  classical
  let extended := extendSymStrat params.next strategy (Polynomial params)
  let family := data.toIdxPolyFamily params strategy eps delta gamma
    restrictionPkg inductionPkg
  let σ : Fq params → Error := fun x => simplifiedMainInductionError params
    (restrictionPkg.profile.axisParallel x)
    (restrictionPkg.profile.selfConsistency x)
    (restrictionPkg.profile.diagonal x)
  let ζ : Fq params → Error := simplifiedSliceDilationError params restrictionPkg
  have hcomplete : ∀ x,
      CompletenessAtLeast extended.state
        ((family.meas x).toSubMeas.liftLeft) ((1 - σ x) - ζ x) := by
    intro x
    simpa [extended, family, σ, ζ, SimplifiedSliceDilationData.toIdxPolyFamily,
      simplifiedSliceDilationError, answerRestrictedCarrier,
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
        (extendSymStrat params (answerRestrictedCarrier params strategy x)
          (Polynomial params)).state = extended.state := by
      simp [extended, extendSymStrat, answerRestrictedCarrier,
        answerSelfImprovementCarrier]
    have hpointEq :
        IdxProjMeas.toIdxSubMeas
          (extendSymStrat params (answerRestrictedCarrier params strategy x)
            (Polynomial params)).pointMeasurement =
        IdxProjMeas.toIdxSubMeas
          (xRestrictedAnswerSymStrat params extended x).pointMeasurement := by
      funext u
      rfl
    have h := (data.conclusion x).pointConsistency
    rw [hstate, hpointEq] at h
    simpa [family, ζ, SimplifiedSliceDilationData.toIdxPolyFamily,
      simplifiedSliceDilationError] using h
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
        (extendSymStrat params (answerRestrictedCarrier params strategy x)
          (Polynomial params)).state = extended.state := by
      simp [extended, extendSymStrat, answerRestrictedCarrier,
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
    simpa [family, ζ, SimplifiedSliceDilationData.toIdxPolyFamily,
      simplifiedSliceDilationError] using h
  have hresidual : ∀ x,
      tensorFailureExpectation extended.state
        (family.witness x) (family.meas x).toSubMeas ≤ ζ x := by
    intro x
    simpa [extended, family, ζ, SimplifiedSliceDilationData.toIdxPolyFamily,
      simplifiedSliceDilationError, answerRestrictedCarrier,
      answerSelfImprovementCarrier, extendSymStrat, tensorFailureExpectation,
      leftTensor_mul_rightTensor_eq_opTensor] using (data.conclusion x).residual
  have hdom : ∀ x : Fq params, ∀ g : Polynomial params,
      IdxPolyFamily.averagedSlicePointEvaluationOperator extended x g ≤
        family.witness x := by
    intro x g
    have heq : IdxPolyFamily.averagedSlicePointEvaluationOperator extended x g =
        averagedPointOperator params
          (extendSymStrat params
            (answerRestrictedCarrier params strategy x) (Polynomial params)) g := by
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
  simpa [simplifiedAverageInductionError, simplifiedAverageDilationError,
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
