import MIPStarRE.LDT.MainInductionStep.Simplified.Statements
import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementAssembly.AnswerSlice

/-!
# Self-improvement of the answer-valued restricted slices

Every restricted slice is improved on the same enlarged local register,
indexed by the original register and `Option (Polynomial params)`. The
diagonal-line measurement is replaced by the established ordinary carrier;
self-improvement uses only its unchanged axis-parallel and point measurements.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:441-454`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The ordinary strategy carrier of an answer-valued restricted slice. Its
state, point measurement, and axis-parallel measurement are those of the
restricted answer-valued strategy. -/
noncomputable def answerRestrictedCarrier
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) : SymStrat params ι :=
  answerSelfImprovementCarrier params (xRestrictedAnswerSymStrat params strategy x)

/-- The local error of the dilation-based self-improvement step. -/
noncomputable def simplifiedSliceDilationError
    (params : Parameters) [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error}
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (x : Fq params) : Error :=
  selfImprovementDilationError params
    (restrictionPkg.profile.axisParallel x)
    (restrictionPkg.profile.selfConsistency x)

/-- Slice-indexed outputs of the common-ancilla self-improvement theorem. -/
structure SimplifiedSliceDilationData
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      SimplifiedAnswerPerSliceData params strategy eps delta gamma restrictionPkg) where
  /-- The projective polynomial submeasurement for each slice. -/
  sliceMeasurement : Fq params →
    ProjSubMeas (Polynomial params) (ι × Option (Polynomial params))
  /-- The positive dual witness for each slice. -/
  sliceWitness : Fq params →
    MIPStarRE.Quantum.Op (ι × Option (Polynomial params))
  /-- The full dilation conclusion for each restricted slice. -/
  conclusion : ∀ x,
    DilationSelfImprovementConclusion params
      (answerRestrictedCarrier params strategy x)
      (sliceMeasurement x) (sliceWitness x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (simplifiedMainInductionError params
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x))

/-- Apply dilation-based self-improvement to all restricted slices. -/
noncomputable def SimplifiedSliceDilationData.ofInductionData
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      SimplifiedAnswerPerSliceData params strategy eps delta gamma restrictionPkg) :
    SimplifiedSliceDilationData params strategy eps delta gamma restrictionPkg inductionPkg := by
  classical
  let output : ∀ x,
      ∃ H : ProjSubMeas (Polynomial params) (ι × Option (Polynomial params)),
        ∃ Z : MIPStarRE.Quantum.Op (ι × Option (Polynomial params)),
          DilationSelfImprovementConclusion params
            (answerRestrictedCarrier params strategy x) H Z
            (restrictionPkg.profile.axisParallel x)
            (restrictionPkg.profile.selfConsistency x)
            (simplifiedMainInductionError params
              (restrictionPkg.profile.axisParallel x)
              (restrictionPkg.profile.selfConsistency x)
              (restrictionPkg.profile.diagonal x)) := by
    intro x
    let answerSlice := xRestrictedAnswerSymStrat params strategy x
    let carrier := answerRestrictedCarrier params strategy x
    have haxis :
        carrier.axisParallelFailureProbability ≤
          restrictionPkg.profile.axisParallel x := by
      have hfail :
          carrier.axisParallelFailureProbability =
            answerSlice.axisParallelFailureProbability := by
        unfold SymStrat.axisParallelFailureProbability
          AnswerSymStrat.axisParallelFailureProbability
          axisParallelPointAnswerFamily AnswerSymStrat.axisParallelPointAnswerFamily
          axisParallelLineAnswerFamily AnswerSymStrat.axisParallelLineAnswerFamily
        simp [carrier, answerRestrictedCarrier, answerSelfImprovementCarrier, answerSlice]
      simpa [hfail] using (restrictionPkg.profile.restrictedGood x).axisParallelTest
    have hself :
        carrier.selfConsistencyFailureProbability ≤
          restrictionPkg.profile.selfConsistency x := by
      have hfail :
          carrier.selfConsistencyFailureProbability =
            answerSlice.selfConsistencyFailureProbability := by
        unfold SymStrat.selfConsistencyFailureProbability
          AnswerSymStrat.selfConsistencyFailureProbability
        simp [carrier, answerRestrictedCarrier, answerSelfImprovementCarrier, answerSlice]
      simpa [hfail] using (restrictionPkg.profile.restrictedGood x).selfConsistencyTest
    have hcons :
        ConsRel carrier.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas carrier.pointMeasurement)
          (polynomialEvaluationFamily params
            (inductionPkg.sliceMeasurement x).toSubMeas)
          (simplifiedMainInductionError params
            (restrictionPkg.profile.axisParallel x)
            (restrictionPkg.profile.selfConsistency x)
            (restrictionPkg.profile.diagonal x)) := by
      simpa [carrier, answerRestrictedCarrier, answerSelfImprovementCarrier,
        answerSlice] using inductionPkg.pointConsistency x
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
