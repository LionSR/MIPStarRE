import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerFamily
import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerPasting
import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerCompression
import MIPStarRE.LDT.MainInductionStep.Simplified.SuccessorPasting

/-!
# Simplified pasting for the answer-valued successor

The common-ancilla slice family is pasted using the genuine answer-valued
diagonal test. The attempt count is chosen internally, and compression
returns a polynomial measurement on the original local register.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:461-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement
open MIPStarRE.LDT.Pasting

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The answer-valued successor construction before the scalar recurrence
is absorbed into the target induction error. -/
theorem answerSuccessorPasting
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (restrictionPkg : SimplifiedAnswerSuccessorRestrictionData
      params strategy eps delta gamma)
    (inductionPkg : SimplifiedAnswerSuccessorPerSliceData
      params strategy eps delta gamma restrictionPkg)
    (data : SimplifiedAnswerSuccessorDilationData
      params strategy eps delta gamma restrictionPkg inductionPkg) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (simplifiedPastingPaperError params
          (simplifiedInductionAttemptCount params) eps delta gamma
          (answerSuccessorAverageInductionError params restrictionPkg +
            answerSuccessorAverageDilationError params restrictionPkg)
          (answerSuccessorAverageDilationError params restrictionPkg)) := by
  classical
  letI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  let answerExtended := extendAnswerSymStrat params.next strategy (Polynomial params)
  let carrier := answerSelfImprovementCarrier params.next strategy
  let extended := extendSymStrat params.next carrier (Polynomial params)
  let family := data.toIdxPolyFamily params strategy eps delta gamma
    restrictionPkg inductionPkg
  obtain ⟨hcomplete, hcons, hself, hbound⟩ :=
    data.pastingInputs params strategy eps delta gamma restrictionPkg inductionPkg
  have hgoodExtended : answerExtended.IsGood eps delta gamma :=
    extendAnswerSymStrat_isGood params.next strategy (Polynomial params)
      eps delta gamma hgood
  have hcompleteAnswer : family.Complete answerExtended.state
      (answerSuccessorAverageInductionError params restrictionPkg +
        answerSuccessorAverageDilationError params restrictionPkg) := by
    simpa [answerExtended, extended, carrier, extendAnswerSymStrat,
      extendSymStrat, answerSelfImprovementCarrier] using hcomplete
  have hconsAnswer : ConsRel answerExtended.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas answerExtended.pointMeasurement)
      family.evaluatedAtNextPoint
      (answerSuccessorAverageDilationError params restrictionPkg) := by
    simpa [answerExtended, extended, carrier, extendAnswerSymStrat,
      extendSymStrat, answerSelfImprovementCarrier] using hcons.pointConsistency
  have hselfAnswer : family.StronglySelfConsistent answerExtended.state
      (answerSuccessorAverageDilationError params restrictionPkg) := by
    simpa [answerExtended, extended, carrier, extendAnswerSymStrat,
      extendSymStrat, answerSelfImprovementCarrier] using hself
  have hboundAnswer : IdxPolyFamily.SliceBoundednessInput
      (answerSelfImprovementCarrier params.next answerExtended) family
      (answerSuccessorAverageDilationError params restrictionPkg) := by
    refine ⟨hbound.sliceOpPSD, ?_, ?_⟩
    · simpa [answerExtended, extended, carrier, extendAnswerSymStrat,
        extendSymStrat, answerSelfImprovementCarrier] using
        hbound.sliceBoundedness
    · intro x g
      simpa [IdxPolyFamily.averagedSlicePointEvaluationOperator,
        answerExtended, extended, carrier, extendAnswerSymStrat,
        extendSymStrat, answerSelfImprovementCarrier] using
        hbound.sliceDominatesAveragedPoint x g
  have hdk : params.d < simplifiedInductionAttemptCount params := by
    unfold simplifiedInductionAttemptCount
    have hm := params.hm
    have hm2 : 2 ≤ params.m + 1 := by omega
    have htwo : params.d < 2 * params.d := by omega
    exact htwo.trans_le (Nat.mul_le_mul_right params.d hm2)
  obtain ⟨T, hT⟩ := answerLdPastingSimplified params answerExtended family
    eps delta gamma
    (answerSuccessorAverageInductionError params restrictionPkg +
      answerSuccessorAverageDilationError params restrictionPkg)
    (answerSuccessorAverageDilationError params restrictionPkg)
    hgoodExtended hcompleteAnswer hconsAnswer hselfAnswer hboundAnswer
    hd (simplifiedInductionAttemptCount params) hdk
  refine ⟨compressMeasurementAtNone T, ?_⟩
  exact compressed_answer_polynomial_consistency params.next strategy T _ hT

end MIPStarRE.LDT.MainInductionStep
