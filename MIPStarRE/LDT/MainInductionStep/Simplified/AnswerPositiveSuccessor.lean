import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerSuccessorPasting
import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerScalarSuccessor

/-!
# Positive-degree successor step for answer-valued strategies

The answer-valued restriction theorem, recursive predecessor conclusion,
common-ancilla self-improvement, simplified pasting, and scalar recurrence
are combined here. The pasting attempt count remains internal.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:374-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

universe uι uF

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Positive-degree answer-valued successor from the predecessor
answer-valued induction hypothesis. -/
theorem simplifiedAnswerPositiveSuccessor_ofRecursiveHypothesis
    (params : Parameters) [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (heps1 : eps ≤ 1) (hdelta1 : delta ≤ 1)
    (hratio1 : ((params.d : Error) / (params.q : Error)) ≤ 1)
    (hinduction : SimplifiedAnswerInductionHypothesis.{uF, uι} params) :
    SimplifiedAnswerInductionConclusion params.next strategy
      eps delta gamma := by
  classical
  have heps0 := answer_eps_nonneg_of_isGood params.next strategy hgood
  have hdelta0 := answer_delta_nonneg_of_isGood params.next strategy hgood
  have hgamma0 := answer_gamma_nonneg_of_isGood params.next strategy hgood
  let restrictionPkg : SimplifiedAnswerSuccessorRestrictionData
      params strategy eps delta gamma :=
    SimplifiedAnswerSuccessorRestrictionData.ofRestrictedProbabilities
      params strategy eps delta gamma hgood
  let inductionPkg : SimplifiedAnswerSuccessorPerSliceData
      params strategy eps delta gamma restrictionPkg :=
    SimplifiedAnswerSuccessorPerSliceData.ofInductionHypothesis
      params strategy eps delta gamma restrictionPkg hinduction
  let data : SimplifiedAnswerSuccessorDilationData
      params strategy eps delta gamma restrictionPkg inductionPkg :=
    SimplifiedAnswerSuccessorDilationData.ofInductionData
      params strategy eps delta gamma restrictionPkg inductionPkg
  obtain ⟨G, hG⟩ := answerSuccessorPasting params strategy eps delta gamma
    hgood hd restrictionPkg inductionPkg data
  refine ⟨G, ?_⟩
  exact ConsRel.mono
    (answerSuccessorPastingError_le_inductionError
      params strategy eps delta gamma restrictionPkg
      hd heps0 heps1 hdelta0 hdelta1 hgamma0 hratio1) hG

end MIPStarRE.LDT.MainInductionStep
