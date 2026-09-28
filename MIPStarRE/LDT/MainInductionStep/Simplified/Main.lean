import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerStrategyConversion
import MIPStarRE.LDT.MainInductionStep.Simplified.PositiveSuccessor

/-!
# Main induction theorem of the simplified low-degree proof

The public ordinary-strategy statement has no pasting attempt count.
Its degree-zero error is `δ + √(8mε)` and its positive-degree error is
`1000d²m⁴(ε^(1/32)+δ^(1/32)+(d/q)^(1/32)+γ^(1/8))`.
The answer-valued strong induction supplies the proof while keeping
the ordinary strategy's state and point measurement unchanged.

## References

- `blueprint/src/low_degree_simplified.tex`, `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:374-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

universe uι uF

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- `thm:main-induction` in the simplified blueprint. A good projective
symmetric strategy has a complete polynomial measurement consistent with
its point measurement at the displayed degree-dependent error.

The public statement keeps the original strategy and polynomial
measurement types and removes only the proof artifact `k` and its
exponential term. The direct degree-zero estimate is the separate
boundary case stated in the simplified blueprint. -/
theorem simplifiedMainInduction
    (params : Parameters) [FieldModel.{uF} params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (simplifiedMainInductionError params eps delta gamma) := by
  let answer := answerStrategyOfSymStrat params strategy
  have hanswer : answer.IsGood eps delta gamma :=
    answerStrategyOfSymStrat_isGood params strategy eps delta gamma hgood
  obtain ⟨G, hG⟩ :=
    simplifiedAnswerMainInduction.{uF, uι} params ι answer
      eps delta gamma hanswer
  exact ⟨G, by simpa [answer, answerStrategyOfSymStrat] using hG⟩

end MIPStarRE.LDT.MainInductionStep
