import MIPStarRE.LDT.MainInductionStep.Simplified.Compression
import MIPStarRE.LDT.SelfImprovement.Simplified.AnswerStrategyExtension

/-!
# Compression for answer-valued ambient strategies

The polynomial measurement produced by enlarged-space answer-valued
pasting compresses to a complete measurement on the original register
with the same point-consistency error.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement

universe u v

/-- Compression of an enlarged polynomial measurement preserves its
consistency with the answer-valued strategy's original point measurement. -/
theorem compressed_answer_polynomial_consistency
    (params : Parameters) [FieldModel params.q]
    {Aux : Type v} [Fintype Aux] [DecidableEq Aux]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : AnswerSymStrat params ι)
    (T : Measurement (Polynomial params) (ι × Option Aux))
    (δ : Error)
    (hcons : ConsRel
      (extendAnswerSymStrat params strategy Aux).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas
        (extendAnswerSymStrat params strategy Aux).pointMeasurement)
      (polynomialEvaluationFamily params T.toSubMeas) δ) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params
        (compressMeasurementAtNone T).toSubMeas) δ := by
  constructor
  have heq := compressed_postprocessed_consistency
    strategy.state (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T (fun u g => g u)
  change bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun u => postprocess (compressMeasurementAtNone T).toSubMeas
        (fun g => g u)) ≤ δ
  rw [heq]
  exact hcons.offDiagonalBound

end MIPStarRE.LDT.MainInductionStep
