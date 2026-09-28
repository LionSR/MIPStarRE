import MIPStarRE.LDT.MainInductionStep.Simplified.DegreeZeroGlobalDistance
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.BadLine

/-!
# Evaluation of the averaged constant-polynomial measurement

Postprocessing the averaged measurement by evaluation at any point
returns the average of the original point measurements. This identity
uses only that the constructed outcomes are constant polynomials.

## References

- `blueprint/src/low_degree_simplified.tex`, degree-zero proof of
  `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.Pasting

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Evaluating the averaged constant-polynomial measurement at any point
is exactly the average of the point measurements. -/
theorem degreeZeroPointAveragedMeasurement_evaluation
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (u : Point params) :
    polynomialEvaluationFamily params
        (degreeZeroPointAveragedMeasurement params strategy).toSubMeas u =
      averageIdxSubMeas (uniformDistribution (Point params))
        (fun v => (strategy.pointMeasurement v).toSubMeas)
        (uniformDistribution_weight_sum_le_one (Point params)) := by
  classical
  let 𝒟 := uniformDistribution (Point params)
  let A : IdxSubMeas (Point params) (Polynomial params) ι :=
    fun v => postprocess (strategy.pointMeasurement v).toSubMeas
      (Polynomial.const params)
  have hpointwise : ∀ v : Point params,
      evaluateAt params u (A v) = (strategy.pointMeasurement v).toSubMeas := by
    intro v
    change postprocess
      (postprocess (strategy.pointMeasurement v).toSubMeas
        (Polynomial.const params)) (fun g => g u) = _
    rw [SubMeas.postprocess_comp]
    have hmap : (fun a : Fq params => Polynomial.const params a u) = id := by
      funext a
      exact Polynomial.const_apply params a u
    rw [hmap]
    exact SubMeas.postprocess_id _
  change evaluateAt params u
      (averageIdxSubMeas 𝒟 A
        (uniformDistribution_weight_sum_le_one (Point params))) = _
  rw [evaluateAt_averageIdxSubMeas]
  congr 1
  funext v
  exact hpointwise v

end MIPStarRE.LDT.MainInductionStep
