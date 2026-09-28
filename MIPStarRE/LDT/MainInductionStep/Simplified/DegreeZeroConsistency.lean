import MIPStarRE.LDT.MainInductionStep.Simplified.DegreeZeroPairConsistency
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.Averaging

/-!
# Degree-zero averaged measurement consistency

The point measurement averaged over an independent point has the same
consistency defect as the pairwise point comparison, up to Jensen's
inequality for the positive-part operation. Together with the global
distance estimate this proves the degree-zero answer-valued branch.

## References

- `blueprint/src/low_degree_simplified.tex`, degree-zero proof of
  `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.Pasting

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Averaging the right-hand point measurement cannot increase the
consistency defect beyond the average pairwise defect. -/
theorem degreeZero_pointConsistency_with_average_le
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun _ => averageIdxSubMeas (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (uniformDistribution_weight_sum_le_one (Point params))) ≤
      bipartiteConsError strategy.state (independentPointPair params)
        (fun uv => (strategy.pointMeasurement uv.1).toSubMeas)
        (fun uv => (strategy.pointMeasurement uv.2).toSubMeas) := by
  classical
  let 𝒟 := uniformDistribution (Point params)
  let M := averageIdxSubMeas 𝒟
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (uniformDistribution_weight_sum_le_one (Point params))
  have hpoint (u : Point params) :
      qBipartiteConsDefect strategy.state
          (strategy.pointMeasurement u).toSubMeas M ≤
        avgOver 𝒟 (fun v => qBipartiteConsDefect strategy.state
          (strategy.pointMeasurement u).toSubMeas
          (strategy.pointMeasurement v).toSubMeas) := by
    calc
      qBipartiteConsDefect strategy.state
          (strategy.pointMeasurement u).toSubMeas M =
        qBipartiteConsDefect strategy.state M
          (strategy.pointMeasurement u).toSubMeas :=
            qBipartiteConsDefect_symm_of_density_fixed
              strategy.state strategy.densityFixed _ _
      _ ≤ avgOver 𝒟 (fun v => qBipartiteConsDefect strategy.state
            (strategy.pointMeasurement v).toSubMeas
            (strategy.pointMeasurement u).toSubMeas) := by
          exact qBipartiteConsDefect_averageIdxSubMeas_left_le
            strategy.state 𝒟
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (strategy.pointMeasurement u).toSubMeas
            (uniformDistribution_weight_sum_le_one (Point params))
      _ = avgOver 𝒟 (fun v => qBipartiteConsDefect strategy.state
            (strategy.pointMeasurement u).toSubMeas
            (strategy.pointMeasurement v).toSubMeas) := by
          apply avgOver_congr
          intro v
          exact qBipartiteConsDefect_symm_of_density_fixed
            strategy.state strategy.densityFixed _ _
  unfold bipartiteConsError
  calc
    avgOver 𝒟 (fun u => qBipartiteConsDefect strategy.state
        (strategy.pointMeasurement u).toSubMeas M) ≤
      avgOver 𝒟 (fun u => avgOver 𝒟
        (fun v => qBipartiteConsDefect strategy.state
          (strategy.pointMeasurement u).toSubMeas
          (strategy.pointMeasurement v).toSubMeas)) :=
        avgOver_mono 𝒟 _ _ hpoint
    _ = avgOver (independentPointPair params)
        (fun uv => qBipartiteConsDefect strategy.state
          (strategy.pointMeasurement uv.1).toSubMeas
          (strategy.pointMeasurement uv.2).toSubMeas) := by
          simpa [𝒟, independentPointPair] using
            (avgOver_uniform_prod
              (fun u v => qBipartiteConsDefect strategy.state
                (strategy.pointMeasurement u).toSubMeas
                (strategy.pointMeasurement v).toSubMeas)).symm

/-- Direct degree-zero point consistency with error `δ + √(8mε)`. -/
theorem simplifiedAnswerDegreeZero
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : params.d = 0) :
    SimplifiedAnswerInductionConclusion params strategy eps delta gamma := by
  let G := degreeZeroPointAveragedMeasurement params strategy
  have hmean := degreeZero_pointConsistency_with_average_le params strategy
  have hpair := degreeZero_independentPointConsistency params strategy hd
    eps delta hgood.axisParallelTest hgood.selfConsistencyTest
  have hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas)
      (delta + Real.sqrt (8 * (params.m : Error) * eps)) := by
    constructor
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas) =
        bipartiteConsError strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (fun _ => averageIdxSubMeas (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (uniformDistribution_weight_sum_le_one (Point params))) := by
            unfold bipartiteConsError
            apply avgOver_congr
            intro u
            rw [degreeZeroPointAveragedMeasurement_evaluation]
            rfl
      _ ≤ bipartiteConsError strategy.state (independentPointPair params)
            (fun uv => (strategy.pointMeasurement uv.1).toSubMeas)
            (fun uv => (strategy.pointMeasurement uv.2).toSubMeas) := hmean
      _ ≤ delta + Real.sqrt (8 * (params.m : Error) * eps) :=
        hpair.offDiagonalBound
  refine ⟨G, ?_⟩
  simpa [simplifiedMainInductionError, hd, simplifiedDegreeZeroError] using hcons

end MIPStarRE.LDT.MainInductionStep
