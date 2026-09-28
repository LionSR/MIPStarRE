import MIPStarRE.LDT.MainInductionStep.Simplified.DegreeZeroAveragedEvaluation

/-!
# Consistency between point measurements at independent points

The self-consistency test controls the same-point comparison. The
global squared-distance bound changes the second point to an
independent uniform point at a Cauchy--Schwarz cost of `√(8mε)`.

## References

- `blueprint/src/low_degree_simplified.tex`, degree-zero proof of
  `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.Preliminaries

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- For a complete point measurement, its consistency defect with
itself agrees with the point self-consistency defect. -/
theorem degreeZero_selfConsDefect_eq_consDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (u : Point params) :
    qBipartiteConsDefect strategy.state
        (strategy.pointMeasurement u).toSubMeas
        (strategy.pointMeasurement u).toSubMeas =
      qBipartiteSSCDefect strategy.state
        (strategy.pointMeasurement u).toSubMeas := by
  simp [qBipartiteConsDefect, qBipartiteSSCDefect,
    qBipartiteMatchMass, (strategy.pointMeasurement u).total_eq_one,
    leftTensor_one]

/-- The point measurements at two independent uniform points are
consistent with error `δ + √(8mε)` in degree zero. -/
theorem degreeZero_independentPointConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (hd : params.d = 0)
    (eps delta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta) :
    ConsRel strategy.state (independentPointPair params)
      (fun uv => (strategy.pointMeasurement uv.1).toSubMeas)
      (fun uv => (strategy.pointMeasurement uv.2).toSubMeas)
      (delta + Real.sqrt (8 * (params.m : Error) * eps)) := by
  classical
  let 𝒟 := independentPointPair params
  let A : IdxMeas (Point params × Point params) (Fq params) ι :=
    fun uv => (strategy.pointMeasurement uv.1).toMeasurement
  let B : IdxMeas (Point params × Point params) (Fq params) ι :=
    fun uv => (strategy.pointMeasurement uv.2).toMeasurement
  have hAA : ConsRel strategy.state 𝒟
      (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) delta := by
    constructor
    calc
      bipartiteConsError strategy.state 𝒟
          (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) =
        strategy.selfConsistencyFailureProbability := by
          unfold bipartiteConsError
          change avgOver (uniformDistribution (Point params × Point params))
              (fun uv => qBipartiteConsDefect strategy.state
                (strategy.pointMeasurement uv.1).toSubMeas
                (strategy.pointMeasurement uv.1).toSubMeas) = _
          calc
            avgOver (uniformDistribution (Point params × Point params))
                (fun uv => qBipartiteConsDefect strategy.state
                  (strategy.pointMeasurement uv.1).toSubMeas
                  (strategy.pointMeasurement uv.1).toSubMeas) =
              avgOver (uniformDistribution (Point params))
                (fun u => qBipartiteConsDefect strategy.state
                  (strategy.pointMeasurement u).toSubMeas
                  (strategy.pointMeasurement u).toSubMeas) := by
                exact avgOver_uniform_fst (α := Point params) (β := Point params)
                  (fun u => qBipartiteConsDefect strategy.state
                    (strategy.pointMeasurement u).toSubMeas
                    (strategy.pointMeasurement u).toSubMeas)
            _ = strategy.selfConsistencyFailureProbability := by
              unfold AnswerSymStrat.selfConsistencyFailureProbability
                bipartiteSSCError
              apply avgOver_congr
              intro u
              exact degreeZero_selfConsDefect_eq_consDefect params strategy u
      _ ≤ delta := hself
  have hBB : SDDRel strategy.state 𝒟
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
      (8 * (params.m : Error) * eps) := by
    change SDDRel strategy.state (independentPointPair params)
      (fun uv => rightPlacedSubMeas (ιA := ι)
        (strategy.pointMeasurement uv.1).toSubMeas)
      (fun uv => rightPlacedSubMeas (ιA := ι)
        (strategy.pointMeasurement uv.2).toSubMeas)
      (8 * (params.m : Error) * eps)
    exact degreeZero_globalPointDistance_le params strategy hd eps haxis
  have hpair := triangleSub_right strategy.state 𝒟 strategy.isNormalized
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    (IdxMeas.toIdxSubMeas A) A B delta
    (8 * (params.m : Error) * eps) hAA hBB
  change ConsRel strategy.state 𝒟
    (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B)
    (delta + Real.sqrt (8 * (params.m : Error) * eps))
  exact hpair

end MIPStarRE.LDT.MainInductionStep
