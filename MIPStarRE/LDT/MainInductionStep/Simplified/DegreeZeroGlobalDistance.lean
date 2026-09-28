import MIPStarRE.LDT.MainInductionStep.Simplified.DegreeZeroLocalDistance

/-!
# Global squared distance of degree-zero point measurements

The outcome-wise hypercube spectral inequality converts the local
`8ε` estimate into the independent-point `8mε` estimate used by the
degree-zero averaged measurement.

## References

- `blueprint/src/low_degree_simplified.tex`, equation
  `eq:d-zero-global-variance`.
- `references/ldt-paper/expansion.tex`, `lem:local-to-global`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The degree-zero point measurements have global squared distance at
most `8mε` on the right local register. -/
theorem degreeZero_globalPointDistance_le
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (hd : params.d = 0)
    (eps : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps) :
    SDDRel strategy.state (independentPointPair params)
      (fun uv => rightPlacedSubMeas (ιA := ι)
        (strategy.pointMeasurement uv.1).toSubMeas)
      (fun uv => rightPlacedSubMeas (ιA := ι)
        (strategy.pointMeasurement uv.2).toSubMeas)
      (8 * (params.m : Error) * eps) := by
  classical
  let A : Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun u a => rightTensor (ι₁ := ι) ((strategy.pointMeasurement u).outcome a)
  have hlocalRaw : avgOver (rerandomizeCoord params)
      (fun uv => qSDDCore strategy.state (A uv.1) (A uv.2)) ≤ 8 * eps := by
    calc
      avgOver (rerandomizeCoord params)
          (fun uv => qSDDCore strategy.state (A uv.1) (A uv.2)) =
        sddError strategy.state
          (uniformDistribution (RerandomizeCoordSample params))
          (fun s => rightPlacedSubMeas (ιA := ι)
            (strategy.pointMeasurement s.1.1).toSubMeas)
          (fun s => rightPlacedSubMeas (ιA := ι)
            (strategy.pointMeasurement
              (Function.update s.1.1 s.1.2 s.2)).toSubMeas) := by
            rw [avgOver_rerandomizeCoord_eq_uniform_sample]
            rfl
      _ ≤ 8 * eps :=
        (degreeZero_localPointDistance_le params strategy hd eps haxis).squaredDistanceBound
  have hglobal := outcomeFamily_localToGlobal params A strategy.state
  have hm0 : 0 ≤ (params.m : Error) := by positivity
  have hbound :
      avgOver (independentPointPair params)
          (fun uv => qSDDCore strategy.state (A uv.1) (A uv.2)) ≤
        (params.m : Error) * (8 * eps) :=
    hglobal.trans (mul_le_mul_of_nonneg_left hlocalRaw hm0)
  constructor
  change avgOver (independentPointPair params)
      (fun uv => qSDDCore strategy.state (A uv.1) (A uv.2)) ≤
    8 * (params.m : Error) * eps
  nlinarith [hbound]

end MIPStarRE.LDT.MainInductionStep
