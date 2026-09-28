import MIPStarRE.LDT.MainInductionStep.Simplified.DegreeZeroEdge

/-!
# Local squared distance of degree-zero point measurements

The two point-line consistency bounds on a hypercube edge give two
state-dependent distance bounds through the same line measurement.
The triangle inequality yields local squared distance at most `8ε`.

## References

- `blueprint/src/low_degree_simplified.tex`, degree-zero proof of
  `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:441-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.Preliminaries

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The degree-zero line test controls the local squared distance
between the point measurements at the endpoints of a hypercube edge. -/
theorem degreeZero_localPointDistance_le
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (hd : params.d = 0)
    (eps : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps) :
    SDDRel strategy.state
      (uniformDistribution (RerandomizeCoordSample params))
      (fun s => rightPlacedSubMeas (ιA := ι)
        (strategy.pointMeasurement s.1.1).toSubMeas)
      (fun s => rightPlacedSubMeas (ιA := ι)
        (strategy.pointMeasurement
          (Function.update s.1.1 s.1.2 s.2)).toSubMeas)
      (8 * eps) := by
  classical
  let 𝒟 := uniformDistribution (RerandomizeCoordSample params)
  let A : IdxMeas (RerandomizeCoordSample params) (Fq params) ι :=
    fun s => (strategy.pointMeasurement s.1.1).toMeasurement
  let B : IdxMeas (RerandomizeCoordSample params) (Fq params) ι :=
    fun s => (strategy.pointMeasurement
      (Function.update s.1.1 s.1.2 s.2)).toMeasurement
  let C : IdxMeas (RerandomizeCoordSample params) (Fq params) ι :=
    fun s => (ProjMeas.postprocess
      (strategy.axisParallelMeasurement
        { base := s.1.1, direction := s.1.2 })
      (· zeroCoord)).toMeasurement
  have hAC : ConsRel strategy.state 𝒟
      (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas C) eps := by
    change ConsRel strategy.state 𝒟
      (fun s => (strategy.pointMeasurement s.1.1).toSubMeas)
      (fun s => AnswerSymStrat.axisParallelLineAnswerFamily strategy s.1) eps
    exact degreeZero_axisConsistency_at_startEndpoint params strategy eps haxis
  have hBC : ConsRel strategy.state 𝒟
      (IdxMeas.toIdxSubMeas B) (IdxMeas.toIdxSubMeas C) eps := by
    change ConsRel strategy.state 𝒟
      (fun s => (strategy.pointMeasurement
        (Function.update s.1.1 s.1.2 s.2)).toSubMeas)
      (fun s => AnswerSymStrat.axisParallelLineAnswerFamily strategy s.1) eps
    exact degreeZero_axisConsistency_at_updatedEndpoint
      params strategy hd eps haxis
  have hCA := consRel_symm_of_density_fixed strategy.state strategy.densityFixed
    𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas C) eps hAC
  have hCB := consRel_symm_of_density_fixed strategy.state strategy.densityFixed
    𝒟 (IdxMeas.toIdxSubMeas B) (IdxMeas.toIdxSubMeas C) eps hBC
  have hCA_sdd := simeqToApprox strategy.state 𝒟 C A eps hCA
  have hCB_sdd := simeqToApprox strategy.state 𝒟 C B eps hCB
  have hAC_sdd : SDDRel strategy.state 𝒟
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
      (2 * eps) := by
    exact sddRel_symm strategy.state 𝒟 _ _ _
      ⟨hCA_sdd.leftRightSquaredDistanceBound⟩
  have hAB_sdd := stateDependentDistanceRel_triangle strategy.state 𝒟
    (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas A))
    (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
    (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
    (2 * eps) (2 * eps) hAC_sdd
    (⟨hCB_sdd.leftRightSquaredDistanceBound⟩)
  have hscalar : 2 * (2 * eps + 2 * eps) = 8 * eps := by ring
  rw [hscalar] at hAB_sdd
  change SDDRel strategy.state 𝒟
    (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas A))
    (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) (8 * eps)
  exact hAB_sdd

end MIPStarRE.LDT.MainInductionStep
