import MIPStarRE.LDT.MainInductionStep.Simplified.DegreeZeroLineAnswers

/-!
# The two endpoints of a degree-zero hypercube edge

The axis-parallel test controls the point-line consistency at both
endpoints of a rerandomized-coordinate edge. The second bound follows
by the measure-preserving involution that exchanges its endpoints.

## References

- `blueprint/src/low_degree_simplified.tex`, degree-zero proof of
  `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:441-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Exchange the two endpoints of a rerandomized-coordinate sample. -/
def degreeZeroEdgeSwap (params : Parameters) [FieldModel params.q] :
    RerandomizeCoordSample params ≃ RerandomizeCoordSample params where
  toFun := fun s =>
    ((Function.update s.1.1 s.1.2 s.2, s.1.2), s.1.1 s.1.2)
  invFun := fun s =>
    ((Function.update s.1.1 s.1.2 s.2, s.1.2), s.1.1 s.1.2)
  left_inv := by
    intro s
    rcases s with ⟨⟨u, i⟩, t⟩
    simp [Function.update_idem, Function.update_eq_self]
  right_inv := by
    intro s
    rcases s with ⟨⟨u, i⟩, t⟩
    simp [Function.update_idem, Function.update_eq_self]

/-- The axis-parallel test error bounds point-line consistency at the
first endpoint of a uniformly sampled edge. -/
theorem degreeZero_axisConsistency_at_startEndpoint
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps) :
    ConsRel strategy.state
      (uniformDistribution (RerandomizeCoordSample params))
      (fun s => (strategy.pointMeasurement s.1.1).toSubMeas)
      (fun s => AnswerSymStrat.axisParallelLineAnswerFamily strategy s.1)
      eps := by
  constructor
  unfold bipartiteConsError
  calc
    avgOver (uniformDistribution (RerandomizeCoordSample params))
        (fun s => qBipartiteConsDefect strategy.state
          (strategy.pointMeasurement s.1.1).toSubMeas
          (AnswerSymStrat.axisParallelLineAnswerFamily strategy s.1)) =
      strategy.axisParallelFailureProbability := by
        simpa [AnswerSymStrat.axisParallelFailureProbability,
          AnswerSymStrat.axisParallelPointAnswerFamily,
          axisParallelPointAnswerFamilyOf,
          bipartiteConsError, RerandomizeCoordSample] using
          (avgOver_uniform_fst (α := AxisParallelTestSample params)
            (β := Fq params)
            (fun s => qBipartiteConsDefect strategy.state
              (strategy.pointMeasurement s.1).toSubMeas
              (AnswerSymStrat.axisParallelLineAnswerFamily strategy s)))
    _ ≤ eps := haxis

/-- The axis-parallel test error also bounds point-line consistency at
the updated endpoint of a uniformly sampled edge. -/
theorem degreeZero_axisConsistency_at_updatedEndpoint
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (hd : params.d = 0)
    (eps : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps) :
    ConsRel strategy.state
      (uniformDistribution (RerandomizeCoordSample params))
      (fun s => (strategy.pointMeasurement
        (Function.update s.1.1 s.1.2 s.2)).toSubMeas)
      (fun s => AnswerSymStrat.axisParallelLineAnswerFamily strategy s.1)
      eps := by
  classical
  let f : RerandomizeCoordSample params → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (strategy.pointMeasurement s.1.1).toSubMeas
      (AnswerSymStrat.axisParallelLineAnswerFamily strategy s.1)
  have hstart : avgOver (uniformDistribution (RerandomizeCoordSample params)) f ≤
      eps := by
    calc
      avgOver (uniformDistribution (RerandomizeCoordSample params)) f =
          strategy.axisParallelFailureProbability := by
        simpa [f, AnswerSymStrat.axisParallelFailureProbability,
          AnswerSymStrat.axisParallelPointAnswerFamily,
          axisParallelPointAnswerFamilyOf,
          bipartiteConsError, RerandomizeCoordSample] using
          (avgOver_uniform_fst (α := AxisParallelTestSample params)
            (β := Fq params)
            (fun s => qBipartiteConsDefect strategy.state
              (strategy.pointMeasurement s.1).toSubMeas
              (AnswerSymStrat.axisParallelLineAnswerFamily strategy s)))
      _ ≤ eps := haxis
  constructor
  unfold bipartiteConsError
  have hcongr : (fun s => f ((degreeZeroEdgeSwap params).symm s)) =
      (fun s => qBipartiteConsDefect strategy.state
        (strategy.pointMeasurement
          (Function.update s.1.1 s.1.2 s.2)).toSubMeas
        (AnswerSymStrat.axisParallelLineAnswerFamily strategy s.1)) := by
    funext s
    rcases s with ⟨⟨u, i⟩, t⟩
    simp [degreeZeroEdgeSwap, f,
      degreeZero_axisAnswer_update_eq params strategy hd]
  calc
    avgOver (uniformDistribution (RerandomizeCoordSample params))
        (fun s => qBipartiteConsDefect strategy.state
          (strategy.pointMeasurement
            (Function.update s.1.1 s.1.2 s.2)).toSubMeas
          (AnswerSymStrat.axisParallelLineAnswerFamily strategy s.1)) =
      avgOver (uniformDistribution (RerandomizeCoordSample params))
        (fun s => f ((degreeZeroEdgeSwap params).symm s)) := by
          rw [hcongr]
    _ = avgOver (uniformDistribution (RerandomizeCoordSample params)) f :=
      (avgOver_uniform_equiv (degreeZeroEdgeSwap params) f).symm
    _ ≤ eps := hstart

end MIPStarRE.LDT.MainInductionStep
