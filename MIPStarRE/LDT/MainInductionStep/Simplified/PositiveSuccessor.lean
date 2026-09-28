import MIPStarRE.LDT.MainInductionStep.Simplified.ScalarSuccessor
import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.AnswerValued

/-!
# Positive-degree successor step for an ordinary symmetric strategy

The restriction theorem, recursive answer-valued hypothesis, common-ancilla
self-improvement, simplified pasting, compression, and scalar absorption
are combined here. The pasting attempt count remains internal.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:374-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

universe uι uF

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Positive-degree successor construction for the ordinary symmetric
strategy, using only the predecessor answer-valued induction theorem.
The unit-parameter side bounds are the nontrivial branch of the proof. -/
theorem simplifiedPositiveSuccessor_ofRecursiveHypothesis
    (params : Parameters) [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (heps1 : eps ≤ 1) (hdelta1 : delta ≤ 1)
    (hratio1 : ((params.d : Error) / (params.q : Error)) ≤ 1)
    (hinduction : SimplifiedAnswerInductionHypothesis.{uF, uι} params) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (simplifiedMainInductionError params.next eps delta gamma) := by
  classical
  have heps0 : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hdelta0 : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hgood.selfConsistencyTest
  have hgamma0 : 0 ≤ gamma :=
    (diagonalFailureProbability_nonneg params.next strategy).trans
      hgood.diagonalLineTest
  let restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma :=
    AnswerSliceRestrictionData.ofRestrictedProbabilities
      params strategy eps delta gamma
      (answerRestrictedProbabilities params strategy eps delta gamma hgood)
  let inductionPkg : SimplifiedAnswerPerSliceData
      params strategy eps delta gamma restrictionPkg :=
    SimplifiedAnswerPerSliceData.ofInductionHypothesis
      params strategy eps delta gamma restrictionPkg hinduction
  let data : SimplifiedSliceDilationData
      params strategy eps delta gamma restrictionPkg inductionPkg :=
    SimplifiedSliceDilationData.ofInductionData
      params strategy eps delta gamma restrictionPkg inductionPkg
  obtain ⟨G, hG⟩ := simplifiedSuccessorPasting params strategy eps delta gamma
    hgood hd restrictionPkg inductionPkg data
  refine ⟨G, ?_⟩
  exact ConsRel.mono
    (simplifiedSuccessorPastingError_le_inductionError
      params strategy eps delta gamma restrictionPkg
      hd heps0 heps1 hdelta0 hdelta1 hgamma0 hratio1) hG

end MIPStarRE.LDT.MainInductionStep
