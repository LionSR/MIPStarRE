import MIPStarRE.LDT.MainInductionStep.Theorems.MainTheorems

/-!
# Section 6 — Corrected source-boundary induction theorem

This module contains the corrected large-`k` source-boundary wrapper for
`thm:main-induction`, together with the public restricted-probability
constructors used by the final soundness handoff.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Corrected source statement of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:7-18`.

The paper statement prints `k ≥ m d`.  The proof of the successor step invokes
the induction-section pasting theorem, which requires the stronger bound
`k ≥ 400 m d`.  The interval `m d ≤ k < 400 m d` is non-vacuous and the
printed implication to the pasting hypothesis is false; the project therefore
treats this as a confirmed source bug rather than as a hidden proof obligation.

**Local fix:** This corrected statement uses the large-`k` hypothesis required
by the proof route through pasting.  The discrepancy is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue #1507. -/
theorem mainInduction_sourceStatement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  exact mainInduction params strategy eps delta gamma k hgood hk

/-- Restricted-probabilities data built from the explicit weighted bounds in the
successor proof of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`), used in the proof of
`\label{thm:main-induction}` at
`references/ldt-paper/inductive_step.tex:441-454`. -/
noncomputable def mainInductionPublicRestrictionData
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma) :
    SliceRestrictionData params strategy eps delta gamma :=
  SliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
    (RestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound)

/-- Answer-valued restricted-probabilities data record built from explicit weighted
answer-valued slice bounds.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`), used in the proof of
`\label{thm:main-induction}` at
`references/ldt-paper/inductive_step.tex:441-454`. -/
noncomputable def answerMainInductionPublicRestrictionData
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma) :
    AnswerSliceRestrictionData params strategy eps delta gamma :=
  AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
    (AnswerRestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound)

end MIPStarRE.LDT.MainInductionStep
