import MIPStarRE.LDT.Test.MainTheorem.OrdinaryRestriction.SliceData

/-!
# Ordinary restricted-slice recursion: public wrapper

This module contains the ordinary successor invocation of the public Section 6
main-induction wrapper.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Successor-case Section 6 handoff for `mainFormal`.

This is the actual invocation of
`MainInductionStep.mainInductionPublicWrapper` on the role-register
symmetrization. It proves that, once the `MainFormalSuccessorBoundary` data are
available and the Section 6 side condition `400 * m * d ≤ k` holds, the public
wrapper returns the global polynomial measurement used by the later
unsymmetrization / Schwartz--Zippel / projectivization cascade.

Universe note: the explicit `[FieldModel.{0} params.q]` matches the Section 6
wrapper's universe; the eventual `mainFormal` residual closure must transport or
instantiate this same base-universe field model when choosing predecessor
parameters.

**Unfaithful:** this conditional handoff assumes
`boundary : MainFormalSuccessorBoundary`, whose fields include recursive slice
witnesses and the slice-wise self-improvement obligation rather than deriving
them from the hypotheses of `thm:main-formal`
(`references/ldt-paper/test_definition.tex:180-202`) and the successor case of
`thm:main-induction` (`references/ldt-paper/inductive_step.tex:441-551`).
This is tracked by #1363, #1507, #1503, and #1458.  Elimination: prove
`mainFormalSuccessorProjectiveCompletionObligation` from the paper hypotheses,
constructing the ordinary successor boundary internally before invoking this
wrapper. -/
theorem mainFormalSuccessorMainInductionPublicWrapper
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) (Role × ι),
      ConsRel (strategy.strategySymmetrization).state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (MainInductionStep.mainInductionError params.next k
          (3 * eps) (3 * eps) (3 * eps)) :=
  MainInductionStep.mainInductionPublicWrapper params
    (strategy := strategy.strategySymmetrization)
    (eps := 3 * eps) (delta := 3 * eps) (gamma := 3 * eps) (k := k)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)
    hd
    boundary.axisWeightedBound
    boundary.diagonalWeightedBound
    boundary.recursiveSlices
    boundary.selfImprovementObligation
    hk_pos hk


end Test

end MIPStarRE.LDT
