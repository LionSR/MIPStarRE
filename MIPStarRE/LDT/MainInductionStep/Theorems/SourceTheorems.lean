import MIPStarRE.LDT.MainInductionStep.Theorems.MainTheorems

/-!
# Section 6 — Source-boundary induction theorems

This module contains the printed source-range wrappers for `thm:main-induction`,
together with the public restricted-probability constructors used by the final
soundness handoff.  The corrected large-`k` interface remains in `MainTheorems`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive-degree non-base small-error source-range obligation with the
derived nonzero-size side condition for `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:7-18`.

This theorem isolates the genuinely nontrivial part of the printed source range
not covered by the corrected large-`k` interface: the positive-degree,
non-base, small-error branch inside the interval
`params.m * params.d ≤ k < 400 * params.m * params.d`, under the branch
conditions `0 < params.d`, `params.m ≠ 1`, and the derived side condition
`1 ≤ k`.  It is not an additional hypothesis of the paper theorem; the wrapper
`mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation` proves `1 ≤ k`
from `params.m * params.d ≤ k`, `params.hm`, and `0 < params.d`.  Rather, this
records the missing scalar-range argument documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.

**Proof gap:** The present formal proof route derives the induction theorem for
`400 * params.m * params.d ≤ k`.  The remaining source interval requires a
separate argument, for example a genuine saturation estimate for this range or
a weaker pasting-and-cascade route.  The base case is already proved by
`mainInductionBaseCase`, and the large-error branch of the same interval is
already proved by `mainInductionOfOneLeError`.  The degree-zero branch is empty
because `k < 400 * params.m * 0` is impossible, and the `1 ≤ k` side condition
is derived in the wrapper.  None of these branches is part of this
positive-degree non-base obligation.

**Unfaithful:** This proof currently contains the tracked `sorry` for the source
interval `params.m * params.d ≤ k < 400 * params.m * params.d` in the
small-error, positive-degree, non-base regime, so it uses `sorryAx` rather than
deriving the printed range of `references/ldt-paper/inductive_step.tex:7-18`.
Documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue
#1458.  Elimination: prove this interval directly or derive it from a corrected
source-range argument. -/
theorem mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (_hk : params.m * params.d ≤ k)
    (_hsmallK : k < 400 * params.m * params.d)
    (_hsmall : mainInductionError params k eps delta gamma < 1)
    (_hd : 0 < params.d)
    (_hk_pos : 1 ≤ k)
    (_hm1 : params.m ≠ 1) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  sorry

/-- Positive-degree non-base small-error source-range wrapper for
`thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:7-18`.

This theorem records the elementary nonzero-size consequence of the remaining
source-range hypotheses.  Since `params.m > 0` and `0 < params.d`, the source
assumption `params.m * params.d ≤ k` implies `1 ≤ k`.  The remaining proof work
is therefore the named obligation
`mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`.

**Unfaithful:** The final line calls the tracked positive-degree source-range
obligation, whose proof is not yet derived from the printed range of
`references/ldt-paper/inductive_step.tex:7-18`.  Documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue #1458.
Elimination: discharge the positive-degree non-base small-error source-range
obligation while keeping the printed `k ≥ md` statement unchanged. -/
theorem mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : params.m * params.d ≤ k)
    (hsmallK : k < 400 * params.m * params.d)
    (hsmall : mainInductionError params k eps delta gamma < 1)
    (hd : 0 < params.d)
    (hm1 : params.m ≠ 1) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  have hk_pos : 1 ≤ k := by
    exact Nat.succ_le_of_lt (lt_of_lt_of_le (Nat.mul_pos params.hm hd) hk)
  exact
    mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation
      params strategy eps delta gamma k hgood hk hsmallK hsmall hd hk_pos hm1

/-- Non-base small-error source-range wrapper for `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:7-18`.

This theorem removes the impossible degree-zero branch from the source-range
frontier.  If `params.d = 0`, then the hypothesis
`k < 400 * params.m * params.d` contradicts `Nat.not_lt_zero k`; otherwise it
calls the named positive-degree non-base obligation
`mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation`.

**Unfaithful:** The positive-degree branch calls the tracked obligation
`mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation`, whose proof is
not yet derived from the printed range of
`references/ldt-paper/inductive_step.tex:7-18`.  Documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue #1458.
Elimination: discharge the positive-degree non-base small-error source-range
obligation while keeping the printed `k ≥ md` statement unchanged. -/
theorem mainInduction_sourceRangeSmallErrorNonBaseObligation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : params.m * params.d ≤ k)
    (hsmallK : k < 400 * params.m * params.d)
    (hsmall : mainInductionError params k eps delta gamma < 1)
    (hm1 : params.m ≠ 1) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  by_cases hd : 0 < params.d
  · exact
      mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation
        params strategy eps delta gamma k hgood hk hsmallK hsmall hd hm1
  · exact False.elim <| by
      have hd_zero : params.d = 0 := Nat.eq_zero_of_not_pos hd
      simp [hd_zero] at hsmallK

/-- Small-error source-range wrapper for `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:7-18`.

This theorem removes the already formalized base case from the source-range
frontier.  If `params.m = 1`, it calls `mainInductionBaseCase`; otherwise it
calls the named non-base obligation
`mainInduction_sourceRangeSmallErrorNonBaseObligation`.  Thus the remaining
direct source-range proof hole is the non-base small-error interval, not the
base case.

**Unfaithful:** The non-base branch calls the tracked obligation
`mainInduction_sourceRangeSmallErrorNonBaseObligation`, whose proof is not yet
derived from the printed range of `references/ldt-paper/inductive_step.tex:7-18`.
Documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue
#1458.  Elimination: discharge the non-base small-error source-range obligation
while keeping the printed `k ≥ md` statement unchanged. -/
theorem mainInduction_sourceRangeSmallErrorObligation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : params.m * params.d ≤ k)
    (hsmallK : k < 400 * params.m * params.d)
    (hsmall : mainInductionError params k eps delta gamma < 1) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  by_cases hm1 : params.m = 1
  · exact mainInductionBaseCase params strategy eps delta gamma k hm1 hgood
  · exact
      mainInduction_sourceRangeSmallErrorNonBaseObligation
        params strategy eps delta gamma k hgood hk hsmallK hsmall hm1

/-- Internal proof obligation for the source range of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:7-18`.

This theorem isolates the part of the printed source statement not covered by
the corrected large-`k` interface: the interval
`params.m * params.d ≤ k < 400 * params.m * params.d`.  It is not an additional
hypothesis of the paper theorem.  The large-error branch is closed by
`mainInductionOfOneLeError`; the remaining work is the named small-error
obligation `mainInduction_sourceRangeSmallErrorObligation`.

**Unfaithful:** The proof currently calls
`mainInduction_sourceRangeSmallErrorObligation`, whose proof is not yet derived
from the printed range of `references/ldt-paper/inductive_step.tex:7-18`.
Documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue
#1458.  Elimination: discharge the small-error source-range obligation while
keeping the printed `k ≥ md` statement unchanged. -/
theorem mainInduction_sourceRangeObligation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : params.m * params.d ≤ k)
    (hsmallK : k < 400 * params.m * params.d) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  by_cases hsmall : mainInductionError params k eps delta gamma < 1
  · exact
      mainInduction_sourceRangeSmallErrorObligation
        params strategy eps delta gamma k hgood hk hsmallK hsmall
  · exact mainInductionOfOneLeError params strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Source statement of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:7-18`.

This theorem records the printed paper statement: a good symmetric strategy for
the `(m,q,d)` low individual degree test and an integer `k ≥ m d` produce a
polynomial measurement point-consistent with the point measurement at the error
`mainInductionError`.

**Proof gap:** The corrected large-`k` range
`400 * params.m * params.d ≤ k` follows from the checked interface
`mainInduction`.  The remaining missing range is the interval allowed by the
paper but not yet covered by the current formal proof route,
`params.m * params.d ≤ k < 400 * params.m * params.d`.  This discrepancy is
documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  In the
covered range, the proof still inherits the named small-error construction
obligation `mainInductionSuccessorNext_ofSmallErrorConstruction`, tracked by
issue #1507 under #1458.  The uncovered source range is isolated as the named
internal obligation `mainInduction_sourceRangeObligation`, rather than being
added as a hypothesis or replacing the paper statement by the strengthened
large-`k` interface.

**Unfaithful:** The proof currently uses two tracked proof obligations:
`mainInductionSuccessorNext_ofSmallErrorConstruction` in the covered large-`k`
range and `mainInduction_sourceRangeObligation` in the remaining source range.
These obligations are not derived from
`references/ldt-paper/inductive_step.tex:7-18`.  Documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`, issue #1507, and issue
#1458.  Elimination: discharge both named obligations while keeping the printed
`k ≥ m d` statement unchanged. -/
theorem mainInduction_sourceStatement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (_hk : params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  by_cases hlargeK : 400 * params.m * params.d ≤ k
  · exact mainInduction params strategy eps delta gamma k hgood hlargeK
  · exact
      mainInduction_sourceRangeObligation params strategy eps delta gamma k hgood _hk
        (lt_of_not_ge hlargeK)

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
