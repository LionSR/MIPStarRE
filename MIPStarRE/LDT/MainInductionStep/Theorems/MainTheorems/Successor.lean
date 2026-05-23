import MIPStarRE.LDT.MainInductionStep.Theorems.MainTheorems.Base

/-!
# Section 6 — Main Induction Theorems: Successor and Public Interfaces

This module contains the answer-valued induction theorem, successor reductions,
and the public corrected large-`k` main-induction interface.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Answer-valued corrected large-`k` induction theorem.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, as an internal
simultaneous-induction strengthening used to prove the ordinary main induction.

This theorem is not advertised as `thm:main-induction`.  It records the
answer-valued induction statement needed for the recursive restricted slices.
The proof is a genuine strong induction on the dimension.  In the successor
branch the predecessor hypothesis is applied to the restricted answer-valued
slices, and the checked successor reduction then carries the result through
the slice restriction, self-improvement, averaging, and scalar estimates.

The answer-valued pasting invocation is now proved from the answer-valued point
commutativity theorem and the Section 11 scalar commutativity chain.  Thus the
successor branch does not require an ordinary dummy diagonal carrier or an
additional pasting datum in the theorem statement. -/
theorem answerMainInduction.{uF, vι}
    (params : Parameters)
    [FieldModel.{uF} params.q] :
    AnswerMainInductionHypothesis.{uF, vι} params := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (params : Parameters), params.m = n → ∀ instField : FieldModel.{uF} params.q,
      @AnswerMainInductionHypothesis.{uF, vι} params instField
  have hAll : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih params hm instField
    letI : FieldModel.{uF} params.q := instField
    intro ι instFintype instDecEq strategy eps delta gamma k hgood _hk_pos hk
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecEq
    by_cases hm1 : params.m = 1
    · exact answerMainInductionBaseCase params strategy eps delta gamma k hm1 hgood
    · by_cases hsmall : mainInductionError params k eps delta gamma < 1
      · rcases Parameters.successorDecompositionOfNeOne params hm1 with ⟨pred, hnext⟩
        have hq : pred.q = params.q := by
          simpa [Parameters.next] using congrArg Parameters.q hnext
        letI : FieldModel.{uF} pred.q := hq.symm ▸ instField
        have hpred_lt : pred.m < n := by
          rw [← hm]
          cases hnext
          simp [Parameters.next]
        have hinduction : AnswerMainInductionHypothesis.{uF, vι} pred :=
          ih pred.m hpred_lt pred rfl inferInstance
        cases hnext
        exact
          answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting
            pred strategy eps delta gamma k hgood hinduction hk hsmall
      · exact answerMainInductionOfOneLeError params strategy eps delta gamma k
          (le_of_not_gt hsmall)
  exact hAll params.m params rfl inferInstance

/-- Internal successor assembly from the predecessor induction hypothesis,
using the answer-valued slice self-improvement construction.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

The self-improvement data are obtained directly from the answer-valued
restricted slices via `AnswerSelfImprovementData.ofAnswerCarrier`.  This is an
internal reduction for the successor proof of `thm:main-induction`, not a paper
theorem.  Its only recursive input is the predecessor answer-valued induction
hypothesis, which is supplied by the strong-induction theorem
`answerMainInduction`. -/
theorem mainInductionSuccessorNext_ofAnswerCarrier.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let answerRestrict : AnswerSliceRestrictionData.{uι, uF} params strategy eps delta gamma :=
    AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
      (answerRestrictedProbabilities params strategy eps delta gamma hgood)
  let answerInduction :
      AnswerPerSliceInductionData.{uι, uF} params strategy eps delta gamma answerRestrict k :=
    let hk_pos := one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
    AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
      answerRestrict hinduction hk_pos hk
  let answerSelf :
      AnswerSelfImprovementData.{uι, uF} params strategy eps delta gamma k answerRestrict
        answerInduction :=
    AnswerSelfImprovementData.ofAnswerCarrier params strategy eps delta gamma k
      answerRestrict answerInduction
  let hrestrict : SliceRestrictionData.{uι, uF} params strategy eps delta gamma :=
    SliceRestrictionData.ofAnswer params strategy eps delta gamma answerRestrict
  let hinduction : PerSliceInductionData.{uι, uF} params strategy eps delta gamma hrestrict k :=
    PerSliceInductionData.ofAnswer params strategy eps delta gamma k answerRestrict
      answerInduction
  let hself : SelfImprovementData.{uι, uF} params strategy eps delta gamma k hrestrict
      hinduction :=
    SelfImprovementData.ofAnswer params strategy eps delta gamma k answerRestrict
      answerInduction answerSelf
  let hpaste : AveragedPastingData.{uι, uF} params strategy eps delta gamma k hself :=
    assembleAveragedPastingDataOfSmallError params strategy eps delta gamma k hgood hsmall
      hrestrict hinduction hself hk
  exact
    mainInductionFromStageData.{uι, uF} (_fieldUniverse := ULift.{uF} PUnit)
      (ULift.up PUnit.unit)
      params strategy eps delta gamma k hgood
      hrestrict hinduction hself hpaste hk

/-- Internal successor assembly from the successor large-`k` hypothesis, using
the answer-valued slice self-improvement construction.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This is an internal reduction for the successor proof of `thm:main-induction`,
not a paper theorem.  It replaces the predecessor large-`k` hypothesis in
`mainInductionSuccessorNext_ofAnswerCarrier` by the successor large-`k`
hypothesis through the elementary successor-to-predecessor bound. -/
theorem mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionSuccessorNext_ofAnswerCarrier
      params strategy eps delta gamma k hgood hsmall hinduction
      (mainInductionSuccessorBound_pred params hk_next)

/-- Small-error construction for the native successor step of
`thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, restricted to
the nontrivial regime
`mainInductionError params.next k eps delta gamma < 1`.

This theorem is the named construction for the nontrivial branch of the
successor proof.  Its public parameters are the
successor strategy hypotheses and the branch condition
`mainInductionError < 1`, so downstream users do not acquire
restricted-probability records, slice-induction data, self-improvement data,
pasting data, residual packages, or arbitrary implication hypotheses as
assumptions of the theorem.

The proof constructs the answer-valued restricted slice profile,
applies the recursive predecessor induction conclusion for each slice, assembles
the pasting input, and prove the scalar absorption estimates.  The checked
answer-carrier assembly obtains the predecessor induction argument from the
genuine strong-induction theorem `answerMainInduction`; it
does not postulate that predecessor conclusion as a hypothesis of the ordinary
successor theorem.  The predecessor induction hypothesis is no longer
restricted by `0 < params.d`; in the nontrivial branch, `1 ≤ k` follows from
`mainInductionError < 1`, and the answer-valued self-improvement data are
constructed by `AnswerSelfImprovementData.ofAnswerCarrier`.

The proof calls `answerMainInduction`, whose successor branch is a genuine
strong-induction argument.  The answer-valued pasting theorem is now proved and
is used inside that route, so this ordinary successor construction does not
carry a transitive `sorryAx` dependency. -/
theorem mainInductionSuccessorNext_ofSmallErrorConstruction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound
      params strategy eps delta gamma k hgood hsmall
      (answerMainInduction params)
      hk

/-- Native successor step for `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the proof
passes from dimension `m` to dimension `m + 1`.

This is the native successor step for the corrected large-`k` Lean interface:
the ambient strategy already lives in dimension `params.next`, so no predecessor
compatibility record is introduced.  The checked reductions above show that the
small-error branch now passes through the genuine answer-valued induction
theorem and the proved answer-valued pasting invocation.

In the small-error regime, the proof uses the recursive predecessor
conclusion for the answer-valued restricted slices, construct the
answer-valued self-improvement data by the carrier route, and apply the
answer-valued analogue of the final induction-section pasting theorem.  No
ordinary `SymStrat` realization of the answer-valued diagonal measurement is
needed for this successor reduction, and the recursive predecessor conclusion
is supplied by `answerMainInduction` rather than by a public hypothesis.

The small-error branch calls
`mainInductionSuccessorNext_ofSmallErrorConstruction`, whose proof depends on
the internal theorem `answerMainInduction`.  That internal theorem supplies the
predecessor induction hypothesis by strong induction and invokes the proved
answer-valued pasting theorem, so the native successor step is now
standard-axiom clean. -/
theorem mainInductionSuccessorNext
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.next.m * params.next.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · exact
      mainInductionSuccessorNext_ofSmallErrorConstruction
        params strategy eps delta gamma k hgood hk hsmall
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Successor branch of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, the induction
step after the restricted-probability estimates and the slice-wise recursive
calls have been set up.

This theorem is the parameter-decomposition form used by `mainInduction`.
Its assumptions are the corrected large-`k` hypotheses for
`thm:main-induction`, together with the branch condition `params.m ≠ 1`; it
does not accept restricted-probability records, per-slice induction data,
self-improvement data, pasting data, auxiliary implication hypotheses, residual
inputs, or data record hypotheses.  The proof decomposes the non-base parameter
bundle as `pred.next` and then invokes the native successor-step theorem
`mainInductionSuccessorNext`.

The proof transitively uses the answer-valued induction theorem
`answerMainInduction`.  That theorem now proves the successor branch by strong
induction, including the answer-valued pasting step, so this decomposition
theorem is standard-axiom clean. -/
theorem mainInductionSuccessor
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k)
    (hm1 : params.m ≠ 1) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  rcases Parameters.successorDecompositionOfNeOne params hm1 with ⟨pred, hnext⟩
  have hq : pred.q = params.q := by
    simpa [Parameters.next] using congrArg Parameters.q hnext
  letI : FieldModel pred.q := hq.symm ▸ (inferInstance : FieldModel params.q)
  cases hnext
  exact mainInductionSuccessorNext pred strategy eps delta gamma k hgood hk

/-- Corrected large-`k` interface for `thm:main-induction`.

This is the Lean theorem linked from the corrected blueprint statement: a good
symmetric strategy and an integer `k ≥ 400 m d` produce a polynomial
measurement consistent with the point measurement at error `mainInductionError`.
The strengthening from the printed `k ≥ m d` hypothesis in
`references/ldt-paper/inductive_step.tex` is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` as a confirmed statement
correction.

The proof uses the base case `mainInductionBaseCase` and the corrected
large-`k` successor theorem `mainInductionSuccessor`.  In the small-error
successor branch the recursive predecessor calls are supplied by the genuine
strong-induction theorem `answerMainInduction`, and the answer-valued pasting
conclusion is derived inside that route. -/
theorem mainInduction
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
  by_cases hm1 : params.m = 1
  · exact mainInductionBaseCase params strategy eps delta gamma k hm1 hgood
  · exact mainInductionSuccessor params strategy eps delta gamma k hgood hk hm1


end MIPStarRE.LDT.MainInductionStep
