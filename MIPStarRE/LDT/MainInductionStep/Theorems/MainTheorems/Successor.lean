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

/-- Answer-valued small-error successor construction for the simultaneous
induction route.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, in the
recursive successor case of `thm:main-induction`.

This is not a paper theorem.  It is the internal answer-valued successor
assertion obtained from the genuine answer-valued induction theorem above.  It
has only the answer-valued successor strategy hypotheses, the corrected
large-`k` condition, and the small-error branch condition; the predecessor
induction hypothesis is supplied by `answerMainInduction`, not by an additional
assumption in the theorem statement.

The proof calls the genuine answer-valued induction theorem.  Its successor
branch supplies the predecessor induction hypothesis internally and uses the
proved answer-valued pasting theorem; no predecessor-induction package or
ordinary-carrier dummy diagonal is assumed by this corollary. -/
theorem answerMainInductionSuccessorNext_ofSmallErrorConstruction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    AnswerMainInductionConclusion params.next strategy eps delta gamma k := by
  have hk_pos : 1 ≤ k :=
    one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  exact
    (answerMainInduction (params := params.next) :
      AnswerMainInductionHypothesis params.next) (ι := ι) strategy eps delta gamma k
        hgood hk_pos hk

/-- Internal successor assembly from the answer-valued recursive obligations.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This theorem is not a paper theorem and should not be advertised as
`\label{thm:main-induction}`.  It records the Lean reduction of the nontrivial
successor branch after three inputs have been supplied internally by the
induction proof:

* the predecessor answer-valued induction hypothesis for the restricted slices;
* the predecessor large-`k` side condition; and
* the concrete answer-valued slice-transport data needed to apply
  `selfImprovementInInductionSection` slice by slice.

The nonzero-`k` side condition required by the predecessor answer-valued
interface is derived here from the small-error branch, not from a
positive-degree assumption.

The answer-valued restricted-probabilities data are derived here from
`strategy.IsGood eps delta gamma`, and the final averaging and pasting step is
delegated to `mainInductionFromAnswerStageDataOfSmallError`.

This is a retained conditional reduction for the successor proof of
`thm:main-induction`.  The active proof route now derives the predecessor
answer-valued induction hypothesis and the answer-valued slice data through
`answerMainInduction`, rather than taking the slice-transport construction as a
separate theorem hypothesis.

**Conditional:** This is an internal reduction for the successor proof of
`thm:main-induction`, tracked in issue #1507, not the source theorem.
Discharge: proved here from the predecessor answer-valued induction hypothesis,
the answer-valued restricted-probabilities theorem, and the supplied
slice-transport construction. -/
theorem mainInductionSuccessorNext_ofAnswerStageObligations.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk : 400 * params.m * params.d ≤ k)
    (sliceTransport :
      let answerRestrict :=
        AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
          (answerRestrictedProbabilities params strategy eps delta gamma hgood)
      let hk_pos := one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
      let answerInduction :=
        AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
          answerRestrict hinduction hk_pos hk
      AnswerSelfImprovementData.SliceStrategyTransport.{uι, uF} params strategy eps delta gamma k
        answerRestrict answerInduction) :
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
    AnswerSelfImprovementData.ofSliceStrategyTransport params strategy eps delta gamma k
      answerRestrict answerInduction sliceTransport
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

/-- Internal successor assembly from the predecessor induction hypothesis,
using the answer-valued slice self-improvement construction.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

**Conditional:** Compared with
`mainInductionSuccessorNext_ofAnswerStageObligations`, this form does not assume
ordinary symmetric strategies realizing the answer-valued restricted slices.
The self-improvement data are obtained directly from the answer-valued
restricted slices via `AnswerSelfImprovementData.ofAnswerCarrier`.  It is an
internal reduction for the successor proof of `thm:main-induction`, tracked in
issue #1507, not the source theorem.  Discharge: proved here from the
predecessor answer-valued induction hypothesis and the answer-valued carrier
self-improvement construction. -/
theorem mainInductionSuccessorNext_ofAnswerStageObligations_ofAnswerCarrier.{uF}
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

/-- Internal positive-degree successor assembly using the successor large-`k`
hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This is the same answer-valued assembly as
`mainInductionSuccessorNext_ofAnswerStageObligations`, but the elementary
predecessor side condition `400md ≤ k` is derived here from the successor
hypothesis `400(m+1)d ≤ k`.  The nontrivial branch hypothesis supplies
`k ≥ 1`; no positivity of the degree is needed for the recursive call.

**Conditional:** This theorem belongs to the stronger slice-transport route,
where the remaining
inputs are the predecessor induction hypothesis and concrete ordinary slice
strategies realizing the answer-valued slices.  The active successor route
below uses `AnswerSelfImprovementData.ofAnswerCarrier`, so the source-facing
frontier no longer includes this slice-transport input.  It is tracked in issue
#1507.  Discharge: proved here from the predecessor answer-valued induction
hypothesis, the supplied slice transport, and the successor large-`k` bound. -/
theorem mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hinduction : AnswerMainInductionHypothesis params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (sliceTransport :
      let hk_pred := mainInductionSuccessorBound_pred params hk_next
      let answerRestrict :=
        AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
          (answerRestrictedProbabilities params strategy eps delta gamma hgood)
      let hk_pos := one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
      let answerInduction :=
        AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
          answerRestrict hinduction hk_pos hk_pred
      AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
        answerRestrict answerInduction) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionSuccessorNext_ofAnswerStageObligations params strategy eps delta gamma k
      hgood hsmall hinduction
      (mainInductionSuccessorBound_pred params hk_next)
      sliceTransport

/-- Internal successor assembly from the successor large-`k` hypothesis, using
the answer-valued slice self-improvement construction.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

**Conditional:** This is an internal reduction for the successor proof of
`thm:main-induction`, tracked in issue #1507, not the source theorem.  It
replaces the predecessor large-`k` hypothesis by the successor large-`k`
hypothesis.  Discharge: proved here from
`mainInductionSuccessorNext_ofAnswerStageObligations_ofAnswerCarrier` and the
elementary successor-to-predecessor bound. -/
theorem mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound_ofAnswerCarrier.{uF}
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
    mainInductionSuccessorNext_ofAnswerStageObligations_ofAnswerCarrier
      params strategy eps delta gamma k hgood hsmall hinduction
      (mainInductionSuccessorBound_pred params hk_next)

/-- Internal successor assembly after the large-error split.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This older theorem removes the already solved large-error branch from the
slice-transport successor route.  In the nontrivial branch it calls
`mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound`; in the
complementary branch it uses the trivial-measurement theorem
`mainInductionOfOneLeError`.  Its small-error branch still assumes concrete
answer-valued slice transport; the active successor reduction below instead
uses the answer-carrier construction and no longer needs that transport input.

**Conditional:** This is an internal conditional reduction retained as a checked composition
lemma; the large-error branch is already discharged here.  The active successor
proof instead uses the answer-carrier construction and `answerMainInduction`.
It is tracked in issue #1507.  Discharge: proved here by splitting on the
large-error branch and applying the retained slice-transport successor route in
the small-error branch. -/
theorem mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBoundSplit
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis params)
    (_hd : 0 < params.d)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (sliceTransport :
      ∀ _hsmall : mainInductionError params.next k eps delta gamma < 1,
        let hk_pred := mainInductionSuccessorBound_pred params hk_next
        let answerRestrict :=
          AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
            (answerRestrictedProbabilities params strategy eps delta gamma hgood)
        let hk_pos :=
          one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma _hsmall
        let answerInduction :=
          AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
            answerRestrict hinduction hk_pos hk_pred
        AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
          answerRestrict answerInduction) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · exact
      mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound
        params strategy eps delta gamma k hgood hsmall hinduction hk_next
        (sliceTransport hsmall)
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Internal successor assembly after both the large-error and degree splits.

This theorem is not the paper theorem and should not be linked as
`\label{thm:main-induction}`.  It records the exact proof obligations that
remain after the already checked large-error branch has been removed.  In the
small-error branch, there are two cases:

* if `0 < params.d`, the proof calls the older answer-valued successor assembly
  from the predecessor answer-valued induction hypothesis and the concrete
  answer-valued slice transport;
* if `params.d = 0`, the proof requires a separate degree-zero successor
  construction, analogous in role to the degree-zero branch of the pasting
  theorem.

Thus the positivity of the degree is not being added to the public successor
statement; it is only the branch condition for one internal construction route.

**Conditional:** This is an internal conditional reduction for the successor proof of
`thm:main-induction`.  The older degree split is retained as a checked
composition lemma; the active recursive-slice route avoids this separate
degree-zero construction by applying the predecessor induction hypothesis also
when `d = 0`.  It is tracked in issue #1507.  Discharge: proved here by
splitting on the large-error and degree-zero branches. -/
theorem mainInductionSuccessorNext_ofDegreeSplitObligations
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (degreeZeroSmall :
      mainInductionError params.next k eps delta gamma < 1 →
        params.d = 0 →
          ∃ G : Measurement (Polynomial params.next) ι,
            ConsRel strategy.state (uniformDistribution (Point params.next))
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              (polynomialEvaluationFamily params.next G.toSubMeas)
              (mainInductionError params.next k eps delta gamma))
    (sliceTransport :
      ∀ (_hd : 0 < params.d),
        ∀ _hsmall : mainInductionError params.next k eps delta gamma < 1,
          let hk_pred := mainInductionSuccessorBound_pred params hk_next
          let answerRestrict :=
            AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
              (answerRestrictedProbabilities params strategy eps delta gamma hgood)
          let hk_pos :=
            one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma _hsmall
          let answerInduction :=
            AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
              answerRestrict hinduction hk_pos hk_pred
          AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
            answerRestrict answerInduction) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · by_cases hd : 0 < params.d
    · exact
        mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound
          params strategy eps delta gamma k hgood hsmall hinduction hk_next
          (sliceTransport hd hsmall)
    · exact degreeZeroSmall hsmall (Nat.eq_zero_of_not_pos hd)
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Internal degree-zero successor reduction through the completed degree-zero
pasting construction.

This theorem is not the degree-zero branch itself.  It records that, when
`params.d = 0`, the existing degree-zero pasting theorem supplies the desired
successor measurement once the successor proof has constructed a slice family
which is complete and point-consistent with sufficiently small parameters
`kappa` and `zeta`.  The final hypothesis is the scalar absorption from the
degree-zero pasting error into the main-induction error.

Thus the remaining degree-zero work is the construction of such a family and
the displayed scalar inequality, not an additional hypothesis on
`thm:main-induction`. -/
theorem mainInductionSuccessorNext_degreeZero_ofPastingFamily
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (kappa zeta : Error)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0)
    (herror :
      ldPastingInInductionError params k eps delta gamma kappa zeta ≤
        mainInductionError params.next k eps delta gamma) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  rcases Pasting.degreeZeroPastedPointConsistency params strategy eps delta gamma
      kappa zeta hgood family hcomplete hcons hd_zero k with
    ⟨H, _hH_eq, hH⟩
  exact ⟨H, ConsRel.mono herror hH⟩

/-- Internal successor reduction whose degree-zero branch is expressed by
concrete pasting-family data.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This theorem refines
`mainInductionSuccessorNext_ofDegreeSplitObligations`: instead of assuming the
degree-zero successor conclusion as a black box, it assumes the construction of
a complete point-consistent slice family and the scalar absorption inequality
needed by `mainInductionSuccessorNext_degreeZero_ofPastingFamily`.  The theorem
is not a paper theorem; it records a checked composition of already isolated
internal obligations.

**Conditional:** This is now a retained alternative route.  The active recursive-slice reduction
applies the predecessor induction hypothesis also when `d = 0`, and therefore
does not require this separate family construction.  It is tracked in issue
#1507.  Discharge: proved here by reducing the degree-zero branch to the
explicit pasting-family construction and using the positive-degree
slice-transport route otherwise. -/
theorem mainInductionSuccessorNext_ofDegreeSplitPastingObligations
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (degreeZeroPasting :
      ∀ _hsmall : mainInductionError params.next k eps delta gamma < 1,
        params.d = 0 →
          ∃ family : IdxPolyFamily params ι, ∃ kappa zeta : Error,
            family.Complete strategy.state kappa ∧
              family.ConsistentWithPoints strategy zeta ∧
                ldPastingInInductionError params k eps delta gamma kappa zeta ≤
                  mainInductionError params.next k eps delta gamma)
    (sliceTransport :
      ∀ (_hd : 0 < params.d),
        ∀ _hsmall : mainInductionError params.next k eps delta gamma < 1,
          let hk_pred := mainInductionSuccessorBound_pred params hk_next
          let answerRestrict :=
            AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
              (answerRestrictedProbabilities params strategy eps delta gamma hgood)
          let hk_pos :=
            one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma _hsmall
          let answerInduction :=
            AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
              answerRestrict hinduction hk_pos hk_pred
          AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
            answerRestrict answerInduction) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  refine
    mainInductionSuccessorNext_ofDegreeSplitObligations
      params strategy eps delta gamma k hgood hinduction hk_next ?_ sliceTransport
  intro hsmall hd_zero
  rcases degreeZeroPasting hsmall hd_zero with
    ⟨family, kappa, zeta, hcomplete, hcons, herror⟩
  exact
    mainInductionSuccessorNext_degreeZero_ofPastingFamily
      params strategy eps delta gamma k hgood family kappa zeta
      hcomplete hcons hd_zero herror

/-- Internal small-error successor reduction through the recursive slice route,
with no degree-positivity hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, restricted to
the nontrivial regime
`mainInductionError params.next k eps delta gamma < 1`.

The paper applies the predecessor induction theorem to every restricted slice.
The previous Lean reduction separated the case `params.d = 0` only because the
internal predecessor hypothesis had been stated with an artificial assumption
`0 < params.d`.  The predecessor hypothesis is now stated for the full corrected
large-`k` interface, and the condition `1 ≤ k` needed by the recursive call is
derived here from the small-error assumption.  Thus this older slice-transport
reduction does not require a separate degree-zero polynomial-family
construction.

This theorem is still conditional: the slice transport datum is the input needed
for the stronger route through ordinary slice strategies.  The active successor
frontier is the answer-carrier theorem below, where the only remaining input is
the predecessor answer-valued induction hypothesis supplied inside a genuine
induction on the dimension. -/
theorem mainInductionSuccessorNext_ofSmallErrorConstruction_ofRecursiveSliceTransport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (sliceTransport :
      let hk_pred := mainInductionSuccessorBound_pred params hk_next
      let answerRestrict :=
        AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
          (answerRestrictedProbabilities params strategy eps delta gamma hgood)
      let hk_pos := one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
      let answerInduction :=
        AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
          answerRestrict hinduction hk_pos hk_pred
      AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
        answerRestrict answerInduction) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound
      params strategy eps delta gamma k hgood hsmall hinduction hk_next sliceTransport

/-- Internal small-error successor reduction through the recursive
answer-valued slice route, with no ordinary slice-transport assumption.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, restricted to
the nontrivial regime
`mainInductionError params.next k eps delta gamma < 1`.

The only mathematical input to this internal reduction is the predecessor
answer-valued induction hypothesis.  The exported simultaneous induction
theorem supplies that hypothesis internally.  The answer-valued slice
self-improvement data are constructed directly by
`AnswerSelfImprovementData.ofAnswerCarrier`; no low-degree support theorem
realizing the answer-valued diagonal measurement as an ordinary
polynomial-valued diagonal measurement is required for this step. -/
theorem mainInductionSuccessorNext_ofSmallErrorConstruction_ofAnswerCarrier.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound_ofAnswerCarrier
      params strategy eps delta gamma k hgood hsmall hinduction hk_next

/-- Native successor reduction from the recursive answer-valued predecessor
induction hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This is the checked successor assembly after the answer-valued
self-improvement construction has been discharged by the carrier route.  Its
only non-source input is the recursive predecessor induction hypothesis, which
must be supplied locally inside the eventual proof by induction on the
dimension.  In the nontrivial branch it calls
`mainInductionSuccessorNext_ofSmallErrorConstruction_ofAnswerCarrier`; in the
large-error branch it uses `mainInductionOfOneLeError`. -/
theorem mainInductionSuccessorNext_ofRecursiveAnswerInduction.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · exact
      mainInductionSuccessorNext_ofSmallErrorConstruction_ofAnswerCarrier
        params strategy eps delta gamma k hgood hinduction hk_next hsmall
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Internal small-error successor reduction from the two remaining
construction inputs and the predecessor induction hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, restricted to
the nontrivial regime
`mainInductionError params.next k eps delta gamma < 1`.

This theorem is not a paper theorem.  It records the precise point at which the
eventual proof by induction on the dimension will use its predecessor
induction hypothesis in the older degree-split route.  It is retained as a
checked composition lemma, but the active successor frontier now uses
`mainInductionSuccessorNext_ofSmallErrorConstruction_ofRecursiveSliceTransport`,
which avoids the separate degree-zero family branch by applying the predecessor
induction hypothesis also at `d = 0`.  None of the inputs to this older helper
should be added to `thm:main-induction` or `thm:main-formal` as source
hypotheses. -/
theorem mainInductionSuccessorNext_ofSmallErrorConstruction_ofInternalConstructions
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (degreeZeroPasting :
      params.d = 0 →
        ∃ family : IdxPolyFamily params ι, ∃ kappa zeta : Error,
          family.Complete strategy.state kappa ∧
            family.ConsistentWithPoints strategy zeta ∧
              ldPastingInInductionError params k eps delta gamma kappa zeta ≤
                mainInductionError params.next k eps delta gamma)
    (sliceTransport :
      ∀ (_hd : 0 < params.d),
        let hk_pred := mainInductionSuccessorBound_pred params hk_next
        let answerRestrict :=
          AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
            (answerRestrictedProbabilities params strategy eps delta gamma hgood)
        let hk_pos :=
          one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
        let answerInduction :=
          AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
            answerRestrict hinduction hk_pos hk_pred
        AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
          answerRestrict answerInduction) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  by_cases hd : 0 < params.d
  · exact
      mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound
        params strategy eps delta gamma k hgood hsmall hinduction hk_next
        (sliceTransport hd)
  · rcases degreeZeroPasting (Nat.eq_zero_of_not_pos hd) with
      ⟨family, kappa, zeta, hcomplete, hcons, herror⟩
    exact
      mainInductionSuccessorNext_degreeZero_ofPastingFamily
        params strategy eps delta gamma k hgood family kappa zeta hcomplete hcons
        (Nat.eq_zero_of_not_pos hd) herror

/-- Small-error construction for the native successor step of
`thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, restricted to
the nontrivial regime
`mainInductionError params.next k eps delta gamma < 1`.

This theorem is the named closure obligation for the only remaining
nontrivial branch of the successor proof.  Its public parameters are the
successor strategy hypotheses and the branch condition
`mainInductionError < 1`, so downstream users do not acquire
restricted-probability records, slice-induction data, self-improvement data,
pasting data, residual packages, or arbitrary implication hypotheses as
assumptions of the theorem.

**Proof obligation:** Construct the answer-valued restricted slice profile,
apply the recursive predecessor induction conclusion for each slice, assemble
the pasting input, and prove the scalar absorption estimates.  The checked
answer-carrier assembly theorem above now obtains the predecessor induction
argument from the genuine strong-induction theorem `answerMainInduction`; it
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
    mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound_ofAnswerCarrier
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

**Proof obligation:** In the small-error regime, use the recursive predecessor
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
bundle as `pred.next` and then invokes the native successor-step obligation
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
