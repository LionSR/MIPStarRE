import MIPStarRE.LDT.Basic.LinePolynomialEmbedding
import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementAssembly.Core
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds
import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly
import MIPStarRE.LDT.MainInductionStep.Theorems.StageDataConstructors
import MIPStarRE.LDT.Pasting.Bernoulli.DegreeZero

/-!
# Section 6 — Main Induction Theorems

The top-level induction theorem `mainInduction`, its proved base case
`mainInductionBaseCase`, and the public restricted-probability data record
constructors used by the Section 3 handoff.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Direct base case of `thm:main-induction` when `m = 1`.

The paper uses the unique axis-parallel line measurement as the global
polynomial measurement in this case. -/
theorem mainInductionBaseCase
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hm1 : params.m = 1)
    (hgood : strategy.IsGood eps delta gamma) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  classical
  haveI hsub : Subsingleton (Fin params.m) := by
    rw [hm1]
    infer_instance
  let i0 : Fin params.m := ⟨0, by simp [hm1]⟩
  let eSample : AxisParallelTestSample params ≃ Point params :=
    { toFun := fun s => s.1
      invFun := fun u => (u, i0)
      left_inv := by
        intro s
        rcases s with ⟨u, j⟩
        have hj : j = i0 := Subsingleton.elim _ _
        simp [hj, i0]
      right_inv := by
        intro u
        rfl }
  let canonicalLine : AxisParallelLine params :=
    AxisParallelLine.throughPoint (params := params) zeroPoint i0
  let G : Measurement (Polynomial params) ι :=
    { toSubMeas :=
        postprocess ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
          (axisLinePolynomialToPolynomial params i0)
      total_eq_one := (strategy.axisParallelMeasurement canonicalLine).total_eq_one }
  have haxisRaw :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
        strategy.axisParallelFailureProbability := by
    exact ⟨le_rfl⟩
  have haxisPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (fun u =>
          postprocess
            ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
            (· zeroCoord))
        strategy.axisParallelFailureProbability := by
    simpa [IdxProjMeas.toIdxSubMeas, axisParallelPointAnswerFamily,
      axisParallelLineAnswerFamily, eSample, i0] using
      ((Preliminaries.consRel_uniform_equiv
        (e := eSample)
        (ψ := strategy.state)
        (A := axisParallelPointAnswerFamily strategy)
        (B := axisParallelLineAnswerFamily strategy)
        (δ := strategy.axisParallelFailureProbability)).mp haxisRaw)
  have hfamily :
      (fun u =>
        postprocess
          ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
          (· zeroCoord)) =
        polynomialEvaluationFamily params G.toSubMeas := by
    funext u
    apply SubMeas.ext
    · intro a
      calc
        (postprocess
            ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
            (· zeroCoord)).outcome a
          = (postprocess
              ((strategy.axisParallelMeasurement
                (AxisParallelLine.rebaseAt
                  (AxisParallelLine.throughPoint (params := params) u i0)
                  (AxisParallelLine.sampleParameter (params := params) u i0))).toSubMeas)
              (· zeroCoord)).outcome a := by
                simp [AxisParallelLine.rebaseAt_throughPoint_sampleParameter]
        _ = (postprocess
              ((strategy.axisParallelMeasurement
                (AxisParallelLine.throughPoint (params := params) u i0)).toSubMeas)
              (fun f =>
                f (AxisParallelLine.sampleParameter (params := params) u i0))).outcome a := by
                exact
                  (AxisParallelCovariantMeasurement.reparamInvariant
                    strategy.axisParallelMeasurement) _ _ _
        _ = (postprocess
              ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
              (fun f => f (u i0))).outcome a := by
                have hthrough :
                    AxisParallelLine.throughPoint (params := params) u i0 = canonicalLine := by
                  simpa [canonicalLine] using
                    throughPoint_eq_zeroPoint_of_m_eq_one params hm1 u i0
                simp [hthrough, AxisParallelLine.sampleParameter]
        _ = (polynomialEvaluationFamily params G.toSubMeas u).outcome a := by
              simp [polynomialEvaluationFamily, evaluateAt, G,
                axisLinePolynomialToPolynomial_apply]
    · change
          (postprocess
              ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
              (· zeroCoord)).total =
            (postprocess ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
              (fun f => f (u i0))).total
      rw [show
          (postprocess
              ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
              (· zeroCoord)).total =
            (strategy.axisParallelMeasurement { base := u, direction := i0 }).total by rfl]
      rw [show
          (postprocess ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
              (fun f => f (u i0))).total =
            (strategy.axisParallelMeasurement canonicalLine).total by rfl]
      rw [(strategy.axisParallelMeasurement { base := u, direction := i0 }).total_eq_one,
        (strategy.axisParallelMeasurement canonicalLine).total_eq_one]
  have hconsG :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        strategy.axisParallelFailureProbability := by
    simpa [hfamily] using haxisPoint
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hgood.selfConsistencyTest
  have hdiag_nonneg : 0 ≤ strategy.diagonalFailureProbability :=
    diagonalFailureProbability_nonneg params strategy
  have hgamma_nonneg : 0 ≤ gamma := le_trans hdiag_nonneg hgood.diagonalLineTest
  have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
    simpa [SymStrat.axisParallelFailureProbability] using
      bipartiteConsError_uniform_le_one
        strategy.state strategy.isNormalized
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
  have herror_le :
      strategy.axisParallelFailureProbability ≤ mainInductionError params k eps delta gamma := by
    exact le_trans
      (le_min hgood.axisParallelTest haxis_le_one)
      (min_eps_one_le_mainInductionError_of_m_eq_one
        params k eps delta gamma hm1 heps_nonneg hdelta_nonneg hgamma_nonneg)
  exact
    mainInductionOfWitness params strategy eps delta gamma k
      ⟨strategy.axisParallelFailureProbability, G, hconsG, herror_le⟩

/-- Trivial branch of `thm:main-induction` when the target error is at least
`1`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the
successor proof reduces to the nontrivial small-error regime before invoking the
pasting argument.  In the complementary branch the normalized consistency defect
is bounded by `1`, so a distinguished trivial polynomial measurement suffices.
-/
theorem mainInductionOfOneLeError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (herror : 1 ≤ mainInductionError params k eps delta gamma) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  classical
  let G : Measurement (Polynomial params) ι :=
    Measurement.trivialDistinguishedOutcome
      (Classical.choice (inferInstance : Nonempty (Polynomial params)))
  refine ⟨G, ?_⟩
  exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas))
    herror⟩

/-- Internal positive-degree successor assembly from the answer-valued recursive
obligations.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This theorem is not a paper theorem and should not be advertised as
`\label{thm:main-induction}`.  It records the Lean reduction of the nontrivial
successor branch after three inputs have been supplied internally by the
induction proof:

* the predecessor answer-valued induction hypothesis for the restricted slices;
* the positive-degree side condition needed by the current answer-valued
  predecessor interface; and
* the concrete answer-valued slice-transport data needed to apply
  `selfImprovementInInductionSection` slice by slice.

The answer-valued restricted-probabilities data are derived here from
`strategy.IsGood eps delta gamma`, and the final averaging and pasting step is
delegated to `mainInductionFromAnswerStageDataOfSmallError`.

**Proof obligation:** This is an internal conditional reduction for the
successor proof of `thm:main-induction`, tracked by issue #1507 and the
source-statement boundary tracker #1458.  Elimination: derive the predecessor
answer-valued induction hypothesis and the answer-valued slice-transport
construction from the induction hypotheses in the eventual proof of
`mainInduction`. -/
theorem mainInductionSuccessorNext_ofAnswerStageObligations
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hinduction : AnswerMainInductionHypothesis.{0, uι} params)
    (hd : 0 < params.d)
    (hk : 400 * params.m * params.d ≤ k)
    (sliceTransport :
      let answerRestrict :=
        AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
          (answerRestrictedProbabilities params strategy eps delta gamma hgood)
      let answerInduction :=
        AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
          answerRestrict hinduction hd hk
      AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
        answerRestrict answerInduction) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let answerRestrict : AnswerSliceRestrictionData params strategy eps delta gamma :=
    AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
      (answerRestrictedProbabilities params strategy eps delta gamma hgood)
  let answerInduction :
      AnswerPerSliceInductionData params strategy eps delta gamma answerRestrict k :=
    AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
      answerRestrict hinduction hd hk
  let answerSelf :
      AnswerSelfImprovementData params strategy eps delta gamma k answerRestrict answerInduction :=
    AnswerSelfImprovementData.ofSliceStrategyTransport params strategy eps delta gamma k
      answerRestrict answerInduction sliceTransport
  exact
    mainInductionFromAnswerStageDataOfSmallError params strategy eps delta gamma k
      hgood hsmall answerRestrict answerInduction answerSelf hk

/-- The successor large-`k` hypothesis implies the predecessor large-`k`
hypothesis used by the recursive slice calls.

This is a boundary arithmetic fact: the successor ambient dimension is
`params.m + 1`, while the recursive calls are made in dimension `params.m`. -/
theorem mainInductionSuccessorBound_pred
    (params : Parameters) {k : ℕ}
    (hk : 400 * params.next.m * params.next.d ≤ k) :
    400 * params.m * params.d ≤ k := by
  have hm_le : params.m ≤ params.next.m := by
    simp [Parameters.next]
  have hcoef : 400 * params.m ≤ 400 * params.next.m :=
    Nat.mul_le_mul_left 400 hm_le
  have hmul :
      400 * params.m * params.d ≤ 400 * params.next.m * params.next.d := by
    simpa [Parameters.next, Nat.mul_assoc] using
      Nat.mul_le_mul_right params.d hcoef
  exact le_trans hmul hk

/-- Internal positive-degree successor assembly using the successor large-`k`
hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This is the same answer-valued assembly as
`mainInductionSuccessorNext_ofAnswerStageObligations`, but the elementary
predecessor side condition `400md ≤ k` is derived here from the successor
hypothesis `400(m+1)d ≤ k`.  The constructor for the answer-valued per-slice
induction data then derives `k ≥ 1` internally from this predecessor bound and
`d > 0`.  The remaining inputs are therefore exactly the mathematical
predecessor induction hypothesis and the answer-valued slice-transport
construction.

**Proof obligation:** This is an internal conditional reduction for the
positive-degree successor branch, tracked by issue #1507.  Elimination: prove
the predecessor answer-valued induction and slice-transport inputs from the
source successor hypotheses inside the induction proof. -/
theorem mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hinduction : AnswerMainInductionHypothesis params)
    (hd : 0 < params.d)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (sliceTransport :
      let hk_pred := mainInductionSuccessorBound_pred params hk_next
      let answerRestrict :=
        AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
          (answerRestrictedProbabilities params strategy eps delta gamma hgood)
      let answerInduction :=
        AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
          answerRestrict hinduction hd hk_pred
      AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
        answerRestrict answerInduction) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionSuccessorNext_ofAnswerStageObligations params strategy eps delta gamma k
      hgood hsmall hinduction hd
      (mainInductionSuccessorBound_pred params hk_next)
      sliceTransport

/-- Internal successor assembly after the large-error split.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This theorem removes the already solved large-error branch from the successor
frontier.  In the nontrivial branch it calls
`mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound`; in the
complementary branch it uses the trivial-measurement theorem
`mainInductionOfOneLeError`.  Thus the remaining positive-degree construction
is exactly the small-error answer-valued slice transport and the predecessor
answer-valued induction hypothesis.

**Proof obligation:** This is an internal conditional reduction for the
successor proof of `thm:main-induction`, tracked by issue #1507.  Elimination:
construct the small-error slice-transport data from the paper hypotheses; the
large-error branch is already discharged here. -/
theorem mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBoundSplit
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis params)
    (hd : 0 < params.d)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (sliceTransport :
      ∀ _hsmall : mainInductionError params.next k eps delta gamma < 1,
        let hk_pred := mainInductionSuccessorBound_pred params hk_next
        let answerRestrict :=
          AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
            (answerRestrictedProbabilities params strategy eps delta gamma hgood)
        let answerInduction :=
          AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
            answerRestrict hinduction hd hk_pred
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
        params strategy eps delta gamma k hgood hsmall hinduction hd hk_next
        (sliceTransport hsmall)
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Internal successor assembly after both the large-error and degree splits.

This theorem is not the paper theorem and should not be linked as
`\label{thm:main-induction}`.  It records the exact proof obligations that
remain after the already checked large-error branch has been removed.  In the
small-error branch, there are two cases:

* if `0 < params.d`, the proof calls the answer-valued successor assembly from
  the predecessor answer-valued induction hypothesis and the concrete
  answer-valued slice transport;
* if `params.d = 0`, the proof requires a separate degree-zero successor
  construction, analogous in role to the degree-zero branch of the pasting
  theorem.

Thus the positivity of the degree is not being added to the public successor
statement; it is only the branch condition for one internal construction route.

**Proof obligation:** This is an internal conditional reduction for the
successor proof of `thm:main-induction`, tracked by issue #1507 and documented
in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` for the surrounding
large-`k` interface correction.  Elimination: prove the degree-zero successor
construction and the positive-degree answer-valued slice realization from the
source successor hypotheses. -/
theorem mainInductionSuccessorNext_ofDegreeSplitObligations
    (params : Parameters)
    [FieldModel.{0} params.q]
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
      ∀ (hd : 0 < params.d),
        ∀ _hsmall : mainInductionError params.next k eps delta gamma < 1,
          let hk_pred := mainInductionSuccessorBound_pred params hk_next
          let answerRestrict :=
            AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
              (answerRestrictedProbabilities params strategy eps delta gamma hgood)
          let answerInduction :=
            AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
              answerRestrict hinduction hd hk_pred
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
          params strategy eps delta gamma k hgood hsmall hinduction hd hk_next
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

/-- Degree-zero successor assembly from averaged pasting data.

Paper origin: `references/ldt-paper/inductive_step.tex:486-551`, in the
successor proof of `\label{thm:main-induction}`.

This theorem identifies the degree-zero branch data used by
`DegreeZeroPastingFamilyObligation` with the already established averaged
pasting-data interface.  It is not a source theorem: the construction of the
averaged pasting data from the successor hypotheses remains the source-facing
work. -/
theorem mainInductionSuccessorNext_degreeZero_ofAveragedPastingData
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    {selfPkg :
      SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg}
    (pastingData :
      AveragedPastingData params strategy eps delta gamma k selfPkg)
    (hd_zero : params.d = 0) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let degreeZeroData :
      DegreeZeroPastingFamilyObligation params strategy eps delta gamma k :=
    DegreeZeroPastingFamilyObligation.ofAveragedPastingData pastingData
  exact
    mainInductionSuccessorNext_degreeZero_ofPastingFamily
      params strategy eps delta gamma k hgood degreeZeroData.family
      degreeZeroData.kappa degreeZeroData.zeta degreeZeroData.complete
      degreeZeroData.consistent hd_zero degreeZeroData.error_le

/-- Construction target for the degree-zero branch of the successor step.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, in the
successor step of `\label{thm:main-induction}`.

When Lean's successor proof is split by whether the predecessor degree is zero,
this is the remaining datum needed in the degree-zero branch: a complete and
point-consistent degree-zero slice family together with the scalar comparison
which absorbs the pasting error into the next main-induction error.  The
conditional assembly theorems below use only the fields of this datum; this
definition is the named construction target that must eventually be proved from
the source hypotheses.

**Proof obligation:** This declaration is intentionally a `sorry`-bodied
construction target, tracked by issue #1507.  Planned discharge: construct the
degree-zero slice family from the hypotheses of
`mainInductionSuccessorNextOfSmallError` under `params.d = 0`, then prove the
displayed scalar inequality for the produced losses. -/
noncomputable def DegreeZeroPastingFamilyObligation.ofSmallError
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (_hgood : strategy.IsGood eps delta gamma)
    (_hk_next : 400 * params.next.m * params.next.d ≤ k)
    (_hsmall : mainInductionError params.next k eps delta gamma < 1)
    (_hd_zero : params.d = 0) :
    DegreeZeroPastingFamilyObligation params strategy eps delta gamma k := by
  classical
  sorry

/-- Internal small-error successor assembly from the two degree branches.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This theorem is not a paper theorem.  It records that the small-error successor
branch follows once the proof has supplied its two branch constructions: in
degree zero, a complete and point-consistent slice family with scalar error
absorbed into the next main-induction error; in positive degree, the
answer-valued predecessor induction hypothesis and the slice-strategy transport
needed to run the induction-section self-improvement theorem.  The equivalent
named degree-zero construction target is
`DegreeZeroPastingFamilyObligation`.

No one of these objects is added as a hypothesis to `thm:main-induction`.  The
source-facing theorem `mainInductionSuccessorNextOfSmallError` must still
construct them from the displayed successor hypotheses.

**Internal proof obligation:** This conditional assembly theorem is tracked by
issue #1507.  Planned discharge: prove the degree-zero family construction and
the positive-degree answer-slice transport from the hypotheses of
`mainInductionSuccessorNextOfSmallError`, and then call this theorem. -/
theorem mainInductionSuccessorNextOfSmallError_ofDegreeSplitPastingObligations
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (degreeZeroPasting :
      params.d = 0 →
        ∃ family : IdxPolyFamily params ι, ∃ kappa zeta : Error,
          family.Complete strategy.state kappa ∧
            family.ConsistentWithPoints strategy zeta ∧
              ldPastingInInductionError params k eps delta gamma kappa zeta ≤
                mainInductionError params.next k eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{0, uι} params)
    (hsliceTransport :
      ∀ (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
        (inductionPkg :
          AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k),
        AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
          restrictionPkg inductionPkg) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  by_cases hd : 0 < params.d
  · let answerRestrict :
        AnswerSliceRestrictionData params strategy eps delta gamma :=
        AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
          (answerRestrictedProbabilities params strategy eps delta gamma hgood)
    let answerInduction :
        AnswerPerSliceInductionData params strategy eps delta gamma answerRestrict k :=
        @AnswerPerSliceInductionData.ofMainInductionHypothesis
          ι _ _ params _ strategy eps delta gamma k answerRestrict hinduction hd
          (mainInductionSuccessorBound_pred params hk_next)
    exact
      @mainInductionSuccessorNext_ofAnswerStageObligations
        ι _ _ params _ strategy eps delta gamma k hgood hsmall hinduction hd
        (mainInductionSuccessorBound_pred params hk_next)
        (hsliceTransport answerRestrict answerInduction)
  · rcases degreeZeroPasting (Nat.eq_zero_of_not_pos hd) with
      ⟨family, kappa, zeta, hcomplete, hcons, herror⟩
    exact
      mainInductionSuccessorNext_degreeZero_ofPastingFamily
        params strategy eps delta gamma k hgood family kappa zeta
        hcomplete hcons (Nat.eq_zero_of_not_pos hd) herror

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

**Proof obligation:** This is an internal conditional reduction for the
degree-zero branch of the successor proof, tracked by issue #1507.  Elimination:
construct the complete point-consistent slice family and prove the scalar
absorption inequality from the source successor hypotheses. -/
theorem mainInductionSuccessorNext_ofDegreeSplitPastingObligations
    (params : Parameters)
    [FieldModel.{0} params.q]
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
      ∀ (hd : 0 < params.d),
        ∀ _hsmall : mainInductionError params.next k eps delta gamma < 1,
          let hk_pred := mainInductionSuccessorBound_pred params hk_next
          let answerRestrict :=
            AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
              (answerRestrictedProbabilities params strategy eps delta gamma hgood)
          let answerInduction :=
            AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
              answerRestrict hinduction hd hk_pred
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

/-- Internal small-error successor reduction from the two remaining
construction inputs and the predecessor induction hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, restricted to
the nontrivial regime
`mainInductionError params.next k eps delta gamma < 1`.

This theorem is not a paper theorem.  It records the precise point at which the
eventual proof by induction on the dimension will use its predecessor
induction hypothesis.  Once that hypothesis, the degree-zero family-and-scalar
construction, and the positive-degree answer-valued slice transport have been
constructed internally, the small-error successor conclusion follows by the
checked degree split above.  None of these inputs should be added to
`thm:main-induction` or `thm:main-formal` as source hypotheses. -/
theorem mainInductionSuccessorNext_ofSmallErrorConstruction_ofInternalConstructions
    (params : Parameters)
    [FieldModel.{0} params.q]
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
      ∀ (hd : 0 < params.d),
        let hk_pred := mainInductionSuccessorBound_pred params hk_next
        let answerRestrict :=
          AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
            (answerRestrictedProbabilities params strategy eps delta gamma hgood)
        let answerInduction :=
          AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
            answerRestrict hinduction hd hk_pred
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
        params strategy eps delta gamma k hgood hsmall hinduction hd hk_next
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
pasting data, or arbitrary implication hypotheses as
assumptions of the theorem.

**Proof obligation:** Construct the answer-valued restricted slice profile,
obtain the recursive predecessor induction conclusion for each slice, realize
the slice-wise self-improvement interface, assemble the pasting input, and prove
the scalar absorption estimates.  The checked assembly theorems above reduce
this to the degree-zero family-and-scalar construction, the predecessor
induction argument, and the positive-degree answer-valued slice realization.
The predecessor induction argument is the genuine recursive part of
`thm:main-induction`: it should be supplied by the eventual proof by induction
on the dimension and then consumed by the internal reduction
`mainInductionSuccessorNext_ofDegreeSplitPastingObligations`, not postulated as
an extra hypothesis of the paper-facing main induction theorem or the final
soundness theorem.

**Unfaithful:** This proof currently contains the tracked `sorry` for the
small-error successor construction, so it uses `sorryAx` rather than deriving
the construction from `references/ldt-paper/inductive_step.tex:441-551`.
Documented in issue #1507 under #1458.  Elimination: prove this theorem by
supplying the predecessor induction argument, the degree-zero family-and-scalar
construction, and the positive-degree answer-valued slice realization, then
apply
`mainInductionSuccessorNext_ofSmallErrorConstruction_ofInternalConstructions`.
This is tracked by issue #1507 under the source-statement boundary tracker
#1458. -/
theorem mainInductionSuccessorNext_ofSmallErrorConstruction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (_hgood : strategy.IsGood eps delta gamma)
    (_hk : 400 * params.next.m * params.next.d ≤ k)
    (_hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  -- TODO(#1507, #1458): supply the predecessor induction hypothesis, construct
  -- the degree-zero family/scalar branch, and realize the positive-degree
  -- slice transport, then apply the checked small-error internal reduction.
  sorry

/-- Native successor step for `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the proof
passes from dimension `m` to dimension `m + 1`.

This is the native successor step for the corrected large-`k` Lean interface:
the ambient strategy already lives in dimension `params.next`, so no predecessor
compatibility record is introduced.  The checked reductions above show that the
small-error branch now reduces to three internal inputs: the predecessor
answer-valued induction hypothesis, the degree-zero family-and-scalar
construction, and the positive-degree slice transport.

**Proof obligation:** In the small-error regime, construct the degree-zero
slice family and scalar absorption, obtain the recursive predecessor induction
conclusion for the answer-valued restricted slices, and either realize the
positive-degree answer-valued slice transport through ordinary `SymStrat`s or
prove the corresponding self-improvement statement in the answer-valued
interface.  The recursive predecessor conclusion should be supplied by the
eventual induction proof, not added as a public hypothesis of this theorem.

**Unfaithful:** The small-error branch currently calls
`mainInductionSuccessorNext_ofSmallErrorConstruction`, whose proof is still a
tracked `sorry`.  Thus this theorem transitively uses `sorryAx` for the
successor construction in `references/ldt-paper/inductive_step.tex:441-551`.
Documented in issue #1507 under #1458.  Elimination: replace the call by a proof
of the named small-error construction from the theorem hypotheses.
This is tracked by issue #1507 under the source-statement boundary tracker
#1458. -/
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

**Unfaithful:** The proof transitively uses the tracked small-error successor
construction
`mainInductionSuccessorNext_ofSmallErrorConstruction`, which is not yet derived
from `references/ldt-paper/inductive_step.tex:441-551`.  Documented in issue
#1507 under #1458.  Elimination: prove the native successor step from the
checked internal constructions and then this decomposition theorem becomes
standard-axiom clean. -/
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

/-- Corrected large-`k` interface toward `thm:main-induction`.

This is not the printed source theorem.  It is the separate Lean interface
linked from `thm:main-induction-current-interface`: a good symmetric strategy
and an integer `k ≥ 400 m d` produce a polynomial measurement consistent with
the point measurement at error `mainInductionError`.  The strengthening from
the printed `k ≥ m d` hypothesis in
`references/ldt-paper/inductive_step.tex` is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`, and the printed source
theorem remains unlinked in the blueprint.

**Proof gap:** the base case is proved by `mainInductionBaseCase`. The
successor case is isolated as the corrected large-`k` theorem
`mainInductionSuccessor`, corresponding to
`references/ldt-paper/inductive_step.tex:441-551`.  This gap is tracked by
#1507 and #1458.  The proof should derive the restricted probability estimates,
recursive slice measurements, slice-wise self-improvement outputs, and pasting
side condition internally, rather than adding any of them to the theorem
statement.

**Unfaithful:** The successor branch transitively uses the tracked construction
obligation `mainInductionSuccessorNext_ofSmallErrorConstruction`, so this
corrected large-`k` interface still imports `sorryAx`.  Documented in issue
#1507 under #1458 and in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  This is the successor
construction of `references/ldt-paper/inductive_step.tex:441-551`.
Elimination: prove the small-error successor construction from the assumptions
of the corrected large-`k` interface. -/
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
