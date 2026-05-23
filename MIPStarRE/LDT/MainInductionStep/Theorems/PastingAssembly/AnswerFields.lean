import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.Basic

/-!
# Section 6 — Pasting Assembly: Answer-Valued Fields

This module assembles the answer-valued averaged family fields and the
commutativity input used by the pasting theorem.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Assemble the averaged polynomial family fields in the answer-valued
successor route.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`.
The statement records exactly the conclusions obtained from the recursive
answer-valued slice measurements and the axis-parallel/self-consistency
self-improvement theorem: averaged completeness, point consistency with the
ambient answer-valued point measurement, strong self-consistency, the
slice-boundedness input for the point-equivalent ordinary carrier, and the two
scalar estimates for `κ` and `ζ`.

**Lean-only:** The final boundedness field is expressed using
`answerSelfImprovementCarrier` only because the present boundedness interface is
typed for ordinary strategies.  This theorem does not invoke
`ldPastingInInductionSection`, and does not assert that the carrier's dummy
diagonal measurement satisfies the answer-valued diagonal-line test.  This
internal construction is tracked in issue #1507.  Discharge: proved here from
the recursive answer-valued slice measurements and the answer-valued
self-improvement construction. -/
theorem answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis.{uι', uF}
    {ι' : Type uι'} [Fintype ι'] [DecidableEq ι']
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next ι')
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι'} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ family : IdxPolyFamily params ι',
      ∃ kappa : Error,
        family.Complete strategy.state kappa ∧
          ConsRel strategy.state (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (IdxPolyFamily.evaluatedAtNextPoint family)
            (selfImprovementInInductionError params.next eps delta gamma) ∧
          family.StronglySelfConsistent strategy.state
            (selfImprovementInInductionError params.next eps delta gamma) ∧
          IdxPolyFamily.SliceBoundednessInput
            (answerSelfImprovementCarrier params.next strategy)
            family
            (selfImprovementInInductionError params.next eps delta gamma) ∧
          kappa ≤
            ((params.m : Error) ^ (2 : ℕ)) *
                (mainInductionNu params.next k eps delta gamma +
                  Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))
              + selfImprovementInInductionError params.next eps delta gamma ∧
          selfImprovementInInductionError params.next eps delta gamma ≤
            mainInductionNu params.next k eps delta gamma := by
  classical
  rcases answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis
      params strategy eps delta gamma k hgood hinduction hk_next hsmall with
    ⟨profile, sliceError, _sliceMeasurement, sliceProj, sliceWitness,
      _haxis, _hself, _hdiag, _hrecPoint, _hrecError, havgSigma, havgZeta,
      hcompleteSlice, hpointSlice, _hsscSlice, hselfCloseSlice, hboundedSlice,
      hdomSlice⟩
  let sliceSelfError : Fq params → Error := fun x =>
    selfImprovementInInductionError params
      (profile.axisParallel x) (profile.selfConsistency x) (profile.diagonal x)
  let family : IdxPolyFamily params ι' :=
    { meas := sliceProj
      witness := sliceWitness
      dominationTarget := fun x h =>
        IdxPolyFamily.averagedSlicePointEvaluationOperator
          (answerSelfImprovementCarrier params.next strategy) x h }
  let kappa : Error :=
    avgOver (uniformDistribution (Fq params)) sliceError +
      avgOver (uniformDistribution (Fq params)) sliceSelfError
  refine ⟨family, kappa, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [family, kappa, sliceSelfError] using
      idxPolyFamily_complete_of_slice_bounds params strategy.state family
        sliceError sliceSelfError
        (by
          intro x
          simpa [family, sliceSelfError] using hcompleteSlice x)
  · simpa [family, sliceSelfError] using
      answer_family_consistency_of_slice_bounds params strategy family
        sliceSelfError
        (selfImprovementInInductionError params.next eps delta gamma)
        (by
          intro x
          simpa [family, sliceSelfError] using hpointSlice x)
        (by
          simpa [sliceSelfError] using havgZeta)
  · simpa [family, sliceSelfError] using
      idxPolyFamily_stronglySelfConsistent_of_slice_bounds params strategy.state family
        sliceSelfError
        (selfImprovementInInductionError params.next eps delta gamma)
        (by
          intro x
          simpa [family, sliceSelfError] using hselfCloseSlice x)
        (by
          simpa [sliceSelfError] using havgZeta)
  · simpa [family, sliceSelfError] using
      idxPolyFamily_sliceBoundednessInput_of_slice_bounds params
        (answerSelfImprovementCarrier params.next strategy) family sliceSelfError
        (selfImprovementInInductionError params.next eps delta gamma)
        (by
          intro x
          simpa [family, sliceSelfError] using hboundedSlice x)
        (by
          simpa [sliceSelfError] using havgZeta)
        (by
          intro x h
          simpa [family] using hdomSlice x h)
  · dsimp [kappa, sliceSelfError]
    nlinarith [havgSigma, havgZeta]
  · have heps_le_one :
        eps ≤ 1 := answer_eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
    have hdelta_le_one :
        delta ≤ 1 :=
      answer_delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
    have hdq_le_q :
        params.d ≤ params.q :=
      answer_dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall
    exact
      answer_selfImprovementInInductionError_le_mainInductionNu
        params strategy eps delta gamma k hgood hsmall heps_le_one hdelta_le_one hdq_le_q

/-- Answer-valued induction-section pasting from an explicit commutativity input.

This theorem performs the checked final assembly once the answer-valued
analogue of the Section 11 commutativity theorem has been supplied for the
point-equivalent ordinary carrier.  The hypotheses `hcom` and `herror_le` are
not source assumptions; they are the internal commutativity construction and
scalar absorption targets for the answer-valued pasting route. -/
theorem answerLdPastingInInductionSectionOfComMainAndErrorBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (kappa zeta : Error)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
        zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound :
      IdxPolyFamily.SliceBoundednessInput
        (answerSelfImprovementCarrier params.next strategy)
        family zeta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k)
    (hcom :
      Commutativity.ComMainConclusion params
        (answerSelfImprovementCarrier params.next strategy) family gamma zeta)
    (herror_le :
      ldPastingInInductionError params k eps delta gamma kappa zeta ≤
        mainInductionError params.next k eps delta gamma) :
    AnswerMainInductionConclusion params.next strategy eps delta gamma k := by
  let carrier := answerSelfImprovementCarrier params.next strategy
  have haxis :
      carrier.axisParallelFailureProbability ≤ eps := by
    have hfail :
        carrier.axisParallelFailureProbability =
          strategy.axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability
        AnswerSymStrat.axisParallelFailureProbability
        axisParallelPointAnswerFamily AnswerSymStrat.axisParallelPointAnswerFamily
        axisParallelLineAnswerFamily AnswerSymStrat.axisParallelLineAnswerFamily
      simp [carrier, answerSelfImprovementCarrier]
    simpa [hfail] using hgood.axisParallelTest
  have hself_good :
      carrier.selfConsistencyFailureProbability ≤ delta := by
    have hfail :
        carrier.selfConsistencyFailureProbability =
          strategy.selfConsistencyFailureProbability := by
      unfold SymStrat.selfConsistencyFailureProbability
        AnswerSymStrat.selfConsistencyFailureProbability
      simp [carrier, answerSelfImprovementCarrier]
    simpa [hfail] using hgood.selfConsistencyTest
  have hcompleteCarrier : family.Complete carrier.state kappa := by
    simpa [carrier, answerSelfImprovementCarrier] using hcomplete
  have hconsCarrier : family.ConsistentWithPoints carrier zeta := by
    exact ⟨by simpa [carrier, answerSelfImprovementCarrier] using hcons⟩
  have hselfCarrier : family.StronglySelfConsistent carrier.state zeta := by
    simpa [carrier, answerSelfImprovementCarrier] using hself
  have hsubmeas :
      ConsRel carrier.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas carrier.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (Pasting.constructedPastedSubMeas params family k))
        (ldPastingInInductionNu params k eps delta gamma zeta) := by
    exact Pasting.hAConsistency_submeas_ofComMain_of_axis_self params carrier
      eps delta gamma zeta haxis hself_good hgamma_nonneg hgamma_le
      hzeta_nonneg hzeta_le hdq_le hd family hconsCarrier hselfCarrier hbound
      hcom k hk_pos
  have hN :
      Pasting.LdPastingNCompletenessStatement params carrier family kappa
        (ldPastingInInductionNu params k eps delta gamma zeta) k := by
    exact Pasting.ldPastingNCompleteness_ofComMain_of_axis_self params carrier
      eps delta gamma kappa zeta haxis hself_good hgamma_nonneg hgamma_le
      hzeta_nonneg hzeta_le hdq_le hd family hcompleteCarrier hconsCarrier
      hselfCarrier hcom k hk_pos hk
  have hpastedCarrier :
      ConsRel carrier.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas carrier.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (Pasting.constructedPastedMeasurement params family k).toSubMeas)
        (ldPastingInInductionError params k eps delta gamma kappa zeta) := by
    exact Pasting.hAConsistency_completed params carrier eps delta gamma kappa zeta
      family k hsubmeas hN.completenessBound
  have hpasted :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (Pasting.constructedPastedMeasurement params family k).toSubMeas)
        (ldPastingInInductionError params k eps delta gamma kappa zeta) := by
    simpa [carrier, answerSelfImprovementCarrier] using hpastedCarrier
  refine ⟨Pasting.constructedPastedMeasurement params family k, ?_⟩
  exact ⟨le_trans hpasted.offDiagonalBound herror_le⟩

/-- Answer-valued Section 11 commutativity input needed by the positive-degree
pasting branch.

This is a Lean-only construction target, not a source theorem and not a
hypothesis of `thm:main-induction`.  It is the precise replacement for the invalid route
through the ordinary carrier's dummy diagonal measurement: the conclusion is
the ordinary `ComMainConclusion` for the point-equivalent carrier, but the
intended proof must use the answer-valued diagonal verifier relation of
`strategy`.

The proof first establishes the Section 10 point-commutativity estimate from
the answer-valued diagonal-line test, transfers that estimate to the
point-equivalent carrier, and then invokes the Section 11 scalar chain in its
form that assumes point commutativity rather than an ordinary diagonal
`IsGood` field. -/
theorem answerComMainForCarrier_ofAnswerGood
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params ι)
    (hcons :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
        zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound :
      IdxPolyFamily.SliceBoundednessInput
        (answerSelfImprovementCarrier params.next strategy)
        family zeta) :
    Commutativity.ComMainConclusion params
      (answerSelfImprovementCarrier params.next strategy) family gamma zeta := by
  let carrier : SymStrat params.next ι := answerSelfImprovementCarrier params.next strategy
  have hcommAnswer :
      SDDOpRel strategy.state
        (uniformDistribution (MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (CommutativityPoints.answerPointMeasurementProductLeft params.next strategy)
        (CommutativityPoints.answerPointMeasurementProductRight params.next strategy)
        (CommutativityPoints.commutativityPointsError params.next gamma) :=
    CommutativityPoints.answerCommutativityPoints
      (params := params.next) strategy eps delta gamma hgood
  have hcommCarrier :
      SDDOpRel carrier.state
        (uniformDistribution (MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (CommutativityPoints.pointMeasurementProductLeft params.next carrier)
        (CommutativityPoints.pointMeasurementProductRight params.next carrier)
        (CommutativityPoints.commutativityPointsError params.next gamma) := by
    simpa [carrier, answerSelfImprovementCarrier,
      CommutativityPoints.answerPointMeasurementProductLeft,
      CommutativityPoints.answerPointMeasurementProductRight,
      CommutativityPoints.pointMeasurementProductLeft,
      CommutativityPoints.pointMeasurementProductRight] using hcommAnswer
  have hconsCarrier : family.ConsistentWithPoints carrier zeta := by
    exact ⟨by simpa [carrier, answerSelfImprovementCarrier] using hcons⟩
  exact
    Commutativity.comMain_of_commutativityPoints
      params carrier gamma zeta carrier.isNormalized hcommCarrier hgamma_nonneg
      family hconsCarrier hself hbound


end MIPStarRE.LDT.MainInductionStep
