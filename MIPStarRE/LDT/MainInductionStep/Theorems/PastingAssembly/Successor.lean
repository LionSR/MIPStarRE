import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.ErrorBounds

/-!
# Section 6 — Pasting Assembly: Successor Assembly

This module contains the final answer-valued pasting obligation, averaged
pasting data constructors, and ordinary successor assembly corollaries.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Answer-valued induction-section pasting obligation for the small-error
successor branch.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-50` and its use in
`references/ldt-paper/inductive_step.tex:541-551`.

This is a Lean-only answer-valued analogue of the final pasting invocation
needed in the simultaneous successor proof.  Its hypotheses are the averaged
family fields already proved from the recursive answer-valued slices: averaged
completeness, consistency with the actual answer-valued point measurement,
strong self-consistency, and the boundedness input currently typed through the
point-equivalent ordinary carrier.  The conclusion is the successor
answer-valued main-induction consistency statement.

This proof uses the answer-valued point-commutativity theorem and the Section 11
scalar commutativity chain, so the diagonal-line input is the answer-valued
verifier relation itself rather than an ordinary dummy diagonal carrier.  It is
an internal successor-construction theorem, not the source theorem
`thm:ld-pasting`. -/
theorem answerLdPastingInInductionSectionOfSmallError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (family : IdxPolyFamily params ι)
    (kappa : Error)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
        (selfImprovementInInductionError params.next eps delta gamma))
    (hself :
      family.StronglySelfConsistent strategy.state
        (selfImprovementInInductionError params.next eps delta gamma))
    (hbound :
      IdxPolyFamily.SliceBoundednessInput
        (answerSelfImprovementCarrier params.next strategy)
        family
        (selfImprovementInInductionError params.next eps delta gamma))
    (hkappa_le :
      kappa ≤
        ((params.m : Error) ^ (2 : ℕ)) *
            (mainInductionNu params.next k eps delta gamma +
              Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))
          + selfImprovementInInductionError params.next eps delta gamma)
    (hzeta_le_nu :
      selfImprovementInInductionError params.next eps delta gamma ≤
        mainInductionNu params.next k eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k) :
    AnswerMainInductionConclusion params.next strategy eps delta gamma k := by
  by_cases hd : 0 < params.d
  · let zeta : Error := selfImprovementInInductionError params.next eps delta gamma
    have hk_pos : 1 ≤ k :=
      one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
    have hgamma_nonneg : 0 ≤ gamma :=
      answer_gamma_nonneg_of_isGood params.next strategy hgood
    have hgamma_le : gamma ≤ 1 :=
      answer_gamma_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
    have hzeta_nonneg : 0 ≤ zeta := by
      exact le_trans
        (bipartiteConsError_nonneg strategy.state
          (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (IdxPolyFamily.evaluatedAtNextPoint family))
        hcons.offDiagonalBound
    have hzeta_le : zeta ≤ 1 := by
      simpa [zeta] using
        answer_selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
          params strategy hgood hsmall
    have hdq_le : params.d ≤ params.q :=
      answer_dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall
    have herror_le :
        ldPastingInInductionError params k eps delta gamma kappa zeta ≤
          mainInductionError params.next k eps delta gamma := by
      exact answerLdPastingInInductionError_le_mainInductionError_of_smallError
        params strategy eps delta gamma kappa k hgood hsmall
        hkappa_le hzeta_le_nu
    have hcom :
        Commutativity.ComMainConclusion params
          (answerSelfImprovementCarrier params.next strategy) family gamma zeta :=
      answerComMainForCarrier_ofAnswerGood params strategy eps delta gamma zeta
        hgood hgamma_nonneg family
        (by simpa [zeta] using hcons) (by simpa [zeta] using hself)
        (by simpa [zeta] using hbound)
    exact answerLdPastingInInductionSectionOfComMainAndErrorBound
      params strategy eps delta gamma k hgood family kappa zeta
      hcomplete (by simpa [zeta] using hcons) (by simpa [zeta] using hself)
      (by simpa [zeta] using hbound)
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hd hk_pos hk hcom herror_le
  · exact answerLdPastingInInductionSectionDegreeZeroOfSmallError
      params strategy eps delta gamma k hgood hsmall family kappa hcomplete hcons hself hbound
      hkappa_le hzeta_le_nu hk (Nat.eq_zero_of_not_pos hd)

/-- Internal successor reduction from the predecessor answer-valued induction
hypothesis and the answer-valued pasting obligation.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

**Conditional:** This theorem is not the source successor theorem.  It records
that, once the
recursive predecessor hypothesis is available inside a genuine induction on
the dimension, all remaining slice restriction, self-improvement, averaging,
and scalar fields reduce the successor branch to
`answerLdPastingInInductionSectionOfSmallError`.  It is tracked in issue #1507.
Discharge: proved here from the predecessor answer-valued induction hypothesis
and the proved answer-valued pasting invocation. -/
theorem answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    AnswerMainInductionConclusion params.next strategy eps delta gamma k := by
  rcases answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis
      params strategy eps delta gamma k hgood hinduction hk_next hsmall with
    ⟨family, kappa, hcomplete, hcons, hself, hbound, hkappa_le, hzeta_le_nu⟩
  exact
    answerLdPastingInInductionSectionOfSmallError
      params strategy eps delta gamma k hgood hsmall family kappa hcomplete hcons hself hbound
      hkappa_le hzeta_le_nu (mainInductionSuccessorBound_pred params hk_next)

namespace AnswerSelfImprovementData

/-- Averaged completeness of the family obtained from answer-valued
self-improvement data. -/
lemma complete_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerPerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : AnswerSelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    hself.family.Complete strategy.state
      (avgOver (uniformDistribution (Fq params)) hinduction.sliceError +
        avgOver (uniformDistribution (Fq params))
          (fun x => answerSliceSelfImprovementError params hrestrict x)) := by
  simpa [AnswerSelfImprovementData.family] using
    idxPolyFamily_complete_of_slice_bounds params strategy.state hself.family
      hinduction.sliceError
      (fun x => answerSliceSelfImprovementError params hrestrict x)
      hself.completeness

/-- Averaged point-consistency of the family obtained from answer-valued
self-improvement data, in the ordinary ambient interface. -/
lemma consistentWithPoints_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerPerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : AnswerSelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    hself.family.ConsistentWithPoints strategy
      (selfImprovementInInductionError params.next eps delta gamma) := by
  refine ⟨?_⟩
  refine ⟨?_⟩
  calc
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint hself.family)
      = avgOver (uniformDistribution (Fq params))
          (fun x =>
            bipartiteConsError strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas
                (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
              (polynomialEvaluationFamily params (hself.family.meas x).toSubMeas)) :=
          family_answerRestrictedPointConsistencyError_eq_avg params strategy hself.family
    _ ≤ avgOver (uniformDistribution (Fq params))
          (fun x => answerSliceSelfImprovementError params hrestrict x) := by
          exact avgOver_mono (uniformDistribution (Fq params)) _ _ fun x =>
            (by simpa [AnswerSelfImprovementData.family] using
              (hself.pointConsistency x).offDiagonalBound)
    _ ≤ selfImprovementInInductionError params.next eps delta gamma :=
          average_answerSliceSelfImprovementError_le params strategy eps delta gamma hgood
            hrestrict

/-- Averaged strong self-consistency of the family obtained from answer-valued
self-improvement data. -/
lemma stronglySelfConsistent_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerPerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : AnswerSelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    hself.family.StronglySelfConsistent strategy.state
      (selfImprovementInInductionError params.next eps delta gamma) := by
  exact
    idxPolyFamily_stronglySelfConsistent_of_slice_bounds params strategy.state hself.family
      (fun x => answerSliceSelfImprovementError params hrestrict x)
      (selfImprovementInInductionError params.next eps delta gamma)
      (by simpa [AnswerSelfImprovementData.family] using hself.selfCloseness)
      (average_answerSliceSelfImprovementError_le params strategy eps delta gamma hgood hrestrict)

/-- Averaged boundedness of the family obtained from answer-valued
self-improvement data, in the ordinary ambient pasting interface.

**Lean-only:** This is an internal adapter for the induction-section pasting
interface, tracked in issue #1507.  Paper origin:
`references/ldt-paper/inductive_step.tex:461-551`.  Discharge: proved here by
applying `idxPolyFamily_sliceBoundednessInput_of_slice_bounds` to the
answer-valued self-improvement data. -/
lemma sliceBoundednessInput_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerPerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : AnswerSelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    IdxPolyFamily.SliceBoundednessInput strategy hself.family
      (selfImprovementInInductionError params.next eps delta gamma) := by
  exact
    idxPolyFamily_sliceBoundednessInput_of_slice_bounds params strategy hself.family
      (fun x => answerSliceSelfImprovementError params hrestrict x)
      (selfImprovementInInductionError params.next eps delta gamma)
      (by simpa [AnswerSelfImprovementData.family] using hself.bounded)
      (average_answerSliceSelfImprovementError_le params strategy eps delta gamma hgood hrestrict)
      (by simpa [AnswerSelfImprovementData.family] using hself.dominatesAveragePointOperator)

end AnswerSelfImprovementData

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:12-50`
(`\label{thm:ld-pasting}`) and
`references/ldt-paper/inductive_step.tex:239-342`.

The remaining averaged step from per-slice self-improvement data to the
pasting hypotheses.

This is where the paper's `E_x[σ_x]`, `E_x[ζ_x]`, and
`σ* ≤ mainInductionError` bookkeeping will eventually live. -/
noncomputable def assembleAveragedPastingData
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1)
    (hdq_le_q : params.d ≤ params.q)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma)
    (hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementData params strategy eps delta gamma k hrestrict hinduction)
    (_hk : 400 * params.m * params.d ≤ k) :
    AveragedPastingData params strategy eps delta gamma k hself := by
  classical
  let 𝒟 : Distribution (Fq params) := uniformDistribution (Fq params)
  let zeta : Error := selfImprovementInInductionError params.next eps delta gamma
  let kappa : Error :=
    avgOver 𝒟 (fun x => hinduction.sliceError x) +
      avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x)
  refine AveragedPastingData.mk kappa zeta ?_ ?_ ?_ ?_ ?_
  · simpa [kappa, SelfImprovementData.family] using
      idxPolyFamily_complete_of_slice_bounds params strategy.state hself.family
        hinduction.sliceError
        (fun x => sliceSelfImprovementError params hrestrict x)
        hself.completeness
  · refine ⟨?_⟩
    refine ⟨?_⟩
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (IdxPolyFamily.evaluatedAtNextPoint hself.family)
        = avgOver 𝒟
            (fun x =>
              bipartiteConsError strategy.state (uniformDistribution (Point params))
                (IdxProjMeas.toIdxSubMeas
                  (xRestrictedStrategy params strategy x).pointMeasurement)
                (polynomialEvaluationFamily params (hself.sliceProj x).toSubMeas)) :=
            family_pointConsistencyError_eq_avg params strategy hself
      _ ≤ avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x) := by
            exact avgOver_mono 𝒟 _ _ fun x => (hself.pointConsistency x).offDiagonalBound
      _ ≤ zeta := by
            simpa [zeta, 𝒟] using
              (average_sliceSelfImprovementError_le
                params strategy eps delta gamma hgood hrestrict)
  · exact
      idxPolyFamily_stronglySelfConsistent_of_slice_bounds params strategy.state hself.family
        (fun x => sliceSelfImprovementError params hrestrict x) zeta
        (by simpa [SelfImprovementData.family] using hself.selfCloseness)
        (by
          simpa [zeta, 𝒟] using
            (average_sliceSelfImprovementError_le
              params strategy eps delta gamma hgood hrestrict))
  · exact
      idxPolyFamily_sliceBoundednessInput_of_slice_bounds params strategy hself.family
        (fun x => sliceSelfImprovementError params hrestrict x) zeta
        (by simpa [SelfImprovementData.family] using hself.bounded)
        (by
          simpa [zeta, 𝒟] using
            (average_sliceSelfImprovementError_le
              params strategy eps delta gamma hgood hrestrict))
        (by simpa [SelfImprovementData.family] using hself.dominatesAveragePointOperator)
  · have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
    have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
    have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
    have heps_le_one :=
      eps_le_one_of_selfImprovementInInductionError_le_one
        params strategy hgood hzeta_le
    have hdelta_le_one :=
      delta_le_one_of_selfImprovementInInductionError_le_one
        params strategy hgood hzeta_le
    have hkappa_le :
        kappa ≤
          ((params.m : Error) ^ (2 : ℕ)) *
              (mainInductionNu params.next k eps delta gamma +
                Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))
            + zeta := by
      dsimp [kappa, zeta]
      nlinarith
        [average_sliceError_le params strategy eps delta gamma k hgood hrestrict hinduction,
          average_sliceSelfImprovementError_le
            params strategy eps delta gamma hgood hrestrict]
    have hzeta_le_nu :
        zeta ≤ mainInductionNu params.next k eps delta gamma := by
      simpa [zeta] using
        selfImprovementInInductionError_le_mainInductionNu
          params strategy eps delta gamma k
          hgood hsmall heps_le_one hdelta_le_one hdq_le_q
    have hnu_le :
        ldPastingInInductionNu params k eps delta gamma zeta ≤
          (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma := by
      simpa [zeta] using
        ldPastingInInductionNu_le_fifth_mainInductionNu
          params eps delta gamma k
          heps_nonneg hdelta_nonneg hgamma_nonneg
          heps_le_one hdelta_le_one hgamma_le hdq_le_q
    exact
      ldPastingInInductionError_le_mainInductionError_of_bounds
        params eps delta gamma k kappa zeta
        heps_nonneg hdelta_nonneg hgamma_nonneg
        hkappa_le hzeta_le_nu hnu_le

/-- Assemble the averaged pasting data in the nontrivial small-error branch.

Paper origin: `references/ldt-paper/inductive_step.tex:486-551`.  The small-error
hypothesis supplies `γ ≤ 1`, `ζ ≤ 1`, and `d ≤ q`, so callers do not carry
those scalar estimates as separate proof inputs. -/
noncomputable def assembleAveragedPastingDataOfSmallError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma)
    (hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementData params strategy eps delta gamma k hrestrict hinduction)
    (hk : 400 * params.m * params.d ≤ k) :
    AveragedPastingData params strategy eps delta gamma k hself :=
  assembleAveragedPastingData params strategy eps delta gamma k hgood hsmall
    (gamma_le_one_of_mainInductionError_lt_one params strategy hgood hsmall)
    (selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
      params strategy hgood hsmall)
    (dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall)
    hrestrict hinduction hself hk

/-- Direct answer-valued small-error successor assembly over an ordinary ambient
strategy.

This is the same mathematical assembly as
`mainInductionFromAnswerStageDataOfSmallError`, but it invokes the
induction-section pasting theorem directly from the answer-valued slice
self-improvement data rather than first converting that data into the legacy
`SelfImprovementData` record. -/
theorem mainInductionFromAnswerStageDataOfSmallErrorDirect.{uι', uF}
    {ι' : Type uι'} [Fintype ι'] [DecidableEq ι']
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next ι')
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (answerRestrict : AnswerSliceRestrictionData.{uι', uF} params strategy eps delta gamma)
    (answerInduction :
      AnswerPerSliceInductionData.{uι', uF} params strategy eps delta gamma answerRestrict k)
    (answerSelf :
      AnswerSelfImprovementData.{uι', uF} params strategy eps delta gamma k answerRestrict
        answerInduction)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι',
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let family : IdxPolyFamily params ι' := answerSelf.family
  let kappa : Error :=
    avgOver (uniformDistribution (Fq params)) answerInduction.sliceError +
      avgOver (uniformDistribution (Fq params))
        (fun x => answerSliceSelfImprovementError params answerRestrict x)
  let zeta : Error := selfImprovementInInductionError params.next eps delta gamma
  have hcomplete : family.Complete strategy.state kappa := by
    simpa [family, kappa] using
      AnswerSelfImprovementData.complete_of_slice_bounds
        params strategy eps delta gamma k answerRestrict answerInduction answerSelf
  have hcons : family.ConsistentWithPoints strategy zeta := by
    simpa [family, zeta] using
      AnswerSelfImprovementData.consistentWithPoints_of_slice_bounds
        params strategy eps delta gamma k hgood answerRestrict answerInduction answerSelf
  have hselfConsistent : family.StronglySelfConsistent strategy.state zeta := by
    simpa [family, zeta] using
      AnswerSelfImprovementData.stronglySelfConsistent_of_slice_bounds
        params strategy eps delta gamma k hgood answerRestrict answerInduction answerSelf
  have hbounded : IdxPolyFamily.SliceBoundednessInput strategy family zeta := by
    simpa [family, zeta] using
      AnswerSelfImprovementData.sliceBoundednessInput_of_slice_bounds
        params strategy eps delta gamma k hgood answerRestrict answerInduction answerSelf
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have heps_le_one :=
    eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hdelta_le_one :=
    delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hgamma_le_one :=
    gamma_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hzeta_le_one :
      selfImprovementInInductionError params.next eps delta gamma ≤ 1 :=
    selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
      params strategy hgood hsmall
  have hdq_le_q :
      params.d ≤ params.q :=
    dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall
  have hkappa_le :
      kappa ≤
        ((params.m : Error) ^ (2 : ℕ)) *
            (mainInductionNu params.next k eps delta gamma +
              Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))
          + zeta := by
    dsimp [kappa, zeta]
    nlinarith
      [average_answerSliceError_le params strategy eps delta gamma k hgood
        answerRestrict answerInduction,
       average_answerSliceSelfImprovementError_le
        params strategy eps delta gamma hgood answerRestrict]
  have hzeta_le_nu :
      zeta ≤ mainInductionNu params.next k eps delta gamma := by
    simpa [zeta] using
      selfImprovementInInductionError_le_mainInductionNu
        params strategy eps delta gamma k hgood hsmall heps_le_one hdelta_le_one hdq_le_q
  have hnu_le :
      ldPastingInInductionNu params k eps delta gamma zeta ≤
        (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma := by
    simpa [zeta] using
      ldPastingInInductionNu_le_fifth_mainInductionNu
        params eps delta gamma k
        heps_nonneg hdelta_nonneg hgamma_nonneg
        heps_le_one hdelta_le_one hgamma_le_one hdq_le_q
  have herror_le :
      ldPastingInInductionError params k eps delta gamma kappa zeta ≤
        mainInductionError params.next k eps delta gamma :=
    ldPastingInInductionError_le_mainInductionError_of_bounds
      params eps delta gamma k kappa zeta
      heps_nonneg hdelta_nonneg hgamma_nonneg
      hkappa_le hzeta_le_nu hnu_le
  have hpasted :
      ∃ H : Measurement (Polynomial params.next) ι',
        LdPastingInInductionSectionConclusion params strategy family H
          eps delta gamma kappa zeta k := by
    exact
      ldPastingInInductionSection params strategy eps delta gamma kappa zeta hgood
        family hcomplete hcons hselfConsistent hbounded k hk
  rcases hpasted with ⟨H, hH⟩
  exact
    mainInductionOfWitness params.next strategy eps delta gamma k
      ⟨ldPastingInInductionError params k eps delta gamma kappa zeta, H,
        hH.pointConsistency, herror_le⟩

/-- Answer-valued small-error successor assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.  This is the
internal answer-valued route through the successor proof: answer-valued
restricted slice data supply the averaged pasting fields directly, the
small-error branch supplies the scalar side conditions for averaged pasting, and
the induction-section pasting theorem produces the next-dimensional
measurement. -/
theorem mainInductionFromAnswerStageDataOfSmallError.{uι', uF}
    {ι' : Type uι'} [Fintype ι'] [DecidableEq ι']
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next ι')
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (answerRestrict : AnswerSliceRestrictionData.{uι', uF} params strategy eps delta gamma)
    (answerInduction :
      AnswerPerSliceInductionData.{uι', uF} params strategy eps delta gamma answerRestrict k)
    (answerSelf :
      AnswerSelfImprovementData.{uι', uF} params strategy eps delta gamma k answerRestrict
        answerInduction)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι',
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionFromAnswerStageDataOfSmallErrorDirect
      params strategy eps delta gamma k hgood hsmall
      answerRestrict answerInduction answerSelf hk



end MIPStarRE.LDT.MainInductionStep
