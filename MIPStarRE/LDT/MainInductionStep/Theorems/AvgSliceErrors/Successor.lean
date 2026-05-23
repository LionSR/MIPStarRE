import MIPStarRE.LDT.MainInductionStep.Theorems.AvgSliceErrors.Core

/-!
# Section 6 — Averaged Slice Error Bounds: Successor Outputs

This module packages recursive answer-valued slice measurements and the final
self-improvement-to-main-induction error comparisons.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι uF

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Extract the recursive answer-valued slice measurements and their averaged
main-induction error bound.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.  After the
restricted-probabilities theorem and the predecessor answer-valued induction
hypothesis are applied to the restricted slices, this theorem packages the
resulting measurements `G^x` and proves the displayed bound
`\mathbb E_x \sigma_x \leq \sigma`.

**Lean-only:** This is an internal construction theorem for the simultaneous
answer-valued successor route tracked in issue #1507; it does not add a
predecessor conclusion as an assumption to any source-facing theorem.
Discharge: proved here from the restricted-probabilities theorem and the
answer-valued predecessor induction hypothesis. -/
theorem answerSuccessorRecursiveSliceMeasurements_ofMainInductionHypothesis
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ profile : AnswerSuccessorRestrictedFailureProfile params strategy,
      ∃ sliceError : Fq params → Error,
        ∃ sliceMeasurement : Fq params → Measurement (Polynomial params) ι,
          averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
              sliceConditioningLoss params * eps ∧
            averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta ∧
            averageAnswerSuccessorRestrictedDiagonalError params profile ≤
              sliceConditioningLoss params * gamma ∧
            (∀ x,
              ConsRel strategy.state (uniformDistribution (Point params))
                (IdxProjMeas.toIdxSubMeas
                  (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
                (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
                (sliceError x)) ∧
            (∀ x,
              sliceError x ≤
                mainInductionError params k
                  (profile.axisParallel x)
                  (profile.selfConsistency x)
                  (profile.diagonal x)) ∧
            avgOver (uniformDistribution (Fq params)) sliceError ≤
              ((params.m : Error) ^ (2 : ℕ)) *
                (mainInductionNu params.next k eps delta gamma +
                  Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
  classical
  rcases answerSuccessorRestrictedSliceConclusions
      params strategy eps delta gamma k hgood hinduction hk_next hsmall with
    ⟨profile, haxis, hself, hdiag, hconclusion⟩
  choose sliceMeasurement hpoint using hconclusion
  let sliceError : Fq params → Error := fun x =>
    mainInductionError params k
      (profile.axisParallel x)
      (profile.selfConsistency x)
      (profile.diagonal x)
  refine ⟨profile, sliceError, sliceMeasurement, haxis, hself, hdiag, ?_, ?_, ?_⟩
  · intro x
    simpa [xRestrictedAnswerSymStratOfAnswer] using hpoint x
  · intro x
    exact le_rfl
  · simpa [sliceError] using
      average_answerSuccessorSliceMainInductionError_le
        params strategy eps delta gamma k hgood profile haxis hself hdiag

/-- Apply self-improvement to the recursive answer-valued successor slices.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`.  Starting from
the recursive answer-valued slice measurements supplied by the predecessor
induction hypothesis, this theorem constructs the projective slice
submeasurements `\widehat G^x` and witnesses `Z^x`, proves their four
self-improvement outputs, and keeps the averaged `\zeta_x` and `\sigma_x`
bounds available.

**Lean-only:** The ordinary carrier appears only in the domination field, where
its point measurement is the same last-coordinate restriction of the ambient
answer-valued point measurement.  The proof invokes only the
axis-parallel/self-consistency form of self-improvement, and therefore does not
claim that the carrier's dummy diagonal measurement is a good diagonal
realization of the answer-valued strategy.  This internal construction is
tracked in issue #1507.  Discharge: proved here from the recursive slice
measurements and the formal self-improvement theorem. -/
theorem answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ profile : AnswerSuccessorRestrictedFailureProfile params strategy,
      ∃ sliceError : Fq params → Error,
        ∃ sliceMeasurement : Fq params → Measurement (Polynomial params) ι,
          ∃ sliceProj : Fq params → ProjSubMeas (Polynomial params) ι,
            ∃ sliceWitness : Fq params → MIPStarRE.Quantum.Op ι,
              averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
                  sliceConditioningLoss params * eps ∧
                averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta ∧
                averageAnswerSuccessorRestrictedDiagonalError params profile ≤
                  sliceConditioningLoss params * gamma ∧
                (∀ x,
                  ConsRel strategy.state (uniformDistribution (Point params))
                    (IdxProjMeas.toIdxSubMeas
                      (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
                    (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
                    (sliceError x)) ∧
                (∀ x,
                  sliceError x ≤
                    mainInductionError params k
                      (profile.axisParallel x)
                      (profile.selfConsistency x)
                      (profile.diagonal x)) ∧
                avgOver (uniformDistribution (Fq params)) sliceError ≤
                  ((params.m : Error) ^ (2 : ℕ)) *
                    (mainInductionNu params.next k eps delta gamma +
                      Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) ∧
                avgOver (uniformDistribution (Fq params))
                    (fun x =>
                      selfImprovementInInductionError params
                        (profile.axisParallel x)
                        (profile.selfConsistency x)
                        (profile.diagonal x)) ≤
                  selfImprovementInInductionError params.next eps delta gamma ∧
                (∀ x,
                  CompletenessAtLeast strategy.state (sliceProj x).toSubMeas.liftLeft
                    ((1 - sliceError x) -
                      selfImprovementInInductionError params
                        (profile.axisParallel x)
                        (profile.selfConsistency x)
                        (profile.diagonal x))) ∧
                (∀ x,
                  ConsRel strategy.state (uniformDistribution (Point params))
                    (IdxProjMeas.toIdxSubMeas
                      (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
                    (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
                    (selfImprovementInInductionError params
                      (profile.axisParallel x)
                      (profile.selfConsistency x)
                      (profile.diagonal x))) ∧
                (∀ x,
                  BipartiteSSCRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily (sliceProj x).toSubMeas)
                    (selfImprovementInInductionError params
                      (profile.axisParallel x)
                      (profile.selfConsistency x)
                      (profile.diagonal x))) ∧
                (∀ x,
                  SDDRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (sliceProj x).toSubMeas))
                    (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (sliceProj x).toSubMeas))
                    (selfImprovementInInductionError params
                      (profile.axisParallel x)
                      (profile.selfConsistency x)
                      (profile.diagonal x))) ∧
                (∀ x,
                  tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas
                    ≤ selfImprovementInInductionError params
                      (profile.axisParallel x)
                      (profile.selfConsistency x)
                      (profile.diagonal x)) ∧
                (∀ x, ∀ h : Polynomial params,
                  IdxPolyFamily.averagedSlicePointEvaluationOperator
                    (answerSelfImprovementCarrier params.next strategy) x h ≤ sliceWitness x) := by
  classical
  rcases answerSuccessorRecursiveSliceMeasurements_ofMainInductionHypothesis
      params strategy eps delta gamma k hgood hinduction hk_next hsmall with
    ⟨profile, sliceError, sliceMeasurement, haxis, hself, hdiag, hpoint, herror, havgSigma⟩
  have havgZeta :
      avgOver (uniformDistribution (Fq params))
          (fun x =>
            selfImprovementInInductionError params
              (profile.axisParallel x)
              (profile.selfConsistency x)
              (profile.diagonal x)) ≤
        selfImprovementInInductionError params.next eps delta gamma :=
    average_answerSuccessorSliceSelfImprovementError_le
      params strategy eps delta gamma hgood profile haxis hself
  have hslice :
      ∀ x,
        ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
          CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
            ((1 - sliceError x) -
              selfImprovementInInductionError params
                (profile.axisParallel x)
                (profile.selfConsistency x)
                (profile.diagonal x)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params H.toSubMeas)
            (selfImprovementInInductionError params
              (profile.axisParallel x)
              (profile.selfConsistency x)
              (profile.diagonal x)) ∧
          BipartiteSSCRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily H.toSubMeas)
            (selfImprovementInInductionError params
              (profile.axisParallel x)
              (profile.selfConsistency x)
              (profile.diagonal x)) ∧
          SDDRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
            (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
            (selfImprovementInInductionError params
              (profile.axisParallel x)
              (profile.selfConsistency x)
              (profile.diagonal x)) ∧
          (tensorFailureExpectation strategy.state Z H.toSubMeas ≤
            selfImprovementInInductionError params
              (profile.axisParallel x)
              (profile.selfConsistency x)
              (profile.diagonal x)) ∧
          (∀ h : Polynomial params,
            IdxPolyFamily.averagedSlicePointEvaluationOperator
              (answerSelfImprovementCarrier params.next strategy) x h ≤ Z) := by
    intro x
    let answerSlice := xRestrictedAnswerSymStratOfAnswer params strategy x
    let carrier := answerSelfImprovementCarrier params answerSlice
    have haxisSlice :
        carrier.axisParallelFailureProbability ≤ profile.axisParallel x := by
      have hfail :
          carrier.axisParallelFailureProbability =
            answerSlice.axisParallelFailureProbability := by
        unfold SymStrat.axisParallelFailureProbability
          AnswerSymStrat.axisParallelFailureProbability
          axisParallelPointAnswerFamily AnswerSymStrat.axisParallelPointAnswerFamily
          axisParallelLineAnswerFamily AnswerSymStrat.axisParallelLineAnswerFamily
        simp [carrier, answerSelfImprovementCarrier]
      simpa [hfail, answerSlice] using (profile.restrictedGood x).axisParallelTest
    have hselfSlice :
        carrier.selfConsistencyFailureProbability ≤ profile.selfConsistency x := by
      have hfail :
          carrier.selfConsistencyFailureProbability =
            answerSlice.selfConsistencyFailureProbability := by
        unfold SymStrat.selfConsistencyFailureProbability
          AnswerSymStrat.selfConsistencyFailureProbability
        simp [carrier, answerSelfImprovementCarrier]
      simpa [hfail, answerSlice] using (profile.restrictedGood x).selfConsistencyTest
    have hconsCarrier :
        ConsRel carrier.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas carrier.pointMeasurement)
          (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
          (sliceError x) := by
      simpa [carrier, answerSelfImprovementCarrier, answerSlice] using hpoint x
    rcases selfImprovementInInductionSection_of_axisParallel_selfConsistency
        params carrier
        (profile.axisParallel x)
        (profile.selfConsistency x)
        (profile.diagonal x)
        (sliceError x)
        haxisSlice hselfSlice
        (sliceMeasurement x)
        hconsCarrier with
      ⟨H, Z, hH⟩
    refine ⟨H, Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [carrier, answerSelfImprovementCarrier, answerSlice] using hH.completeness
    · simpa [carrier, answerSelfImprovementCarrier, answerSlice] using hH.pointConsistency
    · simpa [carrier, answerSelfImprovementCarrier, answerSlice] using hH.strongSelfConsistency
    · simpa [carrier, answerSelfImprovementCarrier, answerSlice] using hH.selfCloseness
    · simpa [carrier, answerSelfImprovementCarrier, answerSlice] using hH.bounded
    · intro h
      let ambientCarrier := answerSelfImprovementCarrier params.next strategy
      let sliceStrategy : Fq params → SymStrat params ι :=
        fun y => answerSelfImprovementCarrier params
          (xRestrictedAnswerSymStratOfAnswer params strategy y)
      have havg_all :=
        AnswerSelfImprovementData.averagedPoint_eq_of_pointMeasurement_eq
          params ambientCarrier sliceStrategy (by intro y; rfl)
      have havg :
          IdxPolyFamily.averagedPointEvaluationOperator carrier h =
            IdxPolyFamily.averagedSlicePointEvaluationOperator
              (answerSelfImprovementCarrier params.next strategy) x h := by
        simpa [ambientCarrier, sliceStrategy, carrier, answerSlice] using havg_all x h
      simpa [havg] using hH.dominatesAveragePointOperator h
  let sliceProj : Fq params → ProjSubMeas (Polynomial params) ι :=
    fun x => Classical.choose (hslice x)
  let sliceWitness : Fq params → MIPStarRE.Quantum.Op ι :=
    fun x => Classical.choose (Classical.choose_spec (hslice x))
  have hslice_props :
      ∀ x,
        CompletenessAtLeast strategy.state (sliceProj x).toSubMeas.liftLeft
          ((1 - sliceError x) -
            selfImprovementInInductionError params
              (profile.axisParallel x)
              (profile.selfConsistency x)
              (profile.diagonal x)) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas
            (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
          (selfImprovementInInductionError params
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)) ∧
        BipartiteSSCRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (sliceProj x).toSubMeas)
          (selfImprovementInInductionError params
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)) ∧
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (sliceProj x).toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (sliceProj x).toSubMeas))
          (selfImprovementInInductionError params
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)) ∧
        (tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas ≤
          selfImprovementInInductionError params
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)) ∧
        (∀ h : Polynomial params,
          IdxPolyFamily.averagedSlicePointEvaluationOperator
            (answerSelfImprovementCarrier params.next strategy) x h ≤ sliceWitness x) := by
    intro x
    simpa [sliceProj, sliceWitness] using
      (Classical.choose_spec (Classical.choose_spec (hslice x)))
  exact
    ⟨profile, sliceError, sliceMeasurement, sliceProj, sliceWitness,
      haxis, hself, hdiag, hpoint, herror, havgSigma, havgZeta,
      (fun x => (hslice_props x).1),
      (fun x => (hslice_props x).2.1),
      (fun x => (hslice_props x).2.2.1),
      (fun x => (hslice_props x).2.2.2.1),
      (fun x => (hslice_props x).2.2.2.2.1),
      (fun x h => (hslice_props x).2.2.2.2.2 h)⟩

/-- Paper's `\eqref{eq:zeta-smaller-than-nu}`: under the small-parameter
hypotheses, the averaged self-improvement interface error `\zeta` is bounded by
the next-stage induction parameter `\nu`. -/
lemma selfImprovementInInductionError_le_mainInductionNu
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (heps_le_one : eps ≤ 1) (hdelta_le_one : delta ≤ 1)
    (hdq_le_q : params.d ≤ params.q) :
    selfImprovementInInductionError params.next eps delta gamma ≤
      mainInductionNu params.next k eps delta gamma := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_le_one := dq_ratio_le_one params hdq_le_q
  have hthree := three_le_k_sq_mul_next_m_of_hsmall params strategy hgood hsmall
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  calc
    selfImprovementInInductionError params.next eps delta gamma
      = 3000 * (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simp [selfImprovementInInductionError, Parameters.next]
    _ ≤ 3000 * (params.next.m : Error) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          gcongr
          · exact Real.rpow_le_rpow_of_exponent_ge' heps_nonneg heps_le_one (by positivity)
              (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
          · exact Real.rpow_le_rpow_of_exponent_ge' hdelta_nonneg hdelta_le_one (by positivity)
              (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
          · exact Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one (by positivity)
              (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          have hcoef :
              3000 * (params.next.m : Error) ≤
                1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
            nlinarith [hthree]
          have hsum_nonneg :
              0 ≤ Real.rpow eps (1 / (1024 : Error)) +
                    Real.rpow delta (1 / (1024 : Error)) +
                    Real.rpow (((params.d : Error) / (params.q : Error)))
                      (1 / (1024 : Error)) := by
            exact add_nonneg
              (add_nonneg (Real.rpow_nonneg heps_nonneg _)
                (Real.rpow_nonneg hdelta_nonneg _))
              (Real.rpow_nonneg hratio_nonneg _)
          exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg
    _ ≤ mainInductionNu params.next k eps delta gamma := by
          have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
          have hsum_le :
              Real.rpow eps (1 / (1024 : Error)) +
                  Real.rpow delta (1 / (1024 : Error)) +
                  Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
                Real.rpow eps (1 / (1024 : Error)) +
                  Real.rpow delta (1 / (1024 : Error)) +
                  Real.rpow gamma (1 / (1024 : Error)) +
                  Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
            nlinarith [hgamma_root_nonneg]
          have hcoef_nonneg :
              0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
            positivity
          have hmul := mul_le_mul_of_nonneg_left hsum_le hcoef_nonneg
          simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Answer-valued analogue of
`selfImprovementInInductionError_le_mainInductionNu`.

This is the scalar part of the successor proof for an ambient answer-valued
strategy.  It uses only the answer-valued goodness bounds and does not replace
the answer-valued diagonal measurement by an ordinary one. -/
lemma answer_selfImprovementInInductionError_le_mainInductionNu
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (heps_le_one : eps ≤ 1) (hdelta_le_one : delta ≤ 1)
    (hdq_le_q : params.d ≤ params.q) :
    selfImprovementInInductionError params.next eps delta gamma ≤
      mainInductionNu params.next k eps delta gamma := by
  have heps_nonneg := answer_eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := answer_delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := answer_gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_le_one := dq_ratio_le_one params hdq_le_q
  have hthree := answer_three_le_k_sq_mul_next_m_of_hsmall params strategy hgood hsmall
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  calc
    selfImprovementInInductionError params.next eps delta gamma
      = 3000 * (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simp [selfImprovementInInductionError, Parameters.next]
    _ ≤ 3000 * (params.next.m : Error) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          gcongr
          · exact Real.rpow_le_rpow_of_exponent_ge' heps_nonneg heps_le_one (by positivity)
              (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
          · exact Real.rpow_le_rpow_of_exponent_ge' hdelta_nonneg hdelta_le_one (by positivity)
              (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
          · exact Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one (by positivity)
              (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          have hcoef :
              3000 * (params.next.m : Error) ≤
                1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
            nlinarith [hthree]
          have hsum_nonneg :
              0 ≤ Real.rpow eps (1 / (1024 : Error)) +
                    Real.rpow delta (1 / (1024 : Error)) +
                    Real.rpow (((params.d : Error) / (params.q : Error)))
                      (1 / (1024 : Error)) := by
            exact add_nonneg
              (add_nonneg (Real.rpow_nonneg heps_nonneg _)
                (Real.rpow_nonneg hdelta_nonneg _))
              (Real.rpow_nonneg hratio_nonneg _)
          exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg
    _ ≤ mainInductionNu params.next k eps delta gamma := by
          have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
          have hsum_le :
              Real.rpow eps (1 / (1024 : Error)) +
                  Real.rpow delta (1 / (1024 : Error)) +
                  Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
                Real.rpow eps (1 / (1024 : Error)) +
                  Real.rpow delta (1 / (1024 : Error)) +
                  Real.rpow gamma (1 / (1024 : Error)) +
                  Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
            nlinarith [hgamma_root_nonneg]
          have hcoef_nonneg :
              0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
            positivity
          have hmul := mul_le_mul_of_nonneg_left hsum_le hcoef_nonneg
          simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul



end MIPStarRE.LDT.MainInductionStep
