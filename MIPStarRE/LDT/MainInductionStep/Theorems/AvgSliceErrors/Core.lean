import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds
import MIPStarRE.LDT.MainInductionStep.Theorems.StageDataConstructors

/-!
# Section 6 — Averaged Slice Error Bounds: Core Estimates

This module contains the Jensen and averaging estimates for ordinary and
answer-valued restricted slice errors.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι uF

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

private lemma avgOver_uniform_fq_rpow_le_rpow_avg
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → Error)
    (n : ℕ)
    (hn : 1 ≤ n)
    (hf : ∀ a, 0 ≤ f a) :
    avgOver (uniformDistribution (Fq params))
        (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
      Real.rpow (avgOver (uniformDistribution (Fq params)) f) (1 / (n : Error)) := by
  simpa using
    avgOver_uniform_rpow_one_div_le_rpow_avg
      (α := Fq params) (f := f) (n := n) hn hf

private lemma avgOver_uniform_fq_nonneg
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → Error)
    (hf : ∀ a, 0 ≤ f a) :
    0 ≤ avgOver (uniformDistribution (Fq params)) f :=
  avgOver_nonneg (uniformDistribution (Fq params)) f hf

private lemma restrictedAxisParallelProb_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : RestrictedSymStrat params ι) :
    0 ≤ strategy.axisParallelFailureProbability := by
  unfold RestrictedSymStrat.axisParallelFailureProbability
  exact bipartiteConsError_nonneg strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (RestrictedSymStrat.axisParallelPointAnswerFamily strategy)
    (RestrictedSymStrat.axisParallelLineAnswerFamily strategy)

private lemma restricted_axis_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.axisParallel x := by
  intro x
  exact le_trans
    (restrictedAxisParallelProb_nonneg params
      (xRestrictedStrategy params strategy x))
    (profile.restrictedGood x).axisParallelTest

private lemma restrictedSelfConsistencyProb_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : RestrictedSymStrat params ι) :
    0 ≤ strategy.selfConsistencyFailureProbability := by
  unfold RestrictedSymStrat.selfConsistencyFailureProbability
  exact bipartiteSSCError_nonneg strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

private lemma restricted_self_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.selfConsistency x := by
  intro x
  exact le_trans
    (restrictedSelfConsistencyProb_nonneg params
      (xRestrictedStrategy params strategy x))
    (profile.restrictedGood x).selfConsistencyTest

private lemma restrictedDiagonalProb_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : RestrictedSymStrat params ι) :
    0 ≤ strategy.diagonalFailureProbability := by
  unfold RestrictedSymStrat.diagonalFailureProbability
  refine mul_nonneg ?_ ?_
  · positivity
  · refine Finset.sum_nonneg ?_
    intro j _
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily strategy j)
      (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily strategy j)

private lemma restricted_diag_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.diagonal x := by
  intro x
  exact le_trans
    (restrictedDiagonalProb_nonneg params
      (xRestrictedStrategy params strategy x))
    (profile.restrictedGood x).diagonalLineTest

private lemma answerSuccessor_restricted_axis_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next ι}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.axisParallel x := by
  intro x
  exact answer_eps_nonneg_of_isGood params
    (xRestrictedAnswerSymStratOfAnswer params strategy x)
    (profile.restrictedGood x)

private lemma answerSuccessor_restricted_self_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next ι}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.selfConsistency x := by
  intro x
  exact answer_delta_nonneg_of_isGood params
    (xRestrictedAnswerSymStratOfAnswer params strategy x)
    (profile.restrictedGood x)

private lemma answerSuccessor_restricted_diag_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next ι}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.diagonal x := by
  intro x
  exact answer_gamma_nonneg_of_isGood params
    (xRestrictedAnswerSymStratOfAnswer params strategy x)
    (profile.restrictedGood x)

/-- Averaging the slice self-improvement errors gives the paper's displayed
bound on `\mathbb{E}_x[\zeta_x]`, i.e. the first inequality from
`inductive_step.tex:555-567`. -/
lemma average_sliceSelfImprovementError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceSelfImprovementError params hrestrict x) ≤
      selfImprovementInInductionError params.next eps delta gamma := by
  let 𝒟 := uniformDistribution (Fq params)
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have haxis_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) ≤
        Real.rpow
          (averageRestrictedAxisParallelError params hrestrict.profile)
          (1 / (32 : Error)) := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        hrestrict.profile.axisParallel 32 (by norm_num)
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) ≤
        Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (32 : Error)) := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        hrestrict.profile.selfConsistency 32 (by norm_num)
        (restricted_self_nonneg params hrestrict.profile)
  have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast Nat.le_succ params.m
  have haxis_nonneg : 0 ≤ averageRestrictedAxisParallelError params hrestrict.profile := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_nonneg params hrestrict.profile.axisParallel
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_nonneg : 0 ≤ averageRestrictedSelfConsistencyError params hrestrict.profile := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_nonneg params hrestrict.profile.selfConsistency
        (restricted_self_nonneg params hrestrict.profile)
  have haxis_rpow_le :
      Real.rpow (averageRestrictedAxisParallelError params hrestrict.profile) (1 / (32 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * eps) (1 / (32 : Error)) := by
    exact Real.rpow_le_rpow haxis_nonneg hrestrict.axisAverageBound (by positivity)
  have hself_rpow_le :
      Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (32 : Error)) ≤
        Real.rpow delta (1 / (32 : Error)) := by
    exact Real.rpow_le_rpow hself_nonneg hrestrict.selfAverageBound (by positivity)
  have haxis_term :
      (params.m : Error) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) ≤
        (params.next.m : Error) * Real.rpow eps (1 / (32 : Error)) := by
    have htmp :=
      mul_le_mul_of_nonneg_left (le_trans haxis_avg haxis_rpow_le) (by positivity : 0
          ≤ (params.m : Error))
    exact le_trans htmp
      (m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow params heps_nonneg (by positivity)
        (by norm_num : (1 / (32 : Error)) ≤ 1))
  have hself_term :
      (params.m : Error) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) ≤
        (params.next.m : Error) * Real.rpow delta (1 / (32 : Error)) := by
    have htmp :
        (params.m : Error) *
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) ≤
          (params.m : Error) * Real.rpow delta (1 / (32 : Error)) := by
      exact mul_le_mul_of_nonneg_left (le_trans hself_avg hself_rpow_le) (by positivity)
    exact le_trans htmp <|
      mul_le_mul_of_nonneg_right hm_le_next (Real.rpow_nonneg hdelta_nonneg _)
  have hratio_term :
      (params.m : Error) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
        (params.next.m : Error) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    exact mul_le_mul_of_nonneg_right hm_le_next (Real.rpow_nonneg hratio_nonneg _)
  have hinner :
      (params.m : Error) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ≤
        (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
    nlinarith [haxis_term, hself_term, hratio_term]
  have hinner' := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ (3000 : Error))
  calc
    avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x)
      = 3000 * (params.m : Error) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simp [sliceSelfImprovementError, selfImprovementInInductionError, avgOver_add,
            avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ 3000 * (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simpa [mul_assoc] using hinner'
    _ = selfImprovementInInductionError params.next eps delta gamma := by
          simp [selfImprovementInInductionError, Parameters.next]

/-- Jensen/conditioning estimate controlling the averaged slice induction
parameter `\mathbb{E}_x[\nu_x]` by the next-stage `\nu`, corresponding to the
second displayed inequality in `inductive_step.tex:555-567`. -/
private lemma average_sliceMainInductionNu_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          mainInductionNu params k
            (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x)
            (hrestrict.profile.diagonal x)) ≤
      mainInductionNu params.next k eps delta gamma := by
  let 𝒟 := uniformDistribution (Fq params)
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have haxis_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageRestrictedAxisParallelError params hrestrict.profile)
          (1 / (1024 : Error)) := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        hrestrict.profile.axisParallel 1024 (by norm_num)
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (1024 : Error)) := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        hrestrict.profile.selfConsistency 1024 (by norm_num)
        (restricted_self_nonneg params hrestrict.profile)
  have hdiag_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageRestrictedDiagonalError params hrestrict.profile)
          (1 / (1024 : Error)) := by
    simpa [averageRestrictedDiagonalError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        hrestrict.profile.diagonal 1024 (by norm_num)
        (restricted_diag_nonneg params hrestrict.profile)
  have hm_sq_le_next_sq : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.next.m : Error) ^ (2 : ℕ)) := by
    have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
      exact_mod_cast Nat.le_succ params.m
    nlinarith
  have haxis_nonneg : 0 ≤ averageRestrictedAxisParallelError params hrestrict.profile := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_nonneg params hrestrict.profile.axisParallel
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_nonneg : 0 ≤ averageRestrictedSelfConsistencyError params hrestrict.profile := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_nonneg params hrestrict.profile.selfConsistency
        (restricted_self_nonneg params hrestrict.profile)
  have hdiag_nonneg : 0 ≤ averageRestrictedDiagonalError params hrestrict.profile := by
    simpa [averageRestrictedDiagonalError, 𝒟] using
      avgOver_uniform_fq_nonneg params hrestrict.profile.diagonal
        (restricted_diag_nonneg params hrestrict.profile)
  have haxis_rpow_le :
      Real.rpow
          (averageRestrictedAxisParallelError params hrestrict.profile)
          (1 / (1024 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * eps) (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow haxis_nonneg hrestrict.axisAverageBound (by positivity)
  have hself_rpow_le :
      Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (1024 : Error)) ≤
        Real.rpow delta (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow hself_nonneg hrestrict.selfAverageBound (by positivity)
  have hdiag_rpow_le :
      Real.rpow (averageRestrictedDiagonalError params hrestrict.profile) (1 / (1024 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * gamma) (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow hdiag_nonneg hrestrict.diagonalAverageBound (by positivity)
  have haxis_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow eps (1 / (1024 : Error)) := by
    have htmp := mul_le_mul_of_nonneg_left (le_trans haxis_avg haxis_rpow_le)
      (by positivity : 0 ≤ ((params.m : Error) ^ (2 : ℕ)))
    exact le_trans htmp
      (m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow params heps_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1))
  have hself_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟
            (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow delta (1 / (1024 : Error)) := by
    have htmp :
        ((params.m : Error) ^ (2 : ℕ)) *
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) ≤
          ((params.m : Error) ^ (2 : ℕ)) * Real.rpow delta (1 / (1024 : Error)) := by
      exact mul_le_mul_of_nonneg_left (le_trans hself_avg hself_rpow_le) (by positivity)
    exact le_trans htmp <|
      mul_le_mul_of_nonneg_right hm_sq_le_next_sq (Real.rpow_nonneg hdelta_nonneg _)
  have hdiag_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow gamma (1 / (1024 : Error)) := by
    have htmp := mul_le_mul_of_nonneg_left (le_trans hdiag_avg hdiag_rpow_le)
      (by positivity : 0 ≤ ((params.m : Error) ^ (2 : ℕ)))
    exact le_trans htmp
      (m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow params hgamma_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1))
  have hratio_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    exact mul_le_mul_of_nonneg_right hm_sq_le_next_sq (Real.rpow_nonneg hratio_nonneg _)
  have hinner :
      ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
    nlinarith [haxis_term, hself_term, hdiag_term, hratio_term]
  have hinner' := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 1000
      * ((k : Error) ^ (2 : ℕ)))
  calc
    avgOver 𝒟 (fun x =>
        mainInductionNu params k (hrestrict.profile.axisParallel x)
          (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x))
      = 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          simp [mainInductionNu, avgOver_add, avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          simpa [mul_assoc] using hinner'
    _ = mainInductionNu params.next k eps delta gamma := by
          simp [mainInductionNu, Parameters.next]

/-- Averaging the recursive slice errors `\sigma_x` and telescoping the slice
main-induction bound yields the paper's `\mathbb{E}_x[\sigma_x]` estimate used
in the final pasting-data record error calculation. -/
lemma average_sliceError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma)
    (hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k) :
    avgOver (uniformDistribution (Fq params)) hinduction.sliceError ≤
      ((params.m : Error) ^ (2 : ℕ)) *
        (mainInductionNu params.next k eps delta gamma +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
  let 𝒟 := uniformDistribution (Fq params)
  have havg := avgOver_mono 𝒟 hinduction.sliceError
    (fun x =>
      mainInductionError params k (hrestrict.profile.axisParallel x)
        (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x))
    hinduction.error_le
  calc
    avgOver 𝒟 hinduction.sliceError
      ≤ avgOver 𝒟 (fun x =>
          mainInductionError params k (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x)) := havg
    _ = ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x =>
              mainInductionNu params k (hrestrict.profile.axisParallel x)
                (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x)) +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
          simp [mainInductionError, avgOver_add, avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ ((params.m : Error) ^ (2 : ℕ)) *
          (mainInductionNu params.next k eps delta gamma +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
          gcongr
          exact average_sliceMainInductionNu_le params strategy eps delta gamma k hgood hrestrict

/-- Answer-valued successor analogue of the averaged self-improvement error
estimate.

For the restricted profiles of an ambient `AnswerSymStrat` successor, the
average of the slice errors `\zeta_x` is bounded by the next-dimensional
quantity `\zeta`.  This is the scalar part of the answer-valued self-improvement
averaging in `inductive_step.tex:486-551`. -/
lemma average_answerSuccessorSliceSelfImprovementError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy)
    (haxis :
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
        sliceConditioningLoss params * eps)
    (hself :
      averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          selfImprovementInInductionError params
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)) ≤
      selfImprovementInInductionError params.next eps delta gamma := by
  let 𝒟 := uniformDistribution (Fq params)
  have heps_nonneg := answer_eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := answer_delta_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have haxis_avg :
      avgOver 𝒟 (fun x => Real.rpow (profile.axisParallel x) (1 / (32 : Error))) ≤
        Real.rpow
          (averageAnswerSuccessorRestrictedAxisParallelError params profile)
          (1 / (32 : Error)) := by
    simpa [averageAnswerSuccessorRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        profile.axisParallel 32 (by norm_num)
        (answerSuccessor_restricted_axis_nonneg params profile)
  have hself_avg :
      avgOver 𝒟 (fun x => Real.rpow (profile.selfConsistency x) (1 / (32 : Error))) ≤
        Real.rpow
          (averageAnswerSuccessorRestrictedSelfConsistencyError params profile)
          (1 / (32 : Error)) := by
    simpa [averageAnswerSuccessorRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        profile.selfConsistency 32 (by norm_num)
        (answerSuccessor_restricted_self_nonneg params profile)
  have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast Nat.le_succ params.m
  have haxis_nonneg :
      0 ≤ averageAnswerSuccessorRestrictedAxisParallelError params profile := by
    simpa [averageAnswerSuccessorRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_nonneg params profile.axisParallel
        (answerSuccessor_restricted_axis_nonneg params profile)
  have hself_nonneg :
      0 ≤ averageAnswerSuccessorRestrictedSelfConsistencyError params profile := by
    simpa [averageAnswerSuccessorRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_nonneg params profile.selfConsistency
        (answerSuccessor_restricted_self_nonneg params profile)
  have haxis_rpow_le :
      Real.rpow
          (averageAnswerSuccessorRestrictedAxisParallelError params profile)
          (1 / (32 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * eps) (1 / (32 : Error)) := by
    exact Real.rpow_le_rpow haxis_nonneg haxis (by positivity)
  have hself_rpow_le :
      Real.rpow
          (averageAnswerSuccessorRestrictedSelfConsistencyError params profile)
          (1 / (32 : Error)) ≤
        Real.rpow delta (1 / (32 : Error)) := by
    exact Real.rpow_le_rpow hself_nonneg hself (by positivity)
  have haxis_term :
      (params.m : Error) *
          avgOver 𝒟 (fun x => Real.rpow (profile.axisParallel x) (1 / (32 : Error))) ≤
        (params.next.m : Error) * Real.rpow eps (1 / (32 : Error)) := by
    have htmp :=
      mul_le_mul_of_nonneg_left (le_trans haxis_avg haxis_rpow_le)
        (by positivity : 0 ≤ (params.m : Error))
    exact le_trans htmp
      (m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow params heps_nonneg (by positivity)
        (by norm_num : (1 / (32 : Error)) ≤ 1))
  have hself_term :
      (params.m : Error) *
          avgOver 𝒟 (fun x => Real.rpow (profile.selfConsistency x) (1 / (32 : Error))) ≤
        (params.next.m : Error) * Real.rpow delta (1 / (32 : Error)) := by
    have htmp :
        (params.m : Error) *
            avgOver 𝒟
              (fun x => Real.rpow (profile.selfConsistency x) (1 / (32 : Error))) ≤
          (params.m : Error) * Real.rpow delta (1 / (32 : Error)) := by
      exact mul_le_mul_of_nonneg_left (le_trans hself_avg hself_rpow_le) (by positivity)
    exact le_trans htmp <|
      mul_le_mul_of_nonneg_right hm_le_next (Real.rpow_nonneg hdelta_nonneg _)
  have hratio_term :
      (params.m : Error) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
        (params.next.m : Error) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    exact mul_le_mul_of_nonneg_right hm_le_next (Real.rpow_nonneg hratio_nonneg _)
  have hinner :
      (params.m : Error) *
          (avgOver 𝒟 (fun x => Real.rpow (profile.axisParallel x) (1 / (32 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (profile.selfConsistency x) (1 / (32 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ≤
        (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
    nlinarith [haxis_term, hself_term, hratio_term]
  have hinner' := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ (3000 : Error))
  calc
    avgOver 𝒟 (fun x =>
        selfImprovementInInductionError params
          (profile.axisParallel x)
          (profile.selfConsistency x)
          (profile.diagonal x))
      = 3000 * (params.m : Error) *
          (avgOver 𝒟 (fun x => Real.rpow (profile.axisParallel x) (1 / (32 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (profile.selfConsistency x) (1 / (32 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simp [selfImprovementInInductionError, avgOver_add, avgOver_const_mul,
            avgOver_uniform_const, 𝒟]
    _ ≤ 3000 * (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simpa [mul_assoc] using hinner'
    _ = selfImprovementInInductionError params.next eps delta gamma := by
          simp [selfImprovementInInductionError, Parameters.next]

/-- Answer-valued successor analogue of the averaged recursive induction
parameter estimate.

For an ambient `AnswerSymStrat` in dimension `m + 1`, the restricted
answer-valued slice profile satisfies the same Jensen and conditioning estimate
as in the ordinary successor route.  This is the scalar calculation needed after
the recursive answer-valued predecessor calls. -/
lemma average_answerSuccessorSliceMainInductionNu_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy)
    (haxis :
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
        sliceConditioningLoss params * eps)
    (hself :
      averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta)
    (hdiag :
      averageAnswerSuccessorRestrictedDiagonalError params profile ≤
        sliceConditioningLoss params * gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          mainInductionNu params k
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)) ≤
      mainInductionNu params.next k eps delta gamma := by
  let 𝒟 := uniformDistribution (Fq params)
  have heps_nonneg := answer_eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := answer_delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := answer_gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have haxis_avg :
      avgOver 𝒟 (fun x => Real.rpow (profile.axisParallel x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageAnswerSuccessorRestrictedAxisParallelError params profile)
          (1 / (1024 : Error)) := by
    simpa [averageAnswerSuccessorRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        profile.axisParallel 1024 (by norm_num)
        (answerSuccessor_restricted_axis_nonneg params profile)
  have hself_avg :
      avgOver 𝒟 (fun x => Real.rpow (profile.selfConsistency x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageAnswerSuccessorRestrictedSelfConsistencyError params profile)
          (1 / (1024 : Error)) := by
    simpa [averageAnswerSuccessorRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        profile.selfConsistency 1024 (by norm_num)
        (answerSuccessor_restricted_self_nonneg params profile)
  have hdiag_avg :
      avgOver 𝒟 (fun x => Real.rpow (profile.diagonal x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageAnswerSuccessorRestrictedDiagonalError params profile)
          (1 / (1024 : Error)) := by
    simpa [averageAnswerSuccessorRestrictedDiagonalError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        profile.diagonal 1024 (by norm_num)
        (answerSuccessor_restricted_diag_nonneg params profile)
  have hm_sq_le_next_sq : ((params.m : Error) ^ (2 : ℕ)) ≤
      ((params.next.m : Error) ^ (2 : ℕ)) := by
    have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
      exact_mod_cast Nat.le_succ params.m
    nlinarith
  have haxis_nonneg :
      0 ≤ averageAnswerSuccessorRestrictedAxisParallelError params profile := by
    simpa [averageAnswerSuccessorRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_nonneg params profile.axisParallel
        (answerSuccessor_restricted_axis_nonneg params profile)
  have hself_nonneg :
      0 ≤ averageAnswerSuccessorRestrictedSelfConsistencyError params profile := by
    simpa [averageAnswerSuccessorRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_nonneg params profile.selfConsistency
        (answerSuccessor_restricted_self_nonneg params profile)
  have hdiag_nonneg :
      0 ≤ averageAnswerSuccessorRestrictedDiagonalError params profile := by
    simpa [averageAnswerSuccessorRestrictedDiagonalError, 𝒟] using
      avgOver_uniform_fq_nonneg params profile.diagonal
        (answerSuccessor_restricted_diag_nonneg params profile)
  have haxis_rpow_le :
      Real.rpow
          (averageAnswerSuccessorRestrictedAxisParallelError params profile)
          (1 / (1024 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * eps) (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow haxis_nonneg haxis (by positivity)
  have hself_rpow_le :
      Real.rpow
          (averageAnswerSuccessorRestrictedSelfConsistencyError params profile)
          (1 / (1024 : Error)) ≤
        Real.rpow delta (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow hself_nonneg hself (by positivity)
  have hdiag_rpow_le :
      Real.rpow
          (averageAnswerSuccessorRestrictedDiagonalError params profile)
          (1 / (1024 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * gamma) (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow hdiag_nonneg hdiag (by positivity)
  have haxis_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟 (fun x => Real.rpow (profile.axisParallel x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow eps (1 / (1024 : Error)) := by
    have htmp := mul_le_mul_of_nonneg_left (le_trans haxis_avg haxis_rpow_le)
      (by positivity : 0 ≤ ((params.m : Error) ^ (2 : ℕ)))
    exact le_trans htmp
      (m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow params heps_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1))
  have hself_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟 (fun x =>
            Real.rpow (profile.selfConsistency x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow delta (1 / (1024 : Error)) := by
    have htmp :
        ((params.m : Error) ^ (2 : ℕ)) *
            avgOver 𝒟 (fun x =>
              Real.rpow (profile.selfConsistency x) (1 / (1024 : Error))) ≤
          ((params.m : Error) ^ (2 : ℕ)) * Real.rpow delta (1 / (1024 : Error)) := by
      exact mul_le_mul_of_nonneg_left (le_trans hself_avg hself_rpow_le) (by positivity)
    exact le_trans htmp <|
      mul_le_mul_of_nonneg_right hm_sq_le_next_sq (Real.rpow_nonneg hdelta_nonneg _)
  have hdiag_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟 (fun x => Real.rpow (profile.diagonal x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow gamma (1 / (1024 : Error)) := by
    have htmp := mul_le_mul_of_nonneg_left (le_trans hdiag_avg hdiag_rpow_le)
      (by positivity : 0 ≤ ((params.m : Error) ^ (2 : ℕ)))
    exact le_trans htmp
      (m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow params hgamma_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1))
  have hratio_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    exact mul_le_mul_of_nonneg_right hm_sq_le_next_sq (Real.rpow_nonneg hratio_nonneg _)
  have hinner :
      ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x => Real.rpow (profile.axisParallel x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (profile.selfConsistency x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (profile.diagonal x) (1 / (1024 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
    nlinarith [haxis_term, hself_term, hdiag_term, hratio_term]
  have hinner' := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 1000
      * ((k : Error) ^ (2 : ℕ)))
  calc
    avgOver 𝒟 (fun x =>
        mainInductionNu params k
          (profile.axisParallel x)
          (profile.selfConsistency x)
          (profile.diagonal x))
      = 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x => Real.rpow (profile.axisParallel x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (profile.selfConsistency x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (profile.diagonal x) (1 / (1024 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          simp [mainInductionNu, avgOver_add, avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          simpa [mul_assoc] using hinner'
    _ = mainInductionNu params.next k eps delta gamma := by
          simp [mainInductionNu, Parameters.next]

/-- Average of the recursive main-induction errors for answer-valued successor
slices.

This is the scalar estimate used after applying the predecessor answer-valued
induction hypothesis to each restricted successor slice. -/
lemma average_answerSuccessorSliceMainInductionError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy)
    (haxis :
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
        sliceConditioningLoss params * eps)
    (hself :
      averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta)
    (hdiag :
      averageAnswerSuccessorRestrictedDiagonalError params profile ≤
        sliceConditioningLoss params * gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          mainInductionError params k
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)) ≤
      ((params.m : Error) ^ (2 : ℕ)) *
        (mainInductionNu params.next k eps delta gamma +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
  let 𝒟 := uniformDistribution (Fq params)
  calc
    avgOver 𝒟 (fun x =>
        mainInductionError params k
          (profile.axisParallel x)
          (profile.selfConsistency x)
          (profile.diagonal x))
      = ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x =>
              mainInductionNu params k
                (profile.axisParallel x)
                (profile.selfConsistency x)
                (profile.diagonal x)) +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
          simp [mainInductionError, avgOver_add, avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ ((params.m : Error) ^ (2 : ℕ)) *
          (mainInductionNu params.next k eps delta gamma +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
          gcongr
          exact average_answerSuccessorSliceMainInductionNu_le
            params strategy eps delta gamma k hgood profile haxis hself hdiag


end MIPStarRE.LDT.MainInductionStep
