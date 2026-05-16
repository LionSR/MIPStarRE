import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds
import MIPStarRE.LDT.MainInductionStep.Theorems.StageDataConstructors

/-!
# Section 6 — Averaged Slice Error Bounds

Private nonneg helpers for restricted failure profiles, and the key averaged
slice-error lemmas: `average_sliceSelfImprovementError_le`,
`average_sliceMainInductionNu_le`, `average_sliceError_le`, and
`selfImprovementInInductionError_le_mainInductionNu`.

Three helpers are exposed for cross-module use in `PastingAssembly` and
`MainTheorems`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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


end MIPStarRE.LDT.MainInductionStep
