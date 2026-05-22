import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.AnswerFields

/-!
# Section 6 — Pasting Assembly: Error Bounds

This module contains the scalar absorption and degree-zero answer-valued pasting
constructions for the small-error branch.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Scalar telescoping from the induction-section pasting error to the next
main-induction error.

The lemma isolates the scalar inequality chain from the assembly of the averaged
slice data: the bound on `κ`, the comparison `ζ ≤ ν`, and the bound on the
pasting-section `ν` term. -/
lemma ldPastingInInductionError_le_mainInductionError_of_bounds
    (params : Parameters)
    [FieldModel params.q]
    (eps delta gamma : Error)
    (k : ℕ)
    (kappa zeta : Error)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hkappa_le :
      kappa ≤
        ((params.m : Error) ^ (2 : ℕ)) *
          (mainInductionNu params.next k eps delta gamma +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))
          + zeta)
    (hzeta_le_nu : zeta ≤ mainInductionNu params.next k eps delta gamma)
    (hnu_le :
      ldPastingInInductionNu params k eps delta gamma zeta ≤
        (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma) :
    ldPastingInInductionError params k eps delta gamma kappa zeta ≤
      mainInductionError params.next k eps delta gamma := by
  let ν : Error := mainInductionNu params.next k eps delta gamma
  let E : Error :=
    Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))
  let E' : Error :=
    Real.exp (-((k : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ)))))
  have hkappa_le' : kappa ≤ ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta := by
    simpa [ν, E] using hkappa_le
  have hzeta_le_nu' : zeta ≤ ν := by
    simpa [ν] using hzeta_le_nu
  have hnu_le' :
      ldPastingInInductionNu params k eps delta gamma zeta ≤
        (1 / (5 : Error)) * ν := by
    simpa [ν] using hnu_le
  have hnu_nonneg : 0 ≤ ν := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    have hratio_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg (by positivity : 0 ≤ ((params.d : Error) / (params.q : Error)))
        (1 / (1024 : Error))
    have hsumnn : 0 ≤ Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow delta (1 / (1024 : Error)) +
        Real.rpow gamma (1 / (1024 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith [heps_root_nonneg, hdelta_root_nonneg, hgamma_root_nonneg, hratio_nonneg]
    dsimp [ν]
    unfold mainInductionNu
    exact mul_nonneg (by positivity) hsumnn
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact le_of_lt (Real.exp_pos _)
  have hE_le : E ≤ E' := by
    dsimp [E, E']
    apply Real.exp_le_exp.mpr
    have hm_sq_le : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.next.m : Error) ^ (2 : ℕ)) := by
      have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
        exact_mod_cast Nat.le_succ params.m
      nlinarith
    have hdenom_pos : 0 < 80000 * ((params.m : Error) ^ (2 : ℕ)) := by
      have hm_pos : (0 : Error) < (params.m : Error) := by
        exact_mod_cast params.hm
      nlinarith
    have hdenom_le :
        80000 * ((params.m : Error) ^ (2 : ℕ)) ≤
          80000 * ((params.next.m : Error) ^ (2 : ℕ)) := by
      nlinarith [hm_sq_le]
    have h_one_div :
        (1 / (80000 * ((params.next.m : Error) ^ (2 : ℕ))) : Error) ≤
          1 / (80000 * ((params.m : Error) ^ (2 : ℕ))) := by
      exact one_div_le_one_div_of_le hdenom_pos hdenom_le
    have hdiv :
        (k : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))) ≤
          (k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left h_one_div (by positivity : 0 ≤ (k : Error)))
    have hneg :
        -((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))) ≤
          -((k : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ)))) := by
      nlinarith [hdiv]
    exact hneg
  have hcoef_nu :
      ((((params.m : Error) ^ (2 : ℕ)) + 1) *
          (1 + 1 / (100 * (params.m : Error))) + 2 / 5 : Error) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) := by
    have hm0 : (params.m : Error) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hm_one : (1 : Error) ≤ (params.m : Error) := by
      exact_mod_cast params.hm
    have hnext_eq : (params.next.m : Error) = (params.m : Error) + 1 := by
      norm_num [Parameters.next]
    rw [hnext_eq]
    have hpoly : 0 ≤ 495 * ((params.m : Error) ^ (2 : ℕ)) - 200 * (params.m : Error) - 5 := by
      nlinarith [hm_one]
    field_simp [hm0]
    nlinarith [hpoly]
  have hcoef_E :
      ((((params.m : Error) ^ (2 : ℕ)) *
          (1 + 1 / (100 * (params.m : Error))) + 1 : Error)) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) := by
    have hm0 : (params.m : Error) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hnext_eq : (params.next.m : Error) = (params.m : Error) + 1 := by
      norm_num [Parameters.next]
    rw [hnext_eq]
    have hsq : 0 ≤ ((params.m : Error) ^ (2 : ℕ)) := by
      positivity
    field_simp [hm0]
    nlinarith [hsq]
  have hnu_bound :
      ((((params.m : Error) ^ (2 : ℕ)) + 1) *
          (1 + 1 / (100 * (params.m : Error))) + 2 / 5 : Error) * ν ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * ν := by
    exact mul_le_mul_of_nonneg_right hcoef_nu hnu_nonneg
  have hE_bound :
      ((((params.m : Error) ^ (2 : ℕ)) *
          (1 + 1 / (100 * (params.m : Error))) + 1 : Error)) * E ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * E := by
    exact mul_le_mul_of_nonneg_right hcoef_E hE_nonneg
  have herror_old :
      ((((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
          (1 + 1 / (100 * (params.m : Error))) +
        (2 / 5 : Error) * ν + E) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * (ν + E) := by
    have hrewrite :
        ((((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
              (1 + 1 / (100 * (params.m : Error))) +
            (2 / 5 : Error) * ν + E) =
          ((((params.m : Error) ^ (2 : ℕ)) + 1) *
              (1 + 1 / (100 * (params.m : Error))) + 2 / 5 : Error) * ν +
            ((((params.m : Error) ^ (2 : ℕ)) *
              (1 + 1 / (100 * (params.m : Error))) + 1 : Error) * E) := by
      ring
    rw [hrewrite]
    nlinarith [hnu_bound, hE_bound]
  have hkappa_scaled :
      kappa * (1 + 1 / (100 * (params.m : Error))) ≤
        (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
          (1 + 1 / (100 * (params.m : Error))) := by
    exact mul_le_mul_of_nonneg_right hkappa_le' (by positivity)
  have hnu_scaled :
      2 * ldPastingInInductionNu params k eps delta gamma zeta ≤ (2 / 5 : Error) * ν := by
    nlinarith [hnu_le']
  have hzeta_scaled :
      (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
          (1 + 1 / (100 * (params.m : Error))) ≤
        (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
          (1 + 1 / (100 * (params.m : Error))) := by
    have hadd :
        ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta ≤
          ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left hzeta_le_nu' (((params.m : Error) ^ (2 : ℕ)) * (ν + E))
    exact mul_le_mul_of_nonneg_right hadd (by positivity)
  have hzeta_scaled_add :
      (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
          (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E ≤
        (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
          (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hzeta_scaled ((2 / 5 : Error) * ν + E)
  have hE_scaled :
      ((params.next.m : Error) ^ (2 : ℕ)) * E ≤ ((params.next.m : Error) ^ (2 : ℕ)) * E' := by
    exact mul_le_mul_of_nonneg_left hE_le (by positivity)
  calc
    ldPastingInInductionError params k eps delta gamma kappa zeta
      = kappa * (1 + 1 / (100 * (params.m : Error))) +
          2 * ldPastingInInductionNu params k eps delta gamma zeta + E := by
            dsimp [E]
            simp [ldPastingInInductionError]
    _ ≤ (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
          (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E := by
            nlinarith [hkappa_scaled, hnu_scaled]
    _ ≤ (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
          (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E := by
            exact hzeta_scaled_add
    _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) * (ν + E) := herror_old
    _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) * (ν + E') := by
            nlinarith [hE_scaled]
    _ = mainInductionError params.next k eps delta gamma := by
            dsimp [ν, E']
            simp [mainInductionError, Parameters.next]

/-- Scalar absorption for the answer-valued pasting route.

This is the answer-valued counterpart of
`ldPastingInInductionError_le_mainInductionError_of_bounds`.  Its proof uses
only the answer-valued scalar consequences of the small-error hypothesis; it
does not pass through the ordinary carrier strategy. -/
theorem answerLdPastingInInductionError_le_mainInductionError_of_smallError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma kappa : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hkappa_le :
      kappa ≤
        ((params.m : Error) ^ (2 : ℕ)) *
            (mainInductionNu params.next k eps delta gamma +
              Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))
          + selfImprovementInInductionError params.next eps delta gamma)
    (hzeta_le_nu :
      selfImprovementInInductionError params.next eps delta gamma ≤
        mainInductionNu params.next k eps delta gamma) :
    ldPastingInInductionError params k eps delta gamma kappa
        (selfImprovementInInductionError params.next eps delta gamma) ≤
      mainInductionError params.next k eps delta gamma := by
  have heps_nonneg := answer_eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := answer_delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := answer_gamma_nonneg_of_isGood params.next strategy hgood
  have heps_le_one :=
    answer_eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hdelta_le_one :=
    answer_delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hgamma_le_one :=
    answer_gamma_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hdq_le_q :=
    answer_dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall
  have hnu_le :
      ldPastingInInductionNu params k eps delta gamma
          (selfImprovementInInductionError params.next eps delta gamma) ≤
        (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma :=
    ldPastingInInductionNu_le_fifth_mainInductionNu
      params eps delta gamma k
      heps_nonneg hdelta_nonneg hgamma_nonneg
      heps_le_one hdelta_le_one hgamma_le_one hdq_le_q
  exact
    ldPastingInInductionError_le_mainInductionError_of_bounds
      params eps delta gamma k kappa
      (selfImprovementInInductionError params.next eps delta gamma)
      heps_nonneg hdelta_nonneg hgamma_nonneg
      hkappa_le hzeta_le_nu hnu_le

/-- Degree-zero answer-valued pasting construction for the small-error successor
branch.

This is the complementary case to the positive-degree branch handled by
`answerLdPastingInInductionSectionOfComMainAndErrorBound`.  The proof applies
the axis/self-consistency form of the degree-zero pasting construction to the
point-equivalent carrier and then uses the answer-valued scalar absorption
estimate.  It does not use the carrier's dummy ordinary diagonal measurement.

Paper location: the pasting invocation in
`references/ldt-paper/inductive_step.tex:541-551`; this is the `d = 0`
complementary branch of the low-degree pasting theorem. -/
theorem answerLdPastingInInductionSectionDegreeZeroOfSmallError
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
    (_hself :
      family.StronglySelfConsistent strategy.state
        (selfImprovementInInductionError params.next eps delta gamma))
    (_hbound :
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
    (_hk : 400 * params.m * params.d ≤ k)
    (hd_zero : params.d = 0) :
    AnswerMainInductionConclusion params.next strategy eps delta gamma k := by
  let carrier := answerSelfImprovementCarrier params.next strategy
  let zeta : Error := selfImprovementInInductionError params.next eps delta gamma
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
  have heps_nonneg := answer_eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := answer_delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := answer_gamma_nonneg_of_isGood params.next strategy hgood
  have hcompleteCarrier : family.Complete carrier.state kappa := by
    simpa [carrier, answerSelfImprovementCarrier] using hcomplete
  have hconsCarrier : family.ConsistentWithPoints carrier zeta := by
    exact ⟨by simpa [carrier, answerSelfImprovementCarrier, zeta] using hcons⟩
  obtain ⟨H, _hHdef, hpastedCarrier⟩ :=
    Pasting.degreeZeroPastedPointConsistency_of_axis_self params carrier
      eps delta gamma kappa zeta haxis hself_good
      heps_nonneg hdelta_nonneg hgamma_nonneg
      family hcompleteCarrier hconsCarrier hd_zero k
  have hpasted :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (ldPastingInInductionError params k eps delta gamma kappa zeta) := by
    simpa [carrier, answerSelfImprovementCarrier, zeta] using hpastedCarrier
  have herror_le :
      ldPastingInInductionError params k eps delta gamma kappa zeta ≤
        mainInductionError params.next k eps delta gamma := by
    exact answerLdPastingInInductionError_le_mainInductionError_of_smallError
      params strategy eps delta gamma kappa k hgood hsmall
      hkappa_le hzeta_le_nu
  refine ⟨H, ?_⟩
  exact ⟨le_trans hpasted.offDiagonalBound herror_le⟩



end MIPStarRE.LDT.MainInductionStep
