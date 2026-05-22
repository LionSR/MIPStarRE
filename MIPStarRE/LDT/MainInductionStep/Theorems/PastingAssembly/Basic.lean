import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds
import MIPStarRE.LDT.MainInductionStep.Theorems.StageDataConstructors
import MIPStarRE.LDT.MainInductionStep.Theorems.AvgSliceErrors
import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.CommutativityPoints.AnswerTheorems
import MIPStarRE.LDT.Pasting.Bernoulli.DegreeZero
import MIPStarRE.LDT.Tactic.AvgCongr

/-!
# Section 6 — Pasting Assembly: Averaged Family Fields

This module contains the scalar preliminary bound and the averaged family-field
lemmas used by the answer-valued successor route.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Paper `inductive_step.tex:552-566`: in the small-parameter regime, the
induction-side `ldPastingInInductionNu` constructed from `ζ =
selfImprovementInInductionError` is bounded by `(1/5) · ν` where `ν =
mainInductionNu`. This bound discharges the first factor of the telescoping
derivation inside `assembleAveragedPastingData.error_le`. -/
lemma ldPastingInInductionNu_le_fifth_mainInductionNu
    (params : Parameters)
    [FieldModel params.q]
    (eps delta gamma : Error)
    (k : ℕ)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hgamma_le : gamma ≤ 1)
    (hdq_le_q : params.d ≤ params.q) :
    ldPastingInInductionNu params k eps delta gamma
        (selfImprovementInInductionError params.next eps delta gamma) ≤
      (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma := by
  let zeta : Error := selfImprovementInInductionError params.next eps delta gamma
  let n : Error := (params.next.m : Error)
  let A : Error := Real.rpow eps (1 / (1024 : Error))
  let B : Error := Real.rpow delta (1 / (1024 : Error))
  let C : Error := Real.rpow gamma (1 / (1024 : Error))
  let D : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hratio_le_one := dq_ratio_le_one params hdq_le_q
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg heps_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg hdelta_nonneg _
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg hgamma_nonneg _
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact Real.rpow_nonneg hratio_nonneg _
  have heps32_le : Real.rpow eps (1 / (32 : Error)) ≤ A := by
    have htmp :
        Real.rpow eps (1 / (32 : Error)) ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' heps_nonneg heps_le_one
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [A] using htmp
  have hdelta32_le : Real.rpow delta (1 / (32 : Error)) ≤ B := by
    have htmp :
        Real.rpow delta (1 / (32 : Error)) ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' hdelta_nonneg hdelta_le_one
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [B] using htmp
  have hgamma32_le : Real.rpow gamma (1 / (32 : Error)) ≤ C := by
    have htmp :
        Real.rpow gamma (1 / (32 : Error)) ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' hgamma_nonneg hgamma_le
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [C] using htmp
  have hratio32_le :
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤ D := by
    have htmp :
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [D] using htmp
  have hn_two : (2 : Error) ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.succ_le_succ params.hm
  have hzeta32_le : Real.rpow zeta (1 / (32 : Error)) ≤ n * (A + B + D) := by
    let S : Error :=
      Real.rpow eps (1 / (32 : Error)) +
        Real.rpow delta (1 / (32 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      nlinarith [Real.rpow_nonneg heps_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))]
    have hSpow : Real.rpow S (1 / (32 : Error)) ≤ A + B + D := by
      have hsum12 :
          Real.rpow
              (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)))
              (1 / (32 : Error)) ≤
            Real.rpow (Real.rpow eps (1 / (32 : Error))) (1 / (32 : Error)) +
              Real.rpow (Real.rpow delta (1 / (32 : Error))) (1 / (32 : Error)) := by
        exact Real.rpow_add_le_add_rpow (Real.rpow_nonneg heps_nonneg _)
          (Real.rpow_nonneg hdelta_nonneg _)
          (by positivity) (by norm_num : (1 / (32 : Error)) ≤ 1)
      have hsum123 :
          Real.rpow
              ((Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
              (1 / (32 : Error)) ≤
            Real.rpow
                (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)))
                (1 / (32 : Error)) +
              Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
                (1 / (32 : Error)) := by
        exact Real.rpow_add_le_add_rpow
          (add_nonneg (Real.rpow_nonneg heps_nonneg _) (Real.rpow_nonneg hdelta_nonneg _))
          (Real.rpow_nonneg hratio_nonneg _)
          (by positivity) (by norm_num : (1 / (32 : Error)) ≤ 1)
      have heps_id : Real.rpow (Real.rpow eps (1 / (32 : Error))) (1 / (32 : Error)) = A := by
        dsimp [A]
        rw [← Real.rpow_mul heps_nonneg]
        congr 1
        norm_num
      have hdelta_id : Real.rpow (Real.rpow delta (1 / (32 : Error))) (1 / (32 : Error)) = B := by
        dsimp [B]
        rw [← Real.rpow_mul hdelta_nonneg]
        congr 1
        norm_num
      have hratio_id :
          Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
              (1 / (32 : Error)) = D := by
        dsimp [D]
        rw [← Real.rpow_mul hratio_nonneg]
        congr 1
        norm_num
      have hstep :
          Real.rpow S (1 / (32 : Error)) ≤
            (Real.rpow (Real.rpow eps (1 / (32 : Error))) (1 / (32 : Error)) +
                Real.rpow (Real.rpow delta (1 / (32 : Error))) (1 / (32 : Error))) +
              Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
                (1 / (32 : Error)) := by
        have hsum123' :
            Real.rpow S (1 / (32 : Error)) ≤
              Real.rpow
                  (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)))
                  (1 / (32 : Error)) +
                Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
                  (1 / (32 : Error)) := by
          simpa [S, add_assoc] using hsum123
        nlinarith [hsum12, hsum123']
      rw [heps_id, hdelta_id, hratio_id] at hstep
      simpa [add_assoc, add_left_comm, add_comm] using hstep
    have hcoeff_bound : Real.rpow (3000 * n) (1 / (32 : Error)) ≤ n := by
      have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : Error) < 2) hn_two
      have hpow31 : (3000 : Error) ≤ n ^ (31 : ℕ) := by
        have htwo31 : (3000 : Error) ≤ (2 : Error) ^ (31 : ℕ) := by norm_num
        have hmono : (2 : Error) ^ (31 : ℕ) ≤ n ^ (31 : ℕ) := by
          gcongr
        exact le_trans htwo31 hmono
      have hcoeff_le_pow : 3000 * n ≤ n ^ (32 : ℕ) := by
        have hmul := mul_le_mul_of_nonneg_right hpow31 (by positivity : 0 ≤ n)
        calc
          3000 * n ≤ (n ^ (31 : ℕ)) * n := hmul
          _ = n ^ (32 : ℕ) := by ring_nf
      calc
        Real.rpow (3000 * n) (1 / (32 : Error)) ≤ Real.rpow (n ^ (32 : ℕ)) (1 / (32 : Error)) := by
              exact Real.rpow_le_rpow (by positivity) hcoeff_le_pow (by positivity)
        _ = n := by
              have hn_nonneg : 0 ≤ n := le_trans (by norm_num : (0 : Error) ≤ 2) hn_two
              calc
                Real.rpow (n ^ (32 : ℕ)) (1 / (32 : Error))
                    = Real.rpow (Real.rpow n (32 : Error)) (1 / (32 : Error)) := by
                        rw [show (n ^ (32 : ℕ)) = Real.rpow n (32 : Error) by
                              symm
                              exact Real.rpow_natCast n 32]
                _ = Real.rpow n ((32 : Error) * (1 / (32 : Error))) := by
                        symm
                        exact Real.rpow_mul hn_nonneg (32 : Error) (1 / (32 : Error))
                _ = n := by
                        norm_num
    calc
      Real.rpow zeta (1 / (32 : Error))
          = Real.rpow (3000 * n * S) (1 / (32 : Error)) := by
              dsimp [zeta, n, S]
              simp [selfImprovementInInductionError, Parameters.next]
      _ = Real.rpow (3000 * n) (1 / (32 : Error)) * Real.rpow S (1 / (32 : Error)) := by
            calc
              Real.rpow (3000 * n * S) (1 / (32 : Error))
                  = Real.rpow ((3000 * n) * S) (1 / (32 : Error)) := by ring_nf
              _ = Real.rpow (3000 * n) (1 / (32 : Error)) * Real.rpow S (1 / (32 : Error)) := by
                    simpa using (Real.mul_rpow (by positivity : 0 ≤ 3000 * n) hS_nonneg :
                      Real.rpow ((3000 * n) * S) (1 / (32 : Error)) =
                        Real.rpow (3000 * n) (1 / (32 : Error)) * Real.rpow S (1 / (32 : Error)))
      _ ≤ Real.rpow (3000 * n) (1 / (32 : Error)) * (A + B + D) := by
            have hcoeff_nonneg : 0 ≤ Real.rpow (3000 * n) (1 / (32 : Error)) := by
              exact Real.rpow_nonneg (by positivity) _
            exact mul_le_mul_of_nonneg_left hSpow hcoeff_nonneg
      _ ≤ n * (A + B + D) := by
            have habd_nonneg : 0 ≤ A + B + D := by
              nlinarith [hA_nonneg, hB_nonneg, hD_nonneg]
            exact mul_le_mul_of_nonneg_right hcoeff_bound habd_nonneg
  have hzeta32_le' : Real.rpow zeta (1 / (32 : Error)) ≤ n * (A + B + C + D) := by
    have habd_le : A + B + D ≤ A + B + C + D := by
      nlinarith [hC_nonneg]
    exact le_trans hzeta32_le (by gcongr)
  have hsum_noz :
      Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)) +
          Real.rpow gamma (1 / (32 : Error)) +
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
        A + B + C + D := by
    nlinarith [heps32_le, hdelta32_le, hgamma32_le, hratio32_le]
  have hsum_nonneg : 0 ≤ A + B + C + D := by
    nlinarith [hA_nonneg, hB_nonneg, hC_nonneg, hD_nonneg]
  have hsum_le :
      Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)) +
          Real.rpow gamma (1 / (32 : Error)) + Real.rpow zeta (1 / (32 : Error)) +
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
        (2 * n) * (A + B + C + D) := by
    have hone_plus_n : (1 : Error) + n ≤ 2 * n := by
      nlinarith [hn_two]
    nlinarith [hsum_noz, hzeta32_le', hsum_nonneg, hone_plus_n]
  calc
    ldPastingInInductionNu params k eps delta gamma zeta
      = 100 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          dsimp [zeta]
          simp [ldPastingInInductionNu]
    _ ≤ 100 * ((k : Error) ^ (2 : ℕ)) * n * ((2 * n) * (A + B + C + D)) := by
          let sum32 : Error :=
            Real.rpow eps (1 / (32 : Error)) +
              Real.rpow delta (1 / (32 : Error)) +
              Real.rpow gamma (1 / (32 : Error)) +
              Real.rpow zeta (1 / (32 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
          have hm_le_n : (params.m : Error) ≤ n := by
            dsimp [n]
            exact_mod_cast Nat.le_succ params.m
          have heps32_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
            Real.rpow_nonneg heps_nonneg (1 / (32 : Error))
          have hdelta32_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
            Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error))
          have hgamma32_nonneg : 0 ≤ Real.rpow gamma (1 / (32 : Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (32 : Error))
          have hzeta_nonneg : 0 ≤ zeta := by
            dsimp [zeta]
            have hratio32_nonneg' :
                0 ≤ Real.rpow
                  (((params.next.d : Error) / (params.next.q : Error)))
                  (1 / (32 : Error)) :=
              Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
            have hsum_nonneg' :
                0 ≤ Real.rpow eps (1 / (32 : Error)) +
                      Real.rpow delta (1 / (32 : Error)) +
                      Real.rpow
                        (((params.next.d : Error) / (params.next.q : Error)))
                        (1 / (32 : Error)) := by
              exact add_nonneg (add_nonneg heps32_nonneg hdelta32_nonneg) hratio32_nonneg'
            unfold selfImprovementInInductionError
            exact mul_nonneg (by positivity) hsum_nonneg'
          have hzeta32_nonneg : 0 ≤ Real.rpow zeta (1 / (32 : Error)) :=
            Real.rpow_nonneg hzeta_nonneg (1 / (32 : Error))
          have hratio32_nonneg :
              0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
            Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
          have hsum32_nonneg : 0 ≤ sum32 := by
            dsimp [sum32]
            exact add_nonneg
              (add_nonneg
                (add_nonneg
                  (add_nonneg heps32_nonneg hdelta32_nonneg)
                  hgamma32_nonneg)
                hzeta32_nonneg)
              hratio32_nonneg
          have hinner : (params.m : Error) * sum32 ≤ n * ((2 * n) * (A + B + C + D)) := by
            have hstep₁ : (params.m : Error) * sum32 ≤ n * sum32 := by
              exact mul_le_mul_of_nonneg_right hm_le_n hsum32_nonneg
            have hstep₂ : n * sum32 ≤ n * ((2 * n) * (A + B + C + D)) := by
              exact mul_le_mul_of_nonneg_left hsum_le (by positivity : 0 ≤ n)
            exact le_trans hstep₁ hstep₂
          simpa [sum32, mul_assoc] using
            (mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 100 * ((k : Error) ^ (2 : ℕ))))
    _ = (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma := by
          dsimp [n, A, B, C, D]
          simp [mainInductionNu, Parameters.next]
          ring

/-- The nontrivial main-induction branch supplies the scalar side condition
`ζ ≤ 1` needed by the averaged pasting assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:486-551`, where the
small-error branch is the one in which the averaged self-improvement and
pasting estimates are used. -/
lemma selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error}
    {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    selfImprovementInInductionError params.next eps delta gamma ≤ 1 := by
  have heps_le_one :
      eps ≤ 1 := eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hdelta_le_one :
      delta ≤ 1 := delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hdq_le_q :
      params.d ≤ params.q := dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall
  have hzeta_le_nu :
      selfImprovementInInductionError params.next eps delta gamma ≤
        mainInductionNu params.next k eps delta gamma :=
    selfImprovementInInductionError_le_mainInductionNu
      params strategy eps delta gamma k hgood hsmall heps_le_one hdelta_le_one hdq_le_q
  have hnu_lt_one :
      mainInductionNu params.next k eps delta gamma < 1 :=
    mainInductionNu_lt_one_of_mainInductionError_lt_one
      params.next k eps delta gamma hsmall
  exact le_trans hzeta_le_nu (le_of_lt hnu_lt_one)

/-- Answer-valued analogue of
`selfImprovementInInductionError_le_one_of_mainInductionError_lt_one`.

This is a scalar consequence of the small-error branch for an ambient
answer-valued strategy.  It does not use the ordinary carrier strategy and does
not assert that the answer-valued diagonal measurement is controlled by an
ordinary diagonal test. -/
lemma answer_selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    {eps delta gamma : Error}
    {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    selfImprovementInInductionError params.next eps delta gamma ≤ 1 := by
  have heps_le_one :
      eps ≤ 1 := answer_eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hdelta_le_one :
      delta ≤ 1 := answer_delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hdq_le_q :
      params.d ≤ params.q :=
    answer_dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall
  have hzeta_le_nu :
      selfImprovementInInductionError params.next eps delta gamma ≤
        mainInductionNu params.next k eps delta gamma :=
    answer_selfImprovementInInductionError_le_mainInductionNu
      params strategy eps delta gamma k hgood hsmall heps_le_one hdelta_le_one hdq_le_q
  have hnu_lt_one :
      mainInductionNu params.next k eps delta gamma < 1 :=
    mainInductionNu_lt_one_of_mainInductionError_lt_one
      params.next k eps delta gamma hsmall
  exact le_trans hzeta_le_nu (le_of_lt hnu_lt_one)

/-- The average of the answer-slice self-improvement errors is bounded by the
ambient induction self-improvement error.

This is the ordinary ambient version: the restricted slices use the
answer-valued interface, but the ambient strategy is an ordinary `SymStrat`. -/
lemma average_answerSliceSelfImprovementError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => answerSliceSelfImprovementError params hrestrict x) ≤
      selfImprovementInInductionError params.next eps delta gamma := by
  simpa [answerSliceSelfImprovementError, sliceSelfImprovementError,
    SliceRestrictionData.ofAnswer] using
    (average_sliceSelfImprovementError_le params strategy eps delta gamma hgood
      (SliceRestrictionData.ofAnswer params strategy eps delta gamma hrestrict))

/-- The average recursive answer-slice induction error satisfies the same bound
as in the ordinary slice route.

The proof is a transport of the already checked ordinary averaging estimate
through the answer-valued slice-to-ordinary data conversion. -/
lemma average_answerSliceError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerPerSliceInductionData params strategy eps delta gamma hrestrict k) :
    avgOver (uniformDistribution (Fq params)) hinduction.sliceError ≤
      ((params.m : Error) ^ (2 : ℕ)) *
        (mainInductionNu params.next k eps delta gamma +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
  simpa [PerSliceInductionData.ofAnswer, SliceRestrictionData.ofAnswer] using
    (average_sliceError_le params strategy eps delta gamma k hgood
      (SliceRestrictionData.ofAnswer params strategy eps delta gamma hrestrict)
      (PerSliceInductionData.ofAnswer params strategy eps delta gamma k hrestrict hinduction))

/-- The mass of the averaged polynomial family is the average of the masses of
the slice measurements.

This is the linearity calculation underlying the completeness part of the
averaged pasting assembly. -/
lemma idxPolyFamily_averagedMass_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) :
    subMeasMass ψ family.averagedSubMeas.liftLeft =
      avgOver (uniformDistribution (Fq params))
        (fun x => subMeasMass ψ ((family.meas x).toSubMeas.liftLeft)) := by
  change
    ev ψ
        (leftTensor (ι₂ := ι)
          (∑ x : Fq params,
            ((1 / (Fintype.card (Fq params) : Error)) : Error) •
              (family.meas x).toSubMeas.total)) =
      ∑ x : Fq params,
        (1 / (Fintype.card (Fq params) : Error)) *
          ev ψ (leftTensor (ι₂ := ι) ((family.meas x).toSubMeas.total))
  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ
    (fun x : Fq params => ((1 / (Fintype.card (Fq params) : Error)) : Error) •
      (family.meas x).toSubMeas.total)]
  rw [ev_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hsmul :
      leftTensor (ι₂ := ι)
          (((1 / (Fintype.card (Fq params) : Error)) : Error) •
            (family.meas x).toSubMeas.total) =
        ((1 / (Fintype.card (Fq params) : Error)) : Error) •
          leftTensor (ι₂ := ι) ((family.meas x).toSubMeas.total) := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
      simp [leftTensor, h₁, h₂]
  rw [hsmul]
  have hreal_complex :
      ((1 / (Fintype.card (Fq params) : Error)) : Error) •
          leftTensor (ι₂ := ι) ((family.meas x).toSubMeas.total) =
        (((1 / (Fintype.card (Fq params) : Error)) : Error) : ℂ) •
          leftTensor (ι₂ := ι) ((family.meas x).toSubMeas.total) := by
    ext i j
    simp
  rw [hreal_complex, ev_scale]

/-- Averaged completeness of a slice-indexed polynomial family from pointwise
slice completeness.

This is the completeness component of the Section 6 averaging argument.  The
statement is family-level: it does not mention diagonal measurements, and hence
can be reused in the answer-valued successor route. -/
lemma idxPolyFamily_complete_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (sliceError sliceSelfError : Fq params → Error)
    (hcomplete :
      ∀ x,
        CompletenessAtLeast ψ ((family.meas x).toSubMeas.liftLeft)
          ((1 - sliceError x) - sliceSelfError x)) :
    family.Complete ψ
      (avgOver (uniformDistribution (Fq params)) sliceError +
        avgOver (uniformDistribution (Fq params)) sliceSelfError) := by
  classical
  let 𝒟 : Distribution (Fq params) := uniformDistribution (Fq params)
  refine ⟨?_⟩
  refine ⟨?_⟩
  have hmass_eq := idxPolyFamily_averagedMass_eq_avg params ψ family
  have havg_lower :
      1 - (avgOver 𝒟 sliceError + avgOver 𝒟 sliceSelfError) ≤
        avgOver 𝒟
          (fun x => subMeasMass ψ ((family.meas x).toSubMeas.liftLeft)) := by
    have hconst1 : avgOver 𝒟 (fun _ : Fq params => (1 : Error)) = 1 := by
      simpa [𝒟] using (avgOver_uniform_const (α := Fq params) (1 : Error))
    have hnegErr : avgOver 𝒟 (fun a => -sliceError a) = -avgOver 𝒟 sliceError := by
      simpa [avgOver_const_mul] using (avgOver_const_mul 𝒟 (-1) sliceError)
    have hnegZeta :
        avgOver 𝒟 (fun a => -sliceSelfError a) = -avgOver 𝒟 sliceSelfError := by
      simpa [avgOver_const_mul] using (avgOver_const_mul 𝒟 (-1) sliceSelfError)
    calc
      1 - (avgOver 𝒟 sliceError + avgOver 𝒟 sliceSelfError) =
          avgOver 𝒟 (fun x => (1 - sliceError x) - sliceSelfError x) := by
            rw [show (fun x => (1 - sliceError x) - sliceSelfError x) =
                fun x => 1 + (-sliceError x) + (-sliceSelfError x) by
                funext x
                ring]
            rw [avgOver_add, avgOver_add, hconst1, hnegErr, hnegZeta]
            ring
      _ ≤ avgOver 𝒟
          (fun x => subMeasMass ψ ((family.meas x).toSubMeas.liftLeft)) := by
            apply avgOver_mono
            intro x
            exact (hcomplete x).lowerBound
  rw [hmass_eq]
  exact havg_lower

lemma family_pointConsistencyError_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    {hrestrict : SliceRestrictionData params strategy eps delta gamma}
    {hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k}
    (hself : SelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint hself.family) =
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params (hself.sliceProj x).toSubMeas)) := by
  let g : Point params.next → Error := fun u =>
    qBipartiteConsDefect strategy.state
      ((strategy.pointMeasurement u).toSubMeas)
      ((IdxPolyFamily.evaluatedAtNextPoint hself.family) u)
  calc
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint hself.family)
      = avgOver (uniformDistribution (Point params.next)) g := by
          rfl
    _ = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => g (appendPoint params ux.1 ux.2)) := by
           simpa [CommutativityPoints.pointNextEquiv] using
            (MIPStarRE.LDT.avgOver_uniform_equiv
              (e := CommutativityPoints.pointNextEquiv params)
              (f := g))
    _ = avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => g (appendPoint params xu.2 xu.1)) := by
           simpa using
            (MIPStarRE.LDT.avgOver_uniform_equiv
              (e := Equiv.prodComm (Point params) (Fq params))
              (f := fun ux : Point params × Fq params => g (appendPoint params ux.1 ux.2)))
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
          simpa using
            (avgOver_uniform_prod (f := fun x u => g (appendPoint params u x)))
    _ = avgOver (uniformDistribution (Fq params))
          (fun x =>
            bipartiteConsError strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
              (polynomialEvaluationFamily params (hself.sliceProj x).toSubMeas)) := by
          unfold bipartiteConsError
          avg_congr with x, u
          simp [g, IdxPolyFamily.evaluatedAtNextPoint, polynomialEvaluationFamily,
            IdxProjMeas.toIdxSubMeas]
          rfl

/-- Point-consistency averaging for answer-valued restricted slices of an
ordinary ambient successor strategy. -/
lemma family_answerRestrictedPointConsistencyError_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family) =
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params (family.meas x).toSubMeas)) := by
  let g : Point params.next → Error := fun u =>
    qBipartiteConsDefect strategy.state
      ((strategy.pointMeasurement u).toSubMeas)
      ((IdxPolyFamily.evaluatedAtNextPoint family) u)
  calc
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
      = avgOver (uniformDistribution (Point params.next)) g := by
          rfl
    _ = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => g (appendPoint params ux.1 ux.2)) := by
           simpa [CommutativityPoints.pointNextEquiv] using
            (MIPStarRE.LDT.avgOver_uniform_equiv
              (e := CommutativityPoints.pointNextEquiv params)
              (f := g))
    _ = avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => g (appendPoint params xu.2 xu.1)) := by
           simpa using
            (MIPStarRE.LDT.avgOver_uniform_equiv
              (e := Equiv.prodComm (Point params) (Fq params))
              (f := fun ux : Point params × Fq params => g (appendPoint params ux.1 ux.2)))
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
          simpa using
            (avgOver_uniform_prod (f := fun x u => g (appendPoint params u x)))
    _ = avgOver (uniformDistribution (Fq params))
          (fun x =>
            bipartiteConsError strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas
                (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
              (polynomialEvaluationFamily params (family.meas x).toSubMeas)) := by
          unfold bipartiteConsError
          avg_congr with x, u
          simp [g, IdxPolyFamily.evaluatedAtNextPoint, polynomialEvaluationFamily,
            IdxProjMeas.toIdxSubMeas, xRestrictedAnswerSymStrat]
          rfl

/-- Answer-valued point-consistency averaging over the last coordinate.

This is the same Fubini/reindexing calculation as
`family_pointConsistencyError_eq_avg`, but for an ambient answer-valued
successor strategy.  It is one of the identities needed to assemble the
answer-valued successor branch without replacing the diagonal-line answer
measurement by an ordinary polynomial-valued one. -/
lemma answer_family_pointConsistencyError_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family) =
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params (family.meas x).toSubMeas)) := by
  let g : Point params.next → Error := fun u =>
    qBipartiteConsDefect strategy.state
      ((strategy.pointMeasurement u).toSubMeas)
      ((IdxPolyFamily.evaluatedAtNextPoint family) u)
  calc
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
      = avgOver (uniformDistribution (Point params.next)) g := by
          rfl
    _ = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => g (appendPoint params ux.1 ux.2)) := by
           simpa [CommutativityPoints.pointNextEquiv] using
            (MIPStarRE.LDT.avgOver_uniform_equiv
              (e := CommutativityPoints.pointNextEquiv params)
              (f := g))
    _ = avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => g (appendPoint params xu.2 xu.1)) := by
           simpa using
            (MIPStarRE.LDT.avgOver_uniform_equiv
              (e := Equiv.prodComm (Point params) (Fq params))
              (f := fun ux : Point params × Fq params => g (appendPoint params ux.1 ux.2)))
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
          simpa using
            (avgOver_uniform_prod (f := fun x u => g (appendPoint params u x)))
    _ = avgOver (uniformDistribution (Fq params))
          (fun x =>
            bipartiteConsError strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas
                (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
              (polynomialEvaluationFamily params (family.meas x).toSubMeas)) := by
          unfold bipartiteConsError
          avg_congr with x, u
          simp [g, IdxPolyFamily.evaluatedAtNextPoint, polynomialEvaluationFamily,
            IdxProjMeas.toIdxSubMeas, xRestrictedAnswerSymStratOfAnswer]
          rfl

/-- Average slice-wise point consistency for an answer-valued successor strategy.

If the slice family is point-consistent with each answer-valued restricted
strategy at error `sliceError x`, and the slice errors average to at most
`zeta`, then the evaluated family is point-consistent with the ambient
answer-valued point measurement at error `zeta`. -/
lemma answer_family_consistency_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (sliceError : Fq params → Error)
    (zeta : Error)
    (hpoint :
      ∀ x,
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas
            (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params (family.meas x).toSubMeas)
          (sliceError x))
    (havg : avgOver (uniformDistribution (Fq params)) sliceError ≤ zeta) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (IdxPolyFamily.evaluatedAtNextPoint family)
      zeta := by
  refine ⟨?_⟩
  calc
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
      = avgOver (uniformDistribution (Fq params))
          (fun x =>
            bipartiteConsError strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas
                (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement)
              (polynomialEvaluationFamily params (family.meas x).toSubMeas)) :=
          answer_family_pointConsistencyError_eq_avg params strategy family
    _ ≤ avgOver (uniformDistribution (Fq params)) sliceError := by
          exact avgOver_mono (uniformDistribution (Fq params)) _ _ fun x =>
            (hpoint x).offDiagonalBound
    _ ≤ zeta := havg

/-- Average slice-wise left/right closeness into strong self-consistency of the
slice-indexed family.

This is the strong self-consistency component of the Section 6 averaging
argument.  It depends only on the state and the slice measurements, not on the
diagonal part of a strategy. -/
lemma idxPolyFamily_stronglySelfConsistent_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (sliceError : Fq params → Error)
    (zeta : Error)
    (hself :
      ∀ x,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (family.meas x).toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (family.meas x).toSubMeas))
          (sliceError x))
    (havg : avgOver (uniformDistribution (Fq params)) sliceError ≤ zeta) :
    family.StronglySelfConsistent ψ zeta := by
  refine ⟨?_⟩
  refine ⟨?_⟩
  have hpointwise :
      ∀ x,
        qSDD ψ ((family.meas x).toSubMeas.liftLeft)
          ((family.meas x).toSubMeas.liftRight) ≤ sliceError x := by
    intro x
    simpa [sddError, avgOver_uniform_const, constSubMeasFamily] using
      (hself x).squaredDistanceBound
  calc
    sddError ψ (uniformDistribution (Fq params))
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
        (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      = avgOver (uniformDistribution (Fq params))
          (fun x =>
            qSDD ψ ((family.meas x).toSubMeas.liftLeft)
              ((family.meas x).toSubMeas.liftRight)) := by
            rfl
    _ ≤ avgOver (uniformDistribution (Fq params)) sliceError := by
          exact avgOver_mono (uniformDistribution (Fq params)) _ _ hpointwise
    _ ≤ zeta := havg

/-- Average slice-wise boundedness into the boundedness input used by the
induction-section pasting theorem.

This is the boundedness component of the Section 6 averaging argument for an
ordinary successor strategy.  The hypotheses are exactly the slice-wise
residual estimate and the paper domination condition
`E_u A^{u,x}_{g(u)} <= Z^x`.

**Lean-only:** This is an internal adapter for the induction-section pasting
interface, tracked in issue #1507.  Paper origin:
`references/ldt-paper/inductive_step.tex:461-551`.  Discharge: proved here by
averaging the slice-wise boundedness estimates and the domination condition. -/
lemma idxPolyFamily_sliceBoundednessInput_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (sliceError : Fq params → Error)
    (zeta : Error)
    (hbounded :
      ∀ x,
        tensorFailureExpectation strategy.state (family.witness x)
          (family.meas x).toSubMeas ≤ sliceError x)
    (havg : avgOver (uniformDistribution (Fq params)) sliceError ≤ zeta)
    (hdom :
      ∀ x, ∀ g : Polynomial params,
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x) :
    IdxPolyFamily.SliceBoundednessInput strategy family zeta := by
  classical
  refine
    { sliceOpPSD := ?_
      sliceBoundedness := ?_
      sliceDominatesAveragedPoint := hdom }
  · intro x
    let g0 : Polynomial params :=
      Classical.choice (inferInstance : Nonempty (Polynomial params))
    have htarget_nonneg :
        0 ≤ IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g0 := by
      unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
      exact Finset.sum_nonneg fun u hu =>
        smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
          ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome_pos (g0 u))
    exact le_trans htarget_nonneg (hdom x g0)
  · have hswap :
        avgOver (uniformDistribution (Fq params))
            (fun x =>
              ev strategy.state
                (leftTensor (ι₂ := ι) (1 - (family.meas x).toSubMeas.total) *
                  rightTensor (ι₁ := ι) (family.witness x))) =
          avgOver (uniformDistribution (Fq params))
            (fun x =>
              tensorFailureExpectation strategy.state (family.witness x)
                (family.meas x).toSubMeas) := by
      apply avgOver_congr
      intro x
      simpa [tensorFailureExpectation, leftTensor_mul_rightTensor_eq_opTensor] using
        (ev_opTensor_swap_of_density_fixed strategy.state
          strategy.permInvState.density_swap
          (1 - (family.meas x).toSubMeas.total) (family.witness x))
    rw [hswap]
    calc
      avgOver (uniformDistribution (Fq params))
          (fun x =>
            tensorFailureExpectation strategy.state (family.witness x)
              (family.meas x).toSubMeas)
        ≤ avgOver (uniformDistribution (Fq params)) sliceError := by
            exact avgOver_mono (uniformDistribution (Fq params)) _ _ hbounded
      _ ≤ zeta := havg

end MIPStarRE.LDT.MainInductionStep
