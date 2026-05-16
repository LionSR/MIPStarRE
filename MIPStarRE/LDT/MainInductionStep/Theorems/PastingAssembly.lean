import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds
import MIPStarRE.LDT.MainInductionStep.Theorems.StageDataConstructors
import MIPStarRE.LDT.MainInductionStep.Theorems.AvgSliceErrors
import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.Tactic.AvgCongr

/-!
# Section 6 — Pasting Assembly

Private helpers for the fifth-of-ν bound on `ldPastingInInductionNu`,
the family-averaging lemmas, and the main assembly definition
`assembleAveragedPastingData`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper `inductive_step.tex:552-566`: in the small-parameter regime, the
induction-side `ldPastingInInductionNu` constructed from `ζ =
selfImprovementInInductionError` is bounded by `(1/5) · ν` where `ν =
mainInductionNu`. This bound discharges the first factor of the telescoping
derivation inside `assembleAveragedPastingData.error_le`. -/
private lemma ldPastingInInductionNu_le_fifth_mainInductionNu
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1)
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
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have heps_le_one :=
    eps_le_one_of_selfImprovementInInductionError_le_one params strategy hgood hzeta_le
  have hdelta_le_one :=
    delta_le_one_of_selfImprovementInInductionError_le_one params strategy hgood hzeta_le
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

private lemma family_averagedMass_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    {hrestrict : SliceRestrictionData params strategy eps delta gamma}
    {hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k}
    (hself : SelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    subMeasMass strategy.state hself.family.averagedSubMeas.liftLeft =
      avgOver (uniformDistribution (Fq params))
        (fun x => subMeasMass strategy.state ((hself.sliceProj x).toSubMeas.liftLeft)) := by
  change
    ev strategy.state
        (leftTensor (ι₂ := ι)
          (∑ x : Fq params,
            ((1 / (Fintype.card (Fq params) : Error)) : Error) •
              (hself.sliceProj x).toSubMeas.total)) =
      ∑ x : Fq params,
        (1 / (Fintype.card (Fq params) : Error)) *
          ev strategy.state (leftTensor (ι₂ := ι) ((hself.sliceProj x).toSubMeas.total))
  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ
    (fun x : Fq params => ((1 / (Fintype.card (Fq params) : Error)) : Error) •
      (hself.sliceProj x).toSubMeas.total)]
  rw [ev_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hsmul :
      leftTensor (ι₂ := ι)
          (((1 / (Fintype.card (Fq params) : Error)) : Error) •
            (hself.sliceProj x).toSubMeas.total) =
        ((1 / (Fintype.card (Fq params) : Error)) : Error) •
          leftTensor (ι₂ := ι) ((hself.sliceProj x).toSubMeas.total) := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
      simp [leftTensor, h₁, h₂]
  rw [hsmul]
  have hreal_complex :
      ((1 / (Fintype.card (Fq params) : Error)) : Error) •
          leftTensor (ι₂ := ι) ((hself.sliceProj x).toSubMeas.total) =
        (((1 / (Fintype.card (Fq params) : Error)) : Error) : ℂ) •
          leftTensor (ι₂ := ι) ((hself.sliceProj x).toSubMeas.total) := by
    ext i j
    simp
  rw [hreal_complex, ev_scale]

private lemma family_pointConsistencyError_eq_avg
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

set_option maxHeartbeats 1000000 in
-- The averaged slice-to-pasting assembly generates several large nonlinear
-- arithmetic goals in the final telescoping estimate.
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
  let ν : Error := mainInductionNu params.next k eps delta gamma
  let E : Error :=
    Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))
  let E' : Error :=
    Real.exp (-((k : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ)))))
  refine
    { kappa := kappa
      zeta := zeta
      gamma_le_one := hgamma_le
      zeta_le_one := hzeta_le
      dq_le_q := hdq_le_q
      complete := by
        refine ⟨?_⟩
        refine ⟨?_⟩
        have hmass_eq := family_averagedMass_eq_avg params strategy hself
        have havg_lower :
            1 - kappa ≤
              avgOver 𝒟
                (fun x => subMeasMass strategy.state ((hself.sliceProj x).toSubMeas.liftLeft)) := by
          have hconst1 : avgOver 𝒟 (fun _ : Fq params => (1 : Error)) = 1 := by
            simpa [𝒟] using (avgOver_uniform_const (α := Fq params) (1 : Error))
          have hnegErr : avgOver 𝒟 (fun a => -hinduction.sliceError a)
              = -avgOver 𝒟 hinduction.sliceError := by
            simpa [avgOver_const_mul] using (avgOver_const_mul 𝒟 (-1) hinduction.sliceError)
          have hnegZeta :
              avgOver 𝒟 (fun a => -sliceSelfImprovementError params hrestrict a) =
                -avgOver 𝒟 (fun a => sliceSelfImprovementError params hrestrict a) := by
            simpa [avgOver_const_mul] using
              (avgOver_const_mul 𝒟 (-1) (fun a => sliceSelfImprovementError params hrestrict a))
          calc
            1 - kappa = avgOver 𝒟
                (fun x => (1 - hinduction.sliceError x) - sliceSelfImprovementError params
                    hrestrict x) := by
                  dsimp [kappa]
                  rw [show (fun x => (1 - hinduction.sliceError x) -
                        sliceSelfImprovementError params hrestrict x) =
                      fun x => 1 + (-hinduction.sliceError x) +
                        (-sliceSelfImprovementError params hrestrict x) by
                        funext x
                        ring]
                  rw [avgOver_add, avgOver_add, hconst1, hnegErr, hnegZeta]
                  ring
            _ ≤ avgOver 𝒟
                (fun x => subMeasMass strategy.state ((hself.sliceProj x).toSubMeas.liftLeft)) := by
                  apply avgOver_mono
                  intro x
                  exact (hself.completeness x).lowerBound
        rw [hmass_eq]
        exact havg_lower
      consistent := by
        refine ⟨?_⟩
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
      selfConsistent := by
        refine ⟨?_⟩
        refine ⟨?_⟩
        have hpointwise :
            ∀ x,
              qSDD strategy.state ((hself.sliceProj x).toSubMeas.liftLeft)
                ((hself.sliceProj x).toSubMeas.liftRight) ≤
              sliceSelfImprovementError params hrestrict x := by
          intro x
          simpa [sddError, avgOver_uniform_const, constSubMeasFamily] using
            (hself.selfCloseness x).squaredDistanceBound
        calc
          sddError strategy.state 𝒟
              (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas hself.family.meas))
              (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas hself.family.meas))
            = avgOver 𝒟
                (fun x =>
                  qSDD strategy.state ((hself.sliceProj x).toSubMeas.liftLeft)
                    ((hself.sliceProj x).toSubMeas.liftRight)) := by
                  rfl
          _ ≤ avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x) := by
                exact avgOver_mono 𝒟 _ _ hpointwise
          _ ≤ zeta := by
                simpa [zeta, 𝒟] using
                  (average_sliceSelfImprovementError_le
                    params strategy eps delta gamma hgood hrestrict)
      bounded := by
        refine
          { sliceOpPSD := ?_
            sliceBoundedness := ?_
            sliceDominatesAveragedPoint := ?_ }
        · intro x
          let g0 : Polynomial params :=
            Classical.choice (inferInstance : Nonempty (Polynomial params))
          have htarget_nonneg :
              0 ≤ IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g0 := by
            unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
            exact Finset.sum_nonneg fun u hu =>
              smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
                ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome_pos
                  (g0 u))
          exact le_trans htarget_nonneg (hself.dominatesAveragePointOperator x g0)
        · have hswap :
              avgOver 𝒟
                  (fun x =>
                    ev strategy.state
                      (leftTensor (ι₂ := ι) (1 - (hself.family.meas x).toSubMeas.total) *
                        rightTensor (ι₁ := ι) (hself.family.witness x))) =
                avgOver 𝒟
                  (fun x =>
                    tensorFailureExpectation strategy.state (hself.sliceWitness x)
                      (hself.sliceProj x).toSubMeas) := by
            apply avgOver_congr
            intro x
            simpa [tensorFailureExpectation, SelfImprovementData.family,
              leftTensor_mul_rightTensor_eq_opTensor] using
              (ev_opTensor_swap_of_density_fixed strategy.state
                strategy.permInvState.density_swap
                (1 - (hself.sliceProj x).toSubMeas.total) (hself.sliceWitness x))
          rw [hswap]
          calc
            avgOver 𝒟
                (fun x =>
                  tensorFailureExpectation strategy.state (hself.sliceWitness x)
                    (hself.sliceProj x).toSubMeas)
              ≤ avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x) := by
                  exact avgOver_mono 𝒟 _ _ hself.bounded
            _ ≤ zeta := by
                  simpa [zeta, 𝒟] using
                    (average_sliceSelfImprovementError_le
                      params strategy eps delta gamma hgood hrestrict)
        · intro x g
          exact hself.dominatesAveragePointOperator x g
      error_le := by
        have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
        have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
        have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
        have heps_le_one :=
          eps_le_one_of_selfImprovementInInductionError_le_one
            params strategy hgood hzeta_le
        have hdelta_le_one :=
          delta_le_one_of_selfImprovementInInductionError_le_one
            params strategy hgood hzeta_le
        have hkappa_le :
            kappa ≤ ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta := by
          dsimp [kappa, zeta, ν, E]
          nlinarith
            [average_sliceError_le params strategy eps delta gamma k hgood hrestrict hinduction,
              average_sliceSelfImprovementError_le
                params strategy eps delta gamma hgood hrestrict]
        have hzeta_le_nu : zeta ≤ ν := by
          simpa [zeta, ν] using
            selfImprovementInInductionError_le_mainInductionNu
              params strategy eps delta gamma k
              hgood hsmall heps_le_one hdelta_le_one hdq_le_q
        have hnu_le :
            ldPastingInInductionNu params k eps delta gamma zeta ≤
              (1 / (5 : Error)) * ν := by
          simpa [zeta, ν] using
            ldPastingInInductionNu_le_fifth_mainInductionNu
              params strategy eps delta gamma k
              hgood hzeta_le hgamma_le hdq_le_q
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
        -- The paper uses the stronger coefficient estimate
        -- `(1 + 1 / (100m)) * (m^2 + 3) ≤ (m + 1)^2`, which needs `m ≥ 2`.
        -- Here we apply `ζ ≤ ν` (`hzeta_le_nu`) *before* telescoping, which
        -- collapses the paper's `2ν` contribution to `(2/5)ν` and yields the
        -- weaker `((m^2 + 1)(1 + 1/(100m)) + 2/5) ≤ (m + 1)^2`, already valid
        -- for every `m ≥ 1`.
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
          exact mul_le_mul_of_nonneg_right hkappa_le (by positivity)
        have hnu_scaled :
            2 * ldPastingInInductionNu params k eps delta gamma zeta ≤ (2 / 5 : Error) * ν := by
          nlinarith [hnu_le]
        have hzeta_scaled :
            (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
                (1 + 1 / (100 * (params.m : Error))) ≤
              (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
                (1 + 1 / (100 * (params.m : Error))) := by
          have hadd :
              ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta ≤
                ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left hzeta_le_nu (((params.m : Error) ^ (2 : ℕ)) * (ν + E))
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
                  simp [mainInductionError, Parameters.next] }


end MIPStarRE.LDT.MainInductionStep
