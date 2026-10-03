module

public import MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.EnvelopeBounds

/-!
# Error cascade — bounds for `σ` and `ζ₁`

This module proves the tight and absorbing bounds for the first two cascade
variables, `σ` and `ζ₁`.  The later variables `ζ₂`, `ζ₃`, and `ζ₄`, together
with the top-level consolidator `errorCascade_le_mainFormalError`, are in the
subsequent leaves of `Test.MainTheorem.ScalarBounds.CascadeBounds`.

The first cascade steps have three components:

* The **tight cascade bound** (`cascadeSigma_tight_bound`, `cascadeZeta1_bound`, …),
  deriving the native estimate directly from the cascade definition.
* The **absorbing bound** (`sigma_bound`, `zeta1_bound`, …), coarsening the
  tight estimate to the final `mainFormalEnvelope` envelope.
* The corresponding nonnegativity lemmas (`cascadeSigma_nonneg`,
  `cascadeZeta1_nonneg`), used by the later cascade estimates.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section


open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

theorem cascadeSigma_tight_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeSigma params k ν ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (1024 : Error) (80000 : Error) := by
  unfold cascadeSigma stepEnvelope
  set m2 : Error := (params.m : Error) ^ (2 : ℕ) with hm2_def
  set m4 : Error := (params.m : Error) ^ (4 : ℕ) with hm4_def
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  have hm2NN : 0 ≤ m2 := by positivity
  have hk2_ge_one : (1 : Error) ≤ k2 := h.k2_ge_one
  have hm2_le_m4 : m2 ≤ m4 := h.m2_le_m4
  have hm2_sq_m4 : m2 * m2 = m4 := by
    simp only [hm2_def, hm4_def]
    ring
  have hStep1 :
      m2 * ν ≤ 10000 * k2 * m4 *
        (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
    have hreorder :
        m2 * (10000 * k2 * m2 *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) =
          10000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
      ring
    calc
      m2 * ν
          ≤ m2 * (10000 * k2 * m2 *
              (Real.rpow eps (1 / (1024 : Error)) +
                Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :=
            mul_le_mul_of_nonneg_left hν hm2NN
      _ = 10000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := hreorder
      _ = 10000 * k2 * m4 *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error))
                (1 / (1024 : Error))) := by
            rw [hm2_sq_m4]
  have hScaleGeOne : (1 : Error) ≤ 10000 * k2 := by
    nlinarith [hk2_ge_one]
  have hm2_le_10k2m4 : m2 ≤ 10000 * k2 * m4 := by
    calc
      m2 ≤ m4 := hm2_le_m4
      _ ≤ (10000 * k2) * m4 := by
        nlinarith [hScaleGeOne, show 0 ≤ m4 by positivity]
      _ = 10000 * k2 * m4 := by ring
  have hStep2 :
      m2 * Real.exp (-((k : Error) / (80000 * m2))) ≤
        10000 * k2 * m4 * Real.exp (-((k : Error) / (80000 * m2))) := by
    have hExpNN : 0 ≤ Real.exp (-((k : Error) / (80000 * m2))) := Real.exp_nonneg _
    exact mul_le_mul_of_nonneg_right hm2_le_10k2m4 hExpNN
  have hExpand : m2 * (ν + Real.exp (-((k : Error) / (80000 * m2)))) =
      m2 * ν + m2 * Real.exp (-((k : Error) / (80000 * m2))) := by ring
  rw [hExpand]
  calc
    m2 * ν + m2 * Real.exp (-((k : Error) / (80000 * m2)))
        ≤ 10000 * k2 * m4 *
              (Real.rpow eps (1 / (1024 : Error)) +
                Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) +
            10000 * k2 * m4 * Real.exp (-((k : Error) / (80000 * m2))) := by
          nlinarith [hStep1, hStep2]
    _ = 10000 * k2 * m4 *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) +
            Real.exp (-((k : Error) / (80000 * m2)))) := by ring

/-- **Paper lines 189–193.** The paper's bound for `σ` is absorbed by
`10000 · k² · m⁴ · mainFormalEnvelope`. -/
theorem sigma_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeSigma params k ν ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps := by
  have hTight := cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hEnv : stepEnvelope params k eps (1024 : Error) (80000 : Error) ≤
      mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (1024 : Error)) (N := (80000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hCoeffNN : 0 ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  calc
    cascadeSigma params k ν
      ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          stepEnvelope params k eps (1024 : Error) (80000 : Error) := hTight
    _ ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hEnv hCoeffNN

theorem cascadeSigma_nonneg {params : Parameters} {k : ℕ} {ν : Error}
    (hνNN : 0 ≤ ν) :
    0 ≤ cascadeSigma params k ν := by
  unfold cascadeSigma
  positivity

theorem cascadeZeta1_nonneg {params : Parameters} {k : ℕ} {eps ν : Error}
    (h : CascadeHypotheses params k eps) (hνNN : 0 ≤ ν) :
    0 ≤ cascadeZeta1 params eps (cascadeSigma params k ν) := by
  have hσNN := cascadeSigma_nonneg (params := params) (k := k) (ν := ν) hνNN
  unfold cascadeZeta1
  positivity [hσNN, h.hepsNN, h.dqNN]

theorem cascadeZeta1_bound_special {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hkm1 : k = 1 ∧ params.m = 1) :
    cascadeZeta1 params eps (cascadeSigma params k ν) ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  rcases hkm1 with ⟨rfl, hm1⟩
  have hm_cast : (params.m : Error) = 1 := by exact_mod_cast hm1
  set a : Error := Real.rpow eps (1 / (2048 : Error))
  set b : Error := Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error))
  set c : Error := Real.exp (-(1 : Error) / (160000 : Error))
  have heps1024 : Real.rpow eps (1 / (1024 : Error)) ≤ a := by
    simpa [a] using rpow_le_of_denom_le h.hepsNN h.hepsOne (n₁ := (1024 : Error))
      (n₂ := (2048 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
  have hdq1024 : Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) ≤ b := by
    simpa [b] using rpow_le_of_denom_le h.dqNN h.dqLeOne (n₁ := (1024 : Error))
      (n₂ := (2048 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
  have hνab : ν ≤ 10000 * (a + b) := by
    calc
      ν ≤ 10000 * (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
            simpa [hm_cast] using hν
      _ ≤ 10000 * (a + b) := by nlinarith [heps1024, hdq1024]
  have hExp80000_le_c :
      Real.exp (-((1 : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤ c := by
    calc
      Real.exp (-((1 : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))
          = Real.exp (-(1 : Error) / (80000 : Error)) := by norm_num [hm_cast]
      _ ≤ Real.exp (-(1 : Error) / (160000 : Error)) := by
            exact Real.exp_le_exp.mpr (by norm_num)
      _ = c := by rfl
  have hσab : cascadeSigma params 1 ν ≤ 10000 * (a + b) + c := by
    have htmp : ν + Real.exp (-((1 : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
        10000 * (a + b) + c := by
      nlinarith [hνab, hExp80000_le_c]
    simpa [cascadeSigma, hm_cast] using htmp
  have ha_le_one : a ≤ 1 := by
    unfold a
    exact Real.rpow_le_one h.hepsNN h.hepsOne (by positivity)
  have hb_le_one : b ≤ 1 := by
    unfold b
    exact Real.rpow_le_one h.dqNN h.dqLeOne (by positivity)
  have hc_le_one : c ≤ 1 := by
    unfold c
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hσ_le_20001 : cascadeSigma params 1 ν ≤ 20001 := by
    nlinarith [hσab, ha_le_one, hb_le_one, hc_le_one]
  have hsqrt_le_401 : 2 * Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) ≤ 401 := by
    have hinside : 3 * eps + 2 * cascadeSigma params 1 ν ≤ 40005 := by
      nlinarith [h.hepsOne, hσ_le_20001]
    have hsqrt : Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) ≤ Real.sqrt (40005 : Error) :=
      Real.sqrt_le_sqrt hinside
    nlinarith [hsqrt, two_sqrt40005_le_401]
  have hdq_le_b : (params.d : Error) / (params.q : Error) ≤ b := by
    exact self_le_rpow_one_div h.dqNN h.dqLeOne (by norm_num)
  have hc_ge_quarter : (1 / 4 : Error) ≤ c := by
    have hexp_neg_one : Real.exp (- (1 : Error)) ≤ c := by
      unfold c
      exact Real.exp_le_exp.mpr (by norm_num)
    have hquarter_lt : (1 / 4 : Error) < Real.exp (- (1 : Error)) := by
      linarith [Real.exp_neg_one_gt_d9]
    exact hquarter_lt.le.trans hexp_neg_one
  have hconst : (401 : Error) ≤ 20202 * c := by
    nlinarith [hc_ge_quarter]
  have htarget :
      2 * cascadeSigma params 1 ν + 2 * Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) +
          (params.d : Error) / (params.q : Error)
        ≤ 20204 * (a + b + c) := by
    have htwoσ : 2 * cascadeSigma params 1 ν ≤ 20000 * (a + b) + 2 * c := by
      nlinarith [hσab]
    calc
      2 * cascadeSigma params 1 ν + 2 * Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) +
          (params.d : Error) / (params.q : Error)
          ≤ (20000 * (a + b) + 2 * c) + 401 + b := by
            nlinarith [htwoσ, hsqrt_le_401, hdq_le_b]
      _ ≤ 20204 * (a + b + c) := by
            nlinarith [hconst,
              show 0 ≤ a by
                unfold a
                exact Real.rpow_nonneg h.hepsNN _,
              show 0 ≤ b by
                unfold b
                exact Real.rpow_nonneg h.dqNN _]
  have hEnv : stepEnvelope params 1 eps (2048 : Error) (160000 : Error) = a + b + c := by
    unfold stepEnvelope a b c
    norm_num [hm_cast]
  simpa [cascadeZeta1, hm_cast, hEnv] using htarget

theorem cascadeZeta1_bound_general {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hkm1 : ¬ (k = 1 ∧ params.m = 1)) :
    cascadeZeta1 params eps (cascadeSigma params k ν) ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m2 : Error := (params.m : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set S : Error := stepEnvelope params k eps (1024 : Error) (80000 : Error)
  set T : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set σ : Error := cascadeSigma params k ν
  have hσtight : σ ≤ 10000 * k2 * m4 * S := by
    simpa [σ, k2, m4, S] using cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hST : S ≤ T := by
    simpa [S, T] using stepEnvelope_le_stepEnvelope (h := h) (n₁ := (1024 : Error))
      (n₂ := (2048 : Error)) (N₁ := (80000 : Error)) (N₂ := (160000 : Error))
      (hn₁Pos := by norm_num) (hn := by norm_num) (hN₁Pos := by norm_num) (hN := by norm_num)
  have hσtoT : σ ≤ 10000 * k2 * m4 * T := by
    calc
      σ ≤ 10000 * k2 * m4 * S := hσtight
      _ ≤ 10000 * k2 * m4 * T := by
        exact mul_le_mul_of_nonneg_left hST (by positivity)
  have htwoσ : 2 * σ ≤ 20000 * k2 * m4 * T := by
    nlinarith [hσtoT]
  have hTNN : 0 ≤ T := by
    simpa [T] using stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hSNN : 0 ≤ S := by
    simpa [S] using stepEnvelope_nonneg (h := h) (n := (1024 : Error)) (N := (80000 : Error))
  have hEpsTerm : Real.rpow eps (1 / (2048 : Error)) ≤ T := by
    unfold T stepEnvelope
    have hdqNN' : 0 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) :=
      Real.rpow_nonneg h.dqNN _
    have hExpNN' :
        0 ≤ Real.exp (-((k : Error) / ((160000 : Error) * ((params.m : Error) ^ (2 : ℕ))))) :=
      Real.exp_nonneg _
    nlinarith
  have hsqrt_eps : Real.sqrt eps ≤ Real.rpow eps (1 / (2048 : Error)) := by
    calc
      Real.sqrt eps = Real.rpow eps (1 / (2 : Error)) := by simpa using (Real.sqrt_eq_rpow eps)
      _ ≤ Real.rpow eps (1 / (2048 : Error)) :=
        rpow_le_of_denom_le h.hepsNN h.hepsOne (n₁ := (2 : Error)) (n₂ := (2048 : Error))
          (hn₁Pos := by norm_num) (hn := by norm_num)
  have hsqrt3eps : Real.sqrt (3 * eps) ≤ 2 * T := by
    calc
      Real.sqrt (3 * eps) = Real.sqrt (3 : Error) * Real.sqrt eps := by
        rw [Real.sqrt_mul (by norm_num)]
      _ ≤ 2 * Real.sqrt eps := by
        exact mul_le_mul_of_nonneg_right sqrt_three_le_two (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.rpow eps (1 / (2048 : Error)) :=
        mul_le_mul_of_nonneg_left hsqrt_eps (by norm_num)
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hEpsTerm (by norm_num)
  have hsqrtScaled : Real.sqrt (20000 * k2 * m4 * S) ≤
      Real.sqrt (20000 : Error) * (k : Error) * m2 * T := by
    simpa [k2, m2, m4, S, T,
      show (2 : Error) * 1024 = 2048 by norm_num,
      show (2 : Error) * 80000 = 160000 by norm_num] using
      sqrt_scaled_stepEnvelope_le (h := h)
        (x := 20000 * k2 * m4 * S) (C := (20000 : Error))
        (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
  have hsqrtScaled142 : Real.sqrt (20000 * k2 * m4 * S) ≤ 142 * (k : Error) * m2 * T := by
    calc
      Real.sqrt (20000 * k2 * m4 * S)
        ≤ Real.sqrt (20000 : Error) * (k : Error) * m2 * T := hsqrtScaled
      _ ≤ 142 * (k : Error) * m2 * T := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_right sqrt20000_le_142
            (show 0 ≤ (k : Error) * m2 * T by positivity [hTNN])
  have hsqrtTmp : Real.sqrt (3 * eps + 2 * σ) ≤
      Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S) := by
    have harg : 3 * eps + 2 * σ ≤ 3 * eps + 20000 * k2 * m4 * S := by
      nlinarith [hσtight, hSNN]
    calc
      Real.sqrt (3 * eps + 2 * σ)
        ≤ Real.sqrt (3 * eps + 20000 * k2 * m4 * S) := Real.sqrt_le_sqrt harg
      _ ≤ Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S) :=
        sqrt_add_le_add_sqrt (by nlinarith [h.hepsNN]) (by positivity [hSNN])
  have hkm2_ge_two : (2 : Error) ≤ (k : Error) * m2 := by
    by_cases hk1 : k = 1
    · have hmNe : params.m ≠ 1 := by
        intro hmEq
        exact hkm1 ⟨hk1, hmEq⟩
      have hmNat2 : 2 ≤ params.m := by
        have hmNat1 : 1 ≤ params.m := by exact_mod_cast h.hm
        omega
      have hm_ge_two : (2 : Error) ≤ (params.m : Error) := by exact_mod_cast hmNat2
      have hm2_ge_two : (2 : Error) ≤ m2 := by
        dsimp [m2]
        nlinarith [hm_ge_two]
      simpa [hk1] using hm2_ge_two
    · have hkNat2 : 2 ≤ k := by
        have hkNat1 : 1 ≤ k := by exact_mod_cast h.hk
        omega
      have hk_ge_two : (2 : Error) ≤ (k : Error) := by exact_mod_cast hkNat2
      nlinarith [hk_ge_two, h.m2_ge_one]
  have hkm2NN : 0 ≤ (k : Error) * m2 := by positivity
  have hkm2_sq : (((k : Error) * m2) ^ (2 : ℕ)) = k2 * m4 := by
    dsimp [k2, m2, m4]
    ring
  have hCoeffDirect : (284 : Error) * ((k : Error) * m2) ≤ 199 * k2 * m4 := by
    have h284 : (284 : Error) ≤ 199 * ((k : Error) * m2) := by
      nlinarith [hkm2_ge_two]
    have hmul := mul_le_mul_of_nonneg_right h284 hkm2NN
    calc
      (284 : Error) * ((k : Error) * m2) ≤ (199 * ((k : Error) * m2)) * ((k : Error) * m2) := by
        simpa [mul_assoc] using hmul
      _ = 199 * (((k : Error) * m2) ^ (2 : ℕ)) := by ring
      _ = 199 * k2 * m4 := by rw [hkm2_sq]; ring
  have hsqrtBig : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ 199 * k2 * m4 * T := by
    have htmp1' : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ 2 * (142 * (k : Error) * m2 * T) :=
      mul_le_mul_of_nonneg_left hsqrtScaled142 (by norm_num : (0 : Error) ≤ 2)
    have htmp1b : 2 * (142 * (k : Error) * m2 * T) = (284 * ((k : Error) * m2)) * T := by
      ring
    have htmp1 : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ (284 * ((k : Error) * m2)) * T := by
      exact htmp1'.trans_eq htmp1b
    have htmp2 : (284 * ((k : Error) * m2)) * T ≤ (199 * k2 * m4) * T :=
      mul_le_mul_of_nonneg_right hCoeffDirect hTNN
    have htmp3 : (199 * k2 * m4) * T = 199 * k2 * m4 * T := by ring
    exact htmp1.trans <| htmp2.trans_eq htmp3
  have hsqrt3Term : 2 * Real.sqrt (3 * eps) ≤ 4 * T := by
    have htmp : 2 * Real.sqrt (3 * eps) ≤ 2 * (2 * T) :=
      mul_le_mul_of_nonneg_left hsqrt3eps (by norm_num : (0 : Error) ≤ 2)
    have hEq : 2 * (2 * T) = 4 * T := by ring
    exact htmp.trans_eq hEq
  have hsqrtTerm : 2 * Real.sqrt (3 * eps + 2 * σ) ≤ 4 * T + 199 * k2 * m4 * T := by
    have hsqrtTmp2' : 2 * Real.sqrt (3 * eps + 2 * σ) ≤ 2 *
        (Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S)) :=
      mul_le_mul_of_nonneg_left hsqrtTmp (by norm_num : (0 : Error) ≤ 2)
    have hEq : 2 *
        (Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S)) =
        2 * Real.sqrt (3 * eps) + 2 * Real.sqrt (20000 * k2 * m4 * S) := by ring
    have hsqrtTmp2 : 2 * Real.sqrt (3 * eps + 2 * σ) ≤
        2 * Real.sqrt (3 * eps) + 2 * Real.sqrt (20000 * k2 * m4 * S) := by
      exact hsqrtTmp2'.trans_eq hEq
    exact hsqrtTmp2.trans (add_le_add hsqrt3Term hsqrtBig)
  have hmdq_to_k2m4T :
      (params.m : Error) * ((params.d : Error) / (params.q : Error)) ≤ k2 * m4 * T := by
    dsimp [k2, m4, T]
    exact mdq_le_k2m4_stepEnvelope2048 (h := h)
  have hfourT : 4 * T ≤ 4 * (k2 * m4) * T := by
    dsimp [k2, m4]
    exact four_mul_le_k2m4_mul (h := h) hTNN
  rw [show cascadeZeta1 params eps σ =
      2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
        (params.m : Error) * (params.d : Error) / (params.q : Error) by rfl]
  have hmdq_to_k2m4T' :
      (params.m : Error) * (params.d : Error) / (params.q : Error) ≤ k2 * m4 * T := by
    calc
      (params.m : Error) * (params.d : Error) / (params.q : Error)
        = (params.m : Error) * ((params.d : Error) / (params.q : Error)) := by ring
      _ ≤ k2 * m4 * T := hmdq_to_k2m4T
  calc
    2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
        (params.m : Error) * (params.d : Error) / (params.q : Error)
      ≤ (20000 * k2 * m4 * T + (4 * T + 199 * k2 * m4 * T)) + k2 * m4 * T :=
          add_le_add (add_le_add htwoσ hsqrtTerm) hmdq_to_k2m4T'
    _ = 20000 * k2 * m4 * T + 4 * T + 199 * k2 * m4 * T + k2 * m4 * T := by ring
    _ = (20000 * k2 * m4 * T + 4 * T) + (199 * k2 * m4 * T + k2 * m4 * T) := by ring
    _ ≤ (20000 * k2 * m4 * T + 4 * (k2 * m4) * T) +
          (199 * k2 * m4 * T + k2 * m4 * T) :=
        add_le_add (add_le_add le_rfl hfourT) le_rfl
    _ = 20204 * k2 * m4 * T := by ring

theorem cascadeZeta1_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta1 params eps (cascadeSigma params k ν) ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  by_cases hkm1 : k = 1 ∧ params.m = 1
  · exact cascadeZeta1_bound_special (h := h) (ν := ν) hν hkm1
  · exact cascadeZeta1_bound_general (h := h) (ν := ν) hν hkm1

/-- **Paper lines 196–201.** The concrete `ζ₁` built from `σ = cascadeSigma params k ν`
is absorbed by `mainFormalError`. -/
theorem zeta1_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν) :
    cascadeZeta1 params eps σ ≤ mainFormalError params k eps := by
  rw [hσEq, mainFormalError_eq_envelope]
  have hζ₁ := cascadeZeta1_bound (h := h) (ν := ν) hν
  have hTightEnvelope :
      stepEnvelope params k eps (2048 : Error) (160000 : Error) ≤ mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (2048 : Error)) (N := (160000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hCoeffNN : 0 ≤ 20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  refine hζ₁.trans ?_
  calc
    20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error)
      ≤ 20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hTightEnvelope hCoeffNN
    _ = (20204 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps := by ring
    _ ≤ (100000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (20204 : Error) ≤ 100000) hk2m4NN) hENN
    _ = 100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps := by ring

end Test

end MIPStarRE.LDT
