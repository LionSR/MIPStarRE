import MIPStarRE.LDT.Test.ErrorCascade.Definitions
import MIPStarRE.LDT.Test.ErrorCascade.EnvelopeBounds

/-!
# Error cascade — bounds for `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄` and the main consolidator

This module proves the tight and absorbing bounds for each cascade variable
`σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄`, and assembles them into
`errorCascade_le_mainFormalError`,
the top-level error-cascade consolidator used by `mainFormalError` (Step 8).

Each cascade-step lemma has three components:

* The **tight cascade bound** (`cascadeSigma_tight_bound`, `cascadeZeta1_bound`, …),
  deriving the native estimate directly from the cascade definition.
* The **absorbing bound** (`sigma_bound`, `zeta1_bound`, …), coarsening the
  tight estimate to the final `mainFormalEnvelope` envelope.
* Where appropriate, nonnegativity lemmas (`cascadeSigma_nonneg`,
  `cascadeZeta1_nonneg`).

The consolidator `errorCascade_le_mainFormalError` packages all five bounds
against `mainFormalError` itself (with `ζ₃/2 ≤ mainFormalError`, as stated
in paper line 230).

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/


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

theorem cascadeZeta2_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta2 (cascadeZeta1 params eps (cascadeSigma params k ν)) ≤
      2568 * (k : Error) * (params.m : Error) *
        stepEnvelope params k eps (16384 : Error) (1280000 : Error) := by
  set Z1 : Error := cascadeZeta1 params eps (cascadeSigma params k ν)
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set E2048 : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set E8192 : Error := stepEnvelope params k eps (8192 : Error) (640000 : Error)
  set E16384 : Error := stepEnvelope params k eps (16384 : Error) (1280000 : Error)
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [Z1, k2, m4, E2048] using cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1NN : 0 ≤ Z1 := by
    simpa [Z1] using cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hE8192 : E8192 ≤ E16384 := by
    simpa [E8192, E16384] using stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (8192 : Error)) (n₂ := (16384 : Error)) (N₁ := (640000 : Error))
      (N₂ := (1280000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hQuarterRoot : Real.rpow Z1 (1 / (4 : Error)) ≤
      12 * (k : Error) * (params.m : Error) * E8192 := by
    exact rpow_Z1_factor_le (params := params) (k := k)
      (hZ1NN := hZ1NN) (hZ1 := hZ1) (hrNN := by positivity)
      (hk2NN := by positivity) (hm4NN := by positivity) (hE2048NN := hE2048NN)
      (hA := by simpa using rpow20204_quarter_le_12)
      (hB := by simpa [k2] using k2_rpow_quarter_le (h := h))
      (hC := by simpa [m4] using (m4_rpow_quarter_eq (params := params)).le)
      (hD := by simpa [E2048, E8192] using stepEnvelope_rpow_quarter_le (h := h))
  have hQuarterRoot' : Real.rpow Z1 (1 / (4 : Error)) ≤
      12 * (k : Error) * (params.m : Error) * E16384 := by
    calc
      Real.rpow Z1 (1 / (4 : Error)) ≤ 12 * (k : Error) * (params.m : Error) * E8192 := hQuarterRoot
      _ ≤ 12 * (k : Error) * (params.m : Error) * E16384 :=
        mul_le_mul_of_nonneg_left hE8192 (by positivity)
  have hEighthRoot : Real.rpow Z1 (1 / (8 : Error)) ≤
      4 * (k : Error) * (params.m : Error) * E16384 := by
    exact rpow_Z1_factor_le (params := params) (k := k)
      (hZ1NN := hZ1NN) (hZ1 := hZ1) (hrNN := by positivity)
      (hk2NN := by positivity) (hm4NN := by positivity) (hE2048NN := hE2048NN)
      (hA := by simpa using rpow20204_eighth_le_4)
      (hB := by simpa [k2] using k2_rpow_eighth_le (h := h))
      (hC := by simpa [m4] using m4_rpow_eighth_le (h := h))
      (hD := by simpa [E2048, E16384] using stepEnvelope_rpow_eighth_le (h := h))
  unfold cascadeZeta2
  calc
    200 * Real.rpow Z1 (1 / (4 : Error)) + 42 * Real.rpow Z1 (1 / (8 : Error))
      ≤ 200 * (12 * (k : Error) * (params.m : Error) * E16384) +
          42 * (4 * (k : Error) * (params.m : Error) * E16384) := by
            nlinarith [hQuarterRoot', hEighthRoot]
    _ = 2568 * (k : Error) * (params.m : Error) * E16384 := by ring

/-- **Paper lines 205–212, with the formal `ζ₂` widening.** The concrete `ζ₂`
built from `ζ₁ = cascadeZeta1 params eps σ` and `σ = cascadeSigma params k ν`
is absorbed by `mainFormalError`. -/
theorem zeta2_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ) :
    cascadeZeta2 ζ₁ ≤ mainFormalError params k eps := by
  rw [hζ₁Eq, hσEq, mainFormalError_eq_envelope]
  have hζ₂ := cascadeZeta2_bound (h := h) (ν := ν) hνNN hν
  have hTightEnvelope :
      stepEnvelope params k eps (16384 : Error) (1280000 : Error) ≤
        mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hm_nn : 0 ≤ (params.m : Error) := by linarith [h.hm]
  have hk_le : (k : Error) ≤ ((k : Error) ^ (2 : ℕ)) := h.k_le_k2
  have hm_le : (params.m : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := h.m_le_m4
  have hkm_le : (k : Error) * (params.m : Error) ≤
      ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) :=
    mul_le_mul hk_le hm_le hm_nn (by positivity)
  have hCoeffNN : 0 ≤ 2568 * (k : Error) * (params.m : Error) := by positivity
  have hk2m4_nn : (0 : Error) ≤
      ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  refine hζ₂.trans ?_
  calc
    2568 * (k : Error) * (params.m : Error) *
        stepEnvelope params k eps (16384 : Error) (1280000 : Error)
      ≤ 2568 * (k : Error) * (params.m : Error) * mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hTightEnvelope hCoeffNN
    _ = (2568 * ((k : Error) * (params.m : Error))) *
          mainFormalEnvelope params k eps := by ring
    _ ≤ (2568 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkm_le (by norm_num)) hENN
    _ ≤ (100000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (2568 : Error) ≤ 100000) hk2m4_nn) hENN
    _ = 100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps := by ring

theorem cascadeZeta3_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta3
        (cascadeZeta1 params eps (cascadeSigma params k ν))
        (cascadeZeta2 (cascadeZeta1 params eps (cascadeSigma params k ν))) ≤
      150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (16384 : Error) (1280000 : Error) := by
  set Z1 : Error := cascadeZeta1 params eps (cascadeSigma params k ν)
  set Z2 : Error := cascadeZeta2 Z1
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set E2048 : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set E16384 : Error := stepEnvelope params k eps (16384 : Error) (1280000 : Error)
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [Z1, k2, m4, E2048] using cascadeZeta1_bound (h := h) (ν := ν) hν
  have hE2048 : E2048 ≤ E16384 := by
    simpa [E2048, E16384] using stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (2048 : Error)) (n₂ := (16384 : Error)) (N₁ := (160000 : Error))
      (N₂ := (1280000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hZ1' : Z1 ≤ 20204 * k2 * m4 * E16384 := by
    calc
      Z1 ≤ 20204 * k2 * m4 * E2048 := hZ1
      _ ≤ 20204 * k2 * m4 * E16384 :=
        mul_le_mul_of_nonneg_left hE2048 (by positivity)
  have hZ2 : Z2 ≤ 2568 * (k : Error) * (params.m : Error) * E16384 := by
    simpa [Z1, Z2, E16384] using cascadeZeta2_bound (h := h) (ν := ν) hνNN hν
  have hE16384NN : 0 ≤ E16384 := by
    simpa [E16384] using
      stepEnvelope_nonneg (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
  have hZ2' : Z2 ≤ 2568 * k2 * m4 * E16384 := by
    have hkm_le : (k : Error) * (params.m : Error) ≤ k2 * m4 := by
      calc
        (k : Error) * (params.m : Error)
          ≤ (k : Error) * ((params.m : Error) ^ (4 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left h.m_le_m4 (by positivity)
        _ ≤ k2 * m4 := by
            exact mul_le_mul_of_nonneg_right h.k_le_k2 (by positivity)
    have hScale : 2568 * ((k : Error) * (params.m : Error)) ≤ 2568 * (k2 * m4) := by
      exact mul_le_mul_of_nonneg_left hkm_le (by norm_num : (0 : Error) ≤ 2568)
    have hScale' : 2568 * (k : Error) * (params.m : Error) ≤ 2568 * (k2 * m4) := by
      simpa [mul_assoc] using hScale
    calc
      Z2 ≤ 2568 * (k : Error) * (params.m : Error) * E16384 := hZ2
      _ ≤ (2568 * (k2 * m4)) * E16384 := by
        exact mul_le_mul_of_nonneg_right hScale' hE16384NN
      _ = 2568 * k2 * m4 * E16384 := by ring
  have hSum : 6 * Z1 + 6 * Z2 ≤ 150000 * k2 * m4 * E16384 := by
    have hCoeff : (136632 : Error) * k2 * m4 ≤ 150000 * k2 * m4 := by
      have hk2m4NN : 0 ≤ k2 * m4 := by positivity
      nlinarith [hk2m4NN]
    calc
      6 * Z1 + 6 * Z2 ≤ 6 * (20204 * k2 * m4 * E16384) + 6 * (2568 * k2 * m4 * E16384) := by
        nlinarith [hZ1', hZ2']
      _ = (136632 : Error) * k2 * m4 * E16384 := by ring
      _ ≤ (150000 * k2 * m4) * E16384 := by
        exact mul_le_mul_of_nonneg_right hCoeff hE16384NN
      _ = 150000 * k2 * m4 * E16384 := by ring
  simpa [cascadeZeta3, Z1, Z2] using hSum

/-- **Paper lines 214–217 and 230.** The concrete `ζ₃` built from the cascade
chain is rewritten as `ζ₃ ≤ 2 · mainFormalError`. -/
theorem zeta3_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁) :
    cascadeZeta3 ζ₁ ζ₂ ≤ 2 * mainFormalError params k eps := by
  rw [hζ₂Eq, hζ₁Eq, hσEq, mainFormalError_eq_envelope]
  have hζ₃ := cascadeZeta3_bound (h := h) (ν := ν) hνNN hν
  have hTightEnvelope :
      stepEnvelope params k eps (16384 : Error) (1280000 : Error) ≤
        mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hCoeffNN : 0 ≤ 150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  refine hζ₃.trans ?_
  calc
    150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (16384 : Error) (1280000 : Error)
      ≤ 150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hTightEnvelope hCoeffNN
    _ = (150000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps := by ring
    _ ≤ (200000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (150000 : Error) ≤ 200000) hk2m4NN) hENN
    _ = 2 *
          (100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
            mainFormalEnvelope params k eps) := by ring

theorem cascadeZeta4_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta4 (cascadeSigma params k ν)
        (cascadeZeta1 params eps (cascadeSigma params k ν))
        (cascadeZeta3
          (cascadeZeta1 params eps (cascadeSigma params k ν))
          (cascadeZeta2 (cascadeZeta1 params eps (cascadeSigma params k ν)))) ≤
      40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (32768 : Error) (2560000 : Error) := by
  set σ : Error := cascadeSigma params k ν
  set Z1 : Error := cascadeZeta1 params eps σ
  set Z2 : Error := cascadeZeta2 Z1
  set Z3 : Error := cascadeZeta3 Z1 Z2
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m2 : Error := (params.m : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set E1024 : Error := stepEnvelope params k eps (1024 : Error) (80000 : Error)
  set E2048 : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set E4096 : Error := stepEnvelope params k eps (4096 : Error) (320000 : Error)
  set E16384 : Error := stepEnvelope params k eps (16384 : Error) (1280000 : Error)
  set E32768 : Error := stepEnvelope params k eps (32768 : Error) (2560000 : Error)
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hE4096NN : 0 ≤ E4096 := by
    simpa [E4096] using stepEnvelope_nonneg (h := h) (n := (4096 : Error)) (N := (320000 : Error))
  have hE16384NN : 0 ≤ E16384 := by
    simpa [E16384] using
      stepEnvelope_nonneg (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
  have hE32768NN : 0 ≤ E32768 := by
    simpa [E32768] using
      stepEnvelope_nonneg (h := h) (n := (32768 : Error)) (N := (2560000 : Error))
  have hσ : σ ≤ 10000 * k2 * m4 * E1024 := by
    simpa [σ, k2, m4, E1024] using cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hσ' : σ ≤ 10000 * k2 * m4 * E32768 := by
    calc
      σ ≤ 10000 * k2 * m4 * E1024 := hσ
      _ ≤ 10000 * k2 * m4 * E32768 := by
        have hMono : E1024 ≤ E32768 := by
          simpa [E1024, E32768] using stepEnvelope_le_stepEnvelope (h := h)
            (n₁ := (1024 : Error)) (n₂ := (32768 : Error)) (N₁ := (80000 : Error))
            (N₂ := (2560000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
            (hN₁Pos := by norm_num) (hN := by norm_num)
        exact mul_le_mul_of_nonneg_left hMono (by positivity)
  have hZ1_raw := cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [σ, Z1, k2, m4, E2048] using hZ1_raw
  have hZ3_raw := cascadeZeta3_bound (h := h) (ν := ν) hνNN hν
  have hZ3 : Z3 ≤ 150000 * k2 * m4 * E16384 := by
    simpa [σ, Z1, Z2, Z3, k2, m4, E16384] using hZ3_raw
  have hZ1NN : 0 ≤ Z1 := by
    simpa [σ, Z1] using cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hZ2NN : 0 ≤ Z2 := by
    unfold Z2 cascadeZeta2
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hZ1NN _)
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hZ1NN _)
  have hZ3NN : 0 ≤ Z3 := by
    unfold Z3 cascadeZeta3
    exact add_nonneg (mul_nonneg (by norm_num) hZ1NN) (mul_nonneg (by norm_num) hZ2NN)
  have hX1NN : 0 ≤ 20204 * k2 * m4 * E2048 := by
    positivity [hE2048NN]
  have hsqrtZ1 : Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : Error) * m2 * E4096 := by
    calc
      Real.sqrt (20204 * k2 * m4 * E2048)
        ≤ Real.sqrt (20204 : Error) * (k : Error) * m2 * E4096 := by
          simpa [k2, m2, m4, E2048, E4096,
            show (2 : Error) * 2048 = 4096 by norm_num,
            show (2 : Error) * 160000 = 320000 by norm_num] using
            sqrt_scaled_stepEnvelope_le (h := h)
              (x := 20204 * k2 * m4 * E2048) (C := (20204 : Error))
              (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
      _ ≤ 143 * (k : Error) * m2 * E4096 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right sqrt20204_le_143
              (show 0 ≤ (k : Error) * m2 * E4096 by positivity [hE4096NN])
  have hE4096 : E4096 ≤ E32768 := by
    simpa [E4096, E32768] using stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (4096 : Error)) (n₂ := (32768 : Error)) (N₁ := (320000 : Error))
      (N₂ := (2560000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hsqrtZ1' : Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : Error) * m2 * E32768 := by
    calc
      Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : Error) * m2 * E4096 := hsqrtZ1
      _ ≤ 143 * (k : Error) * m2 * E32768 :=
        mul_le_mul_of_nonneg_left hE4096 (by positivity)
  have hX3NN : 0 ≤ 150000 * k2 * m4 * E16384 := by
    positivity [hE16384NN]
  have hsqrtZ3 : Real.sqrt (150000 * k2 * m4 * E16384) ≤ 388 * (k : Error) * m2 * E32768 := by
    calc
      Real.sqrt (150000 * k2 * m4 * E16384)
        ≤ Real.sqrt (150000 : Error) * (k : Error) * m2 * E32768 := by
          simpa [k2, m2, m4, E16384, E32768,
            show (2 : Error) * 16384 = 32768 by norm_num,
            show (2 : Error) * 1280000 = 2560000 by norm_num] using
            sqrt_scaled_stepEnvelope_le (h := h)
              (x := 150000 * k2 * m4 * E16384) (C := (150000 : Error))
              (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
      _ ≤ 388 * (k : Error) * m2 * E32768 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right sqrt150000_le_388
              (show 0 ≤ (k : Error) * m2 * E32768 by positivity [hE32768NN])
  have hsqrtTerm : 2 * Real.sqrt (Z1 + Z3 / 2) ≤ 1062 * k2 * m4 * E32768 := by
    have hZ3half : Z3 / 2 ≤ 150000 * k2 * m4 * E16384 := by
      nlinarith [hZ3, hZ3NN]
    have hinside : Z1 + Z3 / 2 ≤ 20204 * k2 * m4 * E2048 + 150000 * k2 * m4 * E16384 := by
      linarith [hZ1, hZ3half]
    have hsqrtSplit : Real.sqrt (Z1 + Z3 / 2) ≤
        Real.sqrt (20204 * k2 * m4 * E2048) + Real.sqrt (150000 * k2 * m4 * E16384) := by
      calc
        Real.sqrt (Z1 + Z3 / 2)
          ≤ Real.sqrt (20204 * k2 * m4 * E2048 + 150000 * k2 * m4 * E16384) :=
            Real.sqrt_le_sqrt hinside
        _ ≤ Real.sqrt (20204 * k2 * m4 * E2048) + Real.sqrt (150000 * k2 * m4 * E16384) :=
            sqrt_add_le_add_sqrt (by positivity [hE2048NN]) (by positivity [hE16384NN])
    have hkm2 : (k : Error) * m2 ≤ k2 * m4 := by simpa [k2, m2, m4] using h.km2_le_k2m4
    have hkm2z1 : 143 * (k : Error) * m2 * E32768 ≤ 143 * k2 * m4 * E32768 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hkm2 (show 0 ≤ 143 * E32768 by positivity [hE32768NN])
    have hkm2z3 : 388 * (k : Error) * m2 * E32768 ≤ 388 * k2 * m4 * E32768 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hkm2 (show 0 ≤ 388 * E32768 by positivity [hE32768NN])
    nlinarith [hsqrtSplit, hsqrtZ1', hsqrtZ3, hkm2z1, hkm2z3]
  unfold cascadeZeta4
  calc
    2 * σ + 2 * Real.sqrt (Z1 + Z3 / 2)
      ≤ 20000 * k2 * m4 * E32768 + 1062 * k2 * m4 * E32768 := by
        nlinarith [hσ', hsqrtTerm]
    _ ≤ 40000 * k2 * m4 * E32768 := by
        nlinarith [show 0 ≤ k2 * m4 * E32768 by positivity]

/-- **Paper lines 220–228.** The concrete `ζ₄` built from the cascade chain is
absorbed by `mainFormalError`. -/
theorem zeta4_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = cascadeZeta3 ζ₁ ζ₂) :
    cascadeZeta4 σ ζ₁ ζ₃ ≤ mainFormalError params k eps := by
  rw [hζ₃Eq, hζ₂Eq, hζ₁Eq, hσEq, mainFormalError_eq_envelope]
  have hζ₄ := cascadeZeta4_bound (h := h) (ν := ν) hνNN hν
  have hTightEnvelope :
      stepEnvelope params k eps (32768 : Error) (2560000 : Error) ≤
        mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (32768 : Error)) (N := (2560000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hCoeffNN : 0 ≤ 40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  refine hζ₄.trans ?_
  calc
    40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (32768 : Error) (2560000 : Error)
      ≤ 40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hTightEnvelope hCoeffNN
    _ = (40000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps := by ring
    _ ≤ (100000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (40000 : Error) ≤ 100000) hk2m4NN) hENN
    _ = 100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps := by ring

/-- **Paper lines 230–234.** Packages the five cascade bounds into the tuple
used by `mainFormal`. -/
theorem errorCascade_le_mainFormalError {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : Error}
    (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = cascadeZeta3 ζ₁ ζ₂) :
    σ ≤ mainFormalError params k eps ∧
    ζ₁ ≤ mainFormalError params k eps ∧
    ζ₂ ≤ mainFormalError params k eps ∧
    ζ₃ ≤ 2 * mainFormalError params k eps ∧
    cascadeZeta4 σ ζ₁ ζ₃ ≤ mainFormalError params k eps := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσEq, mainFormalError_eq_envelope]
    have hENN := h.envelope_nonneg
    have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
      positivity
    nlinarith [sigma_bound h hν, hENN, hk2m4NN]
  · rw [hζ₁Eq]
    exact zeta1_bound h hν hσEq
  · rw [hζ₂Eq]
    exact zeta2_bound h hνNN hν hσEq hζ₁Eq
  · rw [hζ₃Eq]
    exact zeta3_bound h hνNN hν hσEq hζ₁Eq hζ₂Eq
  · exact zeta4_bound h hνNN hν hσEq hζ₁Eq hζ₂Eq hζ₃Eq


end Test

end MIPStarRE.LDT
