import MIPStarRE.LDT.Test.ErrorCascade.CascadeBounds.SigmaZeta1

/-!
# Error cascade — bounds for `ζ₂` and `ζ₃`

This module contains the middle cascade estimates used in Step 8 of the main
inductive step: the absorbing bounds for `ζ₂` and `ζ₃` obtained from the
`σ` and `ζ₁` estimates.

## References

* `references/ldt-paper/inductive_step.tex`, lines 205--217 and 230.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

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

end Test

end MIPStarRE.LDT
