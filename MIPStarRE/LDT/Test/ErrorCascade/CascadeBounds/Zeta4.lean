import MIPStarRE.LDT.Test.ErrorCascade.CascadeBounds.Zeta2Zeta3

/-!
# Error cascade — bound for `ζ₄`

This module contains the `ζ₄` cascade estimate used in Step 8 of the main
inductive step and its absorption into `mainFormalError`.

## References

* `references/ldt-paper/inductive_step.tex`, lines 220--228.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

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

/-- The repaired `ζ₄` obtained by substituting the checked local line-169 repair
into the final point-transport triangle is also absorbed by `mainFormalError`. -/
theorem zeta4Repaired_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = cascadeZeta3 ζ₁ ζ₂) :
    cascadeZeta4Repaired σ ζ₁ ζ₃ ≤ mainFormalError params k eps := by
  rw [hζ₃Eq, hζ₂Eq, hζ₁Eq, hσEq, mainFormalError_eq_envelope]
  set σ0 : Error := cascadeSigma params k ν
  set Z1 : Error := cascadeZeta1 params eps σ0
  set Z2 : Error := cascadeZeta2 Z1
  set Z3 : Error := cascadeZeta3 Z1 Z2
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m2 : Error := (params.m : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set E1024 : Error := stepEnvelope params k eps (1024 : Error) (80000 : Error)
  set E2048 : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set E16384 : Error := stepEnvelope params k eps (16384 : Error) (1280000 : Error)
  set E32768 : Error := stepEnvelope params k eps (32768 : Error) (2560000 : Error)
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using
      stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hE16384NN : 0 ≤ E16384 := by
    simpa [E16384] using
      stepEnvelope_nonneg (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
  have hE32768NN : 0 ≤ E32768 := by
    simpa [E32768] using
      stepEnvelope_nonneg (h := h) (n := (32768 : Error)) (N := (2560000 : Error))
  have hσ : σ0 ≤ 10000 * k2 * m4 * E1024 := by
    simpa [σ0, k2, m4, E1024] using cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hσ' : σ0 ≤ 10000 * k2 * m4 * E32768 := by
    calc
      σ0 ≤ 10000 * k2 * m4 * E1024 := hσ
      _ ≤ 10000 * k2 * m4 * E32768 := by
        have hMono : E1024 ≤ E32768 := by
          simpa [E1024, E32768] using stepEnvelope_le_stepEnvelope (h := h)
            (n₁ := (1024 : Error)) (n₂ := (32768 : Error)) (N₁ := (80000 : Error))
            (N₂ := (2560000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
            (hN₁Pos := by norm_num) (hN := by norm_num)
        exact mul_le_mul_of_nonneg_left hMono (by positivity)
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [σ0, Z1, k2, m4, E2048] using cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1NN : 0 ≤ Z1 := by
    simpa [σ0, Z1] using cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hZ3 : Z3 ≤ 150000 * k2 * m4 * E16384 := by
    simpa [σ0, Z1, Z2, Z3, k2, m4, E16384] using cascadeZeta3_bound (h := h) (ν := ν) hνNN hν
  have hZ1Eighth : Real.rpow Z1 (1 / (8 : Error)) ≤
      4 * (k : Error) * (params.m : Error) * E16384 := by
    exact rpow_Z1_factor_le (params := params) (k := k)
      (hZ1NN := hZ1NN) (hZ1 := hZ1) (hrNN := by positivity)
      (hk2NN := by positivity) (hm4NN := by positivity) (hE2048NN := hE2048NN)
      (hA := by simpa using rpow20204_eighth_le_4)
      (hB := by simpa [k2] using k2_rpow_eighth_le (h := h))
      (hC := by simpa [m4] using m4_rpow_eighth_le (h := h))
      (hD := by simpa [E2048, E16384] using stepEnvelope_rpow_eighth_le (h := h))
  have hZ1to16384 : Z1 ≤ 20204 * k2 * m4 * E16384 := by
    have hE2048_le : E2048 ≤ E16384 := by
      simpa [E2048, E16384] using stepEnvelope_le_stepEnvelope (h := h)
        (n₁ := (2048 : Error)) (n₂ := (16384 : Error)) (N₁ := (160000 : Error))
        (N₂ := (1280000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
        (hN₁Pos := by norm_num) (hN := by norm_num)
    exact hZ1.trans <| mul_le_mul_of_nonneg_left hE2048_le (by positivity)
  have hRepairTerm : 10 * Real.rpow Z1 (1 / (8 : Error)) ≤ 40 * k2 * m4 * E16384 := by
    have hkm : (k : Error) * (params.m : Error) ≤ k2 * m4 := by
      calc
        (k : Error) * (params.m : Error)
          ≤ (k : Error) * ((params.m : Error) ^ (4 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left h.m_le_m4 (by positivity)
        _ ≤ k2 * m4 := by
              exact mul_le_mul_of_nonneg_right h.k_le_k2 (by positivity)
    calc
      10 * Real.rpow Z1 (1 / (8 : Error))
          ≤ 10 * (4 * (k : Error) * (params.m : Error) * E16384) := by
              gcongr
      _ = 40 * ((k : Error) * (params.m : Error)) * E16384 := by ring
      _ ≤ 40 * (k2 * m4) * E16384 := by
        have : 40 * ((k : Error) * (params.m : Error)) ≤ 40 * (k2 * m4) := by
          exact mul_le_mul_of_nonneg_left hkm (by norm_num : (0 : Error) ≤ 40)
        exact mul_le_mul_of_nonneg_right this hE16384NN
      _ = 40 * k2 * m4 * E16384 := by ring
  have hRepair : cascadeLine169RepairError Z1 ≤ 20244 * k2 * m4 * E16384 := by
    unfold cascadeLine169RepairError
    linarith
  have hsqrtTerm : 2 * Real.sqrt (cascadeLine169RepairError Z1 + Z3 / 2)
      ≤ 826 * k2 * m4 * E32768 := by
    have hZ3half : Z3 / 2 ≤ 150000 * k2 * m4 * E16384 := by
      nlinarith [hZ3]
    have hinside : cascadeLine169RepairError Z1 + Z3 / 2 ≤
        170244 * k2 * m4 * E16384 := by
      linarith [hRepair, hZ3half]
    have hsqrtBound : Real.sqrt (170244 * k2 * m4 * E16384) ≤
        413 * (k : Error) * m2 * E32768 := by
      calc
        Real.sqrt (170244 * k2 * m4 * E16384)
            ≤ Real.sqrt (170244 : Error) * (k : Error) * m2 * E32768 := by
              simpa [k2, m2, m4, E16384, E32768,
                show (2 : Error) * 16384 = 32768 by norm_num,
                show (2 : Error) * 1280000 = 2560000 by norm_num] using
                sqrt_scaled_stepEnvelope_le (h := h)
                  (x := 170244 * k2 * m4 * E16384) (C := (170244 : Error))
                  (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
        _ ≤ 413 * (k : Error) * m2 * E32768 := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_right sqrt170244_le_413
                (show 0 ≤ (k : Error) * m2 * E32768 by positivity [hE32768NN])
    have hkm2 : (k : Error) * m2 ≤ k2 * m4 := by simpa [k2, m2, m4] using h.km2_le_k2m4
    have hkm2z : 413 * (k : Error) * m2 * E32768 ≤ 413 * k2 * m4 * E32768 := by
      have : 413 * ((k : Error) * m2) ≤ 413 * (k2 * m4) := by
        exact mul_le_mul_of_nonneg_left hkm2 (by norm_num : (0 : Error) ≤ 413)
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right this hE32768NN
    have hsqrtInside : Real.sqrt (cascadeLine169RepairError Z1 + Z3 / 2) ≤
        Real.sqrt (170244 * k2 * m4 * E16384) := Real.sqrt_le_sqrt hinside
    nlinarith [hsqrtInside, hsqrtBound, hkm2z]
  have hTightEnvelope :
      stepEnvelope params k eps (32768 : Error) (2560000 : Error) ≤
        mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (32768 : Error)) (N := (2560000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ k2 * m4 := by positivity
  calc
    cascadeZeta4Repaired σ0 Z1 Z3
      = 2 * σ0 + 2 * Real.sqrt (cascadeLine169RepairError Z1 + Z3 / 2) := by rfl
    _ ≤ 20000 * k2 * m4 * E32768 + 826 * k2 * m4 * E32768 := by
          nlinarith [hσ', hsqrtTerm]
    _ ≤ 40000 * k2 * m4 * E32768 := by
          nlinarith [hk2m4NN]
    _ ≤ 40000 * k2 * m4 * mainFormalEnvelope params k eps :=
          mul_le_mul_of_nonneg_left hTightEnvelope (by positivity)
    _ = (40000 * (k2 * m4)) * mainFormalEnvelope params k eps := by ring
    _ ≤ (100000 * (k2 * m4)) * mainFormalEnvelope params k eps :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (40000 : Error) ≤ 100000) hk2m4NN) hENN
    _ = mainFormalError params k eps := by
          rw [mainFormalError_eq_envelope]
          ring

end Test

end MIPStarRE.LDT
