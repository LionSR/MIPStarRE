import MIPStarRE.LDT.Test.ErrorCascade.CascadeBounds.Zeta4

/-!
# Error cascade — repaired line-169 and final assembly

This module contains the repaired line-169 point-transport scalar bound and the
final tuple-valued consolidator for the error cascade in Step 8 of the main
inductive step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 230--234.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

set_option maxHeartbeats 800000 in
-- The repaired Step 8 scalar proof expands several step-envelope root bounds and
-- exceeds the default heartbeat budget during elaboration.
/-- The repaired line-169 point-transport error
`2σ + 2√(ζ₁ + 10ζ₁^{1/8} + ζ₃/2)` is still absorbed by `mainFormalError`.

This is the local constant repair coming from replacing the paper's incorrect
exact line-169 `ζ₁` transport by the checked bound
`ζ₁ + 10ζ₁^{1/8}` obtained from the pre-completion orthonormalization
comparison. -/
theorem repairedLine169PointError_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = cascadeZeta3 ζ₁ ζ₂) :
    2 * σ + 2 * Real.sqrt (ζ₁ + 10 * Real.rpow ζ₁ (1 / (8 : Error)) + ζ₃ / 2) ≤
      mainFormalError params k eps := by
  rw [hζ₃Eq, hζ₂Eq, hζ₁Eq, hσEq, mainFormalError_eq_envelope]
  set σ0 : Error := cascadeSigma params k ν
  set Z1 : Error := cascadeZeta1 params eps σ0
  set Z2 : Error := cascadeZeta2 Z1
  set Z3 : Error := cascadeZeta3 Z1 Z2
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set E1024 : Error := stepEnvelope params k eps (1024 : Error) (80000 : Error)
  set E2048 : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set E16384 : Error := stepEnvelope params k eps (16384 : Error) (1280000 : Error)
  set E32768 : Error := stepEnvelope params k eps (32768 : Error) (2560000 : Error)
  have hE16384NN : 0 ≤ E16384 := by
    simpa [E16384] using
      stepEnvelope_nonneg (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
  have hE32768NN : 0 ≤ E32768 := by
    simpa [E32768] using
      stepEnvelope_nonneg (h := h) (n := (32768 : Error)) (N := (2560000 : Error))
  have hE2048_to_16384 : E2048 ≤ E16384 := by
    simpa [E2048, E16384] using stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (2048 : Error)) (n₂ := (16384 : Error))
      (N₁ := (160000 : Error)) (N₂ := (1280000 : Error))
      (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hE1024_to_32768 : E1024 ≤ E32768 := by
    simpa [E1024, E32768] using stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (1024 : Error)) (n₂ := (32768 : Error))
      (N₁ := (80000 : Error)) (N₂ := (2560000 : Error))
      (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hσ : σ0 ≤ 10000 * k2 * m4 * E1024 := by
    simpa [σ0, k2, m4, E1024] using cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hσ' : σ0 ≤ 10000 * k2 * m4 * E32768 := by
    calc
      σ0 ≤ 10000 * k2 * m4 * E1024 := hσ
      _ ≤ 10000 * k2 * m4 * E32768 := by
        exact mul_le_mul_of_nonneg_left hE1024_to_32768 (by positivity)
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [σ0, Z1, k2, m4, E2048] using cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1' : Z1 ≤ 20204 * k2 * m4 * E16384 := by
    calc
      Z1 ≤ 20204 * k2 * m4 * E2048 := hZ1
      _ ≤ 20204 * k2 * m4 * E16384 := by
        exact mul_le_mul_of_nonneg_left hE2048_to_16384 (by positivity)
  have hZ1NN : 0 ≤ Z1 := by
    simpa [σ0, Z1] using cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hZ3 : Z3 ≤ 150000 * k2 * m4 * E16384 := by
    simpa [σ0, Z1, Z2, Z3, k2, m4, E16384] using
      cascadeZeta3_bound (h := h) (ν := ν) hνNN hν
  have hZ3NN : 0 ≤ Z3 := by
    unfold Z3 cascadeZeta3
    have hZ2NN : 0 ≤ Z2 := by
      unfold Z2 cascadeZeta2
      refine add_nonneg ?_ ?_
      · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hZ1NN _)
      · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hZ1NN _)
    positivity [hZ1NN, hZ2NN]
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using
      stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hZ1Eighth : Real.rpow Z1 (1 / (8 : Error)) ≤
      4 * (k : Error) * (params.m : Error) * E16384 := by
    exact rpow_Z1_factor_le (params := params) (k := k)
      (hZ1NN := hZ1NN) (hZ1 := hZ1) (hrNN := by positivity)
      (hk2NN := by positivity) (hm4NN := by positivity) (hE2048NN := hE2048NN)
      (hA := by simpa using rpow20204_eighth_le_4)
      (hB := by simpa [k2] using k2_rpow_eighth_le (h := h))
      (hC := by simpa [m4] using m4_rpow_eighth_le (h := h))
      (hD := by simpa [E2048, E16384] using stepEnvelope_rpow_eighth_le (h := h))
  have hkm : (k : Error) * (params.m : Error) ≤ k2 * m4 := by
    exact mul_le_mul h.k_le_k2 h.m_le_m4 (by positivity) (by positivity)
  have hZ1Eighth' : 10 * Real.rpow Z1 (1 / (8 : Error)) ≤ 40 * k2 * m4 * E16384 := by
    calc
      10 * Real.rpow Z1 (1 / (8 : Error))
          ≤ 10 * (4 * (k : Error) * (params.m : Error) * E16384) := by
            gcongr
      _ = 40 * ((k : Error) * (params.m : Error)) * E16384 := by ring
      _ ≤ 40 * (k2 * m4) * E16384 := by
            gcongr
      _ = 40 * k2 * m4 * E16384 := by ring
  have hZ3half : Z3 / 2 ≤ 75000 * k2 * m4 * E16384 := by
    nlinarith [hZ3, hZ3NN]
  have hinside :
      Z1 + 10 * Real.rpow Z1 (1 / (8 : Error)) + Z3 / 2 ≤ 95244 * k2 * m4 * E16384 := by
    nlinarith [hZ1', hZ1Eighth', hZ3half]
  have hsqrt95244_le_309 : Real.sqrt (95244 : Error) ≤ 309 := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor <;> norm_num
  have hsqrtTerm :
      Real.sqrt (Z1 + 10 * Real.rpow Z1 (1 / (8 : Error)) + Z3 / 2) ≤
        309 * (k : Error) * ((params.m : Error) ^ (2 : ℕ)) * E32768 := by
    calc
      Real.sqrt (Z1 + 10 * Real.rpow Z1 (1 / (8 : Error)) + Z3 / 2)
          ≤ Real.sqrt (95244 * k2 * m4 * E16384) := by
            exact Real.sqrt_le_sqrt hinside
      _ ≤ Real.sqrt (95244 : Error) * (k : Error) * ((params.m : Error) ^ (2 : ℕ)) *
            E32768 := by
            simpa [k2, m4, E16384, E32768,
              show (2 : Error) * 16384 = 32768 by norm_num,
              show (2 : Error) * 1280000 = 2560000 by norm_num] using
              sqrt_scaled_stepEnvelope_le (h := h)
                (x := 95244 * k2 * m4 * E16384) (C := (95244 : Error))
                (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
      _ ≤ 309 * (k : Error) * ((params.m : Error) ^ (2 : ℕ)) * E32768 := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_right hsqrt95244_le_309
                (show 0 ≤ (k : Error) * ((params.m : Error) ^ (2 : ℕ)) * E32768 by
                  positivity [hE32768NN])
  have hsqrtTerm' :
      2 * Real.sqrt (Z1 + 10 * Real.rpow Z1 (1 / (8 : Error)) + Z3 / 2) ≤
        618 * k2 * m4 * E32768 := by
    have hkm2 : (k : Error) * ((params.m : Error) ^ (2 : ℕ)) ≤ k2 * m4 := by
      simpa [k2, m4] using h.km2_le_k2m4
    have hscaled :
        309 * (k : Error) * ((params.m : Error) ^ (2 : ℕ)) * E32768 ≤
          309 * k2 * m4 * E32768 := by
      have hmul : (k : Error) * ((params.m : Error) ^ (2 : ℕ)) ≤ k2 * m4 := hkm2
      nlinarith [hmul, hE32768NN]
    nlinarith [hsqrtTerm, hscaled]
  have hTightEnvelope :
      E32768 ≤ mainFormalEnvelope params k eps := by
    simpa [E32768] using stepEnvelope_le_mainFormalEnvelope (h := h)
      (n := (32768 : Error)) (N := (2560000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ k2 * m4 := by positivity
  calc
    2 * σ0 + 2 * Real.sqrt (Z1 + 10 * Real.rpow Z1 (1 / (8 : Error)) + Z3 / 2)
        ≤ 20000 * k2 * m4 * E32768 + 618 * k2 * m4 * E32768 := by
          nlinarith [hσ', hsqrtTerm']
    _ ≤ 30000 * k2 * m4 * E32768 := by
          nlinarith [hk2m4NN, hE32768NN]
    _ ≤ 30000 * k2 * m4 * mainFormalEnvelope params k eps := by
          exact mul_le_mul_of_nonneg_left hTightEnvelope (by positivity)
    _ ≤ 100000 * k2 * m4 * mainFormalEnvelope params k eps := by
          exact mul_le_mul_of_nonneg_right
            (by nlinarith [hk2m4NN]) hENN
    _ = mainFormalError params k eps := by
          rw [mainFormalError_eq_envelope]

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
