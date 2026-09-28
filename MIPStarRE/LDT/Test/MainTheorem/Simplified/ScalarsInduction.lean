import MIPStarRE.LDT.Test.MainTheorem.Simplified.ScalarsCore
import MIPStarRE.LDT.MainInductionStep.Simplified.Main

/-!
# Scalar induction bound for simplified soundness

Substituting three equal test errors into the simplified induction gives
an error quadratic in the final radius. The degree-zero case is treated
directly, as in the simplified blueprint.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  equation `short-sigma-bound`.
-/

namespace MIPStarRE.LDT.Test

open MIPStarRE.LDT.MainInductionStep

/-- The factor-two unsymmetrized induction error is at most `18000 R²`
in the nontrivial scalar regime. -/
theorem simplifiedFinal_induction_bound
    (params : Parameters) (eps : Error)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) :
    2 * simplifiedMainInductionError params (3 * eps) (3 * eps) (3 * eps) ≤
      18000 * (simplifiedFinalRadius params eps) ^ (2 : ℕ) := by
  let θ : Error := (params.d : Error) / params.q
  let u : Error := Real.rpow eps (1 / (64 : Error))
  let v : Error := Real.rpow θ (1 / (64 : Error))
  let K : Error := simplifiedFinalScale params
  let R : Error := simplifiedFinalRadius params eps
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hu : 0 ≤ u := Real.rpow_nonneg heps _
  have hv : 0 ≤ v := Real.rpow_nonneg hθ _
  have hK1 : 1 ≤ K := by
    have hm : (1 : Error) ≤ params.m := by exact_mod_cast params.hm
    exact hm.trans (simplifiedFinalScale_ge_m params)
  have hRexpr : R = K * (u + v) := rfl
  have hu2 : u ^ (2 : ℕ) = Real.rpow eps (1 / (32 : Error)) := by
    dsimp [u]
    calc
      (Real.rpow eps (1 / (64 : Error))) ^ (2 : ℕ) =
          Real.rpow eps ((1 / (64 : Error)) * (2 : Error)) := by
            simpa using (Real.rpow_mul heps (1 / (64 : Error)) (2 : Error)).symm
      _ = _ := by norm_num
  have hv2 : v ^ (2 : ℕ) = Real.rpow θ (1 / (32 : Error)) := by
    dsimp [v]
    calc
      (Real.rpow θ (1 / (64 : Error))) ^ (2 : ℕ) =
          Real.rpow θ ((1 / (64 : Error)) * (2 : Error)) := by
            simpa using (Real.rpow_mul hθ (1 / (64 : Error)) (2 : Error)).symm
      _ = _ := by norm_num
  have hEpsPow : eps ≤ u ^ (2 : ℕ) := by
    rw [hu2]
    simpa using rpow_le_of_denom_le heps heps1
      (n₁ := (1 : Error)) (n₂ := (32 : Error)) (by norm_num) (by norm_num)
  have hSqrtEps : Real.sqrt eps ≤ u ^ (2 : ℕ) := by
    rw [hu2, Real.sqrt_eq_rpow]
    exact rpow_le_of_denom_le heps heps1
      (n₁ := (2 : Error)) (n₂ := (32 : Error)) (by norm_num) (by norm_num)
  have hR2 : K * (u + v) ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
    rw [hRexpr]
    have hE : 0 ≤ u + v := add_nonneg hu hv
    have hmul : 0 ≤ K * (u + v) ^ (2 : ℕ) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hK1) hmul]
  by_cases hd : params.d = 0
  · have hv0 : v = 0 := by simp [v, θ, hd]
    have hK : K = (params.m : Error) ^ (4 : ℕ) := by
      simp [K, simplifiedFinalScale, hd]
    have hm1 : (1 : Error) ≤ params.m := by exact_mod_cast params.hm
    have hmK : (params.m : Error) ≤ K := by
      simpa [K] using simplifiedFinalScale_ge_m params
    have hrootm : Real.sqrt (24 * (params.m : Error)) ≤
        5 * (params.m : Error) := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith [mul_nonneg (sub_nonneg.mpr hm1)
          (show 0 ≤ (params.m : Error) by positivity)]
    have hroot : Real.sqrt (24 * (params.m : Error) * eps) ≤
        5 * (params.m : Error) * u ^ (2 : ℕ) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 24 * (params.m : Error))]
      exact mul_le_mul hrootm hSqrtEps (Real.sqrt_nonneg _) (by positivity)
    have hE : 0 ≤ u ^ (2 : ℕ) := by positivity
    have hσ :
        2 * simplifiedMainInductionError params (3 * eps) (3 * eps) (3 * eps) ≤
          16 * K * u ^ (2 : ℕ) := by
      simp only [simplifiedMainInductionError, hd, ↓reduceIte,
        simplifiedDegreeZeroError]
      have hroot' : Real.sqrt (8 * (params.m : Error) * (3 * eps)) ≤
          5 * (params.m : Error) * u ^ (2 : ℕ) := by
        have harg : 8 * (params.m : Error) * (3 * eps) =
            24 * (params.m : Error) * eps := by ring
        rw [harg]
        exact hroot
      nlinarith [mul_nonneg (sub_nonneg.mpr hmK) hE,
        mul_nonneg (sub_nonneg.mpr hK1) hE]
    have hKR : K * u ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
      simpa [hv0] using hR2
    nlinarith
  · have hd1 : (1 : Error) ≤ params.d := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
    have hK : K = (params.d : Error) ^ (2 : ℕ) *
        (params.m : Error) ^ (4 : ℕ) := by
      simp [K, simplifiedFinalScale, hd]
    have hThree32 : Real.rpow (3 * eps) (1 / (32 : Error)) ≤
        3 * u ^ (2 : ℕ) := by
      rw [hu2]
      have hmul : Real.rpow (3 * eps) (1 / (32 : Error)) =
          Real.rpow 3 (1 / (32 : Error)) * Real.rpow eps (1 / (32 : Error)) := by
        simpa using (Real.mul_rpow (x := (3 : Error)) (y := eps)
          (z := 1 / (32 : Error)) (by norm_num) heps)
      rw [hmul]
      have h3 : Real.rpow (3 : Error) (1 / (32 : Error)) ≤ 3 :=
        Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
      exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg heps _)
    have hThree8 : Real.rpow (3 * eps) (1 / (8 : Error)) ≤
        3 * u ^ (2 : ℕ) := by
      have hmul : Real.rpow (3 * eps) (1 / (8 : Error)) =
          Real.rpow 3 (1 / (8 : Error)) * Real.rpow eps (1 / (8 : Error)) := by
        simpa using (Real.mul_rpow (x := (3 : Error)) (y := eps)
          (z := 1 / (8 : Error)) (by norm_num) heps)
      rw [hmul]
      have h3 : Real.rpow (3 : Error) (1 / (8 : Error)) ≤ 3 :=
        Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
      have hpow : Real.rpow eps (1 / (8 : Error)) ≤ u ^ (2 : ℕ) := by
        rw [hu2]
        exact rpow_le_of_denom_le heps heps1
          (n₁ := (8 : Error)) (n₂ := (32 : Error)) (by norm_num) (by norm_num)
      exact (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg heps _)).trans
        (mul_le_mul_of_nonneg_left hpow (by norm_num))
    have hsum :
        Real.rpow (3 * eps) (1 / (32 : Error)) +
          Real.rpow (3 * eps) (1 / (32 : Error)) +
          Real.rpow θ (1 / (32 : Error)) +
          Real.rpow (3 * eps) (1 / (8 : Error)) ≤
          9 * (u + v) ^ (2 : ℕ) := by
      rw [← hv2]
      nlinarith [mul_nonneg hu hv]
    have hσ :
        2 * simplifiedMainInductionError params (3 * eps) (3 * eps) (3 * eps) ≤
          18000 * K * (u + v) ^ (2 : ℕ) := by
      simp only [simplifiedMainInductionError, hd, ↓reduceIte,
        simplifiedPositiveDegreeError]
      have hK0 : 0 ≤ K := by linarith
      calc
        2 * (1000 * (params.d : Error) ^ (2 : ℕ) *
            (params.m : Error) ^ (4 : ℕ) *
            (Real.rpow (3 * eps) (1 / (32 : Error)) +
              Real.rpow (3 * eps) (1 / (32 : Error)) +
              Real.rpow θ (1 / (32 : Error)) +
              Real.rpow (3 * eps) (1 / (8 : Error)))) =
          2000 * K *
            (Real.rpow (3 * eps) (1 / (32 : Error)) +
              Real.rpow (3 * eps) (1 / (32 : Error)) +
              Real.rpow θ (1 / (32 : Error)) +
              Real.rpow (3 * eps) (1 / (8 : Error))) := by rw [hK]; ring
        _ ≤ 2000 * K * (9 * (u + v) ^ (2 : ℕ)) := by
          gcongr
        _ = _ := by ring
    nlinarith [hR2]

end MIPStarRE.LDT.Test
