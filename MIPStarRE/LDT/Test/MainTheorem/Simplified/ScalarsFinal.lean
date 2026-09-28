import MIPStarRE.LDT.Test.MainTheorem.Simplified.ScalarsInduction

/-!
# Absorption into the simplified final error

The role-register Step 5 error is linear in the final radius. The linear
rounding estimates therefore fit the displayed coefficient `21000`.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  equations `short-sigma-bound` and the final scalar comparison.
-/

namespace MIPStarRE.LDT.Test

open MIPStarRE.LDT.MainInductionStep

/-- Both point errors from linear rounding and the rounded polynomial
consistency error are absorbed by the simplified final parameter. -/
theorem simplifiedFinal_scalar_absorption
    (params : Parameters) (eps : Error)
    (heps : 0 ≤ eps)
    (hsmall : ¬ 1 ≤ simplifiedMainFormalError params eps) :
    let σ : Error := 2 * simplifiedMainInductionError params
      (3 * eps) (3 * eps) (3 * eps)
    let ζ : Error := σ + 2 * Real.sqrt (3 * eps + σ) +
      (params.m * params.d : Error) / params.q
    2 * (σ + 18 * ζ) ≤ simplifiedMainFormalError params eps ∧
      57 * ζ ≤ simplifiedMainFormalError params eps := by
  dsimp
  let θ : Error := (params.d : Error) / params.q
  let u : Error := Real.rpow eps (1 / (64 : Error))
  let v : Error := Real.rpow θ (1 / (64 : Error))
  let K : Error := simplifiedFinalScale params
  let R : Error := simplifiedFinalRadius params eps
  let σ : Error := 2 * simplifiedMainInductionError params
    (3 * eps) (3 * eps) (3 * eps)
  let ζ : Error := σ + 2 * Real.sqrt (3 * eps + σ) +
    (params.m * params.d : Error) / params.q
  obtain ⟨heps1, hθ1, hR0, hRsmall⟩ :=
    simplifiedFinal_small_regime params eps heps hsmall
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have hu : 0 ≤ u := Real.rpow_nonneg heps _
  have hv : 0 ≤ v := Real.rpow_nonneg hθ0 _
  have hK1 : 1 ≤ K := by
    have hm : (1 : Error) ≤ params.m := by exact_mod_cast params.hm
    exact hm.trans (simplifiedFinalScale_ge_m params)
  have hmK : (params.m : Error) ≤ K := simplifiedFinalScale_ge_m params
  have hRexpr : R = K * (u + v) := rfl
  have huR : u ≤ R := by
    rw [hRexpr]
    calc
      u = 1 * u := by ring
      _ ≤ K * u := mul_le_mul_of_nonneg_right hK1 hu
      _ ≤ K * (u + v) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hv) (by linarith)
  have hvR : v ≤ R := by
    rw [hRexpr]
    calc
      v = 1 * v := by ring
      _ ≤ K * v := mul_le_mul_of_nonneg_right hK1 hv
      _ ≤ K * (u + v) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hu) (by linarith)
  have hEpsPow : eps ≤ u ^ (2 : ℕ) := by
    have hpow : eps ≤ Real.rpow eps (1 / (32 : Error)) := by
      simpa using rpow_le_of_denom_le heps heps1
        (n₁ := (1 : Error)) (n₂ := (32 : Error)) (by norm_num) (by norm_num)
    have hu2 : u ^ (2 : ℕ) = Real.rpow eps (1 / (32 : Error)) := by
      dsimp [u]
      calc
        (Real.rpow eps (1 / (64 : Error))) ^ (2 : ℕ) =
            Real.rpow eps ((1 / (64 : Error)) * (2 : Error)) := by
              simpa using (Real.rpow_mul heps (1 / (64 : Error)) (2 : Error)).symm
        _ = _ := by norm_num
    simpa [hu2] using hpow
  have hEpsR : eps ≤ R ^ (2 : ℕ) :=
    hEpsPow.trans (pow_le_pow_left₀ hu huR 2)
  have hθv : θ ≤ v := by
    dsimp [v]
    simpa using rpow_le_of_denom_le hθ0 (by simpa [θ] using hθ1)
      (n₁ := (1 : Error)) (n₂ := (64 : Error)) (by norm_num) (by norm_num)
  have hmθ : (params.m * params.d : Error) / params.q ≤ R := by
    have hqpos : (0 : Error) < params.q := by exact_mod_cast params.hq
    have hcast : (params.m * params.d : Error) / params.q =
        (params.m : Error) * θ := by
      dsimp [θ]
      ring
    rw [hcast]
    calc
      (params.m : Error) * θ ≤ (params.m : Error) * v := by
        exact mul_le_mul_of_nonneg_left hθv (by positivity)
      _ ≤ K * v := mul_le_mul_of_nonneg_right hmK hv
      _ ≤ R := by
        rw [hRexpr]
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left hu) (by linarith)
  have hσ : σ ≤ 18000 * R ^ (2 : ℕ) :=
    simplifiedFinal_induction_bound params eps heps heps1
  have hrootBound : 3 * eps + σ ≤ 18003 * R ^ (2 : ℕ) := by
    dsimp [σ] at hσ ⊢
    linarith
  have hroot : Real.sqrt (3 * eps + σ) ≤ 135 * R := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [hrootBound]
  have hσζ : σ ≤ ζ := by
    dsimp [ζ]
    have hmθ0 : 0 ≤ (params.m * params.d : Error) / params.q := by positivity
    nlinarith [Real.sqrt_nonneg (3 * eps + σ)]
  have hζ : ζ ≤ 300 * R := by
    have hR2small : 18000 * R ^ (2 : ℕ) ≤ 29 * R := by
      nlinarith [mul_nonneg hR0 (sub_nonneg.mpr (le_of_lt hRsmall))]
    dsimp [ζ]
    linarith
  have herror : simplifiedMainFormalError params eps = 21000 * R :=
    simplifiedMainFormalError_eq_radius params eps
  constructor
  · change 2 * (σ + 18 * ζ) ≤ simplifiedMainFormalError params eps
    rw [herror]
    linarith
  · change 57 * ζ ≤ simplifiedMainFormalError params eps
    rw [herror]
    linarith

end MIPStarRE.LDT.Test
