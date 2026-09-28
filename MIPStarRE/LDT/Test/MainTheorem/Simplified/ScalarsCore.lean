import MIPStarRE.LDT.Test.MainTheorem.Simplified.Statements
import MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.EnvelopeBounds

/-!
# Scalar regime for the simplified final theorem

The nontrivial final-error branch bounds the two basic error parameters
below one. The scale `K_{m,d}` dominates the dimension `m`.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  equations `nontrivial-main-error` and `short-sigma-bound`.
-/

namespace MIPStarRE.LDT.Test

/-- The radius before multiplication by the final numerical constant. -/
noncomputable def simplifiedFinalRadius (params : Parameters) (eps : Error) : Error :=
  simplifiedFinalScale params *
    (Real.rpow eps (1 / (64 : Error)) +
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (64 : Error)))

/-- The final error is `21000` times the radius. -/
theorem simplifiedMainFormalError_eq_radius (params : Parameters) (eps : Error) :
    simplifiedMainFormalError params eps = 21000 * simplifiedFinalRadius params eps := by
  unfold simplifiedMainFormalError simplifiedFinalRadius
  ring

/-- The simplified scale dominates the dimension and hence one. -/
theorem simplifiedFinalScale_ge_m (params : Parameters) :
    (params.m : Error) ≤ simplifiedFinalScale params := by
  have hm : (1 : Error) ≤ params.m := by exact_mod_cast params.hm
  have hm4 : (params.m : Error) ≤ (params.m : Error) ^ (4 : ℕ) := by
    simpa using (pow_le_pow_right₀ hm (show (1 : ℕ) ≤ 4 by norm_num))
  by_cases hd : params.d = 0
  · simpa [simplifiedFinalScale, hd] using hm4
  · have hd1 : (1 : Error) ≤ params.d := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
    have hd2 : (1 : Error) ≤ (params.d : Error) ^ (2 : ℕ) :=
      one_le_pow₀ hd1
    have hm4zero : 0 ≤ (params.m : Error) ^ (4 : ℕ) := by positivity
    have hmul : (params.m : Error) ^ (4 : ℕ) ≤
        (params.d : Error) ^ (2 : ℕ) * (params.m : Error) ^ (4 : ℕ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd2) hm4zero]
    exact hm4.trans (by simpa [simplifiedFinalScale, hd] using hmul)

/-- In the nontrivial branch, the axis-error and degree ratio both lie in
`[0,1]`, and the radius is smaller than `1/21000`. -/
theorem simplifiedFinal_small_regime
    (params : Parameters) (eps : Error)
    (heps : 0 ≤ eps)
    (hsmall : ¬ 1 ≤ simplifiedMainFormalError params eps) :
    eps ≤ 1 ∧ ((params.d : Error) / params.q) ≤ 1 ∧
      0 ≤ simplifiedFinalRadius params eps ∧
      simplifiedFinalRadius params eps < 1 / 21000 := by
  let θ : Error := (params.d : Error) / params.q
  let u : Error := Real.rpow eps (1 / (64 : Error))
  let v : Error := Real.rpow θ (1 / (64 : Error))
  let K : Error := simplifiedFinalScale params
  let R : Error := simplifiedFinalRadius params eps
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hu : 0 ≤ u := Real.rpow_nonneg heps _
  have hv : 0 ≤ v := Real.rpow_nonneg hθ _
  have hK : 1 ≤ K := by
    have hm : (1 : Error) ≤ params.m := by exact_mod_cast params.hm
    exact hm.trans (simplifiedFinalScale_ge_m params)
  have hRexpr : R = K * (u + v) := rfl
  have hR0 : 0 ≤ R := by rw [hRexpr]; positivity
  have hRsmall : R < 1 / 21000 := by
    have hlt : simplifiedMainFormalError params eps < 1 := lt_of_not_ge hsmall
    rw [simplifiedMainFormalError_eq_radius] at hlt
    dsimp [R]
    linarith
  have huR : u ≤ R := by
    rw [hRexpr]
    calc
      u = 1 * u := by ring
      _ ≤ K * u := mul_le_mul_of_nonneg_right hK hu
      _ ≤ K * (u + v) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hv) (by linarith)
  have hvR : v ≤ R := by
    rw [hRexpr]
    calc
      v = 1 * v := by ring
      _ ≤ K * v := mul_le_mul_of_nonneg_right hK hv
      _ ≤ K * (u + v) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hu) (by linarith)
  have heps1 : eps ≤ 1 := by
    by_contra h
    have hp : 1 ≤ u := Real.one_le_rpow (le_of_not_ge h) (by norm_num)
    linarith
  have hθ1 : θ ≤ 1 := by
    by_contra h
    have hp : 1 ≤ v := Real.one_le_rpow (le_of_not_ge h) (by norm_num)
    linarith
  exact ⟨heps1, hθ1, hR0, hRsmall⟩

end MIPStarRE.LDT.Test
