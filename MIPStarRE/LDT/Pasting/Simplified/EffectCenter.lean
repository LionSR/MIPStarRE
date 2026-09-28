import MIPStarRE.LDT.Pasting.Simplified.RandomWordEnergy

/-!
# Centering a quantum effect

The centered effect `M - I/2` has square at most `I/4`. This is the
operator estimate behind the sharp marginal-stability constant in the
simplified random-word argument.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:sequential-bot-marginal`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive contraction centered at `I/2` has square bounded by `I/4`. -/
theorem centered_effect_square_le_quarter
    (M : MIPStarRE.Quantum.Op ι) (hM : 0 ≤ M) (hMle : M ≤ 1) :
    (M - (1 / 2 : ℝ) • (1 : MIPStarRE.Quantum.Op ι)) *
        (M - (1 / 2 : ℝ) • (1 : MIPStarRE.Quantum.Op ι)) ≤
      (1 / 4 : ℝ) • (1 : MIPStarRE.Quantum.Op ι) := by
  have hIM : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) - M := sub_nonneg.mpr hMle
  have hcomm : Commute M (1 - M) :=
    (Commute.one_right M).sub_right (Commute.refl M)
  have hprod : 0 ≤ M * (1 - M) := Commute.mul_nonneg hM hIM hcomm
  apply sub_nonneg.mp
  convert hprod using 1
  simp only [Algebra.smul_def, mul_one]
  let H : MIPStarRE.Quantum.Op ι := algebraMap ℝ _ (1 / 2)
  let Q : MIPStarRE.Quantum.Op ι := algebraMap ℝ _ (1 / 4)
  have hhalf : H + H = 1 := by
    dsimp [H]
    rw [← map_add]
    norm_num
  have hquarter : H * H = Q := by
    dsimp [H, Q]
    rw [← map_mul]
    norm_num
  have hcentral : H * M = M * H := Algebra.commutes _ _
  change Q - (M - H) * (M - H) = M * (1 - M)
  calc
    Q - (M - H) * (M - H) = M * H + H * M - M * M := by
      rw [← hquarter]
      noncomm_ring
    _ = M * (H + H) - M * M := by
      rw [hcentral]
      noncomm_ring
    _ = M * (1 - M) := by rw [hhalf]; noncomm_ring

/-- The centered-effect square bound remains valid inside any operator
sandwich. -/
theorem centered_effect_sandwich_le_quarter
    (M U : MIPStarRE.Quantum.Op ι) (hM : 0 ≤ M) (hMle : M ≤ 1) :
    Uᴴ * ((M - (1 / 2 : ℝ) • (1 : MIPStarRE.Quantum.Op ι)) *
      (M - (1 / 2 : ℝ) • (1 : MIPStarRE.Quantum.Op ι))) * U ≤
        (1 / 4 : ℝ) • (Uᴴ * U) := by
  let C : MIPStarRE.Quantum.Op ι := M - (1 / 2 : ℝ) • 1
  have hcenter : C * C ≤ (1 / 4 : ℝ) • (1 : MIPStarRE.Quantum.Op ι) :=
    centered_effect_square_le_quarter M hM hMle
  have hconj : 0 ≤ Uᴴ * ((1 / 4 : ℝ) • 1 - C * C) * U := by
    simpa only [Matrix.star_eq_conjTranspose] using
      star_left_conjugate_nonneg (sub_nonneg.mpr hcenter) U
  apply sub_nonneg.mp
  convert hconj using 1
  simp only [C, sub_mul, mul_sub, mul_assoc, smul_mul_assoc, mul_smul_comm,
    mul_one, one_mul]

/-- One cross term with a centered effect is bounded by half the product
of the two state-dependent operator norms. -/
theorem ev_centered_effect_cross_abs_le
    (ψ : QuantumState ι) (M D U : MIPStarRE.Quantum.Op ι)
    (hM : 0 ≤ M) (hMle : M ≤ 1) :
    |ev ψ (Dᴴ * (M - (1 / 2 : ℝ) • 1) * U)| ≤
      (1 / 2 : ℝ) * Real.sqrt (ev ψ (Dᴴ * D)) *
        Real.sqrt (ev ψ (Uᴴ * U)) := by
  let C : MIPStarRE.Quantum.Op ι := M - (1 / 2 : ℝ) • 1
  have hMstar : Mᴴ = M := (Matrix.nonneg_iff_posSemidef.mp hM).isHermitian.eq
  have hCstar : Cᴴ = C := by
    simp [C, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hMstar]
  have hnorm :
      ev ψ ((C * U)ᴴ * (C * U)) ≤ (1 / 4 : ℝ) * ev ψ (Uᴴ * U) := by
    have h := ev_mono ψ _ _ (centered_effect_sandwich_le_quarter M U hM hMle)
    change ev ψ (Uᴴ * (C * C) * U) ≤
      ev ψ ((1 / 4 : ℝ) • (Uᴴ * U)) at h
    rw [ev_real_smul] at h
    calc
      ev ψ ((C * U)ᴴ * (C * U)) = ev ψ (Uᴴ * (C * C) * U) := by
        rw [Matrix.conjTranspose_mul, hCstar]
        congr 1
        noncomm_ring
      _ ≤ (1 / 4 : ℝ) * ev ψ (Uᴴ * U) := h
  calc
    |ev ψ (Dᴴ * C * U)| = |ev ψ (Dᴴ * (C * U))| := by rw [mul_assoc]
    _ ≤ Real.sqrt (ev ψ (Dᴴ * D)) *
        Real.sqrt (ev ψ ((C * U)ᴴ * (C * U))) := by
          simpa using ev_abs_mul_le_sqrt ψ Dᴴ (C * U)
    _ ≤ Real.sqrt (ev ψ (Dᴴ * D)) *
        Real.sqrt ((1 / 4 : ℝ) * ev ψ (Uᴴ * U)) := by
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnorm)
            (Real.sqrt_nonneg _)
    _ = (1 / 2 : ℝ) * Real.sqrt (ev ψ (Dᴴ * D)) *
          Real.sqrt (ev ψ (Uᴴ * U)) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
            norm_num
            ring

end MIPStarRE.LDT.Pasting
