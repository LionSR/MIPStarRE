import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.PositiveGram.Sigma

/-!
# Square polar extension

The simplified state-dependent orthogonalization proof uses a unitary polar
factor even when its contraction `X` is singular.  This file derives that
square-matrix form from the positive-Gram polar-extension theorem already
proved in the project.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`, proof of
  `lem:state-dependent-orthogonalization`, the paragraph defining `X` and `U`.
- `references/ldt-paper/orthonormalization.tex`, Section 5, for the original
  orthogonalization construction.
-/

open scoped MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

/-- Every finite square complex matrix has a unitary polar factor, including
the singular case: `X = U sqrt(X†X)`. -/
theorem exists_unitary_polar_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) :
    ∃ U : Matrix ι ι ℂ,
      U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧ X = U * CFC.sqrt (Xᴴ * X) := by
  let Q : Matrix ι ι ℂ := Xᴴ * X
  have hQ : Q.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self X
  have hQpos : Q.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  obtain ⟨U, hU, hXU⟩ :=
    exists_xHat_of_positive_gram_spectrum X Q hQ hQpos rfl le_rfl
  have hUsquare : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hsqrtH : (CFC.sqrt Q)ᴴ = CFC.sqrt Q := by
    simpa using (CFC.sqrt_nonneg Q).isHermitian.eq
  have hUX : Uᴴ * X = CFC.sqrt Q := by
    calc
      Uᴴ * X = (Xᴴ * U)ᴴ := by simp [Matrix.conjTranspose_mul]
      _ = (CFC.sqrt Q)ᴴ := by rw [hXU]
      _ = CFC.sqrt Q := hsqrtH
  refine ⟨U, hU, hUsquare, ?_⟩
  calc
    X = (U * Uᴴ) * X := by rw [hU, one_mul]
    _ = U * (Uᴴ * X) := by rw [Matrix.mul_assoc]
    _ = U * CFC.sqrt (Xᴴ * X) := by rw [hUX]

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
