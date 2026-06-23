import MIPStarRE.Quantum.FiniteMatrix.Order

/-!
# Block-diagonal finite matrix operators

This module contains block-diagonal trace and positive-semidefinite order facts
for finite complex matrices.  The canonical SDP block algebra in Section 9 uses
these lemmas to compare the paper's block form with Mathlib's
`Matrix.blockDiagonal`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp

namespace Matrix

/-- A block-diagonal matrix is the sum of its blocks tensored with the
coordinate projections on the block index. -/
theorem blockDiagonal_eq_sum_kronecker_diagonal {o m : Type*}
    [Fintype o] [DecidableEq o] [Finite m] (B : o → Matrix m m ℂ) :
    Matrix.blockDiagonal B =
      ∑ b : o, Matrix.kronecker (B b)
        (Matrix.diagonal fun c : o => if c = b then (1 : ℂ) else 0) := by
  classical
  letI : Fintype m := Fintype.ofFinite m
  ext x y
  rcases x with ⟨i, bx⟩
  rcases y with ⟨j, cy⟩
  rw [Matrix.sum_apply]
  by_cases hxy : bx = cy
  · subst cy
    simp [Matrix.blockDiagonal_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  · simp [Matrix.blockDiagonal_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, hxy]

/-- A block-diagonal complex matrix is positive semidefinite when all of its
diagonal blocks are positive semidefinite. -/
theorem blockDiagonal_nonneg {o m : Type*}
    [Finite o] [DecidableEq o] [Finite m]
    (B : o → Matrix m m ℂ) (hB : ∀ b, 0 ≤ B b) :
    0 ≤ Matrix.blockDiagonal B := by
  classical
  letI : Fintype o := Fintype.ofFinite o
  letI : Fintype m := Fintype.ofFinite m
  rw [Matrix.blockDiagonal_eq_sum_kronecker_diagonal B]
  exact Finset.sum_nonneg fun b _ =>
    MIPStarRE.Quantum.kronecker_nonneg (hB b) (by
      refine Matrix.nonneg_iff_posSemidef.mpr ?_
      exact Matrix.PosSemidef.diagonal <| by
        intro c
        by_cases hc : c = b <;> simp [hc])

/-- A block-diagonal complex matrix is positive semidefinite exactly when each
of its diagonal blocks is positive semidefinite. -/
theorem blockDiagonal_nonneg_iff {o m : Type*}
    [Finite o] [DecidableEq o] [Finite m]
    (B : o → Matrix m m ℂ) :
    0 ≤ Matrix.blockDiagonal B ↔ ∀ b, 0 ≤ B b := by
  classical
  letI : Fintype o := Fintype.ofFinite o
  letI : Fintype m := Fintype.ofFinite m
  constructor
  · intro hB b
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    let e : m → m × o := fun i => (i, b)
    have hsub :
        ((Matrix.blockDiagonal B).submatrix e e).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef.mp hB).submatrix e
    have hEq : (Matrix.blockDiagonal B).submatrix e e = B b := by
      ext i j
      simp [e, Matrix.blockDiagonal_apply_eq]
    simpa [hEq] using hsub
  · exact Matrix.blockDiagonal_nonneg B

end Matrix
