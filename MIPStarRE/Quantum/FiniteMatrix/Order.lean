import MIPStarRE.Quantum.FiniteMatrix.Basic

/-!
# Positive-semidefinite finite matrix order

This module contains the order-theoretic facts for finite-dimensional
complex matrix operators: trace control of positive operators, closedness of the
positive-semidefinite cone, the corresponding `ProperCone`, and basic
monotonicity facts for sandwiches, Kronecker products, and reindexing.

These are the matrix-operator facts used by the canonical SDP strong-duality
argument in Section 9.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp

namespace MIPStarRE.Quantum

/-! ### Basic order lemmas -/

variable {d : Type*} [Fintype d]

noncomputable local instance : DecidableEq d := Classical.decEq d

local instance : NonnegSpectrumClass ℝ (Op d) :=
  Matrix.instNonnegSpectrumClass (𝕜 := ℂ) (n := d)

noncomputable local instance : NonUnitalContinuousFunctionalCalculus ℝ (Op d) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital (R := ℝ) (A := Op d) (p := IsSelfAdjoint)

private lemma col_norm_sq_le_trace_star_mul_self (Y : Op d) (i : d) :
    ‖toLp 2 (Y · i)‖ ^ 2 ≤ Complex.re (Yᴴ * Y).trace := by
  rw [show Complex.re (Yᴴ * Y).trace = ∑ k : d, ‖toLp 2 (Y · k)‖ ^ 2 by
    simp [Matrix.trace, Matrix.conjTranspose_apply, Matrix.mul_apply,
      PiLp.norm_sq_eq_of_L2 (fun _ : d => ℂ), ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]]
  exact Finset.single_le_sum (fun k _ => sq_nonneg (‖toLp 2 (Y · k)‖))
    (Finset.mem_univ i)

/-- Every entry of a positive semidefinite finite matrix is bounded by its real trace. -/
theorem norm_apply_le_trace_re_of_nonneg {A : Op d} (hA : 0 ≤ A) (i j : d) :
    ‖A i j‖ ≤ Complex.re A.trace := by
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  subst A
  rw [Matrix.star_eq_conjTranspose]
  let u := toLp 2 (Y · i)
  let v := toLp 2 (Y · j)
  have hentry : (Yᴴ * Y) i j = inner ℂ u v := by
    simp only [u, v, Matrix.conjTranspose_apply, Matrix.mul_apply,
      PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply]
  have hu2 : ‖u‖ ^ 2 ≤ Complex.re (Yᴴ * Y).trace := by
    simpa [u] using col_norm_sq_le_trace_star_mul_self (Y := Y) i
  have hv2 : ‖v‖ ^ 2 ≤ Complex.re (Yᴴ * Y).trace := by
    simpa [v] using col_norm_sq_le_trace_star_mul_self (Y := Y) j
  have huv : ‖u‖ * ‖v‖ ≤ Complex.re (Yᴴ * Y).trace := by
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  calc
    ‖(Yᴴ * Y) i j‖ = ‖inner ℂ u v‖ := by rw [hentry]
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
    _ ≤ Complex.re (Yᴴ * Y).trace := huv

/-- The elementwise matrix norm of a positive semidefinite finite matrix is
bounded by its real trace. -/
theorem norm_le_trace_re_of_nonneg {A : Op d} (hA : 0 ≤ A) :
    ‖A‖ ≤ Complex.re A.trace := by
  have htrace_nonneg : 0 ≤ Complex.re A.trace :=
    (Complex.nonneg_iff.mp ((Matrix.nonneg_iff_posSemidef.mp hA).trace_nonneg)).1
  exact (Matrix.norm_le_iff htrace_nonneg).mpr
    (norm_apply_le_trace_re_of_nonneg hA)

/-- The positive-semidefinite cone in a matrix algebra is closed. -/
theorem isClosed_op_nonnegative {ι : Type*} : IsClosed {A : Op ι | 0 ≤ A} := by
  classical
  have hhermitian : IsClosed {A : Op ι | A.IsHermitian} := by
    simpa [Matrix.IsHermitian] using
      isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id
  have hquadratic : IsClosed
      {A : Op ι |
        ∀ x : ι →₀ ℂ,
          0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj} := by
    rw [show
        {A : Op ι |
          ∀ x : ι →₀ ℂ,
            0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj} =
        ⋂ x : ι →₀ ℂ,
          {A : Op ι |
            0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj} by
      ext A
      simp]
    refine isClosed_iInter fun x => ?_
    have hquad : Continuous fun A : Op ι =>
        x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj := by
      simp only [Finsupp.sum]
      exact continuous_finsetSum x.support fun i _ =>
        continuous_finsetSum x.support fun j _ =>
          ((continuous_const.mul (continuous_apply_apply i j)).mul continuous_const)
    exact isClosed_le continuous_const hquad
  have hpsd : IsClosed {A : Op ι | A.PosSemidef} := by
    rw [show {A : Op ι | A.PosSemidef} =
        {A : Op ι | A.IsHermitian} ∩
          {A : Op ι |
            ∀ x : ι →₀ ℂ,
              0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj} by
      ext A
      rfl]
    exact hhermitian.inter hquadratic
  rw [show {A : Op ι | 0 ≤ A} = {A : Op ι | A.PosSemidef} by
    ext A
    exact Matrix.nonneg_iff_posSemidef]
  exact hpsd

/-- The positive-semidefinite cone in a finite matrix algebra as a proper cone. -/
noncomputable def opNonnegativeProperCone (d : Type*) [Fintype d] [DecidableEq d] :
    ProperCone ℝ (Op d) where
  toSubmodule := PointedCone.positive ℝ (Op d)
  isClosed' := by
    change IsClosed ({A : Op d | 0 ≤ A} : Set (Op d))
    exact isClosed_op_nonnegative (ι := d)

/-- Sandwiching a PSD operator by a Hermitian operator preserves positivity. -/
theorem sandwich_nonneg {M P : Op d} (hP : 0 ≤ P) (hMH : Mᴴ = M) :
    0 ≤ M * P * M := by
  simpa [Matrix.star_eq_conjTranspose, hMH] using star_right_conjugate_nonneg hP M

/-- Sandwiching is monotone in the middle factor for a fixed Hermitian outer operator. -/
theorem sandwich_mono {M P Q : Op d} (hMH : Mᴴ = M) (hPQ : P ≤ Q) :
    M * P * M ≤ M * Q * M := by
  exact sub_nonneg.mp <| by
    simpa [mul_sub, sub_mul] using
      sandwich_nonneg (M := M) (P := Q - P) (sub_nonneg.mpr hPQ) hMH

/-! ### Kronecker product order lemmas -/

/-- Kronecker products preserve positivity. -/
theorem kronecker_nonneg
    {d₁ d₂ : Type*} [hd₁ : Finite d₁] [hd₂ : Finite d₂]
    {A : Op d₁} {B : Op d₂} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ Matrix.kronecker A B := by
  letI : Fintype d₁ := Fintype.ofFinite d₁
  letI : Fintype d₂ := Fintype.ofFinite d₂
  exact
    (Matrix.PosSemidef.kronecker
      (Matrix.nonneg_iff_posSemidef.mp hA)
      (Matrix.nonneg_iff_posSemidef.mp hB)).nonneg

/-- If `0 ≤ A` and `B ≤ 1`, then `A ⊗ B ≤ A ⊗ 1`. -/
theorem kronecker_le_kronecker_right_one
    {d₁ d₂ : Type*} [hd₁ : Finite d₁] [hd₂ : Finite d₂] [DecidableEq d₂]
    {A : Op d₁} {B : Op d₂} (hA : 0 ≤ A) (hB : B ≤ 1) :
    Matrix.kronecker A B ≤ Matrix.kronecker A (1 : Op d₂) := by
  letI : Fintype d₁ := Fintype.ofFinite d₁
  letI : Fintype d₂ := Fintype.ofFinite d₂
  change (Matrix.kronecker A (1 : Op d₂) - Matrix.kronecker A B).PosSemidef
  have hpsd : Matrix.PosSemidef (Matrix.kronecker A (1 - B)) := by
    exact Matrix.nonneg_iff_posSemidef.mp <| kronecker_nonneg hA (sub_nonneg.mpr hB)
  rw [kronecker_sub_right]
  exact hpsd

/-- Kronecker product is monotone in the left factor against a PSD right factor. -/
theorem kronecker_mono_left
    {d₁ d₂ : Type*} [hd₁ : Finite d₁] [hd₂ : Finite d₂]
    {A₁ A₂ : Op d₁} {B : Op d₂} (hA : A₁ ≤ A₂) (hB : 0 ≤ B) :
    Matrix.kronecker A₁ B ≤ Matrix.kronecker A₂ B := by
  letI : Fintype d₁ := Fintype.ofFinite d₁
  letI : Fintype d₂ := Fintype.ofFinite d₂
  change (Matrix.kronecker A₂ B - Matrix.kronecker A₁ B).PosSemidef
  have hpsd : Matrix.PosSemidef (Matrix.kronecker (A₂ - A₁) B) := by
    exact Matrix.nonneg_iff_posSemidef.mp <| kronecker_nonneg (sub_nonneg.mpr hA) hB
  rw [kronecker_sub_left]
  exact hpsd

/-- Simultaneous reindexing of rows and columns preserves positive semidefiniteness. -/
theorem reindex_nonneg {d₁ d₂ : Type*} [Finite d₁] [Finite d₂]
    (e : d₁ ≃ d₂) {A : Op d₁} (hA : 0 ≤ A) :
    0 ≤ Matrix.reindex e e A := by
  classical
  let _ : Fintype d₁ := Fintype.ofFinite d₁
  let _ : Fintype d₂ := Fintype.ofFinite d₂
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  rw [Matrix.reindex_apply]
  exact (Matrix.posSemidef_submatrix_equiv (M := A) e.symm).2
    (Matrix.nonneg_iff_posSemidef.mp hA)

/-- An operator between `0` and `1` dominates its square. -/
theorem sq_le_self [DecidableEq d] {X : Op d} (hX : 0 ≤ X) (hXle : X ≤ 1) :
    X * X ≤ X := by
  have hcomm : Commute X (1 - X) :=
    (Commute.one_right X).sub_right (Commute.refl X)
  have hnonneg : 0 ≤ X * (1 - X) :=
    Commute.mul_nonneg hX (sub_nonneg.mpr hXle) hcomm
  exact sub_nonneg.mp <| by
    simpa [mul_sub] using hnonneg

end MIPStarRE.Quantum
