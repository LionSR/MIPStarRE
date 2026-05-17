import Mathlib

/-!
# Finite-dimensional matrix layer for the MIP*=RE project

This file provides the basic operator API around `Matrix d d ℂ` used throughout the LDT
formalization.

## Main definitions

* `Op d` — abbreviation for `Matrix d d ℂ`.
* `normalizedTrace` — the normalized trace `τ(A) = tr(A) / d`.
* `tauNormSq` — the squared τ-norm `‖A‖²_τ = τ(A⋆ A)`.
* `IsProj` — predicate for orthogonal projections.
* `SpectralTruncation` — witness for rounding a Hermitian matrix to a projection.

## References

This file packages the finite-dimensional matrix and PSD API from Mathlib for the
project's quantum layer and the LDT development formalizing `references/ldt-paper/`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace Matrix

/-! ### Trace bookkeeping -/

/-- Reindexing rows and columns by the same equivalence preserves matrix trace.

This generic matrix lemma is used when moving between equivalent finite index
presentations of the same operator. -/
theorem trace_reindex {α β R : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid R] (e : α ≃ β) (M : Matrix α α R) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply]
  rw [← e.symm.sum_comp (fun i : α => M i i)]
  rfl

/-- The trace pairing of two block-diagonal matrices is the sum of the trace
pairings of the corresponding diagonal blocks. -/
theorem trace_blockDiagonal_mul {o m R : Type*}
    [Fintype o] [DecidableEq o] [Fintype m] [NonUnitalNonAssocSemiring R]
    (B D : o → Matrix m m R) :
    Matrix.trace (Matrix.blockDiagonal B * Matrix.blockDiagonal D) =
      ∑ b : o, Matrix.trace (B b * D b) := by
  rw [← Matrix.blockDiagonal_mul B D, Matrix.trace_blockDiagonal]

end Matrix

namespace MIPStarRE.Quantum

/-! ### Basic operator type -/

/-- Square complex matrices as the finite-dimensional operator algebra. -/
abbrev Op (d : Type*) := Matrix d d ℂ

/-! ### Kronecker product bookkeeping -/

/-- Kronecker product is additive in the right factor, rewritten for subtraction. -/
theorem kronecker_sub_right
    {d₁ d₂ : Type*} {A : Op d₁} {B₁ B₂ : Op d₂} :
    Matrix.kronecker A B₁ - Matrix.kronecker A B₂ =
      Matrix.kronecker A (B₁ - B₂) := by
  have hneg : Matrix.kronecker A (-B₂) = -Matrix.kronecker A B₂ := by
    simpa using (Matrix.kronecker_smul (-1 : ℂ) A B₂)
  calc
    Matrix.kronecker A B₁ - Matrix.kronecker A B₂
        = Matrix.kronecker A B₁ + Matrix.kronecker A (-B₂) := by
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = Matrix.kronecker A (B₁ - B₂) := by
          simpa [sub_eq_add_neg] using (Matrix.kronecker_add A B₁ (-B₂)).symm

/-- Kronecker product is additive in the left factor, rewritten for subtraction. -/
theorem kronecker_sub_left
    {d₁ d₂ : Type*} {A₁ A₂ : Op d₁} {B : Op d₂} :
    Matrix.kronecker A₁ B - Matrix.kronecker A₂ B =
      Matrix.kronecker (A₁ - A₂) B := by
  have hneg : Matrix.kronecker (-A₂) B = -Matrix.kronecker A₂ B := by
    simpa using (Matrix.smul_kronecker (-1 : ℂ) A₂ B)
  calc
    Matrix.kronecker A₁ B - Matrix.kronecker A₂ B
        = Matrix.kronecker A₁ B + Matrix.kronecker (-A₂) B := by
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = Matrix.kronecker (A₁ - A₂) B := by
          simpa [sub_eq_add_neg] using (Matrix.add_kronecker A₁ (-A₂) B).symm

/-! ### Basic order lemmas -/

variable {d : Type*} [Fintype d]

/-- Sandwiching a PSD operator by a Hermitian operator preserves positivity. -/
theorem sandwich_nonneg {M P : Op d} (hP : 0 ≤ P) (hMH : Mᴴ = M) :
    0 ≤ M * P * M := by
  simpa [hMH] using
    (Matrix.PosSemidef.mul_mul_conjTranspose_same
      (Matrix.nonneg_iff_posSemidef.mp hP) M).nonneg

/-- Sandwiching is monotone in the middle factor for a fixed Hermitian outer operator. -/
theorem sandwich_mono {M P Q : Op d} (hMH : Mᴴ = M) (hPQ : P ≤ Q) :
    M * P * M ≤ M * Q * M := by
  exact sub_nonneg.mp <| by
    simpa [mul_sub, sub_mul] using
      sandwich_nonneg (M := M) (P := Q - P) (sub_nonneg.mpr hPQ) hMH

/-- The real trace pairing of two positive semidefinite operators is
nonnegative.

This is the finite-dimensional Hilbert-Schmidt positivity fact used in weak
duality arguments: if \(A,B\geq 0\), then
\(\operatorname{Re}\operatorname{Tr}(AB)\geq 0\). -/
theorem trace_mul_nonneg_of_nonneg {A B : Op d} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ Complex.re (Matrix.trace (A * B)) := by
  letI : DecidableEq d := Classical.decEq d
  letI : NonnegSpectrumClass ℝ (Op d) :=
    Matrix.instNonnegSpectrumClass (𝕜 := ℂ) (n := d)
  letI : NonUnitalContinuousFunctionalCalculus ℝ (Op d) IsSelfAdjoint :=
    ContinuousFunctionalCalculus.toNonUnital (R := ℝ) (A := Op d) (p := IsSelfAdjoint)
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB
  subst B
  rw [Matrix.star_eq_conjTranspose]
  have htrace_nonneg :
      (0 : ℂ) ≤ Matrix.trace (Y * A * Yᴴ) :=
    (Matrix.PosSemidef.mul_mul_conjTranspose_same
      (Matrix.nonneg_iff_posSemidef.mp hA) Y).trace_nonneg
  have hre : 0 ≤ Complex.re (Matrix.trace (Y * A * Yᴴ)) :=
    (Complex.nonneg_iff.mp htrace_nonneg).1
  have htrace :
      Matrix.trace (A * (Yᴴ * Y)) = Matrix.trace (Y * A * Yᴴ) := by
    calc
      Matrix.trace (A * (Yᴴ * Y)) = Matrix.trace ((A * Yᴴ) * Y) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (Y * (A * Yᴴ)) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (Y * A * Yᴴ) := by
        simp [Matrix.mul_assoc]
  simpa [htrace] using hre

/-- An operator between `0` and `1` dominates its square. -/
theorem sq_le_self [DecidableEq d] {X : Op d} (hX : 0 ≤ X) (hXle : X ≤ 1) :
    X * X ≤ X := by
  letI : NonnegSpectrumClass ℝ (Op d) :=
    Matrix.instNonnegSpectrumClass (𝕜 := ℂ) (n := d)
  letI : NonUnitalContinuousFunctionalCalculus ℝ (Op d) IsSelfAdjoint :=
    ContinuousFunctionalCalculus.toNonUnital (R := ℝ) (A := Op d) (p := IsSelfAdjoint)
  have hcomm : Commute X (1 - X) :=
    (Commute.one_right X).sub_right (Commute.refl X)
  have hnonneg : 0 ≤ X * (1 - X) :=
    Commute.mul_nonneg hX (sub_nonneg.mpr hXle) hcomm
  exact sub_nonneg.mp <| by
    simpa [mul_sub] using hnonneg

/-- A positive operator annihilated on the right by an operator dominating the
identity must vanish. -/
theorem eq_zero_of_nonneg_mul_eq_zero_of_one_le [DecidableEq d]
    {S Z : Op d} (hS : 0 ≤ S) (hZ : (1 : Op d) ≤ Z) (hSZ : S * Z = 0) :
    S = 0 := by
  letI : NonnegSpectrumClass ℝ (Op d) :=
    Matrix.instNonnegSpectrumClass (𝕜 := ℂ) (n := d)
  letI : NonUnitalContinuousFunctionalCalculus ℝ (Op d) IsSelfAdjoint :=
    ContinuousFunctionalCalculus.toNonUnital (R := ℝ) (A := Op d) (p := IsSelfAdjoint)
  have hZ_nonneg : 0 ≤ Z :=
    le_trans Matrix.PosSemidef.one.nonneg hZ
  have hS_herm : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp hS).isHermitian.eq
  have hZ_herm : Zᴴ = Z :=
    (Matrix.nonneg_iff_posSemidef.mp hZ_nonneg).isHermitian.eq
  have hZS : Z * S = 0 := by
    have hconj : (S * Z)ᴴ = 0 := by
      rw [hSZ]
      simp
    simpa [Matrix.conjTranspose_mul, hS_herm, hZ_herm] using hconj
  have hcomm : Commute S Z :=
    hSZ.trans hZS.symm
  have hcommSub : Commute S (Z - 1) :=
    hcomm.sub_right (Commute.one_right S)
  have hneg_nonneg : 0 ≤ -S := by
    have hprod : 0 ≤ S * (Z - 1) :=
      Commute.mul_nonneg hS (sub_nonneg.mpr hZ) hcommSub
    have hprod_eq : S * (Z - 1) = -S := by
      rw [mul_sub, hSZ, Matrix.mul_one, zero_sub]
    simpa [hprod_eq] using hprod
  exact le_antisymm (neg_nonneg.mp hneg_nonneg) hS

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

end MIPStarRE.Quantum

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
    convert hsub using 1
    ext i j
    simp [e, Matrix.blockDiagonal_apply]
  · exact Matrix.blockDiagonal_nonneg B

end Matrix

namespace MIPStarRE.Quantum

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

variable {d : Type*} [Fintype d]

/-! ### Normalized trace -/

/-- The normalized trace `τ(A) = tr(A) / |d|`. -/
noncomputable def normalizedTrace (A : Op d) : ℂ :=
  A.trace / (Fintype.card d : ℂ)

/-- The normalized trace of the zero operator is zero. -/
@[simp] theorem normalizedTrace_zero : normalizedTrace (0 : Op d) = 0 := by
  simp [normalizedTrace]

/-- The normalized trace of the identity operator is one. -/
@[simp] theorem normalizedTrace_one [DecidableEq d] [Nonempty d] :
    normalizedTrace (1 : Op d) = 1 := by
  unfold normalizedTrace
  rw [Matrix.trace_one]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- The normalized trace is additive. -/
theorem normalizedTrace_add (A B : Op d) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_add, add_div]

/-- The normalized trace sends subtraction to subtraction. -/
theorem normalizedTrace_sub (A B : Op d) :
    normalizedTrace (A - B) = normalizedTrace A - normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_sub, sub_div]

/-- Scalar multiplication pulls out of the normalized trace. -/
theorem normalizedTrace_smul (c : ℂ) (A : Op d) :
    normalizedTrace (c • A) = c * normalizedTrace A := by
  simp [normalizedTrace, Matrix.trace_smul]
  ring

/-- The normalized trace is invariant under swapping two multiplicative factors. -/
theorem normalizedTrace_mul_comm (A B : Op d) :
    normalizedTrace (A * B) = normalizedTrace (B * A) := by
  simp only [normalizedTrace]
  rw [Matrix.trace_mul_comm]

/-! ### Squared τ-norm -/

/--
The squared τ-norm: `‖A‖²_τ = τ(A⋆ A)`.
In finite dimensions this is `(1/d) ∑ᵢⱼ |Aᵢⱼ|²`, the normalized squared
Frobenius norm.
-/
noncomputable def tauNormSq (A : Op d) : ℂ :=
  normalizedTrace (Aᴴ * A)

/-- The squared τ-norm of the zero operator is zero. -/
@[simp] theorem tauNormSq_zero : tauNormSq (0 : Op d) = 0 := by
  simp [tauNormSq]

/-! ### Projector predicate -/

/-- A matrix is an orthogonal projection when it is Hermitian and idempotent. -/
structure IsProj (P : Op d) : Prop where
  /-- The projection is Hermitian. -/
  isHermitian : P.IsHermitian
  /-- The projection is idempotent. -/
  idempotent : P * P = P

/-- A projective operator in the local matrix sense is a Mathlib star projection. -/
lemma IsProj.isStarProjection {P : Op d} (hP : IsProj P) : IsStarProjection P where
  isIdempotentElem := hP.idempotent
  isSelfAdjoint := hP.isHermitian.isSelfAdjoint

/-- A Mathlib star projection is a projective operator in the local matrix sense. -/
lemma IsProj.of_isStarProjection {P : Op d} (hP : IsStarProjection P) : IsProj P where
  isHermitian := hP.isSelfAdjoint.isHermitian
  idempotent := hP.isIdempotentElem

/-! ### Spectral truncation -/

/--
A spectral truncation witness records the passage from a Hermitian matrix `source`
to a projection `target` by truncating the spectrum to `{0, 1}`: eigenvalues
above `1 / 2` are rounded to `1`, and those below are rounded to `0`.

The key output is the τ-distance bound between `source` and `target`.
-/
structure SpectralTruncation (source target : Op d) : Prop where
  /-- The source matrix is Hermitian. -/
  sourceHermitian : source.IsHermitian
  /-- The target matrix is an orthogonal projection. -/
  targetProj : IsProj target
  /-- Spectral truncation does not increase the defect measured by `tauNormSq`. -/
  tauDistanceBound : Complex.re (tauNormSq (source - target)) ≤
    Complex.re (tauNormSq (source * source - source))

end MIPStarRE.Quantum
