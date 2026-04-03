import Mathlib

/-!
# Finite-dimensional matrix layer for the MIP*=RE project

An operator API around `Matrix d d ℂ` used by the LDT formalization.

## Main definitions

* `Op d` — abbreviation for `Matrix d d ℂ`.
* `normalizedTrace` — the normalized trace `τ(A) = tr(A) / d`.
* `tauNormSq` — the squared τ-norm `‖A‖²_τ = τ(A⋆ A)`.
* `IsProj` — predicate for orthogonal projections (Hermitian idempotents).
* `SpectralTruncation` — witness for rounding a Hermitian matrix to a projection.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.Quantum

/-! ### Basic operator type -/

/-- Square complex matrices as the finite-dimensional operator algebra. -/
abbrev Op (d : Type*) := Matrix d d ℂ

/-! ### Basic order lemmas -/

variable {d : Type*} [Fintype d]

/-- Sandwiching a PSD operator by a Hermitian operator preserves PSD. -/
theorem sandwich_nonneg {M P : Op d} (hP : 0 ≤ P) (hMH : Mᴴ = M) :
    0 ≤ M * P * M := by
  simpa [hMH] using
    (Matrix.PosSemidef.mul_mul_conjTranspose_same
      (Matrix.nonneg_iff_posSemidef.mp hP) M).nonneg

/-- Sandwiching is monotone in the middle factor for a fixed Hermitian outer operator. -/
theorem sandwich_mono {M P Q : Op d} (hMH : Mᴴ = M) (hPQ : P ≤ Q) :
    M * P * M ≤ M * Q * M := by
  apply sub_nonneg.mp
  have hsand : 0 ≤ M * (Q - P) * M :=
    sandwich_nonneg (M := M) (P := Q - P) (sub_nonneg.mpr hPQ) hMH
  simpa [mul_sub, sub_mul] using hsand

/-- An operator between `0` and `1` dominates its square. -/
theorem sq_le_self [DecidableEq d] {X : Op d} (hX : 0 ≤ X) (hXle : X ≤ 1) :
    X * X ≤ X := by
  have hcomm : Commute X (1 - X) :=
    (Commute.one_right X).sub_right (Commute.refl X)
  have hnonneg : 0 ≤ X * (1 - X) :=
    Commute.mul_nonneg hX (sub_nonneg.mpr hXle) hcomm
  exact sub_nonneg.mp <| by
    simpa [mul_sub] using hnonneg

/-- Kronecker products preserve positivity. -/
theorem kronecker_nonneg
    {d₁ d₂ : Type*} [hd₁ : Finite d₁] [hd₂ : Finite d₂]
    {A : Op d₁} {B : Op d₂} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ Matrix.kronecker A B := by
  letI := hd₁
  letI := hd₂
  exact
    (Matrix.PosSemidef.kronecker
      (Matrix.nonneg_iff_posSemidef.mp hA)
      (Matrix.nonneg_iff_posSemidef.mp hB)).nonneg

/-- If `0 ≤ A` and `B ≤ 1`, then `A ⊗ B ≤ A ⊗ 1`. -/
theorem kronecker_le_kronecker_right_one
    {d₁ d₂ : Type*} [hd₁ : Finite d₁] [hd₂ : Finite d₂] [DecidableEq d₂]
    {A : Op d₁} {B : Op d₂} (hA : 0 ≤ A) (hB : B ≤ 1) :
    Matrix.kronecker A B ≤ Matrix.kronecker A (1 : Op d₂) := by
  letI := hd₁
  letI := hd₂
  change (Matrix.kronecker A (1 : Op d₂) - Matrix.kronecker A B).PosSemidef
  have hrewrite :
      Matrix.kronecker A (1 : Op d₂) - Matrix.kronecker A B =
        Matrix.kronecker A (1 - B) := by
    have hneg : Matrix.kronecker A (-B) = -Matrix.kronecker A B := by
      simpa using (Matrix.kronecker_smul (-1 : ℂ) A B)
    calc
      Matrix.kronecker A (1 : Op d₂) - Matrix.kronecker A B
          = Matrix.kronecker A (1 : Op d₂) + Matrix.kronecker A (-B) := by
              rw [hneg]
              simp [sub_eq_add_neg]
      _ = Matrix.kronecker A (1 - B) := by
            simpa [sub_eq_add_neg] using (Matrix.kronecker_add A 1 (-B)).symm
  have hpsd : Matrix.PosSemidef (Matrix.kronecker A (1 - B)) := by
    exact Matrix.nonneg_iff_posSemidef.mp <| kronecker_nonneg hA (sub_nonneg.mpr hB)
  rwa [hrewrite]

/-- Kronecker product is monotone in the left factor against a PSD right factor. -/
theorem kronecker_mono_left
    {d₁ d₂ : Type*} [hd₁ : Finite d₁] [hd₂ : Finite d₂]
    {A₁ A₂ : Op d₁} {B : Op d₂} (hA : A₁ ≤ A₂) (hB : 0 ≤ B) :
    Matrix.kronecker A₁ B ≤ Matrix.kronecker A₂ B := by
  letI := hd₁
  letI := hd₂
  change (Matrix.kronecker A₂ B - Matrix.kronecker A₁ B).PosSemidef
  have hrewrite :
      Matrix.kronecker A₂ B - Matrix.kronecker A₁ B =
        Matrix.kronecker (A₂ - A₁) B := by
    have hneg : Matrix.kronecker (-A₁) B = -Matrix.kronecker A₁ B := by
      simpa using (Matrix.smul_kronecker (-1 : ℂ) A₁ B)
    calc
      Matrix.kronecker A₂ B - Matrix.kronecker A₁ B
          = Matrix.kronecker A₂ B + Matrix.kronecker (-A₁) B := by
              rw [hneg]
              simp [sub_eq_add_neg]
      _ = Matrix.kronecker (A₂ - A₁) B := by
            simpa [sub_eq_add_neg] using (Matrix.add_kronecker A₂ (-A₁) B).symm
  have hpsd : Matrix.PosSemidef (Matrix.kronecker (A₂ - A₁) B) := by
    exact Matrix.nonneg_iff_posSemidef.mp <| kronecker_nonneg (sub_nonneg.mpr hA) hB
  rwa [hrewrite]

/-! ### Normalized trace -/

/-- The normalized trace `τ(A) = tr(A) / |d|`. -/
noncomputable def normalizedTrace (A : Op d) : ℂ :=
  A.trace / (Fintype.card d : ℂ)

@[simp] theorem normalizedTrace_zero : normalizedTrace (0 : Op d) = 0 := by
  simp [normalizedTrace]

@[simp] theorem normalizedTrace_one [DecidableEq d] [Nonempty d] :
    normalizedTrace (1 : Op d) = 1 := by
  unfold normalizedTrace
  rw [Matrix.trace_one]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem normalizedTrace_add (A B : Op d) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_add, add_div]

theorem normalizedTrace_sub (A B : Op d) :
    normalizedTrace (A - B) = normalizedTrace A - normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_sub, sub_div]

theorem normalizedTrace_smul (c : ℂ) (A : Op d) :
    normalizedTrace (c • A) = c * normalizedTrace A := by
  simp [normalizedTrace, Matrix.trace_smul]; ring

theorem normalizedTrace_mul_comm (A B : Op d) :
    normalizedTrace (A * B) = normalizedTrace (B * A) := by
  simp only [normalizedTrace]; rw [Matrix.trace_mul_comm]

/-! ### Squared τ-norm -/

/--
The squared τ-norm: `‖A‖²_τ = τ(A⋆ A)`.
In finite dimensions this is `(1/d) ∑ᵢⱼ |Aᵢⱼ|²`, the normalized squared
Frobenius norm.
-/
noncomputable def tauNormSq (A : Op d) : ℂ :=
  normalizedTrace (Aᴴ * A)

@[simp] theorem tauNormSq_zero : tauNormSq (0 : Op d) = 0 := by simp [tauNormSq]

/-! ### Projector predicate -/

/--
A matrix is an (orthogonal) projection if it is Hermitian and idempotent.
-/
structure IsProj (P : Op d) : Prop where
  isHermitian : P.IsHermitian
  idempotent : P * P = P

/-! ### Spectral truncation -/

/--
A spectral truncation witness records the passage from a Hermitian matrix `source`
to a projection `target` by truncating the spectrum to `{0, 1}`: eigenvalues
above `1/2` are rounded to `1`, those below are rounded to `0`.

The key output is the τ-distance bound between source and target.
-/
structure SpectralTruncation (source target : Op d) : Prop where
  sourceHermitian : source.IsHermitian
  targetProj : IsProj target
  tauDistanceBound : Complex.re (tauNormSq (source - target)) ≤
    Complex.re (tauNormSq (source * source - source))

end MIPStarRE.Quantum
