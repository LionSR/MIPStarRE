import MIPStarRE.Quantum.FiniteMatrix.Basic

/-!
# Normalized trace, projectors, and spectral truncation

This module contains the normalized trace `τ`, the squared `τ`-norm, the
local orthogonal-projection predicate, and the spectral-truncation witness used
in the low individual degree test formalization.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp

namespace MIPStarRE.Quantum

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

/-- Simultaneous reindexing of rows and columns preserves the normalized trace. -/
theorem normalizedTrace_reindex {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]
    (e : d₁ ≃ d₂) (A : Op d₁) :
    normalizedTrace (Matrix.reindex e e A) = normalizedTrace A := by
  have hcard : Fintype.card d₂ = Fintype.card d₁ := Fintype.card_congr e.symm
  unfold normalizedTrace
  rw [Matrix.trace_reindex]
  simp [hcard]

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

/-- Orthogonal projections are positive semidefinite operators. -/
lemma IsProj.nonneg (P : Op d) (hP : IsProj P) :
    0 ≤ P := by
  exact hP.isStarProjection.nonneg

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
