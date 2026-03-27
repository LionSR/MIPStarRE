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

/-! ### Normalized trace -/

variable {d : Type*} [Fintype d]

/-- The normalized trace `τ(A) = tr(A) / |d|`. -/
def normalizedTrace (A : Op d) : ℂ :=
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
def tauNormSq (A : Op d) : ℂ :=
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
