import Mathlib

/-!
# Finite-dimensional matrix layer for the MIP*=RE project

This file provides a small but honest operator API around `Matrix d d ℂ`
suitable for the finite-dimensional pilot formalization of arXiv:2111.08131.

## Main definitions

* `Op d` — abbreviation for `Matrix d d ℂ`.
* `normalizedTrace` — the normalized trace `τ(A) = tr(A) / d`.
* `tauNormSq` — the squared τ-norm `‖A‖²_τ = τ(A⋆ A)`.
* `IsProj` — predicate for orthogonal projections (Hermitian idempotents).

## Design notes

- We work with `ℂ`-valued matrices throughout, matching the paper.
- We use Mathlib's `Matrix.trace`, `Matrix.PosSemidef`, and `Matrix.IsHermitian`.
- `open scoped ComplexOrder` provides `PartialOrder ℂ`, which is needed by
  `Matrix.PosSemidef` and `Matrix.PosSemidef.trace_nonneg`.
- The matrix partial order from `open scoped MatrixOrder` gives `0 ≤ A` and
  `A ≤ B` for PSD comparisons of matrices.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.Quantum

/-! ### Basic operator type -/

/-- Square complex matrices as the finite-dimensional operator algebra. -/
abbrev Op (d : Type*) := Matrix d d ℂ

/-! ### Normalized trace -/

variable {d : Type*} [Fintype d]

/-- The normalized trace `τ(A) = tr(A) / |d|`. -/
def normalizedTrace (A : Op d) : ℂ :=
  by
    classical
    exact A.trace / (Fintype.card d : ℂ)

@[simp] theorem normalizedTrace_zero : normalizedTrace (0 : Op d) = 0 := by
  simp [normalizedTrace]

@[simp] theorem normalizedTrace_one [DecidableEq d] [Nonempty d] :
    normalizedTrace (1 : Op d) = 1 := by
  unfold normalizedTrace
  rw [Matrix.trace_one]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem normalizedTrace_add (A B : Op d) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  classical
  simp [normalizedTrace, Matrix.trace_add, add_div]

theorem normalizedTrace_sum {ι : Type*} (s : Finset ι) (f : ι → Op d) :
    normalizedTrace (∑ i ∈ s, f i) = ∑ i ∈ s, normalizedTrace (f i) := by
  classical
  simp [normalizedTrace, Matrix.trace_sum, Finset.sum_div]

theorem normalizedTrace_smul (c : ℂ) (A : Op d) :
    normalizedTrace (c • A) = c * normalizedTrace A := by
  classical
  simp [normalizedTrace, Matrix.trace_smul]; ring

theorem normalizedTrace_mul_comm (A B : Op d) :
    normalizedTrace (A * B) = normalizedTrace (B * A) := by
  classical
  simp only [normalizedTrace]; rw [Matrix.trace_mul_comm]

/-! ### Squared τ-norm -/

/--
The squared τ-norm: `‖A‖²_τ = τ(A⋆ A)`.
In finite dimensions this is `(1/d) ∑ᵢⱼ |Aᵢⱼ|²`, the normalized squared
Frobenius norm.
-/
def tauNormSq (A : Op d) : ℂ :=
  normalizedTrace (Aᴴ * A)

theorem tauNormSq_def (A : Op d) : tauNormSq A = normalizedTrace (Aᴴ * A) := rfl

@[simp] theorem tauNormSq_zero : tauNormSq (0 : Op d) = 0 := by simp [tauNormSq]

/-- The τ-norm squared also equals τ(A A⋆) by cyclicity of trace. -/
theorem tauNormSq_eq_normalizedTrace_mul_conjTranspose (A : Op d) :
    tauNormSq A = normalizedTrace (A * Aᴴ) := by
  simp only [tauNormSq]; rw [normalizedTrace_mul_comm]

/-! ### Projector predicate -/

/--
A matrix is an (orthogonal) projection if it is Hermitian and idempotent.
This matches the paper's notion of projective measurements.
-/
structure IsProj (P : Op d) : Prop where
  isHermitian : P.IsHermitian
  idempotent : P * P = P

/-- A projection P satisfies P⋆ = P. -/
theorem IsProj.conjTranspose_eq {P : Op d} (h : IsProj P) : Pᴴ = P :=
  h.isHermitian.eq

/-- For a projection, τ(P²) = τ(P). -/
theorem IsProj.normalizedTrace_sq {P : Op d} (h : IsProj P) :
    normalizedTrace (P * P) = normalizedTrace P := by
  rw [h.idempotent]

/-- For a projection, tauNormSq P = normalizedTrace P. -/
theorem IsProj.tauNormSq_eq {P : Op d} (h : IsProj P) :
    tauNormSq P = normalizedTrace P := by
  simp [tauNormSq, h.conjTranspose_eq, h.idempotent]

/-- The zero matrix is a projection. -/
theorem isProj_zero : IsProj (0 : Op d) where
  isHermitian := Matrix.isHermitian_zero
  idempotent := by simp

/-- The identity matrix is a projection. -/
theorem isProj_one [DecidableEq d] : IsProj (1 : Op d) where
  isHermitian := Matrix.isHermitian_one
  idempotent := by simp

/-- 1 - P is also a projection when P is. -/
theorem IsProj.one_sub [DecidableEq d] {P : Op d} (h : IsProj P) : IsProj (1 - P) where
  isHermitian := Matrix.isHermitian_one.sub h.isHermitian
  idempotent := by
    simp only [mul_sub, sub_mul, mul_one, one_mul]
    rw [h.idempotent]
    abel

/-- Projections are positive semidefinite (in the matrix order). -/
theorem IsProj.nonneg {P : Op d} (h : IsProj P) : 0 ≤ P := by
  classical
  rw [Matrix.nonneg_iff_posSemidef]
  have := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [h.conjTranspose_eq, h.idempotent] at this

/-- A projection satisfies P ≤ 1 in the matrix order. -/
theorem IsProj.le_one [DecidableEq d] {P : Op d} (h : IsProj P) : P ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  have := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
  rwa [h.one_sub.conjTranspose_eq, h.one_sub.idempotent] at this

/-! ### Trace positivity for PSD matrices -/

/-- The trace of a PSD matrix over ℂ is nonneg under ComplexOrder. -/
theorem trace_nonneg_of_posSemidef {A : Op d} (h : A.PosSemidef) : 0 ≤ A.trace :=
  by
    classical
    exact h.trace_nonneg

/-! ### Summation identities for measurement bookkeeping -/

/-- Splitting a double sum into diagonal and off-diagonal parts. -/
theorem sum_eq_diag_add_offDiag {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α → ℂ) :
    ∑ a, ∑ b, f a b =
    ∑ a, f a a + ∑ a, ∑ b ∈ Finset.univ.filter (· ≠ a), f a b := by
  conv_lhs =>
    arg 2; ext a
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = a)]
  simp only [Finset.sum_add_distrib]
  congr 1
  congr 1 with a
  simp [Finset.sum_filter, eq_comm]

/-- Total trace over all answer pairs = total over same + total over different.
    Applied to `τ(Mₐ Nᵦ)`. -/
theorem normalizedTrace_product_split {α : Type*} [Fintype α] [DecidableEq α]
    (M N : α → Op d) :
    normalizedTrace ((∑ a, M a) * (∑ b, N b)) =
    ∑ a, normalizedTrace (M a * N a) +
    ∑ a, ∑ b ∈ Finset.univ.filter (· ≠ a), normalizedTrace (M a * N b) := by
  conv_lhs =>
    rw [Finset.sum_mul_sum, normalizedTrace_sum]
    arg 2; ext i
    rw [normalizedTrace_sum]
  exact sum_eq_diag_add_offDiag (fun a b => normalizedTrace (M a * N b))

/-! ### Almost-projective predicate -/

/--
A matrix is almost-projective with defect `ζ` if its idempotence defect
`‖P² − P‖²_τ` is at most `ζ`.
-/
structure IsAlmostProj (P : Op d) (ζ : ℝ) : Prop where
  isHermitian : P.IsHermitian
  idempotenceDefect : Complex.re (tauNormSq (P * P - P)) ≤ ζ

/-- Every honest projection is almost-projective with defect 0. -/
theorem IsProj.isAlmostProj {P : Op d} (h : IsProj P) : IsAlmostProj P 0 where
  isHermitian := h.isHermitian
  idempotenceDefect := by simp [h.idempotent]

/-! ### Commutation defect -/

/-- The squared τ-norm commutator `‖[A, B]‖²_τ = τ((AB − BA)⋆(AB − BA))`. -/
def commutatorTauNormSq (A B : Op d) : ℂ :=
  tauNormSq (A * B - B * A)

/-- Commuting operators have vanishing commutator norm. -/
theorem commutatorTauNormSq_zero_of_commute {A B : Op d}
    (h : A * B = B * A) : commutatorTauNormSq A B = 0 := by
  simp [commutatorTauNormSq, h]

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
