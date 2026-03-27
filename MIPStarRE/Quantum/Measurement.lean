import MIPStarRE.Quantum.FiniteMatrix

/-!
# Matrix-valued measurements for the MIP*=RE project

This file provides the matrix-valued measurement layer used by the LDT
formalization.

## Main definitions

* `Submeasurement` — a family of PSD matrices summing to at most the identity.
* `Measurement` — a family of PSD matrices summing to exactly the identity.
* `Submeasurement.postprocess` — data-processed measurement via answer relabeling.
* `inconsistency` — the off-diagonal mass `∑_{a≠b} τ(M_a N_b)`.
* `diagOverlap` — the diagonal mass `∑_a τ(M_a N_a)`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.Quantum

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Submeasurements and measurements -/

/--
A submeasurement on a finite answer type `α` is a family of PSD matrices
`M : α → Op d` with `∑ a, M a ≤ 1`.
-/
structure Submeasurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The effect operators. -/
  effect : α → Op d
  /-- Each effect is positive semidefinite. -/
  pos : ∀ a, 0 ≤ effect a
  /-- The effects sum to at most the identity. -/
  sum_le_one : ∑ a, effect a ≤ 1

/--
A measurement is a submeasurement whose effects sum exactly to the identity.
-/
structure Measurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d]
    extends Submeasurement α d where
  /-- The effects sum to the identity. -/
  sum_eq_one : ∑ a, effect a = 1

namespace Submeasurement

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The total operator `∑ a, M_a`. -/
noncomputable def total (M : Submeasurement α d) : Op d :=
  ∑ a, M.effect a

/--
Data processing: relabel the answer set by `f : α → β`, summing the effects over
fibers.
-/
noncomputable def postprocess [DecidableEq α] [DecidableEq β]
    (M : Submeasurement α d) (f : α → β) : Submeasurement β d where
  effect b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
  pos b := Finset.sum_nonneg fun a _ => M.pos a
  sum_le_one := by
    calc
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
          = ∑ a, M.effect a := Finset.sum_fiberwise Finset.univ f M.effect
      _ ≤ 1 := M.sum_le_one

end Submeasurement

/-! ## Overlap definitions -/

section Overlap

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The off-diagonal overlap mass `∑_{a ≠ b} τ(M_a N_b)`. -/
noncomputable def inconsistency (M N : α → Op d) : ℂ :=
  ∑ a, ∑ b ∈ Finset.univ.filter (fun b => b ≠ a), normalizedTrace (M a * N b)

/-- The diagonal overlap mass `∑_a τ(M_a N_a)`. -/
noncomputable def diagOverlap (M N : α → Op d) : ℂ :=
  ∑ a, normalizedTrace (M a * N a)

end Overlap

end MIPStarRE.Quantum
