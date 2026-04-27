import MIPStarRE.Quantum.FiniteMatrix

/-!
# Matrix-valued measurements for the MIP*=RE project

This file provides the matrix-valued measurement layer used by the LDT formalization.

## Main definitions

* `Submeasurement` — a family of PSD matrices summing to at most the identity.
* `Measurement` — a family of PSD matrices summing to exactly the identity.
* `Submeasurement.postprocess` — data-processed submeasurements via answer relabeling.
* `Measurement.postprocess` — the paper's postprocessing proposition for complete POVMs.
* `inconsistency` — the off-diagonal mass `∑_{a ≠ b} τ(M_a N_b)`.
* `diagOverlap` — the diagonal mass `∑_a τ(M_a N_a)`.

## References

This file builds the project's finite-dimensional measurement layer on top of
`MIPStarRE/Quantum/FiniteMatrix.lean` for the quantum formalization in
`references/ldt-paper/`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.Quantum

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

/-! ## Totals and postprocessing -/

namespace Submeasurement

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Totals and postprocessing -/

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

theorem total_eq_sum (M : Submeasurement α d) :
    M.total = ∑ a, M.effect a :=
  rfl

/-- Restatement of `sum_le_one` in terms of the named total operator. -/
theorem total_le_one (M : Submeasurement α d) :
    M.total ≤ 1 := by
  simpa [total] using M.sum_le_one

/-- Postprocessing preserves the sum of all effects. -/
theorem postprocess_sum_eq [DecidableEq α] [DecidableEq β]
    (M : Submeasurement α d) (f : α → β) :
    ∑ a, M.effect a = ∑ b, (M.postprocess f).effect b :=
  (Finset.sum_fiberwise Finset.univ f M.effect).symm

/-- Postprocessing preserves the named total operator. -/
theorem postprocess_total [DecidableEq α] [DecidableEq β]
    (M : Submeasurement α d) (f : α → β) :
    (M.postprocess f).total = M.total := by
  simpa [total] using (M.postprocess_sum_eq f).symm

end Submeasurement

namespace Measurement

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/--
Build a complete measurement from effects whose sum is exactly the identity.

This constructor keeps the equality proof as the primary hypothesis and derives
the inherited submeasurement inequality automatically.  It is useful at paper
sites that are explicitly POVMs rather than relaxed sub-POVMs.
-/
def ofSumEqOne (effect : α → Op d) (pos : ∀ a, 0 ≤ effect a)
    (sum_eq_one : ∑ a, effect a = 1) : Measurement α d where
  effect := effect
  pos := pos
  sum_le_one := le_of_eq sum_eq_one
  sum_eq_one := sum_eq_one

/-- The named total of a complete measurement is the identity. -/
theorem total_eq_one (M : Measurement α d) :
    M.total = 1 :=
  M.sum_eq_one

/--
Postprocess a complete measurement by relabeling outcomes.

This formalizes `references/ldt-paper/preliminaries.tex:169--180`: regrouping
the effects along the fibers of `f` preserves the total operator, so a POVM
remains a POVM after postprocessing.
-/
noncomputable def postprocess [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) : Measurement β d where
  toSubmeasurement := M.toSubmeasurement.postprocess f
  sum_eq_one := by
    calc
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
          = ∑ a, M.effect a := Finset.sum_fiberwise Finset.univ f M.effect
      _ = 1 := M.sum_eq_one

@[simp] theorem postprocess_effect [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) (b : β) :
    (M.postprocess f).effect b =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a :=
  rfl

@[simp] theorem postprocess_to_submeasurement [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) :
    (M.postprocess f).toSubmeasurement = M.toSubmeasurement.postprocess f :=
  rfl

end Measurement

/-! ## Overlap definitions -/

section Overlap

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The off-diagonal overlap mass `∑_{a ≠ b} τ(M_a N_b)`. -/
noncomputable def inconsistency (M N : α → Op d) : ℂ :=
  ∑ a, ∑ b ∈ Finset.univ.filter (fun b => b ≠ a), normalizedTrace (M a * N b)

/-- The diagonal overlap mass `∑_a τ(M_a N_a)`. -/
noncomputable def diagOverlap (M N : α → Op d) : ℂ :=
  ∑ a, normalizedTrace (M a * N a)

end Overlap

end MIPStarRE.Quantum
