import MIPStarRE.Quantum.FiniteMatrix
import MIPStarRE.Quantum.OutcomeFamily

/-!
# Matrix-valued measurements for the MIP*=RE project

This file provides the matrix-valued measurement layer used throughout the
finite-dimensional pilot formalization of arXiv:2111.08131.

## Main definitions

* `Submeasurement` — a family of PSD matrices summing to at most the identity.
* `Measurement` — a family of PSD matrices summing to exactly the identity.
* `Submeasurement.postprocess` — data-processed measurement via answer relabeling.
* `inconsistency` — the off-diagonal mass `∑_{a≠b} τ(M_a N_b)`.
* `diagOverlap` — the diagonal mass `∑_a τ(M_a N_a)`.

## Main results

* `Submeasurement.postprocess_total` — postprocessing preserves the total effect.
* `Measurement.postprocess` — data processing preserves the measurement property.
* `inconsistency_add_diagOverlap` — off-diagonal plus diagonal mass recovers the
  total overlap `τ((∑ M_a)(∑ N_b))`.

## Design notes

- We work concretely with `Op d = Matrix d d ℂ` and the matrix partial order.
- The generic `OutcomeFamily` from `Quantum/OutcomeFamily.lean` provides the
  purely combinatorial postprocessing; this file adds the PSD/normalization layer.
- We stop short of full closeness/consistency inequalities for now; the current
  milestone is an honest matrix-valued API together with the first bookkeeping
  identities from Section 2.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

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
def total (M : Submeasurement α d) : Op d :=
  ∑ a, M.effect a

/-- The total operator of a submeasurement is bounded by the identity. -/
theorem total_le_one (M : Submeasurement α d) : M.total ≤ 1 :=
  M.sum_le_one

/-- Forget positivity and normalization, retaining only the outcome table. -/
def toOutcomeFamily (M : Submeasurement α d) : OutcomeFamily Unit α (Op d) where
  effect _ a := M.effect a

/--
Data processing: relabel the answer set by `f : α → β`, summing the effects over
fibers. This is the `M_[f | b]` construction from Section 2 of the paper.
-/
def postprocess [DecidableEq α] [DecidableEq β]
    (M : Submeasurement α d) (f : α → β) : Submeasurement β d where
  effect b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
  pos b := Finset.sum_nonneg fun a _ => M.pos a
  sum_le_one := by
    calc
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
          = ∑ a, M.effect a := Finset.sum_fiberwise Finset.univ f M.effect
      _ ≤ 1 := M.sum_le_one

@[simp] theorem postprocess_effect [DecidableEq α] [DecidableEq β]
    (M : Submeasurement α d) (f : α → β) (b : β) :
    (M.postprocess f).effect b = ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a :=
  rfl

/-- Postprocessing preserves the total effect operator. -/
theorem postprocess_total [DecidableEq α] [DecidableEq β]
    (M : Submeasurement α d) (f : α → β) :
    (M.postprocess f).total = M.total := by
  simpa [total, toOutcomeFamily, OutcomeFamily.total] using
    (OutcomeFamily.postprocess_total (M := M.toOutcomeFamily) (f := f) ())

end Submeasurement

namespace Measurement

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The total operator of a measurement is the identity. -/
theorem total_eq_one (M : Measurement α d) : M.toSubmeasurement.total = 1 := by
  simpa [Submeasurement.total] using M.sum_eq_one

/-- Postprocessing a measurement yields another measurement. -/
def postprocess [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) : Measurement β d where
  toSubmeasurement := M.toSubmeasurement.postprocess f
  sum_eq_one := by
    calc
      (M.toSubmeasurement.postprocess f).total = M.toSubmeasurement.total :=
        M.toSubmeasurement.postprocess_total f
      _ = 1 := M.total_eq_one

end Measurement

/-! ## First Section 2 bookkeeping layer -/

section Overlap

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The off-diagonal overlap mass `∑_{a ≠ b} τ(M_a N_b)`. -/
def inconsistency (M N : α → Op d) : ℂ :=
  ∑ a, ∑ b ∈ Finset.univ.filter (fun b => b ≠ a), normalizedTrace (M a * N b)

/-- The diagonal overlap mass `∑_a τ(M_a N_a)`. -/
def diagOverlap (M N : α → Op d) : ℂ :=
  ∑ a, normalizedTrace (M a * N a)

/--
The diagonal and off-diagonal parts together recover the total overlap
`τ((∑_a M_a)(∑_b N_b))`.
-/
theorem inconsistency_add_diagOverlap (M N : α → Op d) :
    inconsistency M N + diagOverlap M N =
      normalizedTrace ((∑ a, M a) * (∑ b, N b)) := by
  rw [normalizedTrace_product_split]
  unfold inconsistency diagOverlap
  ring

-- Section 2 data processing will eventually compare `inconsistency` before and
-- after `Submeasurement.postprocess`. The current repository milestone stops at
-- the exact splitting identity above; the monotonicity inequality needs an
-- additional nonnegativity argument over fibered sums and is left for the next
-- pass.

end Overlap

end MIPStarRE.Quantum
