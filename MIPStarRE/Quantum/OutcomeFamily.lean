import Mathlib

/-!
# Generic outcome families indexed by questions and answers

This file provides a lightweight, purely algebraic outcome-family abstraction:
a table of "effects" indexed by a question type and an answer type. The ambient
effect type is left completely abstract — positivity, traces, and norms are all
handled downstream.

## Main definitions

* `OutcomeFamily` — a question × answer table of effects.
* `OutcomeFamily.postprocess` — relabel answers by summing over fibers.
* `OutcomeFamily.total` — sum all effects at a fixed question.

## Design note

This file is deliberately operator-agnostic. The matrix-valued measurement
layer in `Quantum/Measurement.lean` specializes the effect type and adds
positivity/normalization conditions.
-/

open scoped BigOperators

namespace MIPStarRE.Quantum

/--
A finite family of effects indexed by questions and answers.

Later files specialize `Effect` to a concrete operator type (e.g. `Matrix d d ℂ`)
and add analytic side conditions. This records only the combinatorial data of a
measurement table.
-/
structure OutcomeFamily (Question Answer Effect : Type*) where
  effect : Question → Answer → Effect

namespace OutcomeFamily

variable {Question Answer Answer' Effect Effect' : Type*}

@[ext] theorem ext {M N : OutcomeFamily Question Answer Effect}
    (h : ∀ q a, M.effect q a = N.effect q a) : M = N := by
  cases M
  cases N
  congr
  funext q a
  exact h q a

/-- Evaluate the family at a fixed question. -/
def atQuestion (M : OutcomeFamily Question Answer Effect) (q : Question) : Answer → Effect :=
  M.effect q

/-- Apply a map to every effect in the family. -/
def mapEffect (f : Effect → Effect')
    (M : OutcomeFamily Question Answer Effect) : OutcomeFamily Question Answer Effect' where
  effect q a := f (M.effect q a)

@[simp] theorem mapEffect_effect (f : Effect → Effect')
    (M : OutcomeFamily Question Answer Effect) (q : Question) (a : Answer) :
    (M.mapEffect f).effect q a = f (M.effect q a) :=
  rfl

/-- Sum all effects attached to a fixed question. -/
def total [Fintype Answer] [Zero Effect] [AddCommMonoid Effect]
    (M : OutcomeFamily Question Answer Effect) (q : Question) : Effect :=
  ∑ a : Answer, M.effect q a

/--
Relabel the answers of an outcome family by summing over the fibers of a map.
This is the combinatorial core of the processed-measurement construction
(Section 2, arXiv:2111.08131).
-/
def postprocess [Fintype Answer] [DecidableEq Answer]
    [Zero Effect] [AddCommMonoid Effect] [DecidableEq Answer']
    (M : OutcomeFamily Question Answer Effect) (f : Answer → Answer') :
    OutcomeFamily Question Answer' Effect where
  effect q b := ∑ a ∈ Finset.univ.filter fun a => f a = b, M.effect q a

@[simp] theorem postprocess_effect [Fintype Answer] [DecidableEq Answer]
    [Zero Effect] [AddCommMonoid Effect] [DecidableEq Answer']
    (M : OutcomeFamily Question Answer Effect) (f : Answer → Answer')
    (q : Question) (b : Answer') :
    (M.postprocess f).effect q b =
      ∑ a ∈ Finset.univ.filter fun a => f a = b, M.effect q a :=
  rfl

@[simp] theorem postprocess_id [Fintype Answer] [DecidableEq Answer]
    [Zero Effect] [AddCommMonoid Effect]
    (M : OutcomeFamily Question Answer Effect) :
    M.postprocess id = M := by
  ext q a
  rw [postprocess_effect]
  refine Finset.sum_eq_single_of_mem a ?_ ?_
  · simp
  · intro b hb hba
    have : b = a := by simpa using hb
    exact (hba this).elim

/-- Aggregate the outcomes satisfying a predicate into a single effect. -/
def sumOver [Fintype Answer] [DecidableEq Answer]
    [Zero Effect] [AddCommMonoid Effect]
    (M : OutcomeFamily Question Answer Effect) (q : Question) (p : Answer → Prop)
    [DecidablePred p] : Effect :=
  ∑ a ∈ Finset.univ.filter p, M.effect q a

/-- The total is the sum of all effects. -/
theorem total_eq_sum [Fintype Answer] [Zero Effect] [AddCommMonoid Effect]
    (M : OutcomeFamily Question Answer Effect) (q : Question) :
    M.total q = ∑ a, M.effect q a :=
  rfl

/--
Postprocessing preserves the total: the sum of all processed effects equals
the sum of all original effects. This is the key bookkeeping identity underlying
data processing for consistency.
-/
theorem postprocess_total [Fintype Answer] [Fintype Answer']
    [DecidableEq Answer] [DecidableEq Answer']
    [AddCommMonoid Effect]
    (M : OutcomeFamily Question Answer Effect) (f : Answer → Answer')
    (q : Question) :
    (M.postprocess f).total q = M.total q := by
  simp only [total, postprocess_effect]
  exact Finset.sum_fiberwise Finset.univ f (fun a => M.effect q a)

end OutcomeFamily

/-!
## Off-diagonal sums and data processing

This section captures the core combinatorial fact behind the data-processing
inequality for consistency (Proposition 2.3 / `lem:data-processing` in
arXiv:2111.08131): merging answer classes cannot increase the off-diagonal mass.

We work with a generic kernel `w : α → α → R` and a relabeling map `f : α → β`.
The relabeled off-diagonal sum only keeps ordered pairs with `f a ≠ f a'`, so it
is a subsum of the full off-diagonal sum over `a ≠ a'`.
-/

section OffDiag

/--
The off-diagonal sum of a kernel `w : α → α → R` is
`∑_{a} ∑_{a' ≠ a} w a a'`.
-/
def offDiagSum {α : Type*} [Fintype α] [DecidableEq α] {R : Type*} [AddCommMonoid R]
    (w : α → α → R) : R :=
  ∑ a : α, ∑ a' ∈ Finset.univ.filter (· ≠ a), w a a'

/--
The relabeled off-diagonal sum of a kernel `w : α → α → R` under `f : α → β` is
`∑_{a} ∑_{a' : f a' ≠ f a} w a a'`.
-/
def offDiagSumRelabel {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    {R : Type*} [AddCommMonoid R]
    (w : α → α → R) (f : α → β) : R :=
  ∑ a : α, ∑ a' ∈ Finset.univ.filter (fun a' => f a' ≠ f a), w a a'

/--
Data-processing inequality for off-diagonal sums.

If `w` is pointwise nonnegative, then restricting the sum to pairs with
`f a ≠ f a'` can only decrease the off-diagonal mass, because `f a ≠ f a'`
implies `a ≠ a'`.
-/
theorem offDiagSumRelabel_le {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] {R : Type*}
    [AddCommMonoid R] [PartialOrder R] [AddLeftMono R]
    (w : α → α → R) (f : α → β)
    (hw : ∀ a a', 0 ≤ w a a') :
    offDiagSumRelabel w f ≤ offDiagSum w := by
  unfold offDiagSumRelabel offDiagSum
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a' ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha' ⊢
    exact fun h => ha' (congrArg f h)
  · intro a' _ _
    exact hw a a'

-- In the matrix-valued measurement layer, the next step will be to instantiate
-- this theorem with a concrete nonnegative overlap kernel built from processed
-- measurement effects. That requires a separate positivity lemma for the scalar
-- overlap quantity, and is intentionally deferred to the next proof pass.

end OffDiag

end MIPStarRE.Quantum
