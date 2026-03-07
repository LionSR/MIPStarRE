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
  cases M; cases N; congr; funext q a; exact h q a

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

end MIPStarRE.Quantum
