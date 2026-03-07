import Mathlib

/-!
Foundational measurement infrastructure for the MIP*=RE project.

The first pass stays deliberately lightweight: we only formalize the finite
question/answer bookkeeping that appears throughout arXiv:2111.08131. The
ambient `Effect` type is left abstract so that later work can instantiate it
with finite-dimensional matrices or operators together with positivity,
normalization, traces, consistency, and closeness.

This keeps the early API honest and reusable without forcing heavy
operator-algebra machinery into the scaffold.
-/

open scoped BigOperators

namespace MIPStarRE.Quantum

/--
A finite family of effects indexed by questions and answers.

Later files should specialize `Effect` to a finite-dimensional operator type and
add analytic side conditions. For now this records only the combinatorial data
of a measurement table.
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
def total [Fintype Answer] [DecidableEq Answer] [Zero Effect] [AddCommMonoid Effect]
    (M : OutcomeFamily Question Answer Effect) (q : Question) : Effect :=
  Finset.sum Finset.univ fun a => M.effect q a

/--
Relabel the answers of an outcome family by summing over the fibers of a map.
This is the combinatorial core of the processed-measurement construction used in
Section 2 of the paper.
-/
def postprocess [Fintype Answer] [DecidableEq Answer]
    [Zero Effect] [AddCommMonoid Effect] [DecidableEq Answer']
    (M : OutcomeFamily Question Answer Effect) (f : Answer → Answer') :
    OutcomeFamily Question Answer' Effect where
  effect q b := Finset.sum (Finset.univ.filter fun a => f a = b) fun a => M.effect q a

@[simp] theorem postprocess_effect [Fintype Answer] [DecidableEq Answer]
    [Zero Effect] [AddCommMonoid Effect] [DecidableEq Answer']
    (M : OutcomeFamily Question Answer Effect) (f : Answer → Answer')
    (q : Question) (b : Answer') :
    (M.postprocess f).effect q b =
      Finset.sum (Finset.univ.filter fun a => f a = b) fun a => M.effect q a :=
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
  Finset.sum (Finset.univ.filter p) fun a => M.effect q a

end OutcomeFamily

end MIPStarRE.Quantum
