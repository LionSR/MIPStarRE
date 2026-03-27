import MIPStarRE.LDT.Basic.Parameters

/-!
# Distribution infrastructure for the low individual degree test

Shared distribution definitions: finite-support probability distributions,
averaging, uniform distribution, and outcome summation.
-/

open scoped BigOperators

noncomputable section

namespace MIPStarRE.LDT

/-- Placeholder for a probability distribution, now with an explicit finite support list
and real-valued weights. -/
structure Distribution (α : Type*) where
  support : List α := []
  weight : α → Error := fun _ => 0
  supportNodup : support.Nodup := by simp
  nonnegative : ∀ a, 0 ≤ weight a := by intro _; positivity
  outsideSupport : ∀ a, a ∉ support → weight a = 0 := by intro _ _; rfl

/-- Average a scalar function against the stored finite support of a distribution. -/
def avgOver {α : Type*} (𝒟 : Distribution α) (f : α → Error) : Error :=
  (𝒟.support.map fun a => 𝒟.weight a * f a).sum

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniformDistribution (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] : Distribution α where
  support := (Finset.univ : Finset α).toList
  weight := fun _ => 1 / (Fintype.card α : Error)
  supportNodup := by
    simpa using (Finset.nodup_toList (Finset.univ : Finset α))
  nonnegative := by
    intro _
    positivity
  outsideSupport := by
    intro a ha
    exfalso
    apply ha
    exact Finset.mem_toList.mpr (by simp : a ∈ (Finset.univ : Finset α))

/-- Total variation distance between two distributions.
TODO: implement honest `L¹` computation. -/
noncomputable def totalVariationDistance {α : Type*} (_μ _ν : Distribution α) : Error := by sorry

/-- Sum a scalar quantity over a finite outcome space. -/
noncomputable def sumOutcomes {α : Type*} [Fintype α]
    (f : α → Error) : Error :=
  ∑ a, f a

/-! ### Averaging infrastructure -/

/-- Helper: weighted sum preserves `≤` when weights are nonneg. -/
private theorem list_weighted_sum_le {α : Type*} (l : List α) (w : α → Error) (f g : α → Error)
    (hw : ∀ a, 0 ≤ w a) (hfg : ∀ a, f a ≤ g a) :
    (l.map fun a => w a * f a).sum ≤ (l.map fun a => w a * g a).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (mul_le_mul_of_nonneg_left (hfg a) (hw a)) ih

/-- Helper: weighted sum distributes over function addition. -/
private theorem list_weighted_sum_add {α : Type*} (l : List α) (w : α → Error) (f g : α → Error) :
    (l.map fun a => w a * (f a + g a)).sum =
      (l.map fun a => w a * f a).sum + (l.map fun a => w a * g a).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [mul_add, ih]; ring

/-- Helper: scalar multiplication pulls out of weighted sum. -/
private theorem list_weighted_sum_const_mul {α : Type*}
    (l : List α) (w : α → Error) (c : Error) (f : α → Error) :
    (l.map fun a => w a * (c * f a)).sum = c * (l.map fun a => w a * f a).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]; ring

/-- Averaging the zero function gives zero. -/
theorem avgOver_zero {α : Type*} (𝒟 : Distribution α) :
    avgOver 𝒟 (fun _ => 0) = 0 := by
  unfold avgOver
  simp [mul_zero]

/-- Averaging preserves order when weights are nonneg. -/
theorem avgOver_mono {α : Type*} (𝒟 : Distribution α) (f g : α → Error)
    (hfg : ∀ a, f a ≤ g a) :
    avgOver 𝒟 f ≤ avgOver 𝒟 g := by
  unfold avgOver
  exact list_weighted_sum_le 𝒟.support 𝒟.weight f g 𝒟.nonnegative hfg

/-- Averaging a nonneg function with nonneg weights gives a nonneg result. -/
theorem avgOver_nonneg {α : Type*} (𝒟 : Distribution α) (f : α → Error)
    (hf : ∀ a, 0 ≤ f a) :
    0 ≤ avgOver 𝒟 f := by
  rw [← avgOver_zero 𝒟]
  exact avgOver_mono 𝒟 _ f (fun a => hf a)

/-- Averaging distributes over addition. -/
theorem avgOver_add {α : Type*} (𝒟 : Distribution α) (f g : α → Error) :
    avgOver 𝒟 (fun a => f a + g a) =
      avgOver 𝒟 f + avgOver 𝒟 g := by
  unfold avgOver
  exact list_weighted_sum_add 𝒟.support 𝒟.weight f g

/-- Averaging commutes with scalar multiplication. -/
theorem avgOver_const_mul {α : Type*} (𝒟 : Distribution α)
    (c : Error) (f : α → Error) :
    avgOver 𝒟 (fun a => c * f a) =
      c * avgOver 𝒟 f := by
  unfold avgOver
  exact list_weighted_sum_const_mul 𝒟.support 𝒟.weight c f

/-- If `f = g` pointwise, their averages agree. -/
theorem avgOver_congr {α : Type*} (𝒟 : Distribution α)
    (f g : α → Error) (h : ∀ a, f a = g a) :
    avgOver 𝒟 f = avgOver 𝒟 g := by
  congr 1; exact funext h

end MIPStarRE.LDT
