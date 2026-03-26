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
  name : String := ""
  support : List α := []
  weight : α → Error := fun _ => 0
  supportNodup : support.Nodup := by simp
  nonnegative : ∀ a, 0 ≤ weight a := by intro _; positivity
  outsideSupport : ∀ a, a ∉ support → weight a = 0 := by intro _ _; rfl

/-- Average a scalar function against the stored finite support of a distribution. -/
def averageOverDistribution {α : Type*} (𝒟 : Distribution α) (f : α → Error) : Error :=
  (𝒟.support.map fun a => 𝒟.weight a * f a).sum

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniformDistribution (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] : Distribution α where
  name := "uniform"
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

/-- Placeholder total variation distance. The distribution carrier is now explicit, but the
full `L¹` bookkeeping is postponed to a later pass. -/
def totalVariationDistance {α : Type*} (_μ _ν : Distribution α) : Error := 0

/-- Sum a scalar quantity over an outcome space when a finite enumeration is available,
falling back to a coarser surrogate otherwise. -/
noncomputable def sumOverOutcomesOrElse {α : Type*}
    (fallback : Error) (f : α → Error) : Error := by
  classical
  if h : Nonempty (Fintype α) then
    letI : Fintype α := Classical.choice h
    exact ∑ a, f a
  else
    exact fallback

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
    simp only [List.map_cons, List.sum_cons, mul_add]
    linarith [ih]

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
theorem averageOverDistribution_zero {α : Type*} (𝒟 : Distribution α) :
    averageOverDistribution 𝒟 (fun _ => 0) = 0 := by
  unfold averageOverDistribution
  simp [mul_zero]

/-- Averaging preserves order when weights are nonneg. -/
theorem averageOverDistribution_mono {α : Type*} (𝒟 : Distribution α) (f g : α → Error)
    (hfg : ∀ a, f a ≤ g a) :
    averageOverDistribution 𝒟 f ≤ averageOverDistribution 𝒟 g := by
  unfold averageOverDistribution
  exact list_weighted_sum_le 𝒟.support 𝒟.weight f g 𝒟.nonnegative hfg

/-- Averaging a nonneg function with nonneg weights gives a nonneg result. -/
theorem averageOverDistribution_nonneg {α : Type*} (𝒟 : Distribution α) (f : α → Error)
    (hf : ∀ a, 0 ≤ f a) :
    0 ≤ averageOverDistribution 𝒟 f := by
  rw [← averageOverDistribution_zero 𝒟]
  exact averageOverDistribution_mono 𝒟 _ f (fun a => hf a)

/-- Averaging distributes over addition. -/
theorem averageOverDistribution_add {α : Type*} (𝒟 : Distribution α) (f g : α → Error) :
    averageOverDistribution 𝒟 (fun a => f a + g a) =
      averageOverDistribution 𝒟 f + averageOverDistribution 𝒟 g := by
  unfold averageOverDistribution
  exact list_weighted_sum_add 𝒟.support 𝒟.weight f g

/-- Averaging commutes with scalar multiplication. -/
theorem averageOverDistribution_const_mul {α : Type*} (𝒟 : Distribution α) (c : Error) (f : α → Error) :
    averageOverDistribution 𝒟 (fun a => c * f a) = c * averageOverDistribution 𝒟 f := by
  unfold averageOverDistribution
  exact list_weighted_sum_const_mul 𝒟.support 𝒟.weight c f

/-- If `f = g` pointwise, their averages agree. -/
theorem averageOverDistribution_congr {α : Type*} (𝒟 : Distribution α)
    (f g : α → Error) (h : ∀ a, f a = g a) :
    averageOverDistribution 𝒟 f = averageOverDistribution 𝒟 g := by
  congr 1; exact funext h

end MIPStarRE.LDT
