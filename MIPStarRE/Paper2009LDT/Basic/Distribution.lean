import MIPStarRE.Paper2009LDT.Basic.Parameters

open scoped BigOperators

namespace MIPStarRE.Paper2009LDT

/-- Placeholder for a probability distribution, now with an explicit finite support list
and real-valued weights. -/
structure Distribution (α : Type _) where
  name : String := ""
  support : List α := []
  weight : α → Error := fun _ => 0
  supportNodup : support.Nodup := by simp
  nonnegative : ∀ a, 0 ≤ weight a := by intro _; positivity
  outsideSupport : ∀ a, a ∉ support → weight a = 0 := by intro _ _; rfl

/-- Average a scalar function against the stored finite support of a distribution. -/
def averageOverDistribution {α : Type _} (𝒟 : Distribution α) (f : α → Error) : Error :=
  (𝒟.support.map fun a => 𝒟.weight a * f a).sum

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniformDistribution (α : Type _)
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
def totalVariationDistance {α : Type _} (_μ _ν : Distribution α) : Error := 0

/-- Sum a scalar quantity over an outcome space when a finite enumeration is available,
falling back to a coarser surrogate otherwise. -/
noncomputable def sumOverOutcomesOrElse {α : Type _}
    (fallback : Error) (f : α → Error) : Error := by
  classical
  if h : Nonempty (Fintype α) then
    letI : Fintype α := Classical.choice h
    exact ∑ a, f a
  else
    exact fallback

end MIPStarRE.Paper2009LDT
