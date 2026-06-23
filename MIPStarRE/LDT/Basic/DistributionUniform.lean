import MIPStarRE.LDT.Basic.DistributionPMF

/-!
# Uniform subset estimates

This file contains estimates for the total variation distance between the
uniform distribution on a finite type and the uniform distribution on a
nonempty finite subset, together with averaging bounds for `[0,1]`-valued
functions.  The uniform-subset total-variation identity is proved by transport
through Mathlib probability mass functions.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

/-- Total variation between the uniform distribution on a finite ambient type and
the uniform distribution on a nonempty finite subset.

This is the elementary finite identity
`TV(uniform α, uniform s) = 1 - |s| / |α|`.  The proof transports the project
`Distribution` statement to Mathlib's uniform probability mass functions. -/
theorem totalVariationDistance_uniformDistribution_uniformOnFinset_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty) :
    totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) =
      1 - (s.card : Error) / (Fintype.card α : Error) := by
  rw [totalVariationDistance_eq_toPMF_sum]
  change PMF.totalVariationDistance
      ((uniformDistribution α).toPMF (uniformDistribution_isProbability α))
      ((Distribution.uniformOnFinset s).toPMF
        (Distribution.uniformOnFinset_isProbability s hs)) =
    1 - (s.card : Error) / (Fintype.card α : Error)
  rw [uniformDistribution_toPMF, Distribution.uniformOnFinset_toPMF]
  exact PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq s hs

/-- A `[0,1]`-valued function averaged over a nonempty finite subset is bounded
by its ambient uniform average plus the total variation distance between the
two uniform distributions. -/
theorem avgOver_uniformOnFinset_le_uniformDistribution_add_totalVariationDistance
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty)
    (f : α → Error)
    (hf_nonneg : ∀ a, 0 ≤ f a)
    (hf_le_one : ∀ a, f a ≤ 1) :
    avgOver (Distribution.uniformOnFinset s) f
      ≤ avgOver (uniformDistribution α) f
        + totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) := by
  exact
    avgOver_le_avgOver_add_totalVariationDistance
      (uniformDistribution α) (Distribution.uniformOnFinset s)
      (uniformDistribution_isProbability α)
      (Distribution.uniformOnFinset_isProbability s hs)
      f hf_nonneg hf_le_one

end MIPStarRE.LDT
