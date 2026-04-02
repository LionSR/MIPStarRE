import MIPStarRE.LDT.Basic.Parameters

/-!
# Distribution infrastructure for the low individual degree test

Shared distribution definitions: finite-support probability distributions,
averaging, uniform distribution, and outcome summation.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

/-- A probability distribution with explicit finite support and real-valued weights. -/
structure Distribution (α : Type*) where
  support : Finset α := ∅
  weight : α → Error := fun _ => 0
  nonnegative : ∀ a, 0 ≤ weight a := by intro _; positivity
  outsideSupport : ∀ a, a ∉ support → weight a = 0 := by intro _ _; rfl

/-- Average a scalar function against the stored finite support of a distribution. -/
def avgOver {α : Type*} (𝒟 : Distribution α) (f : α → Error) : Error :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a * f a

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniformDistribution (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] : Distribution α where
  support := Finset.univ
  weight := fun _ => 1 / (Fintype.card α : Error)
  nonnegative := by intro _; positivity
  outsideSupport := by intro a ha; exact absurd (Finset.mem_univ a) ha

/-- Total variation distance between two distributions:
`TV(μ, ν) = ½ ∑_a |μ(a) - ν(a)|` over the union of supports. -/
noncomputable def totalVariationDistance {α : Type*} [DecidableEq α]
    (μ ν : Distribution α) : Error :=
  (1 / 2) * ∑ a ∈ (μ.support ∪ ν.support), |μ.weight a - ν.weight a|


/-! ### Averaging infrastructure

Proofs use Mathlib's `Finset.sum` API: `Finset.sum_le_sum`, `Finset.sum_add_distrib`,
`Finset.mul_sum`, and `Finset.sum_congr`. -/

/-- Averaging the zero function gives zero. -/
theorem avgOver_zero {α : Type*} (𝒟 : Distribution α) :
    avgOver 𝒟 (fun _ => 0) = 0 := by simp [avgOver]

/-- Averaging preserves order when weights are nonneg. -/
theorem avgOver_mono {α : Type*} (𝒟 : Distribution α) (f g : α → Error)
    (hfg : ∀ a, f a ≤ g a) :
    avgOver 𝒟 f ≤ avgOver 𝒟 g := by
  simp only [avgOver]
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hfg a) (𝒟.nonnegative a)

/-- Averaging a nonneg function with nonneg weights gives a nonneg result. -/
theorem avgOver_nonneg {α : Type*} (𝒟 : Distribution α) (f : α → Error)
    (hf : ∀ a, 0 ≤ f a) :
    0 ≤ avgOver 𝒟 f := by
  rw [← avgOver_zero 𝒟]; exact avgOver_mono 𝒟 _ f hf

/-- Averaging distributes over addition. -/
theorem avgOver_add {α : Type*} (𝒟 : Distribution α) (f g : α → Error) :
    avgOver 𝒟 (fun a => f a + g a) =
      avgOver 𝒟 f + avgOver 𝒟 g := by
  simp only [avgOver, mul_add, Finset.sum_add_distrib]

/-- Averaging commutes with scalar multiplication. -/
theorem avgOver_const_mul {α : Type*} (𝒟 : Distribution α)
    (c : Error) (f : α → Error) :
    avgOver 𝒟 (fun a => c * f a) =
      c * avgOver 𝒟 f := by
  simp only [avgOver]
  conv_lhs => arg 2; ext a; rw [show 𝒟.weight a * (c * f a) = c * (𝒟.weight a * f a) by ring]
  exact (Finset.mul_sum 𝒟.support (fun a => 𝒟.weight a * f a) c).symm

/-- If `f = g` pointwise, their averages agree. -/
theorem avgOver_congr {α : Type*} (𝒟 : Distribution α)
    (f g : α → Error) (h : ∀ a, f a = g a) :
    avgOver 𝒟 f = avgOver 𝒟 g := by
  simp only [avgOver]; exact Finset.sum_congr rfl fun a _ => by rw [h a]

end MIPStarRE.LDT

namespace MIPStarRE.LDT

/-- The weights of a uniform distribution sum to at most 1. -/
theorem uniformDistribution_weight_sum_le_one (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a ≤ 1 := by
  simp [uniformDistribution]

end MIPStarRE.LDT
