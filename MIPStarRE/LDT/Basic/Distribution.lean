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

/-- Reindexing a uniform average along an equivalence preserves its value. -/
theorem avgOver_uniform_equiv
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (f : α → Error) :
    avgOver (uniformDistribution α) f =
      avgOver (uniformDistribution β) (fun b => f (e.symm b)) := by
  calc
    avgOver (uniformDistribution α) f
      = (1 / (Fintype.card α : Error)) * ∑ a : α, f a := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]
    _ = (1 / (Fintype.card β : Error)) * ∑ a : α, f a := by
          rw [Fintype.card_congr e]
    _ = (1 / (Fintype.card β : Error)) * ∑ b : β, f (e.symm b) := by
          congr 1
          exact Fintype.sum_equiv e f (fun b => f (e.symm b)) (by
            intro a
            simp)
    _ = avgOver (uniformDistribution β) (fun b => f (e.symm b)) := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]

/-- Split a uniform average over a product into iterated uniform averages. -/
theorem avgOver_uniform_prod
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) =
      avgOver (uniformDistribution α)
        (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
  have hα : ((Fintype.card α : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : ((Fintype.card β : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2)
      = ∑ ab : α × β,
          (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f ab.1 ab.2 := by
            simp [avgOver, uniformDistribution, Fintype.card_prod]
    _ = ∑ a : α, ∑ b : β,
          (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a b := by
            simpa using
              (Fintype.sum_prod_type' (f := fun a : α => fun b : β =>
                (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a b))
    _ = ∑ a : α,
          (1 / (Fintype.card α : Error)) *
            ∑ b : β, (1 / (Fintype.card β : Error)) * f a b := by
            refine Finset.sum_congr rfl ?_
            intro a _
            calc
              ∑ b : β, (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a b
                = ∑ b : β,
                    ((1 / (Fintype.card α : Error)) *
                      (1 / (Fintype.card β : Error))) * f a b := by
                        refine Finset.sum_congr rfl ?_
                        intro b _
                        field_simp [hα, hβ]
                        rw [Nat.cast_mul]
                        ring
              _ = (1 / (Fintype.card α : Error)) *
                    ∑ b : β, (1 / (Fintype.card β : Error)) * f a b := by
                        rw [Finset.mul_sum]
                        simp [mul_assoc]
    _ = avgOver (uniformDistribution α)
          (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
            simp [avgOver, uniformDistribution]

/-- Averaging a function depending only on the first coordinate marginalizes a uniform product. -/
theorem avgOver_uniform_fst {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1) =
      avgOver (uniformDistribution α) f := by
  have hα : (Fintype.card α : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1)
        = ∑ ab : α × β, (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f ab.1 := by
            simp [avgOver, uniformDistribution, Fintype.card_prod]
    _ = ∑ a : α, ∑ b : β, (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a := by
      simpa using
        (Fintype.sum_prod_type'
          (f := fun a : α => fun _ : β =>
            (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a))
    _ = ∑ a : α, (1 / (Fintype.card α : Error)) * f a := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      calc
        ∑ b : β, (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a
            = (Fintype.card β : Error) *
                ((1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a) := by
                  simp
        _ = (1 / (Fintype.card α : Error)) * f a := by
          field_simp [hα, hβ]
          rw [Nat.cast_mul]
          ring
    _ = avgOver (uniformDistribution α) f := by
      simp [avgOver, uniformDistribution]

/-- Averaging a function depending only on the second coordinate marginalizes a uniform product. -/
theorem avgOver_uniform_snd {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.2) =
      avgOver (uniformDistribution β) f := by
  have hα : (Fintype.card α : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.2)
        = ∑ ab : α × β, (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f ab.2 := by
            simp [avgOver, uniformDistribution, Fintype.card_prod]
    _ = ∑ b : β, ∑ a : α, (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f b := by
      simpa using
        (Fintype.sum_prod_type_right'
          (f := fun a : α => fun b : β =>
            (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f b))
    _ = ∑ b : β, (1 / (Fintype.card β : Error)) * f b := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      calc
        ∑ a : α, (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f b
            = (Fintype.card α : Error) *
                ((1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f b) := by
                  simp
        _ = (1 / (Fintype.card β : Error)) * f b := by
          field_simp [hα, hβ]
          rw [Nat.cast_mul]
          ring
    _ = avgOver (uniformDistribution β) f := by
      simp [avgOver, uniformDistribution]

/-- A pointwise upper bound depending only on the first coordinate bounds the product average. -/
theorem avgOver_uniform_prod_le_fst {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α × β → Error) (g : α → Error)
    (h : ∀ ab, f ab ≤ g ab.1) :
    avgOver (uniformDistribution (α × β)) f ≤
      avgOver (uniformDistribution α) g := by
  calc
    avgOver (uniformDistribution (α × β)) f
      ≤ avgOver (uniformDistribution (α × β)) (fun ab => g ab.1) := by
          exact avgOver_mono _ _ _ h
    _ = avgOver (uniformDistribution α) g := avgOver_uniform_fst g

/-- A pointwise upper bound depending only on the second coordinate bounds the product average. -/
theorem avgOver_uniform_prod_le_snd {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α × β → Error) (g : β → Error)
    (h : ∀ ab, f ab ≤ g ab.2) :
    avgOver (uniformDistribution (α × β)) f ≤
      avgOver (uniformDistribution β) g := by
  calc
    avgOver (uniformDistribution (α × β)) f
      ≤ avgOver (uniformDistribution (α × β)) (fun ab => g ab.2) := by
          exact avgOver_mono _ _ _ h
    _ = avgOver (uniformDistribution β) g := avgOver_uniform_snd g

end MIPStarRE.LDT
