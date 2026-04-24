import MIPStarRE.LDT.Basic.Parameters
import MIPStarRE.Quantum.FiniteMatrix

/-!
# Distribution infrastructure for the low individual degree test

Shared distribution definitions: finite-support weighted distributions,
a probability predicate and wrapper, averaging, uniform distribution,
and outcome summation.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

/-- A finite-support weighted distribution with nonnegative real-valued weights. -/
structure Distribution (α : Type*) where
  support : Finset α := ∅
  weight : α → Error := fun _ => 0
  nonnegative : ∀ a, 0 ≤ weight a := by intro _; positivity
  outsideSupport : ∀ a, a ∉ support → weight a = 0 := by intro _ _; rfl

namespace Distribution

/-- The total mass carried by the explicit support of a distribution. -/
def totalWeight {α : Type*} (𝒟 : Distribution α) : Error :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a

/-- A `Distribution` is probabilistic when its total mass is exactly `1`. -/
def IsProbability {α : Type*} (𝒟 : Distribution α) : Prop :=
  𝒟.totalWeight = 1

end Distribution

/-- Bundled finite-support probability distributions. -/
abbrev ProbabilityDistribution (α : Type*) :=
  {𝒟 : Distribution α // 𝒟.IsProbability}

/-- Total mass is nonnegative because each weight is nonnegative. -/
theorem Distribution.totalWeight_nonneg {α : Type*} (𝒟 : Distribution α) :
    0 ≤ 𝒟.totalWeight := by
  unfold Distribution.totalWeight
  exact Finset.sum_nonneg fun a _ => 𝒟.nonnegative a

namespace Distribution.IsProbability

/-- Unpack the equality form of the probability invariant. -/
theorem weight_sum_eq_one {α : Type*}
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a = 1 := by
  simpa [Distribution.IsProbability, Distribution.totalWeight] using h𝒟

/-- A probability distribution has total weight at most `1`. -/
theorem weight_sum_le_one {α : Type*}
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a ≤ 1 :=
  le_of_eq h𝒟.weight_sum_eq_one

end Distribution.IsProbability

/-- Average a scalar function against the stored finite support of a distribution. -/
def avgOver {α : Type*} (𝒟 : Distribution α) (f : α → Error) : Error :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a * f a

/-- Weighted sum of operators over a distribution's finite support, using the same
`support`/`weight` data as the scalar `avgOver`. -/
noncomputable def averageOperatorOverDistribution {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a • f a

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
  simpa [avgOver_zero] using avgOver_mono 𝒟 (fun _ => 0) f hf

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
  calc
    avgOver 𝒟 (fun a => c * f a)
      = ∑ a ∈ 𝒟.support, c * (𝒟.weight a * f a) := by
          unfold avgOver
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = c * ∑ a ∈ 𝒟.support, 𝒟.weight a * f a := by
          rw [Finset.mul_sum]
    _ = c * avgOver 𝒟 f := rfl

/-- If `f = g` pointwise, their averages agree. -/
theorem avgOver_congr {α : Type*} (𝒟 : Distribution α)
    (f g : α → Error) (h : ∀ a, f a = g a) :
    avgOver 𝒟 f = avgOver 𝒟 g := by
  exact Finset.sum_congr rfl fun a _ => by rw [h a]

/-- Averaging a constant against a probability distribution returns that constant. -/
theorem avgOver_const_of_isProbability {α : Type*} (𝒟 : Distribution α)
    (h𝒟 : 𝒟.IsProbability) (c : Error) :
    avgOver 𝒟 (fun _ : α => c) = c := by
  calc
    avgOver 𝒟 (fun _ : α => c)
      = ∑ a ∈ 𝒟.support, 𝒟.weight a * c := by simp [avgOver]
    _ = (∑ a ∈ 𝒟.support, 𝒟.weight a) * c := by rw [← Finset.sum_mul]
    _ = c := by rw [h𝒟.weight_sum_eq_one, one_mul]

namespace ProbabilityDistribution

/-- Unpack the equality form of the bundled probability invariant. -/
theorem weight_sum_eq_one {α : Type*} (𝒟 : ProbabilityDistribution α) :
    ∑ a ∈ (𝒟 : Distribution α).support, (𝒟 : Distribution α).weight a = 1 := by
  have h𝒟 : (𝒟 : Distribution α).IsProbability := 𝒟.2
  exact h𝒟.weight_sum_eq_one

/-- A bundled probability distribution has total weight at most `1`. -/
theorem weight_sum_le_one {α : Type*} (𝒟 : ProbabilityDistribution α) :
    ∑ a ∈ (𝒟 : Distribution α).support, (𝒟 : Distribution α).weight a ≤ 1 :=
  le_of_eq 𝒟.weight_sum_eq_one

/-- The total mass of a bundled probability distribution is nonnegative. -/
theorem totalWeight_nonneg {α : Type*} (𝒟 : ProbabilityDistribution α) :
    0 ≤ (𝒟 : Distribution α).totalWeight :=
  (𝒟 : Distribution α).totalWeight_nonneg

/-- Averaging a constant against a bundled probability distribution returns that constant. -/
theorem avgOver_const {α : Type*} (𝒟 : ProbabilityDistribution α) (c : Error) :
    avgOver (𝒟 : Distribution α) (fun _ : α => c) = c :=
  avgOver_const_of_isProbability (𝒟 : Distribution α) 𝒟.2 c

end ProbabilityDistribution

/-- The weights of a uniform distribution sum to exactly `1`. -/
theorem uniformDistribution_weight_sum_eq_one (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a = 1 := by
  simp [uniformDistribution]

/-- The uniform distribution is a genuine probability distribution. -/
theorem uniformDistribution_isProbability (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    (uniformDistribution α).IsProbability := by
  simpa [Distribution.IsProbability, Distribution.totalWeight] using
    uniformDistribution_weight_sum_eq_one α

/-- The uniform distribution packaged as a bundled probability distribution. -/
noncomputable def uniformProbabilityDistribution (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] : ProbabilityDistribution α :=
  ⟨uniformDistribution α, uniformDistribution_isProbability α⟩

/-- The weights of a uniform distribution sum to at most `1`. -/
theorem uniformDistribution_weight_sum_le_one (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a ≤ 1 :=
  le_of_eq (uniformDistribution_weight_sum_eq_one α)

/-- Averaging a constant against the uniform distribution on a nonempty finite type
returns that constant. -/
theorem avgOver_uniform_const {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (c : Error) :
    avgOver (uniformDistribution α) (fun _ : α => c) = c := by
  simpa [uniformProbabilityDistribution] using
    (ProbabilityDistribution.avgOver_const (uniformProbabilityDistribution α) c)

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
  rw [avgOver_uniform_prod (f := fun a : α => fun _ : β => f a)]
  refine avgOver_congr _ _ _ ?_
  intro a
  simpa using (avgOver_uniform_const (α := β) (c := f a))

/-- Averaging a function depending only on the second coordinate marginalizes a uniform product. -/
theorem avgOver_uniform_snd {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.2) =
      avgOver (uniformDistribution β) f := by
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.2)
      = avgOver (uniformDistribution (β × α)) (fun ba => f ba.1) := by
          simpa using
            (avgOver_uniform_equiv (e := Equiv.prodComm α β)
              (f := fun ab : α × β => f ab.2))
    _ = avgOver (uniformDistribution β) f := avgOver_uniform_fst f

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
