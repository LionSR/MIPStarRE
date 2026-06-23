import MIPStarRE.LDT.Basic.PMFAverages
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Average lemmas for finite-support distributions

This module contains the finite-sum and uniform-average lemmas for the project
`Distribution` type.  The primitive distribution definitions, uniform
distributions, and total variation distance live in
`MIPStarRE.LDT.Basic.Distribution`.

## Main declarations

The main results are the algebraic rules for `avgOver`, the corresponding
operator-valued rules for `averageOperatorOverDistribution`, and the comparison
between finite uniform averages and Mathlib uniform probability mass functions.

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

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

/-- Averaging distributes over subtraction. -/
theorem avgOver_sub {α : Type*} (𝒟 : Distribution α) (f g : α → Error) :
    avgOver 𝒟 (fun a => f a - g a) =
      avgOver 𝒟 f - avgOver 𝒟 g := by
  simp only [avgOver, mul_sub, Finset.sum_sub_distrib]

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

/-- Averaging commutes with scalar multiplication on the right. -/
theorem avgOver_mul_const {α : Type*} (𝒟 : Distribution α)
    (f : α → Error) (c : Error) :
    avgOver 𝒟 (fun a => f a * c) = avgOver 𝒟 f * c := by
  unfold avgOver
  calc
    ∑ a ∈ 𝒟.support, 𝒟.weight a * (f a * c)
      = ∑ a ∈ 𝒟.support, (𝒟.weight a * f a) * c := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = (∑ a ∈ 𝒟.support, 𝒟.weight a * f a) * c := by
          rw [Finset.sum_mul]

/-- Pull a finite outcome sum through an average. -/
theorem avgOver_sum {α β : Type*} [Fintype β]
    (𝒟 : Distribution α) (f : α → β → Error) :
    avgOver 𝒟 (fun a => ∑ b : β, f a b) =
      ∑ b : β, avgOver 𝒟 (fun a => f a b) := by
  unfold avgOver
  calc
    ∑ a ∈ 𝒟.support, 𝒟.weight a * ∑ b : β, f a b
      = ∑ a ∈ 𝒟.support, ∑ b : β, 𝒟.weight a * f a b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ b : β, ∑ a ∈ 𝒟.support, 𝒟.weight a * f a b := by
          rw [Finset.sum_comm]

/-- Pull a finite-set sum through an average. -/
theorem avgOver_finset_sum {α β : Type*}
    (𝒟 : Distribution α) (s : Finset β) (f : α → β → Error) :
    avgOver 𝒟 (fun a => ∑ b ∈ s, f a b) =
      ∑ b ∈ s, avgOver 𝒟 (fun a => f a b) := by
  unfold avgOver
  calc
    ∑ a ∈ 𝒟.support, 𝒟.weight a * ∑ b ∈ s, f a b
        = ∑ a ∈ 𝒟.support, ∑ b ∈ s, 𝒟.weight a * f a b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ b ∈ s, ∑ a ∈ 𝒟.support, 𝒟.weight a * f a b := by
          rw [Finset.sum_comm]

/-- Fubini swap for two nested finite-support distribution averages. -/
theorem avgOver_comm {α β : Type*} (𝒟α : Distribution α) (𝒟β : Distribution β)
    (f : α → β → Error) :
    avgOver 𝒟α (fun a => avgOver 𝒟β (f a)) =
      avgOver 𝒟β (fun b => avgOver 𝒟α (fun a => f a b)) := by
  unfold avgOver
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro b _
  refine Finset.sum_congr rfl ?_
  intro a _
  ring

/-- If `f = g` pointwise, their averages agree. -/
theorem avgOver_congr {α : Type*} (𝒟 : Distribution α)
    (f g : α → Error) (h : ∀ a, f a = g a) :
    avgOver 𝒟 f = avgOver 𝒟 g := by
  exact Finset.sum_congr rfl fun a _ => by rw [h a]

/-- If two scalar functions agree on a distribution's explicit support, their
averages agree.  This support-restricted form is useful for distributions whose
support carries an invariant not available for all ambient values. -/
theorem avgOver_congr_on_support {α : Type*} (𝒟 : Distribution α)
    (f g : α → Error) (h : ∀ a, a ∈ 𝒟.support → f a = g a) :
    avgOver 𝒟 f = avgOver 𝒟 g := by
  simp only [avgOver]
  exact Finset.sum_congr rfl fun a ha => by rw [h a ha]

/-- Averaging preserves supportwise order when weights are nonnegative.  This is
the support-restricted analogue of `avgOver_mono`. -/
theorem avgOver_mono_on_support {α : Type*} (𝒟 : Distribution α)
    (f g : α → Error) (h : ∀ a, a ∈ 𝒟.support → f a ≤ g a) :
    avgOver 𝒟 f ≤ avgOver 𝒟 g := by
  unfold avgOver
  exact Finset.sum_le_sum fun a ha =>
    mul_le_mul_of_nonneg_left (h a ha) (𝒟.nonnegative a)

/-- The average of a constant scalar is the total mass times that scalar. -/
theorem avgOver_const {α : Type*} (𝒟 : Distribution α) (c : Error) :
    avgOver 𝒟 (fun _ : α => c) =
      (∑ a ∈ 𝒟.support, 𝒟.weight a) * c := by
  unfold avgOver
  rw [Finset.sum_mul]

/-- Averaging a constant against a probability distribution returns that constant. -/
theorem avgOver_const_of_isProbability {α : Type*} (𝒟 : Distribution α)
    (h𝒟 : 𝒟.IsProbability) (c : Error) :
    avgOver 𝒟 (fun _ : α => c) = c := by
  rw [avgOver_const, h𝒟.weight_sum_eq_one, one_mul]

/-- A scalar average against a sub-probability distribution is bounded by any
nonnegative pointwise upper bound. -/
theorem avgOver_le_of_weight_sum_le_one {α : Type*} (𝒟 : Distribution α)
    (f : α → Error) (δ : Error)
    (h𝒟 : ∑ a ∈ 𝒟.support, 𝒟.weight a ≤ 1)
    (hδ_nonneg : 0 ≤ δ)
    (hf : ∀ a, f a ≤ δ) :
    avgOver 𝒟 f ≤ δ := by
  calc
    avgOver 𝒟 f ≤ avgOver 𝒟 (fun _ : α => δ) := by
      exact avgOver_mono 𝒟 f (fun _ : α => δ) hf
    _ = (∑ a ∈ 𝒟.support, 𝒟.weight a) * δ := avgOver_const 𝒟 δ
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right h𝒟 hδ_nonneg
    _ = δ := one_mul δ

/-- Fixed left and right multiplications factor through an operator average. -/
theorem averageOperatorOverDistribution_mul_left_right {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (L R : MIPStarRE.Quantum.Op ι)
    (A : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun a => L * A a * R) =
      L * averageOperatorOverDistribution 𝒟 A * R := by
  unfold averageOperatorOverDistribution
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro a _
  simp [mul_assoc]

namespace Distribution

/-- A module-valued finite weighted sum against a probabilistic project
distribution may be written with the real weights of the associated Mathlib
probability mass function, over the stored support. -/
theorem sum_smul_eq_toPMF_support_sum {α M : Type*}
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → M) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a • f a =
      ∑ a ∈ 𝒟.support, (𝒟.toPMF h𝒟 a).toReal • f a := by
  exact Finset.sum_congr rfl fun a _ => by
    rw [Distribution.toPMF_apply_toReal]

/-- A module-valued finite weighted sum against a probabilistic project
distribution may be written as a full finite sum with the real weights of the
associated Mathlib probability mass function. -/
theorem sum_smul_eq_toPMF_sum {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → M) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a • f a =
      ∑ a : α, (𝒟.toPMF h𝒟 a).toReal • f a := by
  rw [Distribution.sum_smul_eq_toPMF_support_sum 𝒟 h𝒟 f]
  exact (Distribution.sum_univ_eq_sum_support 𝒟
    (fun a => (𝒟.toPMF h𝒟 a).toReal • f a)
    (by
      intro a ha
      rw [Distribution.toPMF_apply_of_notMem 𝒟 h𝒟 ha]
      simp)).symm

end Distribution

/-- Averaging against a probabilistic project distribution is the finite sum
over its stored support against the associated Mathlib probability mass
function. -/
theorem avgOver_eq_toPMF_support_sum {α : Type*}
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → Error) :
    avgOver 𝒟 f = ∑ a ∈ 𝒟.support, (𝒟.toPMF h𝒟 a).toReal * f a := by
  simpa [avgOver, smul_eq_mul] using
    Distribution.sum_smul_eq_toPMF_support_sum 𝒟 h𝒟 f

/-- Averaging against a probabilistic project distribution is the finite sum
against its associated Mathlib probability mass function. -/
theorem avgOver_eq_toPMF_sum {α : Type*} [Fintype α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → Error) :
    avgOver 𝒟 f = ∑ a : α, (𝒟.toPMF h𝒟 a).toReal * f a := by
  simpa [avgOver, smul_eq_mul] using
    Distribution.sum_smul_eq_toPMF_sum 𝒟 h𝒟 f

/-- Averaging against a probabilistic project distribution is integration
against its associated Mathlib probability mass function. -/
theorem avgOver_eq_toPMF_integral {α : Type*}
    [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → Error) :
    avgOver 𝒟 f = ∫ a, f a ∂(𝒟.toPMF h𝒟).toMeasure := by
  haveI := Fintype.ofFinite α
  rw [avgOver_eq_toPMF_sum 𝒟 h𝒟 f, PMF.integral_eq_sum]
  simp only [smul_eq_mul]

/-- Operator-valued averaging against a probabilistic project distribution is
the finite operator sum over the stored support against the associated Mathlib
probability mass function. -/
theorem averageOperatorOverDistribution_eq_toPMF_support_sum {α : Type*}
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 f =
      ∑ a ∈ 𝒟.support, (𝒟.toPMF h𝒟 a).toReal • f a := by
  simpa [averageOperatorOverDistribution] using
    Distribution.sum_smul_eq_toPMF_support_sum 𝒟 h𝒟 f

/-- Operator-valued averaging against a probabilistic project distribution is
the finite sum against its associated Mathlib probability mass function. -/
theorem averageOperatorOverDistribution_eq_toPMF_sum {α : Type*}
    [Fintype α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 f =
      ∑ a : α, (𝒟.toPMF h𝒟 a).toReal • f a := by
  simpa [averageOperatorOverDistribution] using
    Distribution.sum_smul_eq_toPMF_sum 𝒟 h𝒟 f

namespace Distribution.IsProbability

/-- A supportwise upper bound also bounds the average of a probability distribution.
This packages the paper convention that expectations are taken against genuine
probability distributions, while still allowing `Distribution` itself to carry a
larger ambient type than its explicit support. -/
theorem avgOver_le_of_forall_le_on_support {α : Type*} {𝒟 : Distribution α}
    (h𝒟 : 𝒟.IsProbability) (f : α → Error) (δ : Error)
    (hf : ∀ a, a ∈ 𝒟.support → f a ≤ δ) :
    avgOver 𝒟 f ≤ δ := by
  calc
    avgOver 𝒟 f ≤ avgOver 𝒟 (fun _ : α => δ) :=
      avgOver_mono_on_support 𝒟 f (fun _ : α => δ) hf
    _ = δ := avgOver_const_of_isProbability 𝒟 h𝒟 δ

end Distribution.IsProbability

/-- For two probability distributions, total variation is the total positive
part of the signed weight difference `ν - μ`.

This is the finite-distribution identity
`(1 / 2) * ∑ |μ(a)-ν(a)| = ∑ max 0 (ν(a)-μ(a))`, written for the
project `Distribution` representation. -/
theorem totalVariationDistance_eq_sum_max_sub {α : Type*} [DecidableEq α]
    (μ ν : Distribution α) (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    totalVariationDistance μ ν =
      ∑ a ∈ μ.support ∪ ν.support, max 0 (ν.weight a - μ.weight a) := by
  classical
  let u : Finset α := μ.support ∪ ν.support
  have hμ_union :
      ∑ a ∈ u, μ.weight a = 1 := by
    have hsubset : μ.support ⊆ u := by
      intro a ha
      exact Finset.mem_union_left ν.support ha
    have hsum :
        ∑ a ∈ μ.support, μ.weight a = ∑ a ∈ u, μ.weight a :=
      Finset.sum_subset hsubset (fun a _ ha => μ.outsideSupport a ha)
    exact hsum ▸ hμ.weight_sum_eq_one
  have hν_union :
      ∑ a ∈ u, ν.weight a = 1 := by
    have hsubset : ν.support ⊆ u := by
      intro a ha
      exact Finset.mem_union_right μ.support ha
    have hsum :
        ∑ a ∈ ν.support, ν.weight a = ∑ a ∈ u, ν.weight a :=
      Finset.sum_subset hsubset (fun a _ ha => ν.outsideSupport a ha)
    exact hsum ▸ hν.weight_sum_eq_one
  have hdiff_sum :
      ∑ a ∈ u, (ν.weight a - μ.weight a) = 0 := by
    rw [Finset.sum_sub_distrib, hν_union, hμ_union, sub_self]
  have hmax_abs :
      ∀ a, max 0 (ν.weight a - μ.weight a) =
        ((ν.weight a - μ.weight a) + |μ.weight a - ν.weight a|) / 2 := by
    intro a
    by_cases hle : ν.weight a - μ.weight a ≤ 0
    · have hmax : max 0 (ν.weight a - μ.weight a) = 0 := max_eq_left hle
      have habs : |μ.weight a - ν.weight a| = μ.weight a - ν.weight a := by
        rw [abs_of_nonneg]
        linarith
      rw [hmax, habs]
      ring
    · have hnonneg : 0 ≤ ν.weight a - μ.weight a := le_of_not_ge hle
      have hmax : max 0 (ν.weight a - μ.weight a) =
          ν.weight a - μ.weight a := max_eq_right hnonneg
      have habs : |μ.weight a - ν.weight a| = ν.weight a - μ.weight a := by
        have hμν : μ.weight a ≤ ν.weight a := by linarith
        rw [abs_of_nonpos (sub_nonpos.mpr hμν)]
        ring
      rw [hmax, habs]
      ring
  calc
    totalVariationDistance μ ν
        = (1 / 2) * ∑ a ∈ u, |μ.weight a - ν.weight a| := by
            rfl
    _ = (∑ a ∈ u, (ν.weight a - μ.weight a) +
          ∑ a ∈ u, |μ.weight a - ν.weight a|) / 2 := by
            rw [hdiff_sum]
            ring
    _ = (∑ a ∈ u,
          ((ν.weight a - μ.weight a) + |μ.weight a - ν.weight a|)) / 2 := by
            rw [Finset.sum_add_distrib]
    _ = ∑ a ∈ u,
          ((ν.weight a - μ.weight a) + |μ.weight a - ν.weight a|) / 2 := by
            rw [Finset.sum_div]
    _ = ∑ a ∈ u, max 0 (ν.weight a - μ.weight a) := by
            exact Finset.sum_congr rfl fun a _ => (hmax_abs a).symm

/-- A `[0,1]`-valued function has expectations over two probability
distributions differing by at most their total variation distance.

The statement is oriented for replacement estimates: averaging against `ν` is
bounded by averaging against `μ`, plus the finite total-variation distance
between the two distributions. -/
theorem avgOver_le_avgOver_add_totalVariationDistance {α : Type*} [DecidableEq α]
    (μ ν : Distribution α) (hμ : μ.IsProbability) (hν : ν.IsProbability)
    (f : α → Error)
    (hf_nonneg : ∀ a, 0 ≤ f a)
    (hf_le_one : ∀ a, f a ≤ 1) :
    avgOver ν f ≤ avgOver μ f + totalVariationDistance μ ν := by
  classical
  let u : Finset α := μ.support ∪ ν.support
  have hμ_avg :
      avgOver μ f = ∑ a ∈ u, μ.weight a * f a := by
    unfold avgOver
    have hsubset : μ.support ⊆ u := by
      intro a ha
      exact Finset.mem_union_left ν.support ha
    exact Finset.sum_subset hsubset (fun a _ ha => by rw [μ.outsideSupport a ha, zero_mul])
  have hν_avg :
      avgOver ν f = ∑ a ∈ u, ν.weight a * f a := by
    unfold avgOver
    have hsubset : ν.support ⊆ u := by
      intro a ha
      exact Finset.mem_union_right μ.support ha
    exact Finset.sum_subset hsubset (fun a _ ha => by rw [ν.outsideSupport a ha, zero_mul])
  have hpoint :
      ∀ a, ν.weight a * f a ≤ μ.weight a * f a + max 0 (ν.weight a - μ.weight a) := by
    intro a
    by_cases hle : ν.weight a ≤ μ.weight a
    · have hmul : ν.weight a * f a ≤ μ.weight a * f a := by
        exact mul_le_mul_of_nonneg_right hle (hf_nonneg a)
      have hmax : max 0 (ν.weight a - μ.weight a) = 0 := by
        rw [max_eq_left]
        linarith
      rw [hmax]
      linarith
    · have hμν : μ.weight a ≤ ν.weight a := le_of_not_ge hle
      have hdiff_nonneg : 0 ≤ ν.weight a - μ.weight a := by linarith
      have hmul :
          (ν.weight a - μ.weight a) * f a ≤ ν.weight a - μ.weight a := by
        have := mul_le_mul_of_nonneg_left (hf_le_one a) hdiff_nonneg
        simpa [one_mul] using this
      have hsplit :
          ν.weight a * f a =
            μ.weight a * f a + (ν.weight a - μ.weight a) * f a := by
        ring
      have hmax : max 0 (ν.weight a - μ.weight a) =
          ν.weight a - μ.weight a := max_eq_right hdiff_nonneg
      rw [hsplit, hmax]
      linarith
  have hsum :
      ∑ a ∈ u, ν.weight a * f a ≤
        ∑ a ∈ u, (μ.weight a * f a + max 0 (ν.weight a - μ.weight a)) :=
    Finset.sum_le_sum fun a _ => hpoint a
  have htv :
      totalVariationDistance μ ν =
        ∑ a ∈ u, max 0 (ν.weight a - μ.weight a) := by
    exact totalVariationDistance_eq_sum_max_sub μ ν hμ hν
  rw [hμ_avg, hν_avg]
  calc
    ∑ a ∈ u, ν.weight a * f a
        ≤ ∑ a ∈ u, (μ.weight a * f a + max 0 (ν.weight a - μ.weight a)) :=
          hsum
    _ = ∑ a ∈ u, μ.weight a * f a +
          ∑ a ∈ u, max 0 (ν.weight a - μ.weight a) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ a ∈ u, μ.weight a * f a + totalVariationDistance μ ν := by
          rw [← htv]

/-- Averaging a constant against the uniform distribution on a nonempty finite type
returns that constant. -/
theorem avgOver_uniform_const {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (c : Error) :
    avgOver (uniformDistribution α) (fun _ : α => c) = c := by
  exact avgOver_const_of_isProbability
    (uniformDistribution α) (uniformDistribution_isProbability α) c

/-- Module-valued finite-sum expression for the uniform distribution, stated
without measurable-space assumptions. -/
theorem uniformDistribution_sum_smul_eq_pmf_sum {α M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [AddCommMonoid M] [Module Error M] (f : α → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
  rw [Distribution.sum_smul_eq_toPMF_sum
    (uniformDistribution α) (uniformDistribution_isProbability α)]
  rw [uniformDistribution_toPMF]

/-- A finite-support uniform weighted sum is the corresponding Mathlib uniform
PMF-weighted sum. -/
theorem uniformOnFinset_sum_smul_eq_pmf_sum {α M : Type*}
    [AddCommMonoid M] [Module Error M]
    (s : Finset α) (hs : s.Nonempty) (f : α → M) :
    ∑ a ∈ (Distribution.uniformOnFinset s).support,
        (Distribution.uniformOnFinset s).weight a • f a =
      ∑ a ∈ s, (PMF.uniformOfFinset s hs a).toReal • f a := by
  rw [Distribution.sum_smul_eq_toPMF_support_sum
    (Distribution.uniformOnFinset s)
    (Distribution.uniformOnFinset_isProbability s hs)]
  rw [Distribution.uniformOnFinset_support, Distribution.uniformOnFinset_toPMF]

/-- Finite-sum expression for the uniform average, stated without measurable-space
assumptions. -/
theorem avgOver_uniform_eq_pmf_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → Error) :
    avgOver (uniformDistribution α) f =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal * f a := by
  simpa [avgOver, smul_eq_mul] using
    uniformDistribution_sum_smul_eq_pmf_sum (α := α) (f := f)

/-- A finite-support uniform average is the corresponding Mathlib uniform PMF sum. -/
theorem avgOver_uniformOnFinset_eq_pmf_sum {α : Type*} (s : Finset α)
    (hs : s.Nonempty) (f : α → Error) :
    avgOver (Distribution.uniformOnFinset s) f =
      ∑ a ∈ s, (PMF.uniformOfFinset s hs a).toReal * f a := by
  simpa [avgOver, smul_eq_mul] using
    uniformOnFinset_sum_smul_eq_pmf_sum (s := s) hs f

/-- A finite-support uniform average is the finite integral with respect to the
corresponding Mathlib uniform probability mass function. -/
theorem avgOver_uniformOnFinset_eq_pmf_integral {α : Type*}
    [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Finset α) (hs : s.Nonempty) (f : α → Error) :
    avgOver (Distribution.uniformOnFinset s) f =
      ∫ a, f a ∂(PMF.uniformOfFinset s hs).toMeasure := by
  haveI := Fintype.ofFinite α
  rw [avgOver_uniformOnFinset_eq_pmf_sum s hs, PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  symm
  refine Distribution.sum_univ_eq_sum_support (Distribution.uniformOnFinset s)
    (fun a => (PMF.uniformOfFinset s hs a).toReal * f a) ?_
  intro a ha
  rw [Distribution.uniformOnFinset_support] at ha
  simp [PMF.uniformOfFinset_apply, ha]

/-- The uniform average with respect to `uniformDistribution` is the finite integral
with respect to the uniform probability mass function. -/
theorem avgOver_uniform_eq_pmf_integral {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → Error) :
    avgOver (uniformDistribution α) f =
      ∫ a, f a ∂(PMF.uniformOfFintype α).toMeasure := by
  rw [avgOver_uniform_eq_pmf_sum, PMF.integral_eq_sum]
  simp

/-- A uniform average over a finite support is the same as the uniform average
over the corresponding finite subtype. -/
theorem avgOver_uniformOnFinset_eq_subtype {α : Type*} [DecidableEq α]
    (s : Finset α) [Nonempty {a : α // a ∈ s}] (f : α → Error) :
    avgOver (Distribution.uniformOnFinset s) f =
      avgOver (uniformDistribution {a : α // a ∈ s}) (fun a => f a.1) := by
  classical
  have hs : s.Nonempty := by
    rcases (inferInstance : Nonempty {a : α // a ∈ s}) with ⟨a⟩
    exact ⟨a.1, a.2⟩
  have hcard : (s.card : Error) = (Fintype.card {a : α // a ∈ s} : Error) := by
    rw [Fintype.card_coe s]
  rw [avgOver_uniformOnFinset_eq_pmf_sum s hs, avgOver_uniform_eq_pmf_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← hcard]
  calc
    ∑ x ∈ s, (PMF.uniformOfFinset s hs x).toReal * f x
        = ∑ x ∈ s, (s.card : Error)⁻¹ * f x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [PMF.uniformOfFinset_apply, hx, ENNReal.toReal_inv,
            ENNReal.toReal_natCast]
    _ = ∑ x ∈ s.attach, (s.card : Error)⁻¹ * f x.1 := by
          exact
            (Finset.sum_attach s
              (fun x : α => (s.card : Error)⁻¹ * f x)).symm
    _ = ∑ x : {x : α // x ∈ s}, (s.card : Error)⁻¹ * f x.1 := by
          rw [Finset.attach_eq_univ]

/-- The uniform operator average is the finite operator sum weighted by
`PMF.uniformOfFintype`. -/
theorem averageOperatorOverDistribution_uniform_eq_pmf_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution α) f =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_eq_pmf_sum (α := α) (f := f)

/-- A finite-support uniform operator average is the corresponding Mathlib uniform PMF sum. -/
theorem averageOperatorOverDistribution_uniformOnFinset_eq_pmf_sum
    {α : Type*} (s : Finset α) (hs : s.Nonempty)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (Distribution.uniformOnFinset s) f =
      ∑ a ∈ s, (PMF.uniformOfFinset s hs a).toReal • f a := by
  simpa [averageOperatorOverDistribution] using
    uniformOnFinset_sum_smul_eq_pmf_sum (s := s) hs f

/-- Reindexing a uniform operator average along an equivalence preserves its value. -/
theorem averageOperatorOverDistribution_uniform_equiv
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution α) f =
      averageOperatorOverDistribution (uniformDistribution β)
        (fun b => f (e.symm b)) := by
  rw [averageOperatorOverDistribution_uniform_eq_pmf_sum,
    averageOperatorOverDistribution_uniform_eq_pmf_sum]
  exact pmf_uniformOfFintype_sum_equiv_smul e f

/-- A uniform operator average over a finite support is the same as the uniform
operator average over the corresponding finite subtype. -/
theorem averageOperatorOverDistribution_uniformOnFinset_eq_subtype
    {α : Type*} [DecidableEq α] (s : Finset α)
    [Nonempty {a : α // a ∈ s}]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (Distribution.uniformOnFinset s) f =
      averageOperatorOverDistribution (uniformDistribution {a : α // a ∈ s})
        (fun a => f a.1) := by
  classical
  have hs : s.Nonempty := by
    rcases (inferInstance : Nonempty {a : α // a ∈ s}) with ⟨a⟩
    exact ⟨a.1, a.2⟩
  have hcard : (s.card : Error) = (Fintype.card {a : α // a ∈ s} : Error) := by
    rw [Fintype.card_coe s]
  rw [averageOperatorOverDistribution_uniformOnFinset_eq_pmf_sum s hs,
    averageOperatorOverDistribution_uniform_eq_pmf_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← hcard]
  calc
    ∑ x ∈ s, (PMF.uniformOfFinset s hs x).toReal • f x
        = ∑ x ∈ s, (s.card : Error)⁻¹ • f x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [PMF.uniformOfFinset_apply, hx, ENNReal.toReal_inv,
            ENNReal.toReal_natCast]
    _ = ∑ x ∈ s.attach, (s.card : Error)⁻¹ • f x.1 := by
          exact
            (Finset.sum_attach s
              (fun x : α => (s.card : Error)⁻¹ • f x)).symm
    _ = ∑ x : {x : α // x ∈ s}, (s.card : Error)⁻¹ • f x.1 := by
          rw [Finset.attach_eq_univ]

/-- A uniform operator average over a finite support may be reindexed by any
finite type equivalent to that support subtype. -/
theorem averageOperatorOverDistribution_uniformOnFinset_equiv
    {α β : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    (s : Finset α) (e : β ≃ {a : α // a ∈ s})
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (Distribution.uniformOnFinset s) f =
      averageOperatorOverDistribution (uniformDistribution β) (fun b => f (e b).1) := by
  classical
  haveI : Nonempty {a : α // a ∈ s} :=
    ⟨e (Classical.choice (inferInstance : Nonempty β))⟩
  calc
    averageOperatorOverDistribution (Distribution.uniformOnFinset s) f =
        averageOperatorOverDistribution (uniformDistribution {a : α // a ∈ s})
          (fun a => f a.1) := by
          exact averageOperatorOverDistribution_uniformOnFinset_eq_subtype s f
    _ = averageOperatorOverDistribution (uniformDistribution β) (fun b => f (e b).1) := by
          simpa using
            (averageOperatorOverDistribution_uniform_equiv (e := e.symm)
              (f := fun a : {a : α // a ∈ s} => f a.1))

/-- A uniform operator average over a filtered finite support is the uniform
operator average over the finite subtype satisfying the predicate. -/
theorem averageOperatorOverDistribution_uniformOnFinset_filter_eq_subtype
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] [Nonempty {a : α // p a}]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution
        (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      averageOperatorOverDistribution (uniformDistribution {a : α // p a})
        (fun a => f a.1) := by
  classical
  let support : Finset α := Finset.univ.filter p
  let e : {a : α // a ∈ support} ≃ {a : α // p a} :=
    { toFun := fun a => ⟨a.1, (Finset.mem_filter.mp a.2).2⟩
      invFun := fun a =>
        ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ a.1, a.2⟩⟩
      left_inv := by
        intro a
        rfl
      right_inv := by
        intro a
        rfl }
  haveI : Nonempty {a : α // a ∈ support} := by
    rcases (inferInstance : Nonempty {a : α // p a}) with ⟨a⟩
    exact ⟨⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ a.1, a.2⟩⟩⟩
  calc
    averageOperatorOverDistribution
        (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
        averageOperatorOverDistribution (Distribution.uniformOnFinset support) f := by
          rfl
    _ = averageOperatorOverDistribution (uniformDistribution {a : α // a ∈ support})
          (fun a => f a.1) := by
          exact averageOperatorOverDistribution_uniformOnFinset_eq_subtype support f
    _ = averageOperatorOverDistribution (uniformDistribution {a : α // p a})
          (fun a => f a.1) := by
          simpa [e] using
            (averageOperatorOverDistribution_uniform_equiv (e := e)
              (f := fun a : {a : α // a ∈ support} => f a.1))

/-- A uniform operator average over a filtered finite type may be reindexed by
any finite seed type equivalent to the predicate subtype. -/
theorem averageOperatorOverDistribution_uniformOnFinset_filter_equiv
    {α β : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : β ≃ {a : α // p a})
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution
        (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      averageOperatorOverDistribution (uniformDistribution β) (fun b => f (e b).1) := by
  classical
  haveI : Nonempty {a : α // p a} :=
    ⟨e (Classical.choice (inferInstance : Nonempty β))⟩
  calc
    averageOperatorOverDistribution
        (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
        averageOperatorOverDistribution (uniformDistribution {a : α // p a})
          (fun a => f a.1) := by
          exact averageOperatorOverDistribution_uniformOnFinset_filter_eq_subtype p f
    _ = averageOperatorOverDistribution (uniformDistribution β) (fun b => f (e b).1) := by
          simpa using
            (averageOperatorOverDistribution_uniform_equiv (e := e.symm)
              (f := fun a : {a : α // p a} => f a.1))

/-- A uniform average of effects is again bounded above by the identity operator. -/
theorem averageOperatorOverDistribution_uniform_le_one {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) (hf : ∀ a, f a ≤ 1) :
    averageOperatorOverDistribution (uniformDistribution α) f ≤ 1 :=
  averageOperatorOverDistribution_le_one_of_isProbability
    (uniformDistribution α) (uniformDistribution_isProbability α) f hf

/-- A uniform average is bounded by any supportwise upper bound. -/
theorem avgOver_uniform_le_of_forall_le_on_support {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) (δ : Error)
    (hf : ∀ a, a ∈ (uniformDistribution α).support → f a ≤ δ) :
    avgOver (uniformDistribution α) f ≤ δ :=
  Distribution.IsProbability.avgOver_le_of_forall_le_on_support
    (uniformDistribution_isProbability α) f δ hf

/-- A uniform average is bounded by any pointwise upper bound. -/
theorem avgOver_uniform_le_const {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) (δ : Error) (hf : ∀ a, f a ≤ δ) :
    avgOver (uniformDistribution α) f ≤ δ :=
  avgOver_uniform_le_of_forall_le_on_support f δ fun a _ => hf a

/-- Reindexing a uniform average along an equivalence preserves its value. -/
theorem avgOver_uniform_equiv
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (f : α → Error) :
    avgOver (uniformDistribution α) f =
      avgOver (uniformDistribution β) (fun b => f (e.symm b)) := by
  rw [avgOver_uniform_eq_pmf_sum, avgOver_uniform_eq_pmf_sum]
  simpa [smul_eq_mul] using
    (pmf_uniformOfFintype_sum_equiv_smul (M := Error) e f)

/-- A uniform average over a finite support may be reindexed by any finite type
equivalent to that support subtype. -/
theorem avgOver_uniformOnFinset_equiv {α β : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    (s : Finset α) (e : β ≃ {a : α // a ∈ s}) (f : α → Error) :
    avgOver (Distribution.uniformOnFinset s) f =
      avgOver (uniformDistribution β) (fun b => f (e b).1) := by
  classical
  haveI : Nonempty {a : α // a ∈ s} :=
    ⟨e (Classical.choice (inferInstance : Nonempty β))⟩
  calc
    avgOver (Distribution.uniformOnFinset s) f =
        avgOver (uniformDistribution {a : α // a ∈ s}) (fun a => f a.1) := by
          exact avgOver_uniformOnFinset_eq_subtype s f
    _ = avgOver (uniformDistribution β) (fun b => f (e b).1) := by
          simpa using
            (avgOver_uniform_equiv (e := e.symm)
              (f := fun a : {a : α // a ∈ s} => f a.1))

/-- A uniform average over a finite filtered support is the uniform average over
the finite subtype satisfying the predicate. -/
theorem avgOver_uniformOnFinset_filter_eq_subtype {α : Type*}
    [Fintype α] [DecidableEq α] (p : α → Prop) [DecidablePred p]
    [Nonempty {a : α // p a}] (f : α → Error) :
    avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      avgOver (uniformDistribution {a : α // p a}) (fun a => f a.1) := by
  classical
  let support : Finset α := Finset.univ.filter p
  let e : {a : α // a ∈ support} ≃ {a : α // p a} :=
    { toFun := fun a => ⟨a.1, (Finset.mem_filter.mp a.2).2⟩
      invFun := fun a =>
        ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ a.1, a.2⟩⟩
      left_inv := by
        intro a
        rfl
      right_inv := by
        intro a
        rfl }
  haveI : Nonempty {a : α // a ∈ support} := by
    rcases (inferInstance : Nonempty {a : α // p a}) with ⟨a⟩
    exact ⟨⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ a.1, a.2⟩⟩⟩
  calc
    avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
        avgOver (Distribution.uniformOnFinset support) f := by
          rfl
    _ = avgOver (uniformDistribution {a : α // a ∈ support}) (fun a => f a.1) := by
          exact avgOver_uniformOnFinset_eq_subtype support f
    _ = avgOver (uniformDistribution {a : α // p a}) (fun a => f a.1) := by
          simpa [e] using
            (avgOver_uniform_equiv (e := e)
              (f := fun a : {a : α // a ∈ support} => f a.1))

/-- A uniform average over a filtered finite type may be reindexed by any finite
seed type equivalent to the predicate subtype. -/
theorem avgOver_uniformOnFinset_filter_equiv {α β : Type*}
    [Fintype α] (p : α → Prop) [DecidablePred p]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : β ≃ {a : α // p a}) (f : α → Error) :
    avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      avgOver (uniformDistribution β) (fun b => f (e b).1) := by
  classical
  haveI : Nonempty {a : α // p a} :=
    ⟨e (Classical.choice (inferInstance : Nonempty β))⟩
  calc
    avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
        avgOver (uniformDistribution {a : α // p a}) (fun a => f a.1) := by
          exact avgOver_uniformOnFinset_filter_eq_subtype p f
    _ = avgOver (uniformDistribution β) (fun b => f (e b).1) := by
          simpa using
            (avgOver_uniform_equiv (e := e.symm)
              (f := fun a : {a : α // p a} => f a.1))

/-- Split a uniform average over a product into iterated uniform averages. -/
theorem avgOver_uniform_prod
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) =
      avgOver (uniformDistribution α)
        (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
  rw [avgOver_uniform_eq_pmf_sum (α := α × β)]
  rw [avgOver_uniform_eq_pmf_sum (α := α)]
  simp_rw [avgOver_uniform_eq_pmf_sum (α := β)]
  simpa [smul_eq_mul] using
    (pmf_uniformOfFintype_prod_sum_smul (M := Error) f)

/-- Swap two nested uniform averages over finite nonempty types. -/
theorem avgOver_uniform_comm
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution α) (fun a => avgOver (uniformDistribution β) (f a)) =
      avgOver (uniformDistribution β) (fun b => avgOver (uniformDistribution α)
        (fun a => f a b)) := by
  calc
    avgOver (uniformDistribution α) (fun a => avgOver (uniformDistribution β) (f a))
        = avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) := by
          exact (avgOver_uniform_prod (α := α) (β := β) (f := f)).symm
    _ = avgOver (uniformDistribution (β × α)) (fun ba => f ba.2 ba.1) := by
          simpa using
            (avgOver_uniform_equiv (e := Equiv.prodComm α β)
              (f := fun ab : α × β => f ab.1 ab.2))
    _ = avgOver (uniformDistribution β) (fun b => avgOver (uniformDistribution α)
          (fun a => f a b)) := by
          exact avgOver_uniform_prod (α := β) (β := α) (f := fun b a => f a b)

/-- Split a uniform average over a product into iterated uniform averages, with
the second coordinate averaged first. -/
theorem avgOver_uniform_prod_swap
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) =
      avgOver (uniformDistribution β)
        (fun b => avgOver (uniformDistribution α) (fun a => f a b)) := by
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2)
        = avgOver (uniformDistribution α)
            (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
          exact avgOver_uniform_prod f
    _ = avgOver (uniformDistribution β)
          (fun b => avgOver (uniformDistribution α) (fun a => f a b)) := by
          exact avgOver_uniform_comm f

/-- Pull a finite sum through a uniform average and express it as a uniform
average over the product, with the cardinality of the summed type as the
normalizing factor. -/
theorem avgOver_uniform_sum_eq_card_mul_prod
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution α) (fun a => ∑ b : β, f a b) =
      (Fintype.card β : Error) *
        avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) := by
  let c : Error := Fintype.card β
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution α) (fun a => ∑ b : β, f a b)
        = ∑ b : β, avgOver (uniformDistribution α) (fun a => f a b) := by
          exact avgOver_sum (uniformDistribution α) f
    _ = c * avgOver (uniformDistribution β)
          (fun b => avgOver (uniformDistribution α) (fun a => f a b)) := by
          symm
          calc
            c * avgOver (uniformDistribution β)
                (fun b => avgOver (uniformDistribution α) (fun a => f a b))
                = c * ((1 / c) *
                    ∑ b : β, avgOver (uniformDistribution α) (fun a => f a b)) := by
                  simp [c, avgOver, uniformDistribution, Finset.mul_sum, hc]
            _ = ∑ b : β, avgOver (uniformDistribution α) (fun a => f a b) := by
                field_simp [hc]
    _ = c * avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) := by
          rw [← avgOver_uniform_prod_swap]

/-- Transport a uniform average through an equivalence whose target is a product,
then split the product average into iterated uniform averages. -/
theorem avgOver_uniform_equiv_prod
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : γ ≃ α × β) (f : γ → Error) :
    avgOver (uniformDistribution γ) f =
      avgOver (uniformDistribution α)
        (fun a => avgOver (uniformDistribution β) (fun b => f (e.symm (a, b)))) := by
  calc
    avgOver (uniformDistribution γ) f
        = avgOver (uniformDistribution (α × β)) (fun ab => f (e.symm ab)) := by
          exact avgOver_uniform_equiv e f
    _ = avgOver (uniformDistribution α)
          (fun a => avgOver (uniformDistribution β) (fun b => f (e.symm (a, b)))) := by
          exact avgOver_uniform_prod (f := fun a b => f (e.symm (a, b)))

/-- Transport a uniform average through an equivalence whose target is a product,
then split the product average with the second coordinate averaged first. -/
theorem avgOver_uniform_equiv_prod_swap
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : γ ≃ α × β) (f : γ → Error) :
    avgOver (uniformDistribution γ) f =
      avgOver (uniformDistribution β)
        (fun b => avgOver (uniformDistribution α) (fun a => f (e.symm (a, b)))) := by
  rw [avgOver_uniform_equiv_prod (e := e) (f := f)]
  exact avgOver_uniform_comm (fun a b => f (e.symm (a, b)))

/-- A function depending only on the first coordinate of a product equivalence
has the corresponding first-coordinate uniform marginal. -/
theorem avgOver_uniform_equiv_fst
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Finite β] [Nonempty β]
    (e : γ ≃ α × β) (f : α → Error) :
    avgOver (uniformDistribution γ) (fun x => f (e x).1) =
      avgOver (uniformDistribution α) f := by
  classical
  haveI := Fintype.ofFinite β
  rw [avgOver_uniform_equiv_prod (e := e) (f := fun x => f (e x).1)]
  refine avgOver_congr _ _ _ ?_
  intro a
  simpa using (avgOver_uniform_const (α := β) (c := f a))

/-- A function depending only on the second coordinate of a product equivalence
has the corresponding second-coordinate uniform marginal. -/
theorem avgOver_uniform_equiv_snd
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : γ ≃ α × β) (f : β → Error) :
    avgOver (uniformDistribution γ) (fun x => f (e x).2) =
      avgOver (uniformDistribution β) f := by
  classical
  haveI := Fintype.ofFinite α
  rw [avgOver_uniform_equiv_prod_swap (e := e) (f := fun x => f (e x).2)]
  refine avgOver_congr _ _ _ ?_
  intro b
  simpa using (avgOver_uniform_const (α := α) (c := f b))

/-- Averaging a function depending only on the first coordinate marginalizes a uniform product. -/
theorem avgOver_uniform_fst {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1) =
      avgOver (uniformDistribution α) f := by
  simpa using (avgOver_uniform_equiv_fst (e := Equiv.refl (α × β)) (f := f))

/-- Averaging a function depending only on the second coordinate marginalizes a uniform product. -/
theorem avgOver_uniform_snd {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.2) =
      avgOver (uniformDistribution β) f := by
  simpa using (avgOver_uniform_equiv_snd (e := Equiv.refl (α × β)) (f := f))

end MIPStarRE.LDT
