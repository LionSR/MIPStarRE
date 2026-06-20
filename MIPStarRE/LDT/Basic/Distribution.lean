import MIPStarRE.LDT.Basic.ParametersBase
import MIPStarRE.Quantum.FiniteMatrix
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Distribution infrastructure for the low individual degree test

Shared distribution definitions: finite-support weighted distributions,
a probability predicate, push-forward distributions, averaging, uniform
distribution, and outcome summation.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

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

/-- Push a finite-support distribution forward along a map.

This is the project `Distribution` analogue of `PMF.map`.  The support is the
image of the original finite support, and each new weight is the sum of the
weights in the corresponding fiber. -/
noncomputable def map {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) : Distribution β where
  support := 𝒟.support.image e
  weight := fun b => ∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a
  nonnegative := by
    intro b
    exact Finset.sum_nonneg fun a _ => 𝒟.nonnegative a
  outsideSupport := by
    intro b hb
    exact Finset.sum_eq_zero fun a ha => by
      rcases Finset.mem_filter.mp ha with ⟨ha𝒟, hae⟩
      have hb' : b ∈ 𝒟.support.image e := by
        rw [← hae]
        exact Finset.mem_image.mpr ⟨a, ha𝒟, rfl⟩
      exact (hb hb').elim

@[simp]
theorem map_support {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) :
    (𝒟.map e).support = 𝒟.support.image e := rfl

@[simp]
theorem map_weight {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) (b : β) :
    (𝒟.map e).weight b =
      ∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a := rfl

/-- Push-forward preserves total mass. -/
theorem map_totalWeight {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) :
    (𝒟.map e).totalWeight = 𝒟.totalWeight := by
  simpa [totalWeight, map] using
    (Finset.sum_fiberwise_of_maps_to
      (s := 𝒟.support) (t := 𝒟.support.image e) (g := e)
      (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) 𝒟.weight)

end Distribution

/-- On a finite ambient type, a summand that vanishes outside a distribution's
explicit support has the same total sum over all ambient values as over that support.

This is a project-local explicit-support adapter around Mathlib's `Finset.sum_subset`:
Mathlib supplies the finite-sum theorem, while this lemma packages the common shape used
when paper expressions sum over a whole question set but the repository stores a smaller
`Distribution.support`.  It is not intended to replace Mathlib probability theory. -/
theorem Distribution.sum_univ_eq_sum_support {α β : Type*} [Fintype α]
    [AddCommMonoid β] (𝒟 : Distribution α) (f : α → β)
    (hf : ∀ a, a ∉ 𝒟.support → f a = 0) :
    (∑ a : α, f a) = ∑ a ∈ 𝒟.support, f a := by
  classical
  simpa using
    (Finset.sum_subset (Finset.subset_univ 𝒟.support)
      (fun a _ ha => hf a ha)).symm

namespace Distribution.IsProbability

/-- Unpack the equality form of the probability invariant. -/
theorem weight_sum_eq_one {α : Type*}
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a = 1 := by
  simpa [Distribution.IsProbability, Distribution.totalWeight] using h𝒟

/-- On a finite ambient type, a probabilistic `Distribution` has total weight `1` even
when its weights are summed over the whole ambient type.

This packages the explicit-support bookkeeping in `Distribution` for downstream Lean
statements that follow the paper's notation `𝔼_{x ∼ 𝒟}` over the question set rather
than over a stored support finset. -/
theorem weight_sum_univ_eq_one {α : Type*} [Fintype α]
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) :
    (∑ a : α, 𝒟.weight a) = 1 := by
  rw [Distribution.sum_univ_eq_sum_support 𝒟 𝒟.weight 𝒟.outsideSupport]
  exact h𝒟.weight_sum_eq_one

/-- A probability distribution has total weight at most `1`. -/
theorem weight_sum_le_one {α : Type*}
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a ≤ 1 :=
  le_of_eq h𝒟.weight_sum_eq_one

/-- Push-forward preserves the probability invariant. -/
theorem map {α β : Type*} [DecidableEq β]
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) (e : α → β) :
    (𝒟.map e).IsProbability := by
  simpa [Distribution.IsProbability, Distribution.map_totalWeight] using h𝒟

end Distribution.IsProbability

/-- Average a scalar function against the stored finite support of a distribution. -/
def avgOver {α : Type*} (𝒟 : Distribution α) (f : α → Error) : Error :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a * f a

namespace Distribution

/-- Averaging against a pushed-forward distribution is averaging the pulled-back
function against the original distribution. -/
theorem avgOver_map {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) (f : β → Error) :
    avgOver (𝒟.map e) f = avgOver 𝒟 (fun a => f (e a)) := by
  classical
  unfold avgOver Distribution.map
  calc
    ∑ b ∈ 𝒟.support.image e,
        (∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a) * f b
        = ∑ b ∈ 𝒟.support.image e,
            ∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a * f (e a) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro a ha
          exact congrArg (fun x => 𝒟.weight a * f x) (Finset.mem_filter.mp ha).2.symm
    _ = ∑ a ∈ 𝒟.support, 𝒟.weight a * f (e a) := by
          exact Finset.sum_fiberwise_of_maps_to
            (s := 𝒟.support) (t := 𝒟.support.image e) (g := e)
            (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
            (fun a => 𝒟.weight a * f (e a))

end Distribution

/-- Weighted sum of operators over a distribution's finite support, using the same
`support`/`weight` data as the scalar `avgOver`.

This is a project-local adapter around Mathlib finite sums for the LDT
`Distribution` representation and `Quantum.Op` scalar action, not a replacement for
Mathlib's probability theory APIs. -/
noncomputable def averageOperatorOverDistribution {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a • f a

namespace Distribution

/-- Operator-valued averaging against a pushed-forward distribution is
operator-valued averaging of the pulled-back family against the original
distribution. -/
theorem averageOperatorOverDistribution_map {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : β → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (𝒟.map e) f =
      averageOperatorOverDistribution 𝒟 (fun a => f (e a)) := by
  classical
  unfold averageOperatorOverDistribution Distribution.map
  calc
    ∑ b ∈ 𝒟.support.image e,
        (∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a) • f b
        = ∑ b ∈ 𝒟.support.image e,
            ∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a • f (e a) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl ?_
          intro a ha
          exact congrArg (fun x => 𝒟.weight a • f x) (Finset.mem_filter.mp ha).2.symm
    _ = ∑ a ∈ 𝒟.support, 𝒟.weight a • f (e a) := by
          exact Finset.sum_fiberwise_of_maps_to
            (s := 𝒟.support) (t := 𝒟.support.image e) (g := e)
            (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
            (fun a => 𝒟.weight a • f (e a))

end Distribution

/-- Operator averages preserve positivity. -/
theorem averageOperatorOverDistribution_nonneg {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι)
    (hf : ∀ a, 0 ≤ f a) :
    0 ≤ averageOperatorOverDistribution 𝒟 f := by
  unfold averageOperatorOverDistribution
  exact Finset.sum_nonneg fun a _ => smul_nonneg (𝒟.nonnegative a) (hf a)

/-- Operator averages preserve pointwise order. -/
theorem averageOperatorOverDistribution_mono {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f g : α → MIPStarRE.Quantum.Op ι)
    (hfg : ∀ a, f a ≤ g a) :
    averageOperatorOverDistribution 𝒟 f ≤ averageOperatorOverDistribution 𝒟 g := by
  unfold averageOperatorOverDistribution
  exact Finset.sum_le_sum fun a _ =>
    smul_le_smul_of_nonneg_left (hfg a) (𝒟.nonnegative a)

/-- The average of a constant operator is the total mass times that operator. -/
theorem averageOperatorOverDistribution_const {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (A : MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun _ : α => A) =
      (∑ a ∈ 𝒟.support, 𝒟.weight a) • A := by
  unfold averageOperatorOverDistribution
  rw [Finset.sum_smul]

/-- The average of a constant operator over a probability distribution is that
operator. -/
theorem averageOperatorOverDistribution_const_of_isProbability {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (A : MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun _ : α => A) = A := by
  rw [averageOperatorOverDistribution_const, h𝒟.weight_sum_eq_one]
  simp

/-- An average of effects against a sub-probability distribution is again bounded
above by the identity operator. -/
theorem averageOperatorOverDistribution_le_one_of_weight_sum_le_one {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι)
    (h𝒟 : ∑ a ∈ 𝒟.support, 𝒟.weight a ≤ 1)
    (hf : ∀ a, f a ≤ 1) :
    averageOperatorOverDistribution 𝒟 f ≤ 1 := by
  calc
    averageOperatorOverDistribution 𝒟 f
        ≤ averageOperatorOverDistribution 𝒟 (fun _ : α => 1) := by
          exact averageOperatorOverDistribution_mono 𝒟 f (fun _ : α => 1) hf
    _ = (∑ a ∈ 𝒟.support, 𝒟.weight a) • (1 : MIPStarRE.Quantum.Op ι) := by
          exact averageOperatorOverDistribution_const 𝒟 1
    _ ≤ (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
          exact smul_le_smul_of_nonneg_right h𝒟 zero_le_one
    _ = 1 := by simp

/-- An average of effects against a probability distribution is again bounded
above by the identity operator. -/
theorem averageOperatorOverDistribution_le_one_of_isProbability {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    (f : α → MIPStarRE.Quantum.Op ι) (hf : ∀ a, f a ≤ 1) :
    averageOperatorOverDistribution 𝒟 f ≤ 1 :=
  averageOperatorOverDistribution_le_one_of_weight_sum_le_one 𝒟 f h𝒟.weight_sum_le_one hf

namespace Distribution

/-- The uniform distribution on a specified finite support.

The stored support is `s`, and the weight of a point is the elementary finite
uniform weight `1 / s.card` on `s` and `0` off `s`.  When the support is empty
this gives the zero sub-probability distribution, matching the convention used
for degenerate filtered supports in the LDT development. -/
noncomputable def uniformOnFinset {α : Type*} (s : Finset α) : Distribution α := by
  classical
  exact
    { support := s
      weight := fun a => if a ∈ s then 1 / (s.card : Error) else 0
      nonnegative := by
        intro a
        by_cases ha : a ∈ s
        · simp [ha]
        · simp [ha]
      outsideSupport := by
        intro a ha
        simp [ha] }

@[simp]
theorem uniformOnFinset_support {α : Type*} (s : Finset α) :
    (uniformOnFinset s).support = s := rfl

@[simp]
theorem uniformOnFinset_weight {α : Type*} [DecidableEq α] (s : Finset α) (a : α) :
    (uniformOnFinset s).weight a =
      if a ∈ s then 1 / (s.card : Error) else 0 := by
  by_cases ha : a ∈ s
  · simp [uniformOnFinset, ha]
  · simp [uniformOnFinset, ha]

/-- A nonempty finite support gives a probability distribution. -/
theorem uniformOnFinset_isProbability {α : Type*} (s : Finset α) (hs : s.Nonempty) :
    (uniformOnFinset s).IsProbability := by
  classical
  dsimp [IsProbability, totalWeight]
  simp_rw [uniformOnFinset_weight]
  have hcard_nat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hcard : (s.card : Error) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hsum :
      (∑ a ∈ s, if a ∈ s then 1 / (s.card : Error) else 0) =
        ∑ _a ∈ s, 1 / (s.card : Error) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    simp [ha]
  rw [hsum]
  simp [Finset.sum_const, hcard]

/-- The uniform distribution on any finite support is a sub-probability
distribution.  It has mass `1` on nonempty support and mass `0` on empty
support. -/
theorem uniformOnFinset_weight_sum_le_one {α : Type*} (s : Finset α) :
    ∑ a ∈ (uniformOnFinset s).support, (uniformOnFinset s).weight a ≤ 1 := by
  classical
  by_cases hs : s.Nonempty
  · exact (uniformOnFinset_isProbability s hs).weight_sum_le_one
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hsempty]

end Distribution

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniformDistribution (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] : Distribution α :=
  Distribution.uniformOnFinset Finset.univ

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

/-- If two operator-valued families agree pointwise, their averages agree. -/
theorem averageOperatorOverDistribution_congr {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (A B : α → MIPStarRE.Quantum.Op ι)
    (h : ∀ a, A a = B a) :
    averageOperatorOverDistribution 𝒟 A = averageOperatorOverDistribution 𝒟 B := by
  exact Finset.sum_congr rfl fun a _ => by rw [h a]

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

/-- The weights of a uniform distribution sum to exactly `1`. -/
theorem uniformDistribution_weight_sum_eq_one (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a = 1 := by
  have h : (uniformDistribution α).IsProbability := by
    simpa [uniformDistribution] using
      Distribution.uniformOnFinset_isProbability (Finset.univ : Finset α)
        Finset.univ_nonempty
  exact h.weight_sum_eq_one

/-- The uniform distribution is a genuine probability distribution. -/
theorem uniformDistribution_isProbability (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    (uniformDistribution α).IsProbability := by
  simpa [uniformDistribution] using
    Distribution.uniformOnFinset_isProbability (Finset.univ : Finset α) Finset.univ_nonempty

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
  exact avgOver_const_of_isProbability
    (uniformDistribution α) (uniformDistribution_isProbability α) c

/-- Finite-sum expression for the uniform average, stated without measurable-space
assumptions. -/
theorem avgOver_uniform_eq_pmf_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → Error) :
    avgOver (uniformDistribution α) f =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal * f a := by
  unfold uniformDistribution avgOver
  rw [Distribution.uniformOnFinset_support]
  simp [Distribution.uniformOnFinset_weight, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

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
  have hcard : (s.card : Error) = (Fintype.card {a : α // a ∈ s} : Error) := by
    rw [Fintype.card_coe s]
  rw [avgOver_uniform_eq_pmf_sum]
  unfold avgOver
  rw [Distribution.uniformOnFinset_support]
  simp_rw [Distribution.uniformOnFinset_weight]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← hcard]
  calc
    ∑ x ∈ s, (if x ∈ s then 1 / (s.card : Error) else 0) * f x
        = ∑ x ∈ s, (s.card : Error)⁻¹ * f x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [hx]
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
  unfold uniformDistribution averageOperatorOverDistribution
  rw [Distribution.uniformOnFinset_support]
  simp [Distribution.uniformOnFinset_weight, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

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
  exact Fintype.sum_equiv e
    (fun a => (PMF.uniformOfFintype α a).toReal * f a)
    (fun b => (PMF.uniformOfFintype β b).toReal * f (e.symm b)) (by
      intro a
      simp [PMF.uniformOfFintype_apply, Fintype.card_congr e])

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
  have hα : ((Fintype.card α : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : ((Fintype.card β : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    ∑ ab : α × β, (PMF.uniformOfFintype (α × β) ab).toReal * f ab.1 ab.2
      = ∑ a : α, ∑ b : β,
          (PMF.uniformOfFintype (α × β) (a, b)).toReal * f a b := by
            simpa using
              (Fintype.sum_prod_type' (f := fun a : α => fun b : β =>
                (PMF.uniformOfFintype (α × β) (a, b)).toReal * f a b))
    _ = ∑ a : α, (PMF.uniformOfFintype α a).toReal *
          ∑ b : β, (PMF.uniformOfFintype β b).toReal * f a b := by
            refine Finset.sum_congr rfl ?_
            intro a _
            calc
              ∑ b : β, (PMF.uniformOfFintype (α × β) (a, b)).toReal * f a b
                = ∑ b : β, ((PMF.uniformOfFintype α a).toReal *
                    (PMF.uniformOfFintype β b).toReal) * f a b := by
                      refine Finset.sum_congr rfl ?_
                      intro b _
                      simp [PMF.uniformOfFintype_apply, Fintype.card_prod]
                      field_simp [hα, hβ]
                      simp
              _ = (PMF.uniformOfFintype α a).toReal *
                    ∑ b : β, (PMF.uniformOfFintype β b).toReal * f a b := by
                      rw [Finset.mul_sum]
                      simp [mul_assoc]

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

end MIPStarRE.LDT
