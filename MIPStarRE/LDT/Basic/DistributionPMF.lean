import MIPStarRE.LDT.Basic.DistributionAvg

/-!
# PMF expectations associated to project distributions

This module relates the project `Distribution` averaging notation to the finite
expectation `PMF.realWeightedSum` on Mathlib probability mass functions.  The
statements keep the project-facing averages available while allowing later
probability arguments to cite the associated Mathlib `PMF` object directly.

## Main declarations

* `avgOver_eq_toPMF_realWeightedSum`
* `averageOperatorOverDistribution_eq_toPMF_realWeightedSum`
* `uniformDistribution_sum_smul_eq_pmf_realWeightedSum`
* `uniformDistribution_sum_smul_equiv`
* `uniformDistribution_sum_smul_prod`
* `uniformDistribution_sum_smul_factor_equiv`
* `avgOver_uniform_eq_pmf_realWeightedSum`
* `averageOperatorOverDistribution_uniform_eq_pmf_realWeightedSum`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- Averaging against a probabilistic project distribution is the finite
expectation against its associated Mathlib probability mass function. -/
theorem avgOver_eq_toPMF_realWeightedSum {α : Type*} [Fintype α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → Error) :
    avgOver 𝒟 f = PMF.realWeightedSum (𝒟.toPMF h𝒟) f := by
  simpa [PMF.realWeightedSum, smul_eq_mul] using
    avgOver_eq_toPMF_sum 𝒟 h𝒟 f

/-- Operator-valued averaging against a probabilistic project distribution is
the finite expectation against its associated Mathlib probability mass
function. -/
theorem averageOperatorOverDistribution_eq_toPMF_realWeightedSum {α : Type*}
    [Fintype α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 f =
      PMF.realWeightedSum (𝒟.toPMF h𝒟) f := by
  simpa [PMF.realWeightedSum] using
    averageOperatorOverDistribution_eq_toPMF_sum 𝒟 h𝒟 f

/-- Module-valued finite expectation for the uniform distribution, stated
directly in terms of Mathlib's uniform probability mass function. -/
theorem uniformDistribution_sum_smul_eq_pmf_realWeightedSum {α M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [AddCommMonoid M] [Module Error M] (f : α → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a =
      PMF.realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa [PMF.realWeightedSum] using
    uniformDistribution_sum_smul_eq_pmf_sum (α := α) (f := f)

/-- A constant family has uniform module-valued average equal to that constant.
This is the project-distribution form of `PMF.realWeightedSum_const`. -/
theorem uniformDistribution_sum_smul_const {α M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [AddCommMonoid M] [Module Error M] (x : M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • x = x := by
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum]
  exact PMF.realWeightedSum_const (PMF.uniformOfFintype α) x

/-- Reindex a uniform module-valued average along an equivalence. -/
theorem uniformDistribution_sum_smul_equiv {α β M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : α ≃ β) (f : α → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a =
      ∑ b ∈ (uniformDistribution β).support,
        (uniformDistribution β).weight b • f (e.symm b) := by
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := β)]
  exact PMF.realWeightedSum_uniformOfFintype_equiv e f

/-- Split a uniform module-valued average over a product into iterated uniform
module-valued averages. -/
theorem uniformDistribution_sum_smul_prod {α β M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (f : α → β → M) :
    ∑ ab ∈ (uniformDistribution (α × β)).support,
        (uniformDistribution (α × β)).weight ab • f ab.1 ab.2 =
      ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a •
        ∑ b ∈ (uniformDistribution β).support,
          (uniformDistribution β).weight b • f a b := by
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := α × β)]
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := α)]
  simp_rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := β)]
  exact PMF.realWeightedSum_uniformOfFintype_prod f

/-- Swap two nested uniform module-valued averages over finite nonempty types. -/
theorem uniformDistribution_sum_smul_comm {α β M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (f : α → β → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a •
        ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b • f a b =
      ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b •
        ∑ a ∈ (uniformDistribution α).support,
          (uniformDistribution α).weight a • f a b := by
  calc
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a •
        ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b • f a b
        = ∑ ab ∈ (uniformDistribution (α × β)).support,
            (uniformDistribution (α × β)).weight ab • f ab.1 ab.2 := by
          exact (uniformDistribution_sum_smul_prod (f := f)).symm
    _ = ∑ ba ∈ (uniformDistribution (β × α)).support,
          (uniformDistribution (β × α)).weight ba • f ba.2 ba.1 := by
          exact uniformDistribution_sum_smul_equiv
            (e := Equiv.prodComm α β) (f := fun ab : α × β => f ab.1 ab.2)
    _ = ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b •
          ∑ a ∈ (uniformDistribution α).support,
            (uniformDistribution α).weight a • f a b := by
          exact uniformDistribution_sum_smul_prod
            (α := β) (β := α) (f := fun b a => f a b)

/-- Split a uniform module-valued average over a product into iterated uniform
module-valued averages, with the second coordinate averaged first. -/
theorem uniformDistribution_sum_smul_prod_swap {α β M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (f : α → β → M) :
    ∑ ab ∈ (uniformDistribution (α × β)).support,
        (uniformDistribution (α × β)).weight ab • f ab.1 ab.2 =
      ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b •
        ∑ a ∈ (uniformDistribution α).support,
          (uniformDistribution α).weight a • f a b := by
  rw [uniformDistribution_sum_smul_prod (f := f)]
  exact uniformDistribution_sum_smul_comm f

/-- Transport a uniform module-valued average through an equivalence whose
target is a product, then split the product average. -/
theorem uniformDistribution_sum_smul_equiv_prod {γ α β M : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : γ → M) :
    ∑ x ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight x • f x =
      ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a •
        ∑ b ∈ (uniformDistribution β).support,
          (uniformDistribution β).weight b • f (e.symm (a, b)) := by
  calc
    ∑ x ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight x • f x
        = ∑ ab ∈ (uniformDistribution (α × β)).support,
            (uniformDistribution (α × β)).weight ab • f (e.symm ab) := by
          exact uniformDistribution_sum_smul_equiv e f
    _ = ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a •
          ∑ b ∈ (uniformDistribution β).support,
            (uniformDistribution β).weight b • f (e.symm (a, b)) := by
          exact uniformDistribution_sum_smul_prod
            (f := fun a b => f (e.symm (a, b)))

/-- Transport a uniform module-valued average through an equivalence whose
target is a product, then split the product average in the other order. -/
theorem uniformDistribution_sum_smul_equiv_prod_swap {γ α β M : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : γ → M) :
    ∑ x ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight x • f x =
      ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b •
        ∑ a ∈ (uniformDistribution α).support,
          (uniformDistribution α).weight a • f (e.symm (a, b)) := by
  rw [uniformDistribution_sum_smul_equiv_prod (e := e) (f := f)]
  exact uniformDistribution_sum_smul_comm (fun a b => f (e.symm (a, b)))

/-- A function depending only on the first coordinate of a product equivalence
has the first-coordinate uniform module-valued marginal. -/
theorem uniformDistribution_sum_smul_equiv_fst {γ α β M : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Finite β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : α → M) :
    ∑ x ∈ (uniformDistribution γ).support,
        (uniformDistribution γ).weight x • f (e x).1 =
      ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a := by
  classical
  haveI := Fintype.ofFinite β
  rw [uniformDistribution_sum_smul_equiv_prod (e := e) (f := fun x => f (e x).1)]
  refine Finset.sum_congr rfl ?_
  intro a _
  have hconst :
      ∑ b ∈ (uniformDistribution β).support,
          (uniformDistribution β).weight b • f (e (e.symm (a, b))).1 = f a := by
    simpa using uniformDistribution_sum_smul_const (α := β) (x := f a)
  rw [hconst]

/-- A function depending only on the second coordinate of a product equivalence
has the second-coordinate uniform module-valued marginal. -/
theorem uniformDistribution_sum_smul_equiv_snd {γ α β M : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : β → M) :
    ∑ x ∈ (uniformDistribution γ).support,
        (uniformDistribution γ).weight x • f (e x).2 =
      ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b • f b := by
  classical
  haveI := Fintype.ofFinite α
  rw [uniformDistribution_sum_smul_equiv_prod_swap (e := e) (f := fun x => f (e x).2)]
  refine Finset.sum_congr rfl ?_
  intro b _
  have hconst :
      ∑ a ∈ (uniformDistribution α).support,
          (uniformDistribution α).weight a • f (e (e.symm (a, b))).2 = f b := by
    simpa using uniformDistribution_sum_smul_const (α := α) (x := f b)
  rw [hconst]

/-- A uniformly sampled seed has the uniform module-valued average of an
equivalent observed coordinate. -/
theorem uniformDistribution_sum_smul_factor_equiv {α β γ M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → M) :
    ∑ a ∈ (uniformDistribution α).support,
        (uniformDistribution α).weight a • f (g (m a)) =
      ∑ c ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight c • f c := by
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := γ)]
  exact PMF.realWeightedSum_uniformOfFintype_factor_equiv
    (m := m) (g := g) (e := e) (h := h) (f := f)

/-- A uniformly sampled seed has the first-coordinate uniform module-valued
marginal when the observed coordinate factors through a product equivalence. -/
theorem uniformDistribution_sum_smul_factor_equiv_fst {α β γ δ M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → M) :
    ∑ a ∈ (uniformDistribution α).support,
        (uniformDistribution α).weight a • f (g (m a)) =
      ∑ c ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight c • f c := by
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := γ)]
  exact PMF.realWeightedSum_uniformOfFintype_factor_equiv_fst
    (m := m) (g := g) (e := e) (h := h) (f := f)

/-- A uniformly sampled seed has the second-coordinate uniform module-valued
marginal when the observed coordinate factors through a product equivalence. -/
theorem uniformDistribution_sum_smul_factor_equiv_snd {α β γ δ M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [DecidableEq δ] [Nonempty δ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2) (f : δ → M) :
    ∑ a ∈ (uniformDistribution α).support,
        (uniformDistribution α).weight a • f (g (m a)) =
      ∑ d ∈ (uniformDistribution δ).support, (uniformDistribution δ).weight d • f d := by
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_realWeightedSum (α := δ)]
  exact PMF.realWeightedSum_uniformOfFintype_factor_equiv_snd
    (m := m) (g := g) (e := e) (h := h) (f := f)

/-- A uniform push-forward has the uniform module-valued average induced by an
equivalent observed coordinate. -/
theorem uniformDistribution_map_sum_smul_eq_uniform_of_factor_equiv
    {α β γ M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → M) :
    ∑ b ∈ ((uniformDistribution α).map m).support,
        ((uniformDistribution α).map m).weight b • f (g b) =
      ∑ c ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight c • f c := by
  rw [Distribution.map_sum_smul]
  exact uniformDistribution_sum_smul_factor_equiv
    (m := m) (g := g) (e := e) (h := h) (f := f)

/-- A uniform push-forward has the first-coordinate uniform module-valued
marginal when the observed coordinate factors through a product equivalence. -/
theorem uniformDistribution_map_sum_smul_eq_uniform_fst_of_factor_equiv
    {α β γ δ M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → M) :
    ∑ b ∈ ((uniformDistribution α).map m).support,
        ((uniformDistribution α).map m).weight b • f (g b) =
      ∑ c ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight c • f c := by
  rw [Distribution.map_sum_smul]
  exact uniformDistribution_sum_smul_factor_equiv_fst
    (m := m) (g := g) (e := e) (h := h) (f := f)

/-- A uniform push-forward has the second-coordinate uniform module-valued
marginal when the observed coordinate factors through a product equivalence. -/
theorem uniformDistribution_map_sum_smul_eq_uniform_snd_of_factor_equiv
    {α β γ δ M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [DecidableEq δ] [Nonempty δ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2) (f : δ → M) :
    ∑ b ∈ ((uniformDistribution α).map m).support,
        ((uniformDistribution α).map m).weight b • f (g b) =
      ∑ d ∈ (uniformDistribution δ).support, (uniformDistribution δ).weight d • f d := by
  rw [Distribution.map_sum_smul]
  exact uniformDistribution_sum_smul_factor_equiv_snd
    (m := m) (g := g) (e := e) (h := h) (f := f)

/-- The uniform average is the finite expectation against Mathlib's uniform
probability mass function. -/
theorem avgOver_uniform_eq_pmf_realWeightedSum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → Error) :
    avgOver (uniformDistribution α) f =
      PMF.realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa [PMF.realWeightedSum, smul_eq_mul] using
    avgOver_uniform_eq_pmf_sum (α := α) f

/-- The uniform operator average is the finite expectation against Mathlib's
uniform probability mass function. -/
theorem averageOperatorOverDistribution_uniform_eq_pmf_realWeightedSum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution α) f =
      PMF.realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa [PMF.realWeightedSum] using
    averageOperatorOverDistribution_uniform_eq_pmf_sum (α := α) f

end MIPStarRE.LDT
