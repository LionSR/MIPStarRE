import MIPStarRE.LDT.Basic.Distribution
import MIPStarRE.LDT.Basic.PMFAverages

/-!
# Module-valued uniform finite sums for project distributions

This module contains the module-valued finite-sum algebra for the project
`Distribution` type.  The statements keep the paper-facing
`uniformDistribution` notation, but their proofs reduce the probability
calculation to Mathlib probability mass functions.

## Main declarations

* `Distribution.sum_smul_eq_toPMF_support_sum`
* `Distribution.sum_smul_eq_toPMF_sum`
* `uniformDistribution_sum_smul_eq_pmf_sum`
* `uniformDistribution_sum_smul_equiv`
* `uniformDistribution_sum_smul_prod`
* `uniformDistribution_map_sum_smul_eq_uniform_of_factor_equiv`
* `uniformOnFinset_sum_smul_eq_subtype`
* `uniformOnFinset_filter_sum_smul_equiv`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

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

/-- A constant family has uniform module-valued average equal to that constant.
This is the project-distribution form of `PMF.sum_const_smul`. -/
theorem uniformDistribution_sum_smul_const {α M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [AddCommMonoid M] [Module Error M] (x : M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • x = x := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum]
  exact PMF.sum_const_smul (PMF.uniformOfFintype α) x

/-- Reindex a uniform module-valued average along an equivalence. -/
theorem uniformDistribution_sum_smul_equiv {α β M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : α ≃ β) (f : α → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a =
      ∑ b ∈ (uniformDistribution β).support,
        (uniformDistribution β).weight b • f (e.symm b) := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  exact PMF.uniformOfFintype_sum_equiv_smul e f

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
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α × β)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  simp_rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  exact PMF.uniformOfFintype_prod_sum_smul f

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
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := γ)]
  exact PMF.uniformOfFintype_sum_factor_equiv_smul
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
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := γ)]
  exact PMF.uniformOfFintype_sum_factor_equiv_fst_smul
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
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := δ)]
  exact PMF.uniformOfFintype_sum_factor_equiv_snd_smul
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

/-- A finite-support uniform module-valued average is the corresponding uniform
average over the support subtype. -/
theorem uniformOnFinset_sum_smul_eq_subtype {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] [Module Error M]
    (s : Finset α) [Nonempty {a : α // a ∈ s}] (f : α → M) :
    ∑ a ∈ (Distribution.uniformOnFinset s).support,
        (Distribution.uniformOnFinset s).weight a • f a =
      ∑ a ∈ (uniformDistribution {a : α // a ∈ s}).support,
        (uniformDistribution {a : α // a ∈ s}).weight a • f a.1 := by
  classical
  have hs : s.Nonempty := by
    rcases (inferInstance : Nonempty {a : α // a ∈ s}) with ⟨a⟩
    exact ⟨a.1, a.2⟩
  have hcard : (s.card : Error) = (Fintype.card {a : α // a ∈ s} : Error) := by
    rw [Fintype.card_coe s]
  rw [uniformOnFinset_sum_smul_eq_pmf_sum s hs, uniformDistribution_sum_smul_eq_pmf_sum]
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
          exact (Finset.sum_attach s (fun x : α => (s.card : Error)⁻¹ • f x)).symm
    _ = ∑ x : {x : α // x ∈ s}, (s.card : Error)⁻¹ • f x.1 := by
          rw [Finset.attach_eq_univ]

/-- A finite-support uniform module-valued average may be reindexed by any
finite type equivalent to the support subtype. -/
theorem uniformOnFinset_sum_smul_equiv {α β M : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (s : Finset α) (e : β ≃ {a : α // a ∈ s}) (f : α → M) :
    ∑ a ∈ (Distribution.uniformOnFinset s).support,
        (Distribution.uniformOnFinset s).weight a • f a =
      ∑ b ∈ (uniformDistribution β).support,
        (uniformDistribution β).weight b • f (e b).1 := by
  classical
  haveI : Nonempty {a : α // a ∈ s} :=
    ⟨e (Classical.choice (inferInstance : Nonempty β))⟩
  calc
    ∑ a ∈ (Distribution.uniformOnFinset s).support,
        (Distribution.uniformOnFinset s).weight a • f a =
        ∑ a ∈ (uniformDistribution {a : α // a ∈ s}).support,
          (uniformDistribution {a : α // a ∈ s}).weight a • f a.1 := by
          exact uniformOnFinset_sum_smul_eq_subtype s f
    _ = ∑ b ∈ (uniformDistribution β).support,
          (uniformDistribution β).weight b • f (e b).1 := by
          simpa using
            (uniformDistribution_sum_smul_equiv (e := e.symm)
              (f := fun a : {a : α // a ∈ s} => f a.1))

/-- A uniform module-valued average over a filtered finite support is the uniform
average over the finite subtype satisfying the predicate. -/
theorem uniformOnFinset_filter_sum_smul_eq_subtype {α M : Type*}
    [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] [Nonempty {a : α // p a}]
    [AddCommMonoid M] [Module Error M] (f : α → M) :
    ∑ a ∈ (Distribution.uniformOnFinset (Finset.univ.filter p)).support,
        (Distribution.uniformOnFinset (Finset.univ.filter p)).weight a • f a =
      ∑ a ∈ (uniformDistribution {a : α // p a}).support,
        (uniformDistribution {a : α // p a}).weight a • f a.1 := by
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
    ∑ a ∈ (Distribution.uniformOnFinset (Finset.univ.filter p)).support,
        (Distribution.uniformOnFinset (Finset.univ.filter p)).weight a • f a =
        ∑ a ∈ (Distribution.uniformOnFinset support).support,
          (Distribution.uniformOnFinset support).weight a • f a := by
          rfl
    _ = ∑ a ∈ (uniformDistribution {a : α // a ∈ support}).support,
          (uniformDistribution {a : α // a ∈ support}).weight a • f a.1 := by
          exact uniformOnFinset_sum_smul_eq_subtype support f
    _ = ∑ a ∈ (uniformDistribution {a : α // p a}).support,
          (uniformDistribution {a : α // p a}).weight a • f a.1 := by
          simpa [e] using
            (uniformDistribution_sum_smul_equiv (e := e)
              (f := fun a : {a : α // a ∈ support} => f a.1))

/-- A uniform module-valued average over a filtered finite type may be reindexed
by any finite seed type equivalent to the predicate subtype. -/
theorem uniformOnFinset_filter_sum_smul_equiv {α β M : Type*}
    [Fintype α] (p : α → Prop) [DecidablePred p]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : β ≃ {a : α // p a}) (f : α → M) :
    ∑ a ∈ (Distribution.uniformOnFinset (Finset.univ.filter p)).support,
        (Distribution.uniformOnFinset (Finset.univ.filter p)).weight a • f a =
      ∑ b ∈ (uniformDistribution β).support,
        (uniformDistribution β).weight b • f (e b).1 := by
  classical
  haveI : Nonempty {a : α // p a} :=
    ⟨e (Classical.choice (inferInstance : Nonempty β))⟩
  calc
    ∑ a ∈ (Distribution.uniformOnFinset (Finset.univ.filter p)).support,
        (Distribution.uniformOnFinset (Finset.univ.filter p)).weight a • f a =
        ∑ a ∈ (uniformDistribution {a : α // p a}).support,
          (uniformDistribution {a : α // p a}).weight a • f a.1 := by
          exact uniformOnFinset_filter_sum_smul_eq_subtype p f
    _ = ∑ b ∈ (uniformDistribution β).support,
          (uniformDistribution β).weight b • f (e b).1 := by
          simpa using
            (uniformDistribution_sum_smul_equiv (e := e.symm)
              (f := fun a : {a : α // p a} => f a.1))

end MIPStarRE.LDT
