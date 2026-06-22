import MIPStarRE.LDT.Basic.DistributionProduct

/-!
# Uniform push-forward averaging lemmas

This file contains shared averaging lemmas for uniformly sampled finite seeds
that are pushed forward to a question distribution.  The main use case is a
random seed `a : α`, a pushed-forward value `m a : β`, and an observed
coordinate `g (m a)` which is identified with a uniform coordinate by an
equivalence.

## Main declarations

* `avgOver_uniform_map_eq_uniform_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_of_factor_equiv`
* `avgOver_uniform_map_eq_uniform_fst_of_factor_equiv`
* `avgOver_uniform_map_eq_uniform_snd_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_fst_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_snd_of_factor_equiv`
* `pmf_uniformOfFintype_sum_const_smul`
* `pmf_uniformOfFintype_sum_equiv_fst_smul`
* `pmf_uniformOfFintype_sum_equiv_snd_smul`
* `pmf_uniformOfFintype_sum_factor_equiv_smul`
* `pmf_uniformOfFintype_sum_factor_equiv_fst_smul`
* `pmf_uniformOfFintype_sum_factor_equiv_snd_smul`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### PMF-weighted map identities -/

/-- The uniform PMF-weighted sum of a constant family is the constant value. -/
theorem pmf_uniformOfFintype_sum_const_smul {α M : Type*}
    [Fintype α] [Nonempty α]
    [AddCommMonoid M] [Module Error M]
    (x : M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • x = x := by
  have hcard : (Fintype.card α : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hweight :
      (∑ a : α, (PMF.uniformOfFintype α a).toReal) = (1 : Error) := by
    simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Finset.sum_const, nsmul_eq_mul, hcard]
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • x =
        (∑ a : α, (PMF.uniformOfFintype α a).toReal) • x := by
          exact (Finset.sum_smul (s := Finset.univ)
            (f := fun a : α => (PMF.uniformOfFintype α a).toReal) (x := x)).symm
    _ = x := by rw [hweight, one_smul]

/-- Marginalize a uniform PMF-weighted sum along the first coordinate of a
product equivalence. -/
theorem pmf_uniformOfFintype_sum_equiv_fst_smul {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Fintype α] [Nonempty α]
    [Finite β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : α → M) :
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).1 =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
  classical
  haveI := Fintype.ofFinite β
  calc
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).1
        = ∑ ab : α × β,
            (PMF.uniformOfFintype (α × β) ab).toReal • f ab.1 := by
          simpa using
            (pmf_uniformOfFintype_sum_equiv_smul
              (e := e) (f := fun x : γ => f (e x).1))
    _ = ∑ a : α, (PMF.uniformOfFintype α a).toReal •
          ∑ b : β, (PMF.uniformOfFintype β b).toReal • f a := by
          exact pmf_uniformOfFintype_prod_sum_smul (fun a (_ : β) => f a)
    _ = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [pmf_uniformOfFintype_sum_const_smul (α := β) (x := f a)]

/-- Marginalize a uniform PMF-weighted sum along the second coordinate of a
product equivalence. -/
theorem pmf_uniformOfFintype_sum_equiv_snd_smul {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : β → M) :
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).2 =
      ∑ b : β, (PMF.uniformOfFintype β b).toReal • f b := by
  classical
  haveI := Fintype.ofFinite α
  simpa using
    (pmf_uniformOfFintype_sum_equiv_fst_smul
      (e := e.trans (Equiv.prodComm α β)) (f := f))

/-- A uniform PMF-weighted sum pushed forward through a map has the uniform
average of an equivalent observed coordinate. -/
theorem pmf_uniformOfFintype_sum_factor_equiv_smul {α β γ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a)) =
      ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a))
        = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (e a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [h a]
    _ = ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
          simpa using
            (pmf_uniformOfFintype_sum_equiv_smul
              (e := e) (f := fun a : α => f (e a)))

/-- A uniform PMF-weighted sum pushed forward through a map has the first
coordinate uniform marginal when the seed is equivalent to a product. -/
theorem pmf_uniformOfFintype_sum_factor_equiv_fst_smul {α β γ δ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a)) =
      ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a))
        = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (e a).1 := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [h a]
    _ = ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
          exact pmf_uniformOfFintype_sum_equiv_fst_smul (e := e) (f := f)

/-- A uniform PMF-weighted sum pushed forward through a map has the second
coordinate uniform marginal when the seed is equivalent to a product. -/
theorem pmf_uniformOfFintype_sum_factor_equiv_snd_smul {α β γ δ M : Type*}
    [Fintype α] [Nonempty α]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [Nonempty δ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2) (f : δ → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a)) =
      ∑ d : δ, (PMF.uniformOfFintype δ d).toReal • f d := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a))
        = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (e a).2 := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [h a]
    _ = ∑ d : δ, (PMF.uniformOfFintype δ d).toReal • f d := by
          exact pmf_uniformOfFintype_sum_equiv_snd_smul (e := e) (f := f)

/-! ### Project-distribution map averages -/

/-- A uniform push-forward has the uniform average induced by an equivalent
observed coordinate.

The map `m` is the finite random seed map, `g` is the observed coordinate on
the pushed-forward value, and `e` records that this observed coordinate is
equivalent to a uniform sample of `γ`. -/
theorem avgOver_uniform_map_eq_uniform_of_factor_equiv
    {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → Error) :
    avgOver ((uniformDistribution α).map m) (fun b => f (g b)) =
      avgOver (uniformDistribution γ) f := by
  rw [avgOver_uniformDistribution_map]
  rw [avgOver_uniform_eq_pmf_sum, avgOver_uniform_eq_pmf_sum]
  simpa [smul_eq_mul] using
    (pmf_uniformOfFintype_sum_factor_equiv_smul
      (m := m) (g := g) (e := e) (h := h) (f := f))

/-- A uniform push-forward has the uniform operator average induced by an
equivalent observed coordinate.

The map `m` is the finite random seed map, `g` is the observed coordinate on
the pushed-forward value, and `e` records that this observed coordinate is
equivalent to a uniform sample of `γ`. -/
theorem averageOperatorOverDistribution_uniform_map_eq_uniform_of_factor_equiv
    {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : γ → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b)) =
      averageOperatorOverDistribution (uniformDistribution γ) A := by
  rw [averageOperatorOverDistribution_uniformDistribution_map]
  rw [averageOperatorOverDistribution_uniform_eq_pmf_sum,
    averageOperatorOverDistribution_uniform_eq_pmf_sum]
  exact pmf_uniformOfFintype_sum_factor_equiv_smul
    (m := m) (g := g) (e := e) (h := h) (f := A)

/-- A uniform push-forward has the first-coordinate uniform marginal when the
observed coordinate factors through a product equivalence of the seed. -/
theorem avgOver_uniform_map_eq_uniform_fst_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → Error) :
    avgOver ((uniformDistribution α).map m) (fun b => f (g b)) =
      avgOver (uniformDistribution γ) f := by
  rw [avgOver_uniformDistribution_map]
  rw [avgOver_uniform_eq_pmf_sum, avgOver_uniform_eq_pmf_sum]
  simpa [smul_eq_mul] using
    (pmf_uniformOfFintype_sum_factor_equiv_fst_smul
      (m := m) (g := g) (e := e) (h := h) (f := f))

/-- A uniform push-forward has the second-coordinate uniform marginal when the
observed coordinate factors through a product equivalence of the seed. -/
theorem avgOver_uniform_map_eq_uniform_snd_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [DecidableEq δ] [Nonempty δ]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2) (f : δ → Error) :
    avgOver ((uniformDistribution α).map m) (fun b => f (g b)) =
      avgOver (uniformDistribution δ) f := by
  rw [avgOver_uniformDistribution_map]
  rw [avgOver_uniform_eq_pmf_sum, avgOver_uniform_eq_pmf_sum]
  simpa [smul_eq_mul] using
    (pmf_uniformOfFintype_sum_factor_equiv_snd_smul
      (m := m) (g := g) (e := e) (h := h) (f := f))

/-- A uniform push-forward has the first-coordinate uniform operator marginal
when the observed coordinate factors through a product equivalence of the seed. -/
theorem averageOperatorOverDistribution_uniform_map_eq_uniform_fst_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : γ → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b)) =
      averageOperatorOverDistribution (uniformDistribution γ) A := by
  rw [averageOperatorOverDistribution_uniformDistribution_map]
  rw [averageOperatorOverDistribution_uniform_eq_pmf_sum,
    averageOperatorOverDistribution_uniform_eq_pmf_sum]
  exact pmf_uniformOfFintype_sum_factor_equiv_fst_smul
    (m := m) (g := g) (e := e) (h := h) (f := A)

/-- A uniform push-forward has the second-coordinate uniform operator marginal
when the observed coordinate factors through a product equivalence of the seed. -/
theorem averageOperatorOverDistribution_uniform_map_eq_uniform_snd_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [DecidableEq δ] [Nonempty δ]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : δ → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b)) =
      averageOperatorOverDistribution (uniformDistribution δ) A := by
  rw [averageOperatorOverDistribution_uniformDistribution_map]
  rw [averageOperatorOverDistribution_uniform_eq_pmf_sum,
    averageOperatorOverDistribution_uniform_eq_pmf_sum]
  exact pmf_uniformOfFintype_sum_factor_equiv_snd_smul
    (m := m) (g := g) (e := e) (h := h) (f := A)

end MIPStarRE.LDT
