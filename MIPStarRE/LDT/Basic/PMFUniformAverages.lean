import MIPStarRE.LDT.Basic.PMFAverages

/-!
# Uniform PMF finite-expectation identities

This module contains high-level uniform-expectation identities for Mathlib
probability mass functions.  The statements are phrased in terms of
`PMF.realWeightedSum`, rather than finite sums, so that product,
marginalization, equivalence-transport, and finite push-forward arguments can
be carried out directly in the probability-mass-function language.

## Main declarations

* `PMF.realWeightedSum_uniformOfFintype_comm`
* `PMF.realWeightedSum_uniformOfFintype_prod_swap`
* `PMF.realWeightedSum_uniformOfFintype_equiv_prod`
* `PMF.realWeightedSum_uniformOfFintype_equiv_prod_swap`
* `PMF.realWeightedSum_uniformOfFintype_equiv_fst`
* `PMF.realWeightedSum_uniformOfFintype_equiv_snd`
* `PMF.realWeightedSum_uniformOfFintype_fst`
* `PMF.realWeightedSum_uniformOfFintype_snd`
* `PMF.realWeightedSum_map_uniformOfFintype_factor_equiv`
* `PMF.realWeightedSum_map_uniformOfFintype_factor_equiv_fst`
* `PMF.realWeightedSum_map_uniformOfFintype_factor_equiv_snd`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators

namespace PMF

/-- Swap two nested finite expectations against uniform probability mass
functions. -/
theorem realWeightedSum_uniformOfFintype_comm {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (f : α → β → M) :
    realWeightedSum (PMF.uniformOfFintype α)
        (fun a => realWeightedSum (PMF.uniformOfFintype β) (fun b => f a b)) =
      realWeightedSum (PMF.uniformOfFintype β)
        (fun b => realWeightedSum (PMF.uniformOfFintype α) (fun a => f a b)) := by
  calc
    realWeightedSum (PMF.uniformOfFintype α)
        (fun a => realWeightedSum (PMF.uniformOfFintype β) (fun b => f a b))
        = realWeightedSum (PMF.uniformOfFintype (α × β))
            (fun ab => f ab.1 ab.2) := by
          exact (realWeightedSum_uniformOfFintype_prod (f := f)).symm
    _ = realWeightedSum (PMF.uniformOfFintype (β × α))
          (fun ba => f ba.2 ba.1) := by
          exact realWeightedSum_uniformOfFintype_equiv
            (e := Equiv.prodComm α β) (f := fun ab : α × β => f ab.1 ab.2)
    _ = realWeightedSum (PMF.uniformOfFintype β)
          (fun b => realWeightedSum (PMF.uniformOfFintype α) (fun a => f a b)) := by
          exact realWeightedSum_uniformOfFintype_prod
            (α := β) (β := α) (f := fun b a => f a b)

/-- Split a finite expectation against the uniform PMF on a product into
iterated finite expectations, with the second coordinate averaged first. -/
theorem realWeightedSum_uniformOfFintype_prod_swap {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (f : α → β → M) :
    realWeightedSum (PMF.uniformOfFintype (α × β)) (fun ab => f ab.1 ab.2) =
      realWeightedSum (PMF.uniformOfFintype β)
        (fun b => realWeightedSum (PMF.uniformOfFintype α) (fun a => f a b)) := by
  rw [realWeightedSum_uniformOfFintype_prod (f := f)]
  exact realWeightedSum_uniformOfFintype_comm f

/-- Transport a finite expectation against a uniform PMF through an equivalence
whose target is a product, then split the product expectation. -/
theorem realWeightedSum_uniformOfFintype_equiv_prod {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : γ → M) :
    realWeightedSum (PMF.uniformOfFintype γ) f =
      realWeightedSum (PMF.uniformOfFintype α)
        (fun a => realWeightedSum (PMF.uniformOfFintype β)
          (fun b => f (e.symm (a, b)))) := by
  calc
    realWeightedSum (PMF.uniformOfFintype γ) f =
        realWeightedSum (PMF.uniformOfFintype (α × β))
          (fun ab => f (e.symm ab)) := by
          exact realWeightedSum_uniformOfFintype_equiv (e := e) (f := f)
    _ = realWeightedSum (PMF.uniformOfFintype α)
          (fun a => realWeightedSum (PMF.uniformOfFintype β)
            (fun b => f (e.symm (a, b)))) := by
          exact realWeightedSum_uniformOfFintype_prod
            (f := fun a b => f (e.symm (a, b)))

/-- Transport a finite expectation against a uniform PMF through an equivalence
whose target is a product, then split the product expectation with the second
coordinate averaged first. -/
theorem realWeightedSum_uniformOfFintype_equiv_prod_swap {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : γ → M) :
    realWeightedSum (PMF.uniformOfFintype γ) f =
      realWeightedSum (PMF.uniformOfFintype β)
        (fun b => realWeightedSum (PMF.uniformOfFintype α)
          (fun a => f (e.symm (a, b)))) := by
  rw [realWeightedSum_uniformOfFintype_equiv_prod (e := e) (f := f)]
  exact realWeightedSum_uniformOfFintype_comm (fun a b => f (e.symm (a, b)))

/-- A finite expectation against a uniform PMF marginalizes a function depending
only on the first coordinate of a product equivalence. -/
theorem realWeightedSum_uniformOfFintype_equiv_fst {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Fintype α] [Nonempty α]
    [Finite β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : α → M) :
    realWeightedSum (PMF.uniformOfFintype γ) (fun x => f (e x).1) =
      realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_equiv_fst_smul (e := e) (f := f)

/-- A finite expectation against a uniform PMF marginalizes a function depending
only on the second coordinate of a product equivalence. -/
theorem realWeightedSum_uniformOfFintype_equiv_snd {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : β → M) :
    realWeightedSum (PMF.uniformOfFintype γ) (fun x => f (e x).2) =
      realWeightedSum (PMF.uniformOfFintype β) f := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_equiv_snd_smul (e := e) (f := f)

/-- A finite expectation against the uniform PMF on a product marginalizes a
function depending only on the first coordinate. -/
theorem realWeightedSum_uniformOfFintype_fst {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (f : α → M) :
    realWeightedSum (PMF.uniformOfFintype (α × β)) (fun ab => f ab.1) =
      realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa using
    realWeightedSum_uniformOfFintype_equiv_fst
      (e := Equiv.refl (α × β)) (f := f)

/-- A finite expectation against the uniform PMF on a product marginalizes a
function depending only on the second coordinate. -/
theorem realWeightedSum_uniformOfFintype_snd {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (f : β → M) :
    realWeightedSum (PMF.uniformOfFintype (α × β)) (fun ab => f ab.2) =
      realWeightedSum (PMF.uniformOfFintype β) f := by
  simpa using
    realWeightedSum_uniformOfFintype_equiv_snd
      (e := Equiv.refl (α × β)) (f := f)

/-- A pushed-forward uniform PMF has the uniform expectation induced by an
equivalent observed coordinate. -/
theorem realWeightedSum_map_uniformOfFintype_factor_equiv {α β γ M : Type*}
    [Fintype α] [Fintype β] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → M) :
    realWeightedSum ((PMF.uniformOfFintype α).map m) (fun b => f (g b)) =
      realWeightedSum (PMF.uniformOfFintype γ) f := by
  rw [realWeightedSum_map]
  exact realWeightedSum_uniformOfFintype_factor_equiv
    (m := m) (g := g) (e := e) (h := h) (f := f)

/-- A pushed-forward uniform PMF has the first-coordinate uniform marginal when
the seed is equivalent to a product. -/
theorem realWeightedSum_map_uniformOfFintype_factor_equiv_fst
    {α β γ δ M : Type*}
    [Fintype α] [Fintype β] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → M) :
    realWeightedSum ((PMF.uniformOfFintype α).map m) (fun b => f (g b)) =
      realWeightedSum (PMF.uniformOfFintype γ) f := by
  rw [realWeightedSum_map]
  exact realWeightedSum_uniformOfFintype_factor_equiv_fst
    (m := m) (g := g) (e := e) (h := h) (f := f)

/-- A pushed-forward uniform PMF has the second-coordinate uniform marginal when
the seed is equivalent to a product. -/
theorem realWeightedSum_map_uniformOfFintype_factor_equiv_snd
    {α β γ δ M : Type*}
    [Fintype α] [Fintype β] [Nonempty α]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [Nonempty δ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2) (f : δ → M) :
    realWeightedSum ((PMF.uniformOfFintype α).map m) (fun b => f (g b)) =
      realWeightedSum (PMF.uniformOfFintype δ) f := by
  rw [realWeightedSum_map]
  exact realWeightedSum_uniformOfFintype_factor_equiv_snd
    (m := m) (g := g) (e := e) (h := h) (f := f)

end PMF
