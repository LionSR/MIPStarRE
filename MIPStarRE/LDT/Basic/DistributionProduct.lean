import MIPStarRE.LDT.Basic.DistributionAvg

/-!
# Product rules for finite-support distribution averages

This module contains product and marginalization rules for operator-valued
uniform averages.  The scalar product rules, together with the common
PMF-weighted finite-sum identities on which both scalar and operator rules
depend, are in `MIPStarRE.LDT.Basic.DistributionAvg` and
`MIPStarRE.LDT.Basic.PMFAverages`.

## Main definitions / statements

* `averageOperatorOverDistribution_uniform_prod`
* `averageOperatorOverDistribution_uniform_comm`
* `averageOperatorOverDistribution_uniform_prod_swap`
* `averageOperatorOverDistribution_uniform_fst`
* `averageOperatorOverDistribution_uniform_snd`
* `averageOperatorOverDistribution_uniform_equiv_prod`
* `averageOperatorOverDistribution_uniform_equiv_prod_swap`
* `averageOperatorOverDistribution_uniform_equiv_fst`
* `averageOperatorOverDistribution_uniform_equiv_snd`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- Split a uniform operator average over a product into iterated uniform
operator averages. -/
theorem averageOperatorOverDistribution_uniform_prod
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → β → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution (α × β))
        (fun ab => f ab.1 ab.2) =
      averageOperatorOverDistribution (uniformDistribution α)
        (fun a => averageOperatorOverDistribution (uniformDistribution β)
          (fun b => f a b)) := by
  rw [averageOperatorOverDistribution_uniform_eq_pmf_sum (α := α × β)]
  rw [averageOperatorOverDistribution_uniform_eq_pmf_sum (α := α)]
  simp_rw [averageOperatorOverDistribution_uniform_eq_pmf_sum (α := β)]
  exact pmf_uniformOfFintype_prod_sum_smul f

/-- Swap two nested uniform operator averages over finite nonempty types. -/
theorem averageOperatorOverDistribution_uniform_comm
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → β → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution α)
        (fun a => averageOperatorOverDistribution (uniformDistribution β) (f a)) =
      averageOperatorOverDistribution (uniformDistribution β)
        (fun b => averageOperatorOverDistribution (uniformDistribution α)
          (fun a => f a b)) := by
  calc
    averageOperatorOverDistribution (uniformDistribution α)
        (fun a => averageOperatorOverDistribution (uniformDistribution β) (f a))
        = averageOperatorOverDistribution (uniformDistribution (α × β))
            (fun ab => f ab.1 ab.2) := by
          exact (averageOperatorOverDistribution_uniform_prod
            (α := α) (β := β) (f := f)).symm
    _ = averageOperatorOverDistribution (uniformDistribution (β × α))
          (fun ba => f ba.2 ba.1) := by
          simpa using
            (averageOperatorOverDistribution_uniform_equiv (e := Equiv.prodComm α β)
              (f := fun ab : α × β => f ab.1 ab.2))
    _ = averageOperatorOverDistribution (uniformDistribution β)
          (fun b => averageOperatorOverDistribution (uniformDistribution α)
            (fun a => f a b)) := by
          exact averageOperatorOverDistribution_uniform_prod
            (α := β) (β := α) (f := fun b a => f a b)

/-- Split a uniform operator average over a product into iterated uniform
operator averages, with the second coordinate averaged first. -/
theorem averageOperatorOverDistribution_uniform_prod_swap
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → β → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution (α × β))
        (fun ab => f ab.1 ab.2) =
      averageOperatorOverDistribution (uniformDistribution β)
        (fun b => averageOperatorOverDistribution (uniformDistribution α)
          (fun a => f a b)) := by
  calc
    averageOperatorOverDistribution (uniformDistribution (α × β))
        (fun ab => f ab.1 ab.2)
        = averageOperatorOverDistribution (uniformDistribution α)
            (fun a => averageOperatorOverDistribution (uniformDistribution β)
              (fun b => f a b)) := by
          exact averageOperatorOverDistribution_uniform_prod f
    _ = averageOperatorOverDistribution (uniformDistribution β)
          (fun b => averageOperatorOverDistribution (uniformDistribution α)
            (fun a => f a b)) := by
          exact averageOperatorOverDistribution_uniform_comm f

/-- Operator averaging of a family depending only on the first coordinate
marginalizes a uniform product. -/
theorem averageOperatorOverDistribution_uniform_fst
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution (α × β)) (fun ab => f ab.1) =
      averageOperatorOverDistribution (uniformDistribution α) f := by
  calc
    averageOperatorOverDistribution (uniformDistribution (α × β)) (fun ab => f ab.1)
        = averageOperatorOverDistribution (uniformDistribution (α × β))
            (fun ab => (fun a (_ : β) => f a) ab.1 ab.2) := rfl
    _ = averageOperatorOverDistribution (uniformDistribution α)
          (fun a => averageOperatorOverDistribution (uniformDistribution β)
            (fun _ : β => f a)) := by
          exact averageOperatorOverDistribution_uniform_prod
            (α := α) (β := β) (f := fun a (_ : β) => f a)
    _ = averageOperatorOverDistribution (uniformDistribution α) f := by
          refine averageOperatorOverDistribution_congr _ _ _ ?_
          intro a
          exact averageOperatorOverDistribution_const_of_isProbability
            (uniformDistribution β) (uniformDistribution_isProbability β) (f a)

/-- Operator averaging of a family depending only on the second coordinate
marginalizes a uniform product. -/
theorem averageOperatorOverDistribution_uniform_snd
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : β → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution (α × β)) (fun ab => f ab.2) =
      averageOperatorOverDistribution (uniformDistribution β) f := by
  calc
    averageOperatorOverDistribution (uniformDistribution (α × β)) (fun ab => f ab.2)
        = averageOperatorOverDistribution (uniformDistribution (α × β))
            (fun ab => (fun (_ : α) b => f b) ab.1 ab.2) := rfl
    _ = averageOperatorOverDistribution (uniformDistribution β)
          (fun b => averageOperatorOverDistribution (uniformDistribution α)
            (fun _ : α => f b)) := by
          exact averageOperatorOverDistribution_uniform_prod_swap
            (α := α) (β := β) (f := fun (_ : α) b => f b)
    _ = averageOperatorOverDistribution (uniformDistribution β) f := by
          refine averageOperatorOverDistribution_congr _ _ _ ?_
          intro b
          exact averageOperatorOverDistribution_const_of_isProbability
            (uniformDistribution α) (uniformDistribution_isProbability α) (f b)

/-- Transport a uniform operator average through an equivalence whose target is
a product, then split the product average into iterated uniform averages. -/
theorem averageOperatorOverDistribution_uniform_equiv_prod
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : γ ≃ α × β) (f : γ → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution γ) f =
      averageOperatorOverDistribution (uniformDistribution α)
        (fun a => averageOperatorOverDistribution (uniformDistribution β)
          (fun b => f (e.symm (a, b)))) := by
  calc
    averageOperatorOverDistribution (uniformDistribution γ) f
        = averageOperatorOverDistribution (uniformDistribution (α × β))
            (fun ab => f (e.symm ab)) := by
          exact averageOperatorOverDistribution_uniform_equiv e f
    _ = averageOperatorOverDistribution (uniformDistribution α)
          (fun a => averageOperatorOverDistribution (uniformDistribution β)
            (fun b => f (e.symm (a, b)))) := by
          exact averageOperatorOverDistribution_uniform_prod
            (f := fun a b => f (e.symm (a, b)))

/-- Transport a uniform operator average through an equivalence whose target is
a product, then split the product average with the second coordinate averaged
first. -/
theorem averageOperatorOverDistribution_uniform_equiv_prod_swap
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : γ ≃ α × β) (f : γ → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution γ) f =
      averageOperatorOverDistribution (uniformDistribution β)
        (fun b => averageOperatorOverDistribution (uniformDistribution α)
          (fun a => f (e.symm (a, b)))) := by
  rw [averageOperatorOverDistribution_uniform_equiv_prod (e := e) (f := f)]
  exact averageOperatorOverDistribution_uniform_comm
    (fun a b => f (e.symm (a, b)))

/-- A function depending only on the first coordinate of a product equivalence
has the corresponding first-coordinate uniform operator marginal. -/
theorem averageOperatorOverDistribution_uniform_equiv_fst
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Finite β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : γ ≃ α × β) (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution γ) (fun x => f (e x).1) =
      averageOperatorOverDistribution (uniformDistribution α) f := by
  classical
  haveI := Fintype.ofFinite β
  rw [averageOperatorOverDistribution_uniform_equiv_prod
    (e := e) (f := fun x => f (e x).1)]
  refine averageOperatorOverDistribution_congr _ _ _ ?_
  intro a
  simpa using
    (averageOperatorOverDistribution_const_of_isProbability
      (uniformDistribution β) (uniformDistribution_isProbability β) (f a))

/-- A function depending only on the second coordinate of a product equivalence
has the corresponding second-coordinate uniform operator marginal. -/
theorem averageOperatorOverDistribution_uniform_equiv_snd
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : γ ≃ α × β) (f : β → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution γ) (fun x => f (e x).2) =
      averageOperatorOverDistribution (uniformDistribution β) f := by
  classical
  haveI := Fintype.ofFinite α
  rw [averageOperatorOverDistribution_uniform_equiv_prod_swap
    (e := e) (f := fun x => f (e x).2)]
  refine averageOperatorOverDistribution_congr _ _ _ ?_
  intro b
  simpa using
    (averageOperatorOverDistribution_const_of_isProbability
      (uniformDistribution α) (uniformDistribution_isProbability α) (f b))

end MIPStarRE.LDT
