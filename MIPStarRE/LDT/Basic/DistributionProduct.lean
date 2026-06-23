import MIPStarRE.LDT.Basic.DistributionPMF

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
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_prod (f := f)

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
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_comm (f := f)

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
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_prod_swap (f := f)

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
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_equiv_fst
      (e := Equiv.refl (α × β)) (f := f)

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
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_equiv_snd
      (e := Equiv.refl (α × β)) (f := f)

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
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_equiv_prod (e := e) (f := f)

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
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_equiv_prod_swap (e := e) (f := f)

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
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_equiv_fst (e := e) (f := f)

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
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_equiv_snd (e := e) (f := f)

end MIPStarRE.LDT
