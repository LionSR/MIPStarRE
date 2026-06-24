import MIPStarRE.LDT.Basic.DistributionUniformSums

/-!
# PMF expectations associated to project distributions

This module relates the project `Distribution` averaging notation to the finite
expectation `PMF.realWeightedSum` on Mathlib probability mass functions.  The
statements keep the project-facing averages available while allowing later
probability arguments to cite the associated Mathlib `PMF` object directly.
The module-valued finite-sum algebra for uniform project distributions lives in
`MIPStarRE.LDT.Basic.DistributionUniformSums`; this file records the additional
comparison with `PMF.realWeightedSum`.

## Main declarations

* `avgOver_eq_toPMF_realWeightedSum`
* `averageOperatorOverDistribution_eq_toPMF_realWeightedSum`
* `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum`
* `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSumLinearMap`
* `uniformDistribution_sum_smul_eq_pmf_realWeightedSum`
* `avgOver_uniform_eq_pmf_realWeightedSum`
* `averageOperatorOverDistribution_uniform_eq_pmf_realWeightedSum`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Distribution

/-- The module-valued weighted sum against a probabilistic `Distribution` agrees
with finite expectation against its associated Mathlib probability mass
function. -/
theorem weightedSumLinearMap_eq_toPMF_realWeightedSum {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → M) :
    𝒟.weightedSumLinearMap M f = PMF.realWeightedSum (𝒟.toPMF h𝒟) f := by
  simpa [PMF.realWeightedSum] using
    Distribution.sum_smul_eq_toPMF_sum 𝒟 h𝒟 f

/-- The weighted-sum linear map of a probabilistic `Distribution` is the
finite-expectation linear map of its associated Mathlib probability mass
function. -/
theorem weightedSumLinearMap_eq_toPMF_realWeightedSumLinearMap {α M : Type*}
    [Fintype α] [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) :
    𝒟.weightedSumLinearMap M =
      PMF.realWeightedSumLinearMap (M := M) (𝒟.toPMF h𝒟) := by
  ext f
  exact weightedSumLinearMap_eq_toPMF_realWeightedSum 𝒟 h𝒟 f

end Distribution

/-- Averaging against a probabilistic project distribution is the finite
expectation against its associated Mathlib probability mass function. -/
theorem avgOver_eq_toPMF_realWeightedSum {α : Type*} [Fintype α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → Error) :
    avgOver 𝒟 f = PMF.realWeightedSum (𝒟.toPMF h𝒟) f := by
  simpa [Distribution.avgOver_eq_weightedSumLinearMap] using
    Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum 𝒟 h𝒟 f

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
  simpa [Distribution.averageOperatorOverDistribution_eq_weightedSumLinearMap] using
    Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum 𝒟 h𝒟 f

/-- Module-valued finite expectation for the uniform distribution, stated
directly in terms of Mathlib's uniform probability mass function. -/
theorem uniformDistribution_sum_smul_eq_pmf_realWeightedSum {α M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [AddCommMonoid M] [Module Error M] (f : α → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a =
      PMF.realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa [PMF.realWeightedSum] using
    uniformDistribution_sum_smul_eq_pmf_sum (α := α) (f := f)

/-- The uniform average is the finite expectation against Mathlib's uniform
probability mass function. -/
theorem avgOver_uniform_eq_pmf_realWeightedSum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → Error) :
    avgOver (uniformDistribution α) f =
      PMF.realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa [PMF.realWeightedSum, avgOver, smul_eq_mul] using
    uniformDistribution_sum_smul_eq_pmf_sum (α := α) (f := f)

/-- The uniform operator average is the finite expectation against Mathlib's
uniform probability mass function. -/
theorem averageOperatorOverDistribution_uniform_eq_pmf_realWeightedSum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution α) f =
      PMF.realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa [PMF.realWeightedSum, averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_eq_pmf_sum (α := α) (f := f)

end MIPStarRE.LDT
