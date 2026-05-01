import MIPStarRE.LDT.Basic.Distribution
import Mathlib.Probability.Distributions.Uniform

/-!
# Optional bridge from local uniform distributions to Mathlib PMFs

This opt-in module relates the project-local `uniformDistribution`/`avgOver` API to
Mathlib's `PMF.uniformOfFintype`.  Keeping the PMF import here avoids pulling the
probability stack into foundational files that only need `Distribution`.

These lemmas are adapter proofs only; they do **not** replace the custom
`Distribution` type or introduce a general `Distribution.toPMF` conversion.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

/-- The weight of the custom `uniformDistribution` matches the real-valued
probability mass of `PMF.uniformOfFintype`. -/
theorem uniformDistribution_weight_eq_pmf_toReal (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] (a : α) :
    (uniformDistribution α).weight a = ((PMF.uniformOfFintype α) a).toReal := by
  simp [uniformDistribution, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, div_eq_inv_mul]

/-- The expectation under the custom `uniformDistribution` is exactly the sum
weighted by the real-valued `PMF.uniformOfFintype` masses.
This is the key bridge for moving between the paper's averaging notation and
Mathlib's probability mass function API. -/
theorem avgOver_uniform_eq_pmf_expectation (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) :
    avgOver (uniformDistribution α) f =
    ∑ a : α, ((PMF.uniformOfFintype α) a).toReal * f a := by
  calc
    avgOver (uniformDistribution α) f
        = ∑ a : α, (uniformDistribution α).weight a * f a :=
      avgOver_eq_sum_univ _ _
    _ = ∑ a : α, ((PMF.uniformOfFintype α) a).toReal * f a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [uniformDistribution_weight_eq_pmf_toReal α a]

end MIPStarRE.LDT
