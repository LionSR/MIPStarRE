import MIPStarRE.LDT.Basic.DistributionMeasure
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Optional bridge from project-local distributions to Mathlib PMFs

This opt-in module converts probability-valued project-local `Distribution`s to Mathlib
`PMF`s and relates scalar `avgOver` expressions to PMF expectations.  Use it when a
`Distribution.IsProbability` proof is available and downstream code wants Mathlib's PMF or
probability-expectation APIs.

For arbitrary finite nonnegative weights, including subnormalized weights or empty support,
import `MIPStarRE.LDT.Basic.DistributionMeasure` directly instead.  This PMF module imports
that finite measure adapter only to state the coherence lemmas;
`MIPStarRE.LDT.Basic.Distribution` itself remains free of PMF and measure-theory imports.

The declarations here are adapter lemmas only; they do **not** replace the custom
`Distribution` type or migrate downstream operator-valued averages.
-/

open scoped BigOperators
open MeasureTheory

namespace MIPStarRE.LDT

namespace Distribution

/-- Convert a project-local finite-support probability distribution to a Mathlib `PMF`.

The PMF mass at `a` is `ENNReal.ofReal (𝒟.weight a)`.  The probability hypothesis supplies
the total mass proof, while `Distribution.outsideSupport` supplies the finite-support proof
required by `PMF.ofFinset`. -/
noncomputable def toPMF {α : Type*} (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) : PMF α :=
  PMF.ofFinset (fun a => ENNReal.ofReal (𝒟.weight a)) 𝒟.support
    (by
      calc
        ∑ a ∈ 𝒟.support, ENNReal.ofReal (𝒟.weight a)
            = ENNReal.ofReal (∑ a ∈ 𝒟.support, 𝒟.weight a) := by
              exact (ENNReal.ofReal_sum_of_nonneg fun a _ => 𝒟.nonnegative a).symm
        _ = 1 := by
              simpa [Distribution.IsProbability, Distribution.totalWeight]
                using congrArg ENNReal.ofReal h𝒟)
    (by
      intro a ha
      simp [𝒟.outsideSupport a ha])

@[simp]
theorem toPMF_apply {α : Type*} (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (a : α) :
    𝒟.toPMF h𝒟 a = ENNReal.ofReal (𝒟.weight a) := by
  rfl

/-- Reading back the converted PMF mass as a real recovers the original weight. -/
@[simp]
theorem toPMF_apply_toReal {α : Type*} (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    (a : α) :
    ((𝒟.toPMF h𝒟) a).toReal = 𝒟.weight a := by
  simp [Distribution.toPMF, ENNReal.toReal_ofReal (𝒟.nonnegative a)]

@[simp]
theorem toPMF_apply_of_notMem {α : Type*} (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    {a : α} (ha : a ∉ 𝒟.support) :
    𝒟.toPMF h𝒟 a = 0 := by
  simp [Distribution.toPMF, 𝒟.outsideSupport a ha]

/-- Coherence between the PMF adapter and the finite-measure adapter on singleton masses.

Both adapters assign the same `ENNReal.ofReal (𝒟.weight a)` mass to the singleton `{a}`; the
probability hypothesis is only needed to construct the PMF side. -/
theorem toPMF_apply_eq_toMeasure_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (a : α) :
    𝒟.toPMF h𝒟 a = 𝒟.toMeasure ({a} : Set α) := by
  rw [toPMF_apply, toMeasure_singleton]

/-- Real-valued form of `Distribution.toPMF_apply_eq_toMeasure_singleton`.

This is often the convenient bridge when downstream scalar averages read PMF masses through
`ENNReal.toReal`. -/
theorem toPMF_apply_toReal_eq_toMeasure_real_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (a : α) :
    ((𝒟.toPMF h𝒟) a).toReal = (𝒟.toMeasure ({a} : Set α)).toReal := by
  rw [toPMF_apply_toReal, toMeasure_real_singleton]

end Distribution

/-- Finite-sum scalar bridge from project-local `avgOver` to the real-valued masses of
`Distribution.toPMF`. -/
theorem avgOver_eq_sum_toPMF {α : Type*} [Fintype α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → Error) :
    avgOver 𝒟 f = ∑ a : α, ((𝒟.toPMF h𝒟) a).toReal * f a := by
  calc
    avgOver 𝒟 f = ∑ a : α, 𝒟.weight a * f a := avgOver_eq_sum_univ 𝒟 f
    _ = ∑ a : α, ((𝒟.toPMF h𝒟) a).toReal * f a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Distribution.toPMF_apply_toReal]

/-- Scalar expectation bridge from project-local `avgOver` to integration against the
Mathlib PMF obtained from `Distribution.toPMF`. -/
theorem avgOver_eq_integral_toPMF {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → Error) :
    avgOver 𝒟 f = ∫ a, f a ∂((𝒟.toPMF h𝒟).toMeasure) := by
  classical
  letI := Fintype.ofFinite α
  calc
    avgOver 𝒟 f = ∑ a : α, ((𝒟.toPMF h𝒟) a).toReal * f a :=
      avgOver_eq_sum_toPMF 𝒟 h𝒟 f
    _ = ∑ a : α, ((𝒟.toPMF h𝒟) a).toReal • f a := by
      simp [smul_eq_mul]
    _ = ∫ a, f a ∂((𝒟.toPMF h𝒟).toMeasure) := by
      exact (PMF.integral_eq_sum (𝒟.toPMF h𝒟) f).symm

end MIPStarRE.LDT
