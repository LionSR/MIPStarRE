import MIPStarRE.LDT.Basic.Distribution
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Measure adapter for project-local finite-support distributions

This optional module views the repository-local `Distribution` type as a finite measure by
placing a Dirac atom of mass `ENNReal.ofReal (𝒟.weight a)` at each point of the explicit support.
It intentionally lives outside `Distribution.lean` so the foundational LDT distribution API does
not acquire measure-theory imports.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace MIPStarRE.LDT

namespace Distribution

noncomputable section

/-- Interpret a finite-support nonnegative `Distribution` as a measure.

The construction does not require the distribution to have total mass `1`: each supported point
`a` contributes a Dirac atom with mass `ENNReal.ofReal (𝒟.weight a)`.  The nonnegativity field of
`Distribution` ensures that the real-valued weights are faithfully represented by `ofReal`. -/
def toMeasure {α : Type*} [MeasurableSpace α] (𝒟 : Distribution α) : Measure α :=
  ∑ a ∈ 𝒟.support, ENNReal.ofReal (𝒟.weight a) • Measure.dirac a

/-- Applying `Distribution.toMeasure` unfolds to the corresponding finite Dirac sum. -/
@[simp]
theorem toMeasure_apply {α : Type*} [MeasurableSpace α]
    (𝒟 : Distribution α) (s : Set α) :
    𝒟.toMeasure s =
      ∑ a ∈ 𝒟.support, ENNReal.ofReal (𝒟.weight a) * Measure.dirac a s := by
  simp [toMeasure, Measure.finset_sum_apply, Measure.smul_apply]

/-- The total mass of the associated measure is the `ENNReal` coercion of
`Distribution.totalWeight`. -/
@[simp]
theorem toMeasure_univ {α : Type*} [MeasurableSpace α]
    (𝒟 : Distribution α) :
    𝒟.toMeasure Set.univ = ENNReal.ofReal 𝒟.totalWeight := by
  classical
  rw [toMeasure_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  exact (ENNReal.ofReal_sum_of_nonneg (s := 𝒟.support) (f := 𝒟.weight)
    (fun a ha => 𝒟.nonnegative a)).symm

/-- The measure associated to a `Distribution` is finite, even when it is not normalized. -/
instance instIsFiniteMeasureToMeasure {α : Type*} [MeasurableSpace α]
    (𝒟 : Distribution α) : IsFiniteMeasure 𝒟.toMeasure where
  measure_univ_lt_top := by
    rw [toMeasure_univ]
    exact ENNReal.ofReal_lt_top

/-- The associated measure has the expected singleton mass.  Points outside the explicit support
have weight zero by `Distribution.outsideSupport`. -/
@[simp]
theorem toMeasure_singleton {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (𝒟 : Distribution α) (a : α) :
    𝒟.toMeasure ({a} : Set α) = ENNReal.ofReal (𝒟.weight a) := by
  classical
  rw [toMeasure_apply]
  by_cases ha : a ∈ 𝒟.support
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb_ne
      simp [hb_ne]
    · intro hnot
      exact False.elim (hnot ha)
  · rw [Finset.sum_eq_zero]
    · simp [𝒟.outsideSupport a ha]
    · intro b hb
      have hb_ne : b ≠ a := by
        intro hba
        exact ha (hba ▸ hb)
      simp [hb_ne]

/-- Real-valued singleton masses recover the original distribution weights. -/
@[simp]
theorem toMeasure_real_singleton {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (𝒟 : Distribution α) (a : α) :
    (𝒟.toMeasure ({a} : Set α)).toReal = 𝒟.weight a := by
  rw [toMeasure_singleton]
  exact ENNReal.toReal_ofReal (𝒟.nonnegative a)

/-- Integrating a scalar function against `Distribution.toMeasure` is the same finite weighted
sum as the project-local `avgOver`.

This is a bridge lemma only: it does not replace `avgOver`, and it imposes no probability-mass
hypothesis on `𝒟`. -/
theorem integral_toMeasure_eq_avgOver {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (𝒟 : Distribution α) (f : α → Error) :
    (∫ a, f a ∂𝒟.toMeasure) = avgOver 𝒟 f := by
  classical
  rw [toMeasure]
  rw [integral_finset_sum_measure]
  · unfold avgOver
    simp_rw [integral_smul_measure, integral_dirac]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [ENNReal.toReal_ofReal (𝒟.nonnegative a)]
    simp [smul_eq_mul]
  · intro a _
    exact (integrable_dirac (a := a) (f := f) (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Symmetric form of `Distribution.integral_toMeasure_eq_avgOver`, convenient for rewriting an
existing `avgOver` into a measure integral. -/
theorem avgOver_eq_integral_toMeasure {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (𝒟 : Distribution α) (f : α → Error) :
    avgOver 𝒟 f = ∫ a, f a ∂𝒟.toMeasure :=
  (integral_toMeasure_eq_avgOver 𝒟 f).symm

end

end Distribution

end MIPStarRE.LDT
