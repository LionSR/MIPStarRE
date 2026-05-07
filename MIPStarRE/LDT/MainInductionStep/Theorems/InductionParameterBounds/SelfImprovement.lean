import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries

/-!
# Section 6 — Self-Improvement Error Bounds

This file is one leaf of `InductionParameterBounds`. It contains the scalar
consequences of the non-vacuous hypothesis
`selfImprovementInInductionError ≤ 1`, namely the bounds `eps ≤ 1` and
`delta ≤ 1` used before applying self-improvement inside the induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma selfImprovementCoeff_ge_one
    (params : Parameters) :
    (1 : Error) ≤ 3000 * (params.next.m : Error) := by
  have hm_one : (1 : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast params.next.hm
  nlinarith

private lemma le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound
    (params : Parameters) {eps delta gamma x : Error}
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1)
    (hscaled_le :
      3000 * (params.next.m : Error) * Real.rpow x (1 / (32 : Error)) ≤
        selfImprovementInInductionError params.next eps delta gamma) :
    x ≤ 1 := by
  have hcoef_ge_one := selfImprovementCoeff_ge_one params
  have hroot_le_one : Real.rpow x (1 / (32 : Error)) ≤ 1 := by
    by_contra hroot
    have hroot_gt : 1 < Real.rpow x (1 / (32 : Error)) := lt_of_not_ge hroot
    have : 1 < 3000 * (params.next.m : Error) * Real.rpow x (1 / (32 : Error)) := by
      nlinarith [hcoef_ge_one]
    linarith [hscaled_le, hzeta_le]
  exact le_one_of_rpow_le_one (by positivity) hroot_le_one

private lemma selfImprovementInInduction_scaled_component_le
    (params : Parameters) {x y z : Error}
    (hrest_nonneg : 0 ≤ y + z) :
    3000 * (params.next.m : Error) * x ≤
      3000 * (params.next.m : Error) * (x + y + z) := by
  have hsummono : x ≤ x + y + z := by
    nlinarith [hrest_nonneg]
  have hcoef_nonneg : 0 ≤ 3000 * (params.next.m : Error) := by
    positivity
  exact mul_le_mul_of_nonneg_left hsummono hcoef_nonneg

/-- Internal helper: under `selfImprovementInInductionError ≤ 1`, the axis-parallel error `eps ≤ 1`.

Exposed for cross-module use in `AvgSliceErrors` and `PastingAssembly`. -/
lemma eps_le_one_of_selfImprovementInInductionError_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1) :
    eps ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
    nlinarith
  have heps_scaled_le :
      3000 * (params.next.m : Error) * Real.rpow eps (1 / (32 : Error)) ≤
        selfImprovementInInductionError params.next eps delta gamma := by
    simpa [selfImprovementInInductionError, Parameters.next, mul_assoc, mul_left_comm,
        mul_comm] using
      (selfImprovementInInduction_scaled_component_le (params := params)
        (x := Real.rpow eps (1 / (32 : Error)))
        (y := Real.rpow delta (1 / (32 : Error)))
        (z := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
        hrest_nonneg)
  exact
    le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound
      params hzeta_le heps_scaled_le

/-- Internal helper: under `selfImprovementInInductionError ≤ 1`,
the self-consistency error `delta ≤ 1`.

Exposed for cross-module use in `AvgSliceErrors` and `PastingAssembly`. -/
lemma delta_le_one_of_selfImprovementInInductionError_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1) :
    delta ≤ 1 := by
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (32 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
    nlinarith
  have hdelta_scaled_le :
      3000 * (params.next.m : Error) * Real.rpow delta (1 / (32 : Error)) ≤
        selfImprovementInInductionError params.next eps delta gamma := by
    simpa [selfImprovementInInductionError, Parameters.next, mul_assoc, mul_left_comm,
        mul_comm, add_assoc, add_left_comm, add_comm] using
      (selfImprovementInInduction_scaled_component_le (params := params)
        (x := Real.rpow delta (1 / (32 : Error)))
        (y := Real.rpow eps (1 / (32 : Error)))
        (z := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
        hrest_nonneg)
  exact
    le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound
      params hzeta_le hdelta_scaled_le

end MIPStarRE.LDT.MainInductionStep
