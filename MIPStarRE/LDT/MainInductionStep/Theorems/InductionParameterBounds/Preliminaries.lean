import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Test.StrategyFailures

/-!
# Section 6 — Induction Parameter Bound Preliminaries

This file is one leaf of `InductionParameterBounds`. It contains the elementary
point-line reduction for the base case, the real-variable comparison lemmas used
by the small-parameter estimates, and the bound `d/q ≤ 1`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At `m = 1`, `AxisParallelLine.throughPoint u i` does not depend on the
base point `u`: all axis-parallel lines in direction `i` are geometrically the
unique line and share the same canonical representative. -/
theorem throughPoint_eq_zeroPoint_of_m_eq_one
    (params : Parameters) [FieldModel params.q]
    (hm1 : params.m = 1)
    (u : Point params) (i : Fin params.m) :
    AxisParallelLine.throughPoint (params := params) u i =
      AxisParallelLine.throughPoint (params := params) zeroPoint i := by
  change
    ({ base := fun j => if j = i then zeroCoord else u j
       direction := i } : AxisParallelLine params) =
      { base := fun j => if j = i then zeroCoord else zeroPoint j
        direction := i }
  congr
  funext j
  haveI : Subsingleton (Fin params.m) := by
    rw [hm1]
    infer_instance
  have hji : j = i := Subsingleton.elim _ _
  simp [hji]

lemma min_le_rpow_of_nonneg_of_exponent_le_one {x c : Error}
    (hx : 0 ≤ x) (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) :
    min x 1 ≤ Real.rpow x c := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_left hx1]
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hx hx1 hc_nonneg hc_le_one)
  · rw [min_eq_right (le_of_not_ge hx1)]
    simpa using Real.rpow_le_rpow (by positivity) (le_of_not_ge hx1) hc_nonneg

lemma le_one_of_rpow_le_one {x c : Error}
    (hc_pos : 0 < c) (h : Real.rpow x c ≤ 1) :
    x ≤ 1 := by
  by_contra hx_gt
  have hx_gt' : 1 < x := lt_of_not_ge hx_gt
  have : 1 < Real.rpow x c := Real.one_lt_rpow hx_gt' hc_pos
  linarith

/-- Internal helper: `d/q ≤ 1` under the assumption `params.d ≤ params.q`.

Exposed for cross-module use in `AvgSliceErrors` and `PastingAssembly`. -/
lemma dq_ratio_le_one
    (params : Parameters)
    (hdq_le_q : params.d ≤ params.q) :
    ((params.d : Error) / (params.q : Error)) ≤ 1 := by
  have hq_pos : (0 : Error) < (params.q : Error) := by
    exact_mod_cast params.hq
  have hdq_real : (params.d : Error) ≤ (params.q : Error) := by
    exact_mod_cast hdq_le_q
  exact (div_le_iff₀ hq_pos).2 (by simpa using hdq_real)

/-- Internal helper: `min eps 1 ≤ mainInductionError` when `params.m = 1`.

Exposed for cross-module use in `MainTheorems`. -/
lemma min_eps_one_le_mainInductionError_of_m_eq_one
    (params : Parameters)
    [FieldModel params.q]
    (k : ℕ) (eps delta gamma : Error)
    (hm1 : params.m = 1)
    (heps_nonneg : 0 ≤ eps) (hdelta_nonneg : 0 ≤ delta) (hgamma_nonneg : 0 ≤ gamma) :
    min eps 1 ≤ mainInductionError params k eps delta gamma := by
  by_cases hk0 : k = 0
  · subst hk0
    simp [mainInductionError, mainInductionNu, hm1]
  · have hmin : min eps 1 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      min_le_rpow_of_nonneg_of_exponent_le_one heps_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1)
    have hother_nonneg :
        0 ≤ Real.rpow delta (1 / (1024 : Error)) +
              Real.rpow gamma (1 / (1024 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
      have hdelta_rpow_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
        Real.rpow_nonneg hdelta_nonneg _
      have hgamma_rpow_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
        Real.rpow_nonneg hgamma_nonneg _
      have hratio_rpow_nonneg :
          0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
        Real.rpow_nonneg hratio_nonneg _
      nlinarith
    have hsum_ge :
        Real.rpow eps (1 / (1024 : Error)) ≤
          Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith
    have hk1 : (1 : Error) ≤ (k : Error) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    have hk2 : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
      nlinarith
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) := by
      positivity
    have hcoef :
        (1 : Error) ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) := by
      simp [hm1]
      nlinarith
    have hrpow_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) := by
      exact Real.rpow_nonneg heps_nonneg _
    have hmul :
        Real.rpow eps (1 / (1024 : Error)) ≤
          1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            Real.rpow eps (1 / (1024 : Error)) := by
      simpa using (mul_le_mul_of_nonneg_right hcoef hrpow_nonneg)
    have hsum_mul :
        1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            Real.rpow eps (1 / (1024 : Error)) ≤
          1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow delta (1 / (1024 : Error)) +
              Real.rpow gamma (1 / (1024 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
      exact mul_le_mul_of_nonneg_left hsum_ge hcoef_nonneg
    have hexp_nonneg :
        0 ≤ Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
      positivity
    calc
      min eps 1 ≤ Real.rpow eps (1 / (1024 : Error)) := hmin
      _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            Real.rpow eps (1 / (1024 : Error)) := hmul
      _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow delta (1 / (1024 : Error)) +
              Real.rpow gamma (1 / (1024 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error)))
                (1 / (1024 : Error))) := hsum_mul
      _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow delta (1 / (1024 : Error)) +
              Real.rpow gamma (1 / (1024 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
            linarith
      _ = mainInductionError params k eps delta gamma := by
            simp [mainInductionError, mainInductionNu, hm1]

end MIPStarRE.LDT.MainInductionStep
