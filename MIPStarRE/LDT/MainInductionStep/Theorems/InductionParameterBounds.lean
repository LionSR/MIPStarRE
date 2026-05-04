import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Test.StrategyFailures
-- Provides `Nonempty (Polynomial params)` instance for `trivialPolynomialMeasurement`.
import MIPStarRE.LDT.GlobalVariance.Defs.Core

/-!
# Section 6 — Induction Parameter Bounds

Private and internal-helper lemmas bounding the error parameters under
`mainInductionError < 1` and `selfImprovementInInductionError ≤ 1`.
Also contains the Jensen-type averaging helper and geometric-series bounds
used throughout the slice assembly proofs.

Several helpers in this module are exposed (not `private`) because they are
used across the leaf modules `AvgSliceErrors`, `PastingAssembly`, and
`MainTheorems`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
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

private lemma min_le_rpow_of_nonneg_of_exponent_le_one {x c : Error}
    (hx : 0 ≤ x) (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) :
    min x 1 ≤ Real.rpow x c := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_left hx1]
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hx hx1 hc_nonneg hc_le_one)
  · rw [min_eq_right (le_of_not_ge hx1)]
    simpa using Real.rpow_le_rpow (by positivity) (le_of_not_ge hx1) hc_nonneg

private lemma le_one_of_rpow_le_one {x c : Error}
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

/-- Throwaway polynomial measurement used only as a witness in the vacuous
`mainInductionError ≥ 1` fallback branch of `mainInductionByRecursionOnM`.
All mass is concentrated on `default : Polynomial params`. -/
noncomputable def trivialPolynomialMeasurement
    (params : Parameters) [FieldModel params.q] : Measurement (Polynomial params) ι := by
  classical
  haveI : Inhabited (Polynomial params) :=
    ⟨Classical.choice (inferInstance : Nonempty (Polynomial params))⟩
  exact default

/-- Jensen's inequality for `Real.rpow (1/n)` against a uniform distribution:
the average of `(f a)^{1/n}` is at most `(average f)^{1/n}`. This is the
workhorse used inside each of the averaged-slice bounds (`average_slice…_le`)
to push `rpow (1/32)` or `rpow (1/1024)` through a uniform `avgOver` on
`Fq params`. -/
lemma avgOver_uniform_rpow_one_div_le_rpow_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) (n : ℕ) (hn : 1 ≤ n) (hf : ∀ a, 0 ≤ f a) :
    avgOver (uniformDistribution α)
        (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
      Real.rpow (avgOver (uniformDistribution α) f) (1 / (n : Error)) := by
  let w : α → Error := fun _ => 1 / (Fintype.card α : Error)
  let z : α → Error := fun a => Real.rpow (f a) (1 / (n : Error))
  have hw_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ w a := by
    intro a ha
    simp [w]
  have hw_sum : ∑ a ∈ (Finset.univ : Finset α), w a = 1 := by
    simp [w]
  have hz_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ z a := by
    intro a ha
    exact Real.rpow_nonneg (hf a) _
  have hn_nat_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) hn
  have hn_pos : 0 < (n : Error) := by
    exact_mod_cast hn_nat_pos
  have hp : (1 : Error) ≤ (n : Error) := by
    exact_mod_cast hn
  have hzpow : ∀ a, (Real.rpow (f a) (1 / (n : Error))) ^ n = f a := by
    intro a
    calc
      (Real.rpow (f a) (1 / (n : Error))) ^ n
          = (Real.rpow (f a) (1 / (n : Error))) ^ (n : Error) := by
              rw [← Real.rpow_natCast]
      _ = Real.rpow (f a) ((1 / (n : Error)) * (n : Error)) := by
              symm
              exact Real.rpow_mul (hf a) _ _
      _ = Real.rpow (f a) 1 := by
              congr 1
              field_simp [hn_pos.ne']
      _ = f a := by simp
  have hsum_eq :
      ∑ a ∈ (Finset.univ : Finset α), w a * z a ^ n =
        ∑ a ∈ (Finset.univ : Finset α), w a * f a := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [hzpow a]
  have hmean :=
    (Real.arith_mean_le_rpow_mean (s := (Finset.univ : Finset α)) w z
      hw_nonneg hw_sum hz_nonneg (p := (n : Error)) hp)
  have hmean' :
      avgOver (uniformDistribution α) (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
        Real.rpow (∑ a ∈ (Finset.univ : Finset α), w a * z a ^ n) (1 / (n : Error)) := by
    simpa [avgOver, uniformDistribution, w, z] using hmean
  rw [hsum_eq] at hmean'
  simpa [avgOver, uniformDistribution, w] using hmean'

/-- Internal helper: `m · (sliceConditioningLoss · x)^c ≤ m_next · x^c` for `c ≤ 1`.

Exposed for cross-module use in `AvgSliceErrors`. -/
lemma m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow
    (params : Parameters) {x c : Error}
    (hx : 0 ≤ x) (_hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) :
    (params.m : Error) * Real.rpow (sliceConditioningLoss params * x) c ≤
      (params.next.m : Error) * Real.rpow x c := by
  have hm0 : (params.m : Error) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt params.hm
  have hloss_nonneg : 0 ≤ sliceConditioningLoss params := by
    unfold sliceConditioningLoss
    positivity
  have hloss_ge_one : (1 : Error) ≤ sliceConditioningLoss params := by
    unfold sliceConditioningLoss
    have hm_pos : (0 : Error) < (params.m : Error) := by
      exact_mod_cast params.hm
    have hnum_ge : (params.m : Error) ≤ ((params.m + 1 : ℕ) : Error) := by
      exact_mod_cast Nat.le_succ params.m
    exact (one_le_div₀ hm_pos).2 hnum_ge
  have hloss_rpow_le :
      Real.rpow (sliceConditioningLoss params) c ≤ sliceConditioningLoss params := by
    calc
      Real.rpow (sliceConditioningLoss params) c
          ≤ Real.rpow (sliceConditioningLoss params) 1 := by
            exact Real.rpow_le_rpow_of_exponent_le hloss_ge_one hc_le_one
      _ = sliceConditioningLoss params := by simp
  calc
    (params.m : Error) * Real.rpow (sliceConditioningLoss params * x) c
      = (params.m : Error) *
          (Real.rpow (sliceConditioningLoss params) c * Real.rpow x c) := by
            rw [show Real.rpow (sliceConditioningLoss params * x) c =
                Real.rpow (sliceConditioningLoss params) c * Real.rpow x c by
                exact Real.mul_rpow hloss_nonneg hx]
    _ ≤ (params.m : Error) * (sliceConditioningLoss params * Real.rpow x c) := by
          gcongr
          exact Real.rpow_nonneg hx c
    _ = (params.next.m : Error) * Real.rpow x c := by
          have hnext_eq : (params.next.m : Error) = ((params.m + 1 : ℕ) : Error) := by
            norm_num [Parameters.next]
          rw [hnext_eq]
          unfold sliceConditioningLoss
          field_simp [hm0]
/-- Internal helper: `m² · (sliceConditioningLoss · x)^c ≤ m_next² · x^c` for `c ≤ 1`.

Exposed for cross-module use in `AvgSliceErrors`. -/
lemma m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow
    (params : Parameters) {x c : Error}
    (hx : 0 ≤ x) (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) :
    ((params.m : Error) ^ (2 : ℕ)) * Real.rpow (sliceConditioningLoss params * x) c ≤
      ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow x c := by
  have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast Nat.le_succ params.m
  calc
    ((params.m : Error) ^ (2 : ℕ)) * Real.rpow (sliceConditioningLoss params * x) c
      = (params.m : Error) *
          ((params.m : Error) * Real.rpow (sliceConditioningLoss params * x) c) := by
            ring
    _ ≤ (params.m : Error) * ((params.next.m : Error) * Real.rpow x c) := by
          exact mul_le_mul_of_nonneg_left
            (m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow params hx hc_nonneg hc_le_one)
            (by positivity)
    _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow x c := by
          have hcoef :
              (params.m : Error) * (params.next.m : Error) ≤
                ((params.next.m : Error) ^ (2 : ℕ)) := by
            nlinarith
          have hrpow_nonneg : 0 ≤ Real.rpow x c := Real.rpow_nonneg hx c
          simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hcoef hrpow_nonneg)

private lemma k_ne_zero_of_mainInductionError_lt_one
    (params : Parameters)
    (k : ℕ) (eps delta gamma : Error)
    (hsmall : mainInductionError params k eps delta gamma < 1) :
    k ≠ 0 := by
  intro hk0
  subst hk0
  have hm_sq_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
    have hm_one : (1 : Error) ≤ (params.m : Error) := by
      exact_mod_cast params.hm
    nlinarith
  have hmain_ge_one : (1 : Error) ≤ mainInductionError params 0 eps delta gamma := by
    calc
      (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) * (0 + 1) := by
            nlinarith
      _ = mainInductionError params 0 eps delta gamma := by
            simp [mainInductionError, mainInductionNu]
  linarith

/-- Internal helper: `mainInductionNu < 1` follows from `mainInductionError < 1`.

Exposed for cross-module use in `MainTheorems`. -/
lemma mainInductionNu_lt_one_of_mainInductionError_lt_one
    (params : Parameters)
    (k : ℕ) (eps delta gamma : Error)
    (hsmall : mainInductionError params k eps delta gamma < 1) :
    mainInductionNu params k eps delta gamma < 1 := by
  by_cases hnu_nonneg : 0 ≤ mainInductionNu params k eps delta gamma
  · have hm_sq_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
      have hm_one : (1 : Error) ≤ (params.m : Error) := by
        exact_mod_cast params.hm
      nlinarith
    have hexp_nonneg :
        0 ≤ Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
      positivity
    have hnu_le : mainInductionNu params k eps delta gamma
        ≤ mainInductionError params k eps delta gamma := by
      calc
        mainInductionNu params k eps delta gamma
          ≤ ((params.m : Error) ^ (2 : ℕ)) * mainInductionNu params k eps delta gamma := by
              nlinarith
        _ ≤ ((params.m : Error) ^ (2 : ℕ)) *
              (mainInductionNu params k eps delta gamma +
                Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
              have hinner :
                  mainInductionNu params k eps delta gamma ≤
                    mainInductionNu params k eps delta gamma +
                      Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) :=
                le_add_of_nonneg_right hexp_nonneg
              exact mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = mainInductionError params k eps delta gamma := by
              simp [mainInductionError]
    exact lt_of_le_of_lt hnu_le hsmall
  · linarith

private lemma mainInductionCoeff_ge_one
    (params : Parameters) {k : ℕ}
    (hk0 : k ≠ 0) :
    (1 : Error) ≤
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
  have hk_one : (1 : Error) ≤ (k : Error) := by
    have hk_nat_one : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    exact_mod_cast hk_nat_one
  have hm_one : (1 : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast params.next.hm
  have hk_sq_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
    nlinarith [hk_one]
  have hm_sq_ge_one : (1 : Error) ≤ ((params.next.m : Error) ^ (2 : ℕ)) := by
    nlinarith [hm_one]
  nlinarith

private lemma le_one_of_mainInductionError_lt_one_of_scaled_bound
    (params : Parameters) {k : ℕ} {eps delta gamma x : Error}
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hscaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow x (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma) :
    x ≤ 1 := by
  have hk0 :=
    k_ne_zero_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  have hcoef_ge_one := mainInductionCoeff_ge_one params hk0
  have hnu_lt :=
    mainInductionNu_lt_one_of_mainInductionError_lt_one
      params.next k eps delta gamma hsmall
  have hroot_lt : Real.rpow x (1 / (1024 : Error)) < 1 := by
    by_contra hroot
    have hroot_ge : 1 ≤ Real.rpow x (1 / (1024 : Error)) :=
      le_of_not_gt hroot
    have : 1 ≤
        1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow x (1 / (1024 : Error)) := by
      nlinarith [hcoef_ge_one]
    linarith
  exact le_one_of_rpow_le_one (by positivity) hroot_lt.le

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

/-- Internal helper: under `mainInductionError < 1`, the axis-parallel error `eps ≤ 1`.

Exposed for cross-module use in `MainTheorems`. -/
lemma eps_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    eps ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
    nlinarith
  have heps_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow eps (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    have hsummono :
        Real.rpow eps (1 / (1024 : Error)) ≤
          Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact
    le_one_of_mainInductionError_lt_one_of_scaled_bound
      params hsmall heps_scaled_le

/-- Internal helper: under `mainInductionError < 1`, the self-consistency error `delta ≤ 1`.

Exposed for cross-module use in `MainTheorems`. -/
lemma delta_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    delta ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
    nlinarith
  have hdelta_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow delta (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    have hsummono :
        Real.rpow delta (1 / (1024 : Error)) ≤
          Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact
    le_one_of_mainInductionError_lt_one_of_scaled_bound
      params hsmall hdelta_scaled_le

/-- Internal helper: `3 ≤ k² · m_next` in the small-parameter regime.

Exposed for cross-module use in `AvgSliceErrors`. -/
lemma three_le_k_sq_mul_next_m_of_hsmall
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    (3 : Error) ≤ ((k : Error) ^ (2 : ℕ)) * (params.next.m : Error) := by
  have hk0 := k_ne_zero_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  have hk1_nat : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
  by_cases hk1 : k = 1
  · subst hk1
    by_cases hnext_two : params.next.m = 2
    · have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
      have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
      have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
      have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
        positivity
      have hnu_nonneg : 0 ≤ mainInductionNu params.next 1 eps delta gamma := by
        have hsumnn :
            0 ≤ Real.rpow eps (1 / (1024 : Error)) +
                  Real.rpow delta (1 / (1024 : Error)) +
                  Real.rpow gamma (1 / (1024 : Error)) +
                  Real.rpow (((params.next.d : Error) / (params.next.q : Error)))
                    (1 / (1024 : Error)) := by
          have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
            Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
          have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
            Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
          have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
          have hratio_root_nonneg :
              0 ≤ Real.rpow (((params.next.d : Error) / (params.next.q : Error)))
                    (1 / (1024 : Error)) :=
            Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
          nlinarith [heps_root_nonneg, hdelta_root_nonneg, hgamma_root_nonneg,
            hratio_root_nonneg]
        unfold mainInductionNu
        exact mul_nonneg (by positivity) hsumnn
      have hnext_two' : (params.next.m : Error) = 2 := by
        exact_mod_cast hnext_two
      have hexp_quarter :
          (1 / 4 : Error) ≤
            Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))))) := by
        have hbase : (1 / 4 : Error) ≤ 1 - (1 / 320000 : Error) := by
          norm_num
        have hexp :
            1 - (1 / 320000 : Error) ≤ Real.exp (-(1 / 320000 : Error)) := by
          simpa using Real.one_sub_le_exp_neg (1 / 320000 : Error)
        calc
          (1 / 4 : Error) ≤ 1 - (1 / 320000 : Error) := hbase
          _ ≤ Real.exp (-(1 / 320000 : Error)) := hexp
          _ = Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))))) := by
                rw [hnext_two']
                norm_num
      have hmain_ge_one : (1 : Error) ≤ mainInductionError params.next 1 eps delta gamma := by
        have hm_sq_eq_four : ((params.next.m : Error) ^ (2 : ℕ)) = 4 := by
          nlinarith [hnext_two']
        have hinner :
            (1 / 4 : Error) ≤
              mainInductionNu params.next 1 eps delta gamma +
                Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))))) := by
          nlinarith
        calc
          (1 : Error) = ((params.next.m : Error) ^ (2 : ℕ)) * (1 / 4 : Error) := by
              rw [hm_sq_eq_four]
              norm_num
          _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) *
                (mainInductionNu params.next 1 eps delta gamma +
                  Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ)))))) := by
                gcongr
          _ = mainInductionError params.next 1 eps delta gamma := by
                simp [mainInductionError]
      have hsmall' : mainInductionError params.next 1 eps delta gamma < 1 := by
        simpa using hsmall
      linarith
    · have hmnat : 2 ≤ params.next.m := Nat.succ_le_succ params.hm
      have hnext_ge_three : 3 ≤ params.next.m := by
        omega
      have : (3 : Error) ≤ (params.next.m : Error) := by
        exact_mod_cast hnext_ge_three
      simpa using this
  · have hk_ge_two : 2 ≤ k := by
      omega
    have hk_sq_ge_four : (4 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
      have hk_two : (2 : Error) ≤ (k : Error) := by
        exact_mod_cast hk_ge_two
      nlinarith
    have hnext_ge_two : (2 : Error) ≤ (params.next.m : Error) := by
      exact_mod_cast Nat.succ_le_succ params.hm
    nlinarith

/-- Internal helper: under `mainInductionError < 1`, the diagonal error `gamma ≤ 1`.

Exposed for cross-module use in `MainTheorems`. -/
lemma gamma_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    gamma ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
    exact add_nonneg (add_nonneg heps_root_nonneg hdelta_root_nonneg) hratio_root_nonneg
  have hgamma_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow gamma (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    have hsummono :
        Real.rpow gamma (1 / (1024 : Error)) ≤
          Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact
    le_one_of_mainInductionError_lt_one_of_scaled_bound
      params hsmall hgamma_scaled_le

/-- Internal helper: under `mainInductionError < 1`, `params.d ≤ params.q`.

Exposed for cross-module use in `MainTheorems`. -/
lemma dq_le_q_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    params.d ≤ params.q := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    nlinarith
  have hratio_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    have hsummono :
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
          Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hratio_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 := by
    exact
      le_one_of_mainInductionError_lt_one_of_scaled_bound
        params hsmall hratio_scaled_le
  have hq_pos : (0 : Error) < (params.q : Error) := by
    exact_mod_cast params.hq
  exact_mod_cast ((div_le_one hq_pos).1 hratio_le_one)

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
    have hsummono :
        Real.rpow eps (1 / (32 : Error)) ≤
          Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg : 0 ≤ 3000 * (params.next.m : Error) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [selfImprovementInInductionError, Parameters.next, mul_assoc, mul_left_comm,
        mul_comm] using hmul
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
    have hsummono :
        Real.rpow delta (1 / (32 : Error)) ≤
          Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg : 0 ≤ 3000 * (params.next.m : Error) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [selfImprovementInInductionError, Parameters.next, mul_assoc, mul_left_comm,
        mul_comm] using hmul
  exact
    le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound
      params hzeta_le hdelta_scaled_le


end MIPStarRE.LDT.MainInductionStep
