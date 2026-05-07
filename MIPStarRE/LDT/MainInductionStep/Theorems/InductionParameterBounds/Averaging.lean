import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries

/-!
# Section 6 — Induction Parameter Averaging Bounds

This file is one leaf of `InductionParameterBounds`. It contains the uniform
Jensen estimate used for averaged slice errors, together with the
`sliceConditioningLoss` comparisons which replace the ambient factor `m` by
`m + 1` in the induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

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

end MIPStarRE.LDT.MainInductionStep
