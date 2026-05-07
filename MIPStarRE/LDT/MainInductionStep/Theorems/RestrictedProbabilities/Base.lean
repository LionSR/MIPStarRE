import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Test.StrategyFailures
import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.Tactic.AvgCongr

/-!
# Section 6 -- Restricted Probability Common Lemmas

This module contains the averaging and scalar normalization lemmas shared by the
axis-parallel, diagonal, and answer-valued restricted-probability bounds.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Averaging the self-consistency defect over all horizontal restrictions
recovers the ambient self-consistency defect. -/
lemma selfConsistencyRestrictedAverage_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability) =
      strategy.selfConsistencyFailureProbability := by
  let g : Point params.next → Error :=
    fun u =>
      qBipartiteSSCDefect strategy.state ((strategy.pointMeasurement u).toSubMeas)
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
              rfl
    _ = avgOver (uniformDistribution (Point params.next)) g := by
          simpa using (CommutativityPoints.avgOver_uniform_pointNext_decompose params g).symm
    _ = strategy.selfConsistencyFailureProbability := by
          rfl

/-- The weighted average over embedded transverse directions is bounded by the
ambient average over all directions. -/
lemma weighted_embedded_average_le_full_average
    (params : Parameters)
    (f : Fin params.next.m → Error)
    (hf : ∀ i, 0 ≤ f i) :
    sliceTransverseDirectionWeight params *
        avgOver (uniformDistribution (Fin params.m)) (fun i => f (embedCoord params i)) ≤
      avgOver (uniformDistribution (Fin params.next.m)) f := by
  have hm : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hnextm : (params.next.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.next.hm)
  have hsum_le :
      ∑ i : Fin params.m, f (embedCoord params i) ≤ ∑ j : Fin params.next.m, f j := by
    classical
    calc
      ∑ i : Fin params.m, f (embedCoord params i)
        = Finset.sum
            (((Finset.univ : Finset (Fin params.m)).image (embedCoord params)))
            (fun j => f j) := by
            symm
            refine Finset.sum_image ?_
            intro a _ b _ hab
            exact embedCoord_injective params hab
      _ ≤ ∑ j : Fin params.next.m, f j := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (by simp) ?_
            intro j _ _
            exact hf j
  calc
    sliceTransverseDirectionWeight params *
        avgOver (uniformDistribution (Fin params.m)) (fun i => f (embedCoord params i))
      = sliceTransverseDirectionWeight params *
          ∑ i : Fin params.m, (1 / (params.m : Error)) * f (embedCoord params i) := by
            simp [avgOver, uniformDistribution, Fintype.card_fin]
    _ = ∑ i : Fin params.m,
          (sliceTransverseDirectionWeight params * (1 / (params.m : Error)))
              * f (embedCoord params i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
    _ = ∑ i : Fin params.m, (1 / (params.next.m : Error)) * f (embedCoord params i) := by
            have hnext : (params.next.m : Error) = (params.m : Error) + 1 := by
              simp [Parameters.next]
            have hplus_ne : (params.m : Error) + 1 ≠ 0 := hnext ▸ hnextm
            have hweight :
                sliceTransverseDirectionWeight params =
                  (params.m : Error) / ((params.m : Error) + 1) := by
              unfold sliceTransverseDirectionWeight
              push_cast
              ring
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hweight, hnext]
            field_simp
    _ = (1 / (params.next.m : Error)) * ∑ i : Fin params.m, f (embedCoord params i) := by
            symm
            rw [Finset.mul_sum]
    _ ≤ (1 / (params.next.m : Error)) * ∑ j : Fin params.next.m, f j := by
            exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = ∑ j : Fin params.next.m, (1 / (params.next.m : Error)) * f j := by
            rw [Finset.mul_sum]
    _ = avgOver (uniformDistribution (Fin params.next.m)) f := by
            simp [avgOver, uniformDistribution, Fintype.card_fin]

/-- Remove the transverse-direction weight from an averaged restricted bound. -/
lemma weighted_bound_to_average
    (params : Parameters)
    {a b : Error}
    (h : sliceTransverseDirectionWeight params * a ≤ b) :
    a ≤ sliceConditioningLoss params * b := by
  have hmul :
      sliceConditioningLoss params * (sliceTransverseDirectionWeight params * a) ≤
        sliceConditioningLoss params * b :=
    mul_le_mul_of_nonneg_left h (by
      unfold sliceConditioningLoss
      positivity)
  have hcancel :
      sliceConditioningLoss params * (sliceTransverseDirectionWeight params * a) = a := by
    unfold sliceConditioningLoss sliceTransverseDirectionWeight
    have hm : (params.m : Error) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt params.hm)
    have hms : (((params.m + 1 : ℕ) : Error)) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero params.m)
    field_simp [hm, hms]
  calc
    a = sliceConditioningLoss params * (sliceTransverseDirectionWeight params * a) := by
          symm
          exact hcancel
    _ ≤ sliceConditioningLoss params * b := hmul

end MIPStarRE.LDT.MainInductionStep
