import MIPStarRE.LDT.Pasting.Simplified.FirstMoment
import MIPStarRE.LDT.Pasting.Simplified.WordMarginal
import MIPStarRE.LDT.Pasting.Simplified.DistinctSuccessConstruction
import MIPStarRE.LDT.Pasting.Core.DDistinct

/-!
# Joint distribution of random questions and completed word outcomes

Sampling a uniform tuple of slice questions and performing its sequential
completed measurement gives a finite probability distribution. The success
count is the number of non-failure outcomes in the resulting word.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:first-success-completeness`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Joint law of a uniform question tuple and its sequential completed
measurement outcome, evaluated on a bipartite state through the first register. -/
noncomputable def completedWordOutcomeDistribution
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) :
    Distribution (PointTuple params k × GHatTupleOutcome params k) where
  support := Finset.univ
  weight := fun p =>
    (uniformDistribution (PointTuple params k)).weight p.1 *
      ev ψ (leftTensor (ι₂ := ι)
        ((gHatSandwichFamily params family k p.1).outcome p.2))
  nonnegative := by
    intro p
    exact mul_nonneg
      ((uniformDistribution (PointTuple params k)).nonnegative p.1)
      (ev_nonneg_of_psd ψ _
        (leftTensor_nonneg ((gHatSandwichFamily params family k p.1).outcome_pos p.2)))
  outsideSupport := by
    intro p hp
    exact (hp (Finset.mem_univ p)).elim

/-- For fixed questions, the completed sequential measurement has unit
outcome mass on a normalized bipartite state. -/
theorem completedWordOutcomeMass_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (xs : PointTuple params k) :
    (∑ gs : GHatTupleOutcome params k,
      ev ψ (leftTensor (ι₂ := ι)
        ((gHatSandwichFamily params family k xs).outcome gs))) = 1 := by
  rw [← ev_finset_sum, leftTensor_finset_sum,
    (gHatSandwichFamily params family k xs).sum_eq_total]
  have htotal : (gHatSandwichFamily params family k xs).total = 1 := by
    simp [gHatSandwichFamily, gHatHalfProductTotalOperator_eq_one]
  rw [htotal, leftTensor_one]
  exact ev_one_of_isNormalized ψ hψ

/-- The joint law has total mass one for a normalized state. -/
theorem completedWordOutcomeDistribution_isProbability
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized) :
    (completedWordOutcomeDistribution params family k ψ).IsProbability := by
  unfold Distribution.IsProbability Distribution.totalWeight
  simp only [completedWordOutcomeDistribution]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  have hpoint (xs : PointTuple params k) :=
    completedWordOutcomeMass_eq_one params family k ψ hψ xs
  calc
    (∑ xs : PointTuple params k, ∑ gs : GHatTupleOutcome params k,
      (uniformDistribution (PointTuple params k)).weight xs *
        ev ψ (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family k xs).outcome gs))) =
      ∑ xs : PointTuple params k,
        (uniformDistribution (PointTuple params k)).weight xs *
          (∑ gs : GHatTupleOutcome params k,
            ev ψ (leftTensor (ι₂ := ι)
              ((gHatSandwichFamily params family k xs).outcome gs))) := by
          exact Finset.sum_congr rfl fun xs _ => (Finset.mul_sum ..).symm
    _ = ∑ xs : PointTuple params k,
          (uniformDistribution (PointTuple params k)).weight xs := by
            simp_rw [hpoint]
            simp
    _ = 1 := by
      have hprob :=
        (uniformDistribution_isProbability (PointTuple params k)).weight_sum_eq_one
      change (∑ xs : PointTuple params k,
        (uniformDistribution (PointTuple params k)).weight xs) = 1 at hprob
      exact hprob

/-- Marginalizing over completed word outcomes recovers the uniform law of
the question tuple. -/
theorem completedWordOutcomeDistribution_question_marginal
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (f : PointTuple params k → Error) :
    avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => f p.1) =
      avgOver (uniformDistribution (PointTuple params k)) f := by
  unfold avgOver
  simp only [completedWordOutcomeDistribution]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  calc
    (∑ xs : PointTuple params k, ∑ gs : GHatTupleOutcome params k,
      (uniformDistribution (PointTuple params k)).weight xs *
        ev ψ (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family k xs).outcome gs)) * f xs) =
      ∑ xs : PointTuple params k,
        (uniformDistribution (PointTuple params k)).weight xs *
          ((∑ gs : GHatTupleOutcome params k,
            ev ψ (leftTensor (ι₂ := ι)
              ((gHatSandwichFamily params family k xs).outcome gs))) * f xs) := by
          refine Finset.sum_congr rfl ?_
          intro xs _
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun gs _ => by ring
    _ = ∑ xs : PointTuple params k,
          (uniformDistribution (PointTuple params k)).weight xs * f xs := by
            simp_rw [completedWordOutcomeMass_eq_one params family k ψ hψ]
            simp
    _ = ∑ xs ∈ (uniformDistribution (PointTuple params k)).support,
          (uniformDistribution (PointTuple params k)).weight xs * f xs := by
            rfl

/-- Total variation distance is symmetric on a finite outcome space. -/
private theorem totalVariationDistance_comm' {α : Type*}
    [Finite α] [DecidableEq α] (μ ν : Distribution α) :
    totalVariationDistance μ ν = totalVariationDistance ν μ := by
  letI : Fintype α := Fintype.ofFinite α
  rw [totalVariationDistance_eq_univ_sum, totalVariationDistance_eq_univ_sum]
  simp_rw [abs_sub_comm]

/-- Uniform question tuples have collision probability at most `k²/q`.
The existing distinct-tuple total-variation bound supplies the estimate
when `k ≤ q`; otherwise the right side is at least one. -/
theorem uniformQuestionCollision_le
    (params : Parameters) (k : ℕ) :
    avgOver (uniformDistribution (PointTuple params k))
        (fun xs => if Function.Injective xs then (0 : Error) else 1) ≤
      ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  classical
  let f : PointTuple params k → Error :=
    fun xs => if Function.Injective xs then 0 else 1
  have hf0 (xs : PointTuple params k) : 0 ≤ f xs := by simp [f]; split_ifs <;> norm_num
  have hf1 (xs : PointTuple params k) : f xs ≤ 1 := by simp [f]; split_ifs <;> norm_num
  by_cases hk : k ≤ params.q
  · have hzero : avgOver (distinctTupleDistribution params k) f = 0 := by
      unfold avgOver
      apply Finset.sum_eq_zero
      intro xs hxs
      have hinj : Function.Injective xs := by
        exact (mem_distinctTupleSupport params k xs).mp
          (by simpa using hxs)
      simp [f, hinj]
    have htv := avgOver_le_avgOver_add_totalVariationDistance
      (distinctTupleDistribution params k)
      (uniformDistribution (PointTuple params k))
      (distinctTupleDistribution_isProbability_of_le params k hk)
      (uniformDistribution_isProbability (PointTuple params k))
      f hf0 hf1
    rw [hzero, zero_add, totalVariationDistance_comm'] at htv
    exact htv.trans (ldDnoteq params k)
  · have hbound :
        avgOver (uniformDistribution (PointTuple params k)) f ≤ 1 := by
      apply avgOver_le_of_weight_sum_le_one
      · exact uniformDistribution_weight_sum_le_one (PointTuple params k)
      · norm_num
      · exact hf1
    have hqpos : (0 : Error) < params.q := by exact_mod_cast params.hq
    have hkq : params.q < k := Nat.lt_of_not_ge hk
    have hkcast : (params.q : Error) ≤ k := by exact_mod_cast hkq.le
    have hkone : (1 : Error) ≤ k := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (params.hq.trans hkq)))
    have hsq : (params.q : Error) ≤ (k : Error) ^ (2 : ℕ) := by
      nlinarith
    have hratio : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) / params.q := by
      apply (le_div_iff₀ hqpos).2
      simpa using hsq
    exact hbound.trans hratio

/-- Number of successful slice outcomes in a completed word. -/
def completedWordSuccessCount
    (params : Parameters) [FieldModel params.q] {k : ℕ}
    (p : PointTuple params k × GHatTupleOutcome params k) : ℕ :=
  gHatTupleHammingWeight p.2

/-- The success count is the sum of the individual success indicators. -/
theorem completedWordSuccessCount_eq_sum_indicators
    (params : Parameters) [FieldModel params.q] (k : ℕ)
    (p : PointTuple params k × GHatTupleOutcome params k) :
    (completedWordSuccessCount params p : Error) =
      ∑ i : Fin k, if (p.2 i).isSome then (1 : Error) else 0 := by
  classical
  simp [completedWordSuccessCount, gHatTupleHammingWeight,
    gHatTupleSupport]

/-- The expected number of successful outcomes is the sum of the
per-position success probabilities. -/
theorem completedWord_expectedSuccessCount_eq_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) :
    avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => (completedWordSuccessCount params p : Error)) =
      ∑ i : Fin k,
        avgOver (completedWordOutcomeDistribution params family k ψ)
          (fun p => if (p.2 i).isSome then (1 : Error) else 0) := by
  rw [show (fun p : PointTuple params k × GHatTupleOutcome params k =>
      (completedWordSuccessCount params p : Error)) =
        (fun p => ∑ i : Fin k, if (p.2 i).isSome then
          (1 : Error) else 0) by
            funext p
            exact completedWordSuccessCount_eq_sum_indicators params k p]
  exact avgOver_sum _ _

/-- A completed word has at most one success at each position. -/
theorem completedWordSuccessCount_le
    (params : Parameters) [FieldModel params.q] (k : ℕ)
    (p : PointTuple params k × GHatTupleOutcome params k) :
    completedWordSuccessCount params p ≤ k := by
  simp only [completedWordSuccessCount, gHatTupleHammingWeight]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

/-- The successful interpolation event contains the threshold event whenever
the sampled question heights are distinct. -/
theorem completedWord_threshold_indicator_le_eligible_add_collision
    (params : Parameters) [FieldModel params.q] (k : ℕ)
    (p : PointTuple params k × GHatTupleOutcome params k) :
    (if params.d + 1 ≤ completedWordSuccessCount params p then (1 : Error) else 0) ≤
      (if HasDistinctSuccessSupport params p.1 p.2 then (1 : Error) else 0) +
        (if Function.Injective p.1 then (0 : Error) else 1) := by
  classical
  by_cases hcount : params.d + 1 ≤ completedWordSuccessCount params p
  · by_cases hxs : Function.Injective p.1
    · have helig : HasDistinctSuccessSupport params p.1 p.2 :=
        hasDistinctSuccessSupport_of_injective params p.1 p.2 hxs hcount
      simp [hcount, hxs, helig]
    · simp [hcount, hxs]
      split_ifs <;> norm_num
  · simp [hcount]
    split_ifs <;> norm_num

/-- First-moment lower bound for the mass of outcomes admitting distinct
successful interpolation, before estimating the collision probability. -/
theorem completedWord_eligible_probability_ge_first_moment_sub_collision
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (hdk : params.d < k) :
    (avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => (completedWordSuccessCount params p : Error)) -
          (params.d : Error)) / ((k - params.d : ℕ) : Error) -
      avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => if Function.Injective p.1 then (0 : Error) else 1) ≤
      avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => if HasDistinctSuccessSupport params p.1 p.2 then
          (1 : Error) else 0) := by
  classical
  let D := completedWordOutcomeDistribution params family k ψ
  have hfirst := threshold_probability_ge_first_moment D
    (completedWordOutcomeDistribution_isProbability params family k ψ hψ)
    (completedWordSuccessCount params) k params.d
    (completedWordSuccessCount_le params k) hdk
  have hpoint := avgOver_mono D
    (fun p => if params.d + 1 ≤ completedWordSuccessCount params p then
      (1 : Error) else 0)
    (fun p =>
      (if HasDistinctSuccessSupport params p.1 p.2 then (1 : Error) else 0) +
        (if Function.Injective p.1 then (0 : Error) else 1))
    (completedWord_threshold_indicator_le_eligible_add_collision params k)
  rw [avgOver_add] at hpoint
  dsimp [D] at hfirst hpoint ⊢
  linarith

/-- Explicit first-moment lower bound with the uniform-question collision
term estimated by the existing distinct-tuple lemma. -/
theorem completedWord_eligible_probability_ge_first_moment
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (hdk : params.d < k) :
    (avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => (completedWordSuccessCount params p : Error)) -
          (params.d : Error)) / ((k - params.d : ℕ) : Error) -
      ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
      avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => if HasDistinctSuccessSupport params p.1 p.2 then
          (1 : Error) else 0) := by
  have hfirst := completedWord_eligible_probability_ge_first_moment_sub_collision
    params family k ψ hψ hdk
  have hcollision :
      avgOver (completedWordOutcomeDistribution params family k ψ)
          (fun p => if Function.Injective p.1 then (0 : Error) else 1) ≤
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
    calc
      avgOver (completedWordOutcomeDistribution params family k ψ)
          (fun p => if Function.Injective p.1 then (0 : Error) else 1) =
        avgOver (uniformDistribution (PointTuple params k))
          (fun xs => if Function.Injective xs then (0 : Error) else 1) := by
            exact completedWordOutcomeDistribution_question_marginal
              params family k ψ hψ
              (fun xs => if Function.Injective xs then (0 : Error) else 1)
      _ ≤ ((k : Error) ^ (2 : ℕ)) / (params.q : Error) :=
        uniformQuestionCollision_le params k
  linarith

/-- Degree-zero interpolation has no distinct-height collision cost. -/
theorem completedWord_eligible_probability_degree_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (hd : params.d = 0) (hk : 0 < k) :
    avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => (completedWordSuccessCount params p : Error)) /
          (k : Error) ≤
      avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => if HasDistinctSuccessSupport params p.1 p.2 then
          (1 : Error) else 0) := by
  classical
  have hfirst := threshold_probability_ge_first_moment
    (completedWordOutcomeDistribution params family k ψ)
    (completedWordOutcomeDistribution_isProbability params family k ψ hψ)
    (completedWordSuccessCount params) k 0
    (completedWordSuccessCount_le params k) hk
  have hmono := avgOver_mono
    (completedWordOutcomeDistribution params family k ψ)
    (fun p => if 1 ≤ completedWordSuccessCount params p then
      (1 : Error) else 0)
    (fun p => if HasDistinctSuccessSupport params p.1 p.2 then
      (1 : Error) else 0) (by
        intro p
        by_cases hcount : 1 ≤ completedWordSuccessCount params p
        · have helig := hasDistinctSuccessSupport_of_degree_zero
            params p.1 p.2 hd hcount
          simp [hcount, helig]
        · simp [hcount]
          split_ifs <;> norm_num)
  simpa [hd] using hfirst.trans hmono

end MIPStarRE.LDT.Pasting
