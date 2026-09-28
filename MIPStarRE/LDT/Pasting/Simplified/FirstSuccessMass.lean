import MIPStarRE.LDT.Pasting.Simplified.WordOutcomeDistribution

/-!
# Mass of the first-success pasted submeasurement

The total mass retained by distinct-success interpolation equals the
probability that the completed sequential measurement produces an eligible
word. This identifies the operator construction with the finite probability
estimate used in the simplified pasting argument.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:first-success-completeness`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At fixed questions, the retained total is the sum of the eligible
completed word outcomes. -/
theorem distinctSuccessSandwichFamily_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params k) :
    (distinctSuccessSandwichFamily params family k xs).total =
      ∑ gs : GHatTupleOutcome params k,
        if HasDistinctSuccessSupport params xs gs then
          (gHatSandwichFamily params family k xs).outcome gs else 0 := by
  classical
  simp [distinctSuccessSandwichFamily, postprocess_total, restrictSubMeas,
    Finset.sum_filter]

/-- The pasted submeasurement's first-register mass is the probability of
an outcome with sufficiently many distinct successful slice heights. -/
theorem distinctSuccessPastedMass_eq_eligible_probability
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) :
    ev ψ (leftTensor (ι₂ := ι)
        (distinctSuccessPastedSubMeas params family k).total) =
      avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => if HasDistinctSuccessSupport params p.1 p.2 then
          (1 : Error) else 0) := by
  classical
  have hfixed (xs : PointTuple params k) :
      ev ψ (leftTensor (ι₂ := ι)
          (distinctSuccessSandwichFamily params family k xs).total) =
        ∑ gs : GHatTupleOutcome params k,
          ev ψ (leftTensor (ι₂ := ι)
            ((gHatSandwichFamily params family k xs).outcome gs)) *
              (if HasDistinctSuccessSupport params xs gs then (1 : Error) else 0) := by
    rw [distinctSuccessSandwichFamily_total, ← leftTensor_finset_sum, ev_finset_sum]
    apply Finset.sum_congr rfl
    intro gs _
    split_ifs <;> simp [leftTensor, Matrix.kronecker, ev_zero]
  calc
    ev ψ (leftTensor (ι₂ := ι)
        (distinctSuccessPastedSubMeas params family k).total) =
      avgOver (uniformDistribution (PointTuple params k))
        (fun xs => ev ψ (leftTensor (ι₂ := ι)
          (distinctSuccessSandwichFamily params family k xs).total)) := by
            simp only [distinctSuccessPastedSubMeas, averageIdxSubMeas]
            exact ev_leftTensor_averageOperatorOverDistribution ψ
              (uniformDistribution (PointTuple params k))
              (fun xs => (distinctSuccessSandwichFamily params family k xs).total)
    _ = avgOver (uniformDistribution (PointTuple params k))
          (fun xs => ∑ gs : GHatTupleOutcome params k,
            ev ψ (leftTensor (ι₂ := ι)
              ((gHatSandwichFamily params family k xs).outcome gs)) *
                (if HasDistinctSuccessSupport params xs gs then
                  (1 : Error) else 0)) := by
            exact avgOver_congr _ _ _ hfixed
    _ = avgOver (completedWordOutcomeDistribution params family k ψ)
          (fun p => if HasDistinctSuccessSupport params p.1 p.2 then
            (1 : Error) else 0) := by
            unfold avgOver
            simp only [completedWordOutcomeDistribution]
            rw [← Finset.univ_product_univ, Finset.sum_product]
            apply Finset.sum_congr rfl
            intro xs _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro gs _
            ring

/-- The pasted mass is bounded below by the first moment of successful
completed slices, with the distinct-height collision cost. -/
theorem distinctSuccessPastedMass_ge_first_moment
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (hdk : params.d < k) :
    (avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => (completedWordSuccessCount params p : Error)) -
          (params.d : Error)) / ((k - params.d : ℕ) : Error) -
      ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
      ev ψ (leftTensor (ι₂ := ι)
        (distinctSuccessPastedSubMeas params family k).total) := by
  rw [distinctSuccessPastedMass_eq_eligible_probability]
  exact completedWord_eligible_probability_ge_first_moment
    params family k ψ hψ hdk

/-- Degree-zero pasted mass requires no collision deduction. -/
theorem distinctSuccessPastedMass_degree_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (hd : params.d = 0) (hk : 0 < k) :
    avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => (completedWordSuccessCount params p : Error)) /
          (k : Error) ≤
      ev ψ (leftTensor (ι₂ := ι)
        (distinctSuccessPastedSubMeas params family k).total) := by
  rw [distinctSuccessPastedMass_eq_eligible_probability]
  exact completedWord_eligible_probability_degree_zero
    params family k ψ hψ hd hk

end MIPStarRE.LDT.Pasting
