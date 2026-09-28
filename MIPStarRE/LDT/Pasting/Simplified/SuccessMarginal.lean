import MIPStarRE.LDT.Pasting.Simplified.FirstSuccessMass
import MIPStarRE.LDT.Pasting.Simplified.UniformPrefix
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.OutcomeLemmas

/-!
# Marginal of a successful completed word position

The success event at a fixed position is the total effect of the existing
one-point sandwich family. Its established prefix identity eliminates all
later completed outcomes.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:first-success-completeness`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar success mass at a position is the total effect of the
one-point family used in the original pasting argument. -/
theorem completedWord_successMass_eq_onePointTotal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ)
    (i : ℕ) (hi : i < k) (xs : PointTuple params k)
    (u : Point params) (ψ : QuantumState (ι × ι)) :
    (∑ gs : GHatTupleOutcome params k,
        ev ψ (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family k xs).outcome gs)) *
            (if (gs ⟨i, hi⟩).isSome then (1 : Error) else 0)) =
      ev ψ (leftTensor (ι₂ := ι)
        ((ldSandwichLineOnePointLeftFamily params strategy family k i)
          (u, xs)).total) := by
  classical
  have htotal :
      ((ldSandwichLineOnePointLeftFamily params strategy family k i)
          (u, xs)).total =
        ∑ gs : GHatTupleOutcome params k,
          if (gs ⟨i, hi⟩).isSome then
            (gHatSandwichFamily params family k xs).outcome gs else 0 := by
    simp [ldSandwichLineOnePointLeftFamily, hi, postprocess_total,
      restrictSubMeas, Finset.sum_filter]
  rw [htotal, ← leftTensor_finset_sum, ev_finset_sum]
  apply Finset.sum_congr rfl
  intro gs _
  split_ifs <;> simp [leftTensor, Matrix.kronecker, ev_zero]

/-- Later completed outcomes do not affect the success mass at position `i`.
The right side uses only the first `i + 1` slice questions. -/
theorem completedWord_successMass_eq_prefixTotal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ)
    (i : ℕ) (hi : i < k) (xs : PointTuple params k)
    (u : Point params) (ψ : QuantumState (ι × ι)) :
    (∑ gs : GHatTupleOutcome params k,
        ev ψ (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family k xs).outcome gs)) *
            (if (gs ⟨i, hi⟩).isSome then (1 : Error) else 0)) =
      ev ψ (leftTensor (ι₂ := ι)
        ((ldSandwichLineOnePointPrefixOriginalFamily params family hi)
          (u, xs)).total) := by
  rw [completedWord_successMass_eq_onePointTotal params strategy family k i hi xs u ψ]
  exact congrArg (fun A : IdxSubMeas (SandwichedLineQuestion params k)
      (Option (Fq params)) ι => ev ψ (leftTensor (ι₂ := ι) (A (u, xs)).total))
    (ldSandwichLineOnePointLeftFamily_eq_prefixOriginal
      params strategy family hi)

/-- The success probability at position `i` is an average of prefix-only
effects. This is the finite-distribution form of deleting later outcomes. -/
theorem completedWord_successProbability_eq_prefixAverage
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ)
    (i : ℕ) (hi : i < k)
    (u : Point params) (ψ : QuantumState (ι × ι)) :
    avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => if (p.2 ⟨i, hi⟩).isSome then (1 : Error) else 0) =
      avgOver (uniformDistribution (PointTuple params k))
        (fun xs => ev ψ (leftTensor (ι₂ := ι)
          ((ldSandwichLineOnePointPrefixOriginalFamily params family hi)
            (u, xs)).total)) := by
  classical
  unfold avgOver
  simp only [completedWordOutcomeDistribution]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro xs _
  dsimp
  calc
    (∑ gs : GHatTupleOutcome params k,
      (uniformDistribution (PointTuple params k)).weight xs *
        ev ψ (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family k xs).outcome gs)) *
            (if (gs ⟨i, hi⟩).isSome then (1 : Error) else 0)) =
      (uniformDistribution (PointTuple params k)).weight xs *
        (∑ gs : GHatTupleOutcome params k,
          ev ψ (leftTensor (ι₂ := ι)
            ((gHatSandwichFamily params family k xs).outcome gs)) *
              (if (gs ⟨i, hi⟩).isSome then (1 : Error) else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro gs _
          ring
    _ = (uniformDistribution (PointTuple params k)).weight xs *
        ev ψ (leftTensor (ι₂ := ι)
          ((ldSandwichLineOnePointPrefixOriginalFamily params family hi)
            (u, xs)).total) := by
          rw [completedWord_successMass_eq_prefixTotal
            params strategy family k i hi xs u ψ]

/-- At position `i`, the success probability depends only on the first
`i + 1` uniformly sampled questions. -/
theorem completedWord_successProbability_eq_shortPrefixAverage
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (i t : ℕ)
    (u : Point params) (ψ : QuantumState (ι × ι)) :
    avgOver (completedWordOutcomeDistribution params family (i + 1 + t) ψ)
        (fun p => if (p.2 ⟨i, by omega⟩).isSome then
          (1 : Error) else 0) =
      avgOver (uniformDistribution (PointTuple params (i + 1)))
        (fun xs => ev ψ (leftTensor (ι₂ := ι)
          ((ldSandwichLineOnePointPrefixOriginalFamily params family
            (Nat.lt_succ_self i)) (u, xs)).total)) := by
  let hi : i < i + 1 + t := by omega
  let F : PointTuple params (i + 1) → Error := fun xs =>
    ev ψ (leftTensor (ι₂ := ι)
      ((ldSandwichLineOnePointPrefixOriginalFamily params family
        (Nat.lt_succ_self i)) (u, xs)).total)
  have hpoint (xs : PointTuple params (i + 1 + t)) :
      ev ψ (leftTensor (ι₂ := ι)
        ((ldSandwichLineOnePointPrefixOriginalFamily params family hi)
          (u, xs)).total) =
        F (pointTuplePrefix params (Nat.le_add_right (i + 1) t) xs) := by
    rfl
  calc
    avgOver (completedWordOutcomeDistribution params family (i + 1 + t) ψ)
        (fun p => if (p.2 ⟨i, by omega⟩).isSome then
          (1 : Error) else 0) =
      avgOver (uniformDistribution (PointTuple params (i + 1 + t)))
        (fun xs => ev ψ (leftTensor (ι₂ := ι)
          ((ldSandwichLineOnePointPrefixOriginalFamily params family hi)
            (u, xs)).total)) := by
          exact completedWord_successProbability_eq_prefixAverage
            params strategy family (i + 1 + t) i hi u ψ
    _ = avgOver (uniformDistribution (PointTuple params (i + 1 + t)))
          (fun xs => F (pointTuplePrefix params
            (Nat.le_add_right (i + 1) t) xs)) := by
          exact avgOver_congr _ _ _ hpoint
    _ = avgOver (uniformDistribution (PointTuple params (i + 1))) F :=
      avgOver_uniform_pointTuple_prefix params (i + 1) t F

/-- Summing the successful outcomes of one completed slice leaves the
original slice total inside the surrounding sandwich. -/
theorem completedSlice_successSandwich_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params)
    (P : MIPStarRE.Quantum.Op ι) :
    (∑ g : GHatOutcome params,
        if g.isSome then
          (P * (gHatIdxMeas params family x).outcome g) *
            (P * (gHatIdxMeas params family x).outcome g)ᴴ
        else 0) =
      P * (family.meas x).total * Pᴴ := by
  classical
  rw [Fintype.sum_option]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    Option.isSome_some, zero_add]
  change (∑ g : Polynomial params,
    (P * (family.meas x).outcome g) *
      (P * (family.meas x).outcome g)ᴴ) =
      P * (family.meas x).total * Pᴴ
  calc
    (∑ g : Polynomial params,
      (P * (family.meas x).outcome g) *
        (P * (family.meas x).outcome g)ᴴ) =
      ∑ g : Polynomial params, P * (family.meas x).outcome g * Pᴴ := by
        apply Finset.sum_congr rfl
        intro g _
        rw [Matrix.conjTranspose_mul,
          (family.meas x).outcome_hermitian g,
          ← mul_assoc, mul_assoc P,
          (family.meas x).proj g]
    _ = P * (∑ g : Polynomial params, (family.meas x).outcome g) * Pᴴ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = P * (family.meas x).total * Pᴴ := by
      rw [(family.meas x).sum_eq_total]

/-- The final success event in a prefix word is the original slice total
inserted after the preceding completed outcomes. -/
theorem completedWord_shortPrefixSuccessTotal_eq_sandwich
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (i : ℕ)
    (xs : PointTuple params (i + 1)) (u : Point params) :
    ((ldSandwichLineOnePointPrefixOriginalFamily params family
      (Nat.lt_succ_self i)) (u, xs)).total =
      ∑ gs : GHatTupleOutcome params i,
        let W := gHatHalfProductOutcomeOperator params family i (Fin.init xs) gs
        W * (family.meas (xs (Fin.last i))).total * Wᴴ := by
  classical
  let e := gHatTupleOutcomePrefixLastEquiv params i
  have htotal :
      ((ldSandwichLineOnePointPrefixOriginalFamily params family
        (Nat.lt_succ_self i)) (u, xs)).total =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if (gs (Fin.last i)).isSome then
          (gHatSandwichFamily params family (i + 1) xs).outcome gs else 0 := by
    simp [ldSandwichLineOnePointPrefixOriginalFamily, postprocess_total,
      restrictSubMeas, Finset.sum_filter, Fin.last]
    rfl
  rw [htotal]
  calc
    (∑ gs : GHatTupleOutcome params (i + 1),
      if (gs (Fin.last i)).isSome then
        (gHatSandwichFamily params family (i + 1) xs).outcome gs else 0) =
      ∑ p : GHatTupleOutcome params i × GHatOutcome params,
        if p.2.isSome then
          let W := gHatHalfProductOutcomeOperator params family i (Fin.init xs) p.1
          (W * (gHatIdxMeas params family (xs (Fin.last i))).outcome p.2) *
            (W * (gHatIdxMeas params family (xs (Fin.last i))).outcome p.2)ᴴ
        else 0 := by
          apply Fintype.sum_equiv e
          intro gs
          have hlast : (e gs).2 = gs (Fin.last i) := by
            simp [e, gHatTupleOutcomePrefixLastEquiv, Fin.last]
          have hhalf :=
            gHatHalfProductOutcomeOperator_prefix_last params family i xs gs
          have hxs : (fun j : Fin i => xs ⟨j.1, by omega⟩) = Fin.init xs := by
            funext j
            rfl
          rw [hxs] at hhalf
          simp only [gHatSandwichFamily]
          rw [hlast]
          simpa [e, gHatTupleOutcomePrefixLastEquiv, Fin.init, Fin.last]
            using congrArg (fun W => if (gs (Fin.last i)).isSome then W * Wᴴ else 0)
              hhalf
    _ = ∑ gs : GHatTupleOutcome params i,
          ∑ g : GHatOutcome params,
            if g.isSome then
              let W := gHatHalfProductOutcomeOperator params family i (Fin.init xs) gs
              (W * (gHatIdxMeas params family (xs (Fin.last i))).outcome g) *
                (W * (gHatIdxMeas params family (xs (Fin.last i))).outcome g)ᴴ
            else 0 := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ gs : GHatTupleOutcome params i,
          let W := gHatHalfProductOutcomeOperator params family i (Fin.init xs) gs
          W * (family.meas (xs (Fin.last i))).total * Wᴴ := by
          apply Finset.sum_congr rfl
          intro gs _
          exact completedSlice_successSandwich_sum params family
            (xs (Fin.last i)) _

end MIPStarRE.LDT.Pasting
