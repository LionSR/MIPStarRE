import MIPStarRE.LDT.Pasting.Simplified.MatchingContraction
import MIPStarRE.LDT.Pasting.Sandwich.GHatSandwich

/-!
# Normalization of completed measurement words

For a fixed tuple of slice questions, summing the adjoint-square of every
completed outcome word gives the identity. This is one of the two diagonal
normalizations in the simplified random-word energy identity.

## References

- `blueprint/src/low_degree_simplified.tex`, equation `eq:random-word-energy`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Outcome summation of the adjoint-square of a completed measurement word. -/
theorem gHatHalfProduct_adjoint_square_sum_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k),
      (∑ gs : GHatTupleOutcome params k,
        (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ *
          gHatHalfProductOutcomeOperator params family k xs gs) = 1 := by
  intro k
  induction k with
  | zero =>
      intro xs
      simp [gHatHalfProductOutcomeOperator]
  | succ k ih =>
      intro xs
      let P := (gHatIdxMeas params family (xs 0)).toSubMeas
      let tail := fun gs : GHatTupleOutcome params k =>
        gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs
      have hsplit :
          (∑ gs : GHatTupleOutcome params (k + 1),
            (gHatHalfProductOutcomeOperator params family (k + 1) xs gs)ᴴ *
              gHatHalfProductOutcomeOperator params family (k + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params k,
              (P.outcome p.1 * tail p.2)ᴴ * (P.outcome p.1 * tail p.2) := by
        symm
        exact (Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params k)
          (fun gs =>
            (gHatHalfProductOutcomeOperator params family (k + 1) xs gs)ᴴ *
              gHatHalfProductOutcomeOperator params family (k + 1) xs gs)
          (fun p => (P.outcome p.1 * tail p.2)ᴴ * (P.outcome p.1 * tail p.2))
          (by intro gs; rfl)).symm
      rw [hsplit, ← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
      have hPtotal : (∑ a : GHatOutcome params, P.outcome a) = 1 := by
        rw [P.sum_eq_total]
        simp [P, gHatIdxMeas, completeSubMeas]
      calc
        ∑ gs : GHatTupleOutcome params k,
            ∑ a : GHatOutcome params,
              (P.outcome a * tail gs)ᴴ * (P.outcome a * tail gs)
          = ∑ gs : GHatTupleOutcome params k,
              (tail gs)ᴴ * (∑ a : GHatOutcome params, P.outcome a) * tail gs := by
                refine Finset.sum_congr rfl ?_
                intro gs _
                rw [Matrix.mul_sum, Matrix.sum_mul]
                refine Finset.sum_congr rfl ?_
                intro a _
                rw [Matrix.conjTranspose_mul, P.outcome_hermitian a]
                have hproj : P.outcome a * P.outcome a = P.outcome a := by
                  simpa [P] using gHatIdxMeas_proj params family (xs 0) a
                calc
                  (tail gs)ᴴ * P.outcome a * (P.outcome a * tail gs) =
                      (tail gs)ᴴ * (P.outcome a * P.outcome a) * tail gs := by
                        noncomm_ring
                  _ = (tail gs)ᴴ * P.outcome a * tail gs := by rw [hproj]
        _ = ∑ gs : GHatTupleOutcome params k, (tail gs)ᴴ * tail gs := by
              simp [hPtotal]
        _ = 1 := ih (pointTupleTail xs)

/-- The opposite adjoint-square normalization follows from completeness of
the existing sequential sandwich measurement. -/
theorem gHatHalfProduct_square_adjoint_sum_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (k : ℕ) (xs : PointTuple params k) :
    (∑ gs : GHatTupleOutcome params k,
      gHatHalfProductOutcomeOperator params family k xs gs *
        (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ) = 1 := by
  calc
    (∑ gs : GHatTupleOutcome params k,
      gHatHalfProductOutcomeOperator params family k xs gs *
        (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ) =
        (gHatSandwichFamily params family k xs).total := by
          exact (gHatSandwichFamily params family k xs).sum_eq_total
    _ = 1 := by
      simp [gHatSandwichFamily, gHatHalfProductTotalOperator_eq_one]

end MIPStarRE.LDT.Pasting
