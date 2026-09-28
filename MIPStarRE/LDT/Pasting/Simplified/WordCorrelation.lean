import MIPStarRE.LDT.Pasting.Simplified.WordEnergyAlgebra
import MIPStarRE.LDT.Basic.DistributionProduct

/-!
# Tensor correlation of completed measurement words

For fixed questions, the sum of the two-register word operators factors
into the ordered product of matching-outcome operators. This is the
deterministic part of the random-word correlation identity.

## References

- `blueprint/src/low_degree_simplified.tex`, equation `eq:random-word-energy`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two-register correlation of all completed words at fixed questions. -/
noncomputable def matchingWordCorrelation
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) (xs : PointTuple params k) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  ∑ gs : GHatTupleOutcome params k,
    opTensor (gHatHalfProductOutcomeOperator params family k xs gs)
      (gHatHalfProductOutcomeOperator params family k xs gs)

/-- Splitting the first completed question factors the word correlation. -/
theorem matchingWordCorrelation_succ
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1)) :
    matchingWordCorrelation params family (k + 1) xs =
      matchingOutcomeAt params family (xs 0) *
        matchingWordCorrelation params family k (pointTupleTail xs) := by
  let P := (gHatIdxMeas params family (xs 0)).toSubMeas
  let tail := fun gs : GHatTupleOutcome params k =>
    gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs
  have hsplit : matchingWordCorrelation params family (k + 1) xs =
      ∑ p : GHatOutcome params × GHatTupleOutcome params k,
        opTensor (P.outcome p.1 * tail p.2) (P.outcome p.1 * tail p.2) := by
    unfold matchingWordCorrelation
    symm
    exact (Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params k)
      (fun gs => opTensor
        (gHatHalfProductOutcomeOperator params family (k + 1) xs gs)
        (gHatHalfProductOutcomeOperator params family (k + 1) xs gs))
      (fun p => opTensor (P.outcome p.1 * tail p.2) (P.outcome p.1 * tail p.2))
      (by intro gs; rfl)).symm
  rw [hsplit, ← Finset.univ_product_univ, Finset.sum_product]
  calc
    ∑ a : GHatOutcome params, ∑ gs : GHatTupleOutcome params k,
        opTensor (P.outcome a * tail gs) (P.outcome a * tail gs) =
      ∑ a : GHatOutcome params, ∑ gs : GHatTupleOutcome params k,
        opTensor (P.outcome a) (P.outcome a) * opTensor (tail gs) (tail gs) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact Finset.sum_congr rfl fun gs _ => (opTensor_mul _ _ _ _).symm
    _ = matchingOutcomeAt params family (xs 0) *
        matchingWordCorrelation params family k (pointTupleTail xs) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
          rfl

/-- The correlation averaged over independent uniform questions. -/
noncomputable def matchingWordCorrelationAverage
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  averageOperatorOverDistribution (uniformDistribution (PointTuple params k))
    (matchingWordCorrelation params family k)

/-- Independence of the questions makes the averaged word correlation a power
of the single-question matching contraction. -/
theorem matchingWordCorrelationAverage_eq_pow
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ k : ℕ, matchingWordCorrelationAverage params family k =
      matchingOutcomeAverage params family ^ k := by
  intro k
  induction k with
  | zero =>
      have hword : ∀ xs : PointTuple params 0,
          matchingWordCorrelation params family 0 xs = 1 := by
        intro xs
        simp only [matchingWordCorrelation, gHatHalfProductOutcomeOperator,
          Finset.sum_const]
        simp [opTensor]
      unfold matchingWordCorrelationAverage
      rw [averageOperatorOverDistribution_congr _ _ _ hword]
      simpa using averageOperatorOverDistribution_const_of_isProbability
        (uniformDistribution (PointTuple params 0))
        (uniformDistribution_isProbability (PointTuple params 0))
        (1 : MIPStarRE.Quantum.Op (ι × ι))
  | succ k ih =>
      let D := uniformDistribution (Fq params)
      let E := uniformDistribution (PointTuple params k)
      have hsplit : matchingWordCorrelationAverage params family (k + 1) =
          averageOperatorOverDistribution D (fun x =>
            averageOperatorOverDistribution E (fun xs =>
              matchingOutcomeAt params family x *
                matchingWordCorrelation params family k xs)) := by
        unfold matchingWordCorrelationAverage
        rw [averageOperatorOverDistribution_uniform_equiv_prod
          (Fin.consEquiv (fun _ : Fin (k + 1) => Fq params)).symm]
        apply averageOperatorOverDistribution_congr
        intro x
        apply averageOperatorOverDistribution_congr
        intro xs
        have htail : pointTupleTail (Fin.cons x xs) = xs := by
          funext i
          rfl
        simpa [Fin.consEquiv, htail] using
          matchingWordCorrelation_succ params family k (Fin.cons x xs)
      rw [hsplit]
      have hinner (x : Fq params) :
          averageOperatorOverDistribution E (fun xs =>
            matchingOutcomeAt params family x *
              matchingWordCorrelation params family k xs) =
            matchingOutcomeAt params family x *
              matchingWordCorrelationAverage params family k := by
        simpa [matchingWordCorrelationAverage, E] using
          (averageOperatorOverDistribution_mul_left_right E
            (matchingOutcomeAt params family x) 1
            (matchingWordCorrelation params family k))
      simp_rw [hinner]
      have houter :
          averageOperatorOverDistribution D (fun x =>
            matchingOutcomeAt params family x *
              matchingWordCorrelationAverage params family k) =
            matchingOutcomeAverage params family *
              matchingWordCorrelationAverage params family k := by
        simpa [matchingOutcomeAverage, D] using
          (averageOperatorOverDistribution_mul_left_right D 1
            (matchingWordCorrelationAverage params family k)
            (matchingOutcomeAt params family))
      rw [houter, ih]
      simp only [pow_succ']

end MIPStarRE.LDT.Pasting
