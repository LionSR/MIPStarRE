import MIPStarRE.LDT.Pasting.Simplified.WordCorrelation

/-!
# Random-word mirror energy

The two word normalizations and the correlation power identity yield the
exact averaged mirror-energy identity of the simplified pasting proof.

## References

- `blueprint/src/low_degree_simplified.tex`, equation `eq:random-word-energy`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugate transpose commutes with an operator average carrying real
distribution weights. -/
private theorem averageOperator_conjTranspose {α : Type*}
    (D : Distribution α) (A : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution D (fun a => (A a)ᴴ) =
      (averageOperatorOverDistribution D A)ᴴ := by
  unfold averageOperatorOverDistribution
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl ?_
  intro a _
  simp

/-- The sum of adjoint correlations is the adjoint of the word correlation. -/
private theorem matchingWordCorrelation_adjoint
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) (xs : PointTuple params k) :
    (∑ gs : GHatTupleOutcome params k,
      opTensor
        (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ
        (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ) =
      (matchingWordCorrelation params family k xs)ᴴ := by
  unfold matchingWordCorrelation
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun gs _ => (conjTranspose_opTensor _ _).symm

/-- Averaged squared mirror difference for length-`k` completed words. -/
noncomputable def randomWordMirrorEnergy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  averageOperatorOverDistribution (uniformDistribution (PointTuple params k))
    (fun xs => ∑ gs : GHatTupleOutcome params k,
      let W := gHatHalfProductOutcomeOperator params family k xs gs
      (wordMirrorDifference W)ᴴ * wordMirrorDifference W)

/-- The random-word energy is exactly `2(I - K^k)` as an operator identity. -/
theorem randomWordMirrorEnergy_eq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    randomWordMirrorEnergy params family k =
      (1 + 1 : MIPStarRE.Quantum.Op (ι × ι)) -
        (matchingOutcomeAverage params family ^ k +
          matchingOutcomeAverage params family ^ k) := by
  let D := uniformDistribution (PointTuple params k)
  let K := matchingOutcomeAverage params family
  have hfixed (xs : PointTuple params k) :
      (∑ gs : GHatTupleOutcome params k,
        let W := gHatHalfProductOutcomeOperator params family k xs gs
        (wordMirrorDifference W)ᴴ * wordMirrorDifference W) =
        (1 + 1 : MIPStarRE.Quantum.Op (ι × ι)) -
          (matchingWordCorrelation params family k xs +
            (matchingWordCorrelation params family k xs)ᴴ) := by
    rw [wordMirrorEnergy_eq_tensor_correlations
      (fun gs => gHatHalfProductOutcomeOperator params family k xs gs)
      (gHatHalfProduct_adjoint_square_sum_eq_one params family k xs)
      (gHatHalfProduct_square_adjoint_sum_eq_one params family k xs)]
    rw [matchingWordCorrelation_adjoint]
    rfl
  unfold randomWordMirrorEnergy
  rw [averageOperatorOverDistribution_congr D _ _ hfixed]
  simp only [averageOperatorOverDistribution, smul_sub, Finset.sum_sub_distrib]
  have hconst := averageOperatorOverDistribution_const_of_isProbability D
    (uniformDistribution_isProbability (PointTuple params k))
    (1 + 1 : MIPStarRE.Quantum.Op (ι × ι))
  simp only [averageOperatorOverDistribution] at hconst
  rw [hconst]
  simp only [smul_add, Finset.sum_add_distrib]
  have hadj :
      (∑ xs ∈ D.support, D.weight xs •
          (matchingWordCorrelation params family k xs)ᴴ) =
        (matchingWordCorrelationAverage params family k)ᴴ := by
    simpa [matchingWordCorrelationAverage, D,
      averageOperatorOverDistribution] using
      averageOperator_conjTranspose D (matchingWordCorrelation params family k)
  rw [hadj]
  change (1 + 1 : MIPStarRE.Quantum.Op (ι × ι)) -
      (matchingWordCorrelationAverage params family k +
        (matchingWordCorrelationAverage params family k)ᴴ) = _
  rw [matchingWordCorrelationAverage_eq_pow]
  have hK : Kᴴ = K :=
    (Matrix.nonneg_iff_posSemidef.mp
      (matchingOutcomeAverage_nonneg params family)).isHermitian.eq
  simp [K, Matrix.conjTranspose_pow, hK]

/-- Linear growth of the random-word mirror energy. -/
theorem randomWordMirrorEnergy_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    randomWordMirrorEnergy params family k ≤
      k • ((1 + 1 : MIPStarRE.Quantum.Op (ι × ι)) -
        (matchingOutcomeAverage params family +
          matchingOutcomeAverage params family)) := by
  rw [randomWordMirrorEnergy_eq]
  have h := matchingOutcomeAverage_power_bound params family k
  have htwo :
      (1 + 1 : MIPStarRE.Quantum.Op (ι × ι)) -
        (matchingOutcomeAverage params family ^ k +
          matchingOutcomeAverage params family ^ k) =
        (1 - matchingOutcomeAverage params family ^ k) +
          (1 - matchingOutcomeAverage params family ^ k) := by abel
  rw [htwo]
  calc
    (1 - matchingOutcomeAverage params family ^ k) +
        (1 - matchingOutcomeAverage params family ^ k) ≤
      k • (1 - matchingOutcomeAverage params family) +
        k • (1 - matchingOutcomeAverage params family) := add_le_add h h
    _ = k • ((1 + 1 : MIPStarRE.Quantum.Op (ι × ι)) -
          (matchingOutcomeAverage params family +
            matchingOutcomeAverage params family)) := by
            simp only [smul_sub, smul_add]
            abel

/-- The one-step matching mirror energy is the completed-slice squared
distance already present in the LDT interface. -/
theorem ev_matchingMirrorEnergyAverage_eq_sddError
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι)) :
    ev ψ (matchingMirrorEnergyAverage params family) =
      sddError ψ (uniformDistribution (Fq params))
        (gHatSelfConsistencyLeftFamily params family)
        (gHatSelfConsistencyRightFamily params family) := by
  unfold matchingMirrorEnergyAverage sddError
  rw [ev_averageOperatorOverDistribution]
  apply avgOver_congr
  intro x
  rw [ev_finset_sum]
  unfold qSDD qSDDCore
  refine Finset.sum_congr rfl ?_
  intro a _
  let P := (gHatIdxMeas params family x).outcome a
  have hP : Pᴴ = P := by
    exact (gHatIdxMeas params family x).toSubMeas.outcome_hermitian a
  have hM :
      (leftTensor (ι₂ := ι) P - rightTensor (ι₁ := ι) P)ᴴ =
        leftTensor (ι₂ := ι) P - rightTensor (ι₁ := ι) P := by
    simp [Matrix.conjTranspose_sub, leftTensor_conjTranspose,
      rightTensor_conjTranspose, hP]
  simp [gHatSelfConsistencyLeftFamily, gHatSelfConsistencyRightFamily,
    leftPlacedSubMeas, rightPlacedSubMeas, P, hM]

/-- Completed-slice self-consistency bounds every random-word mirror error
linearly in its length. -/
theorem ev_randomWordMirrorEnergy_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι))
    (zeta : Error) (k : ℕ)
    (hsc : SDDRel ψ (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    ev ψ (randomWordMirrorEnergy params family k) ≤
      (k : Error) * (2 * zeta) := by
  have hop : randomWordMirrorEnergy params family k ≤
      k • matchingMirrorEnergyAverage params family := by
    simpa only [matchingMirrorEnergyAverage_eq] using
      randomWordMirrorEnergy_le params family k
  have hstep : ev ψ (matchingMirrorEnergyAverage params family) ≤ 2 * zeta := by
    rw [ev_matchingMirrorEnergyAverage_eq_sddError]
    exact hsc.squaredDistanceBound
  calc
    ev ψ (randomWordMirrorEnergy params family k) ≤
        ev ψ (k • matchingMirrorEnergyAverage params family) := ev_mono ψ _ _ hop
    _ = (k : Error) * ev ψ (matchingMirrorEnergyAverage params family) := by
          rw [← Nat.cast_smul_eq_nsmul Error k
            (matchingMirrorEnergyAverage params family)]
          exact ev_real_smul ψ (k : Error)
            (matchingMirrorEnergyAverage params family)
    _ ≤ (k : Error) * (2 * zeta) := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)

end MIPStarRE.LDT.Pasting
