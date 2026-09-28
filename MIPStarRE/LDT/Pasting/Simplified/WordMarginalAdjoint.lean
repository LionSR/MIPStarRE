import MIPStarRE.LDT.Pasting.Simplified.WordMarginal

/-!
# Marginal stability for adjoint completed words

The success probability of a later slice is a sandwich by the adjoint of
the preceding completed word. Both word normalizations give the same mirror
energy estimate for this orientation, so the marginal-stability bound applies
directly to the sequential success count.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `lem:sequential-bot-marginal` and `lem:first-success-completeness`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The adjoint completed word on the first register. -/
noncomputable def completedWordLeftAdjoint
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι)
    (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ

/-- The unadjointed completed word on the second register. -/
noncomputable def completedWordRightAdjoint
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  rightTensor (ι₁ := ι)
    (gHatHalfProductOutcomeOperator params family k xs gs)

/-- Adjoint words on the first register have unit averaged norm. -/
theorem completedWordLeftAdjoint_norm_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized) :
    averagedOperatorNormSq ψ (uniformDistribution (PointTuple params k))
      (completedWordLeftAdjoint params family k) = 1 := by
  have hpoint (xs : PointTuple params k) :
      (∑ gs : GHatTupleOutcome params k,
        (completedWordLeftAdjoint params family k xs gs)ᴴ *
          completedWordLeftAdjoint params family k xs gs) = 1 := by
    calc
      (∑ gs : GHatTupleOutcome params k,
        (completedWordLeftAdjoint params family k xs gs)ᴴ *
          completedWordLeftAdjoint params family k xs gs) =
        ∑ gs : GHatTupleOutcome params k,
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family k xs gs *
              (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ) := by
            apply Finset.sum_congr rfl
            intro gs _
            simp only [completedWordLeftAdjoint, leftTensor_conjTranspose,
              Matrix.conjTranspose_conjTranspose]
            exact leftTensor_mul_leftTensor _ _
      _ = leftTensor (ι₂ := ι)
          (∑ gs : GHatTupleOutcome params k,
            gHatHalfProductOutcomeOperator params family k xs gs *
              (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ) := by
            exact leftTensor_finset_sum _ _
      _ = 1 := by
        rw [gHatHalfProduct_square_adjoint_sum_eq_one params family k xs]
        exact leftTensor_one
  unfold averagedOperatorNormSq
  apply Eq.trans (avgOver_congr _ _ _ (fun xs => by
    rw [← ev_finset_sum, hpoint xs]))
  rw [avgOver_const_of_isProbability _
    (uniformDistribution_isProbability (PointTuple params k))]
  exact ev_one_of_isNormalized ψ hψ

/-- Unadjointed words on the second register have unit averaged norm. -/
theorem completedWordRightAdjoint_norm_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized) :
    averagedOperatorNormSq ψ (uniformDistribution (PointTuple params k))
      (completedWordRightAdjoint params family k) = 1 := by
  have hpoint (xs : PointTuple params k) :
      (∑ gs : GHatTupleOutcome params k,
        (completedWordRightAdjoint params family k xs gs)ᴴ *
          completedWordRightAdjoint params family k xs gs) = 1 := by
    calc
      (∑ gs : GHatTupleOutcome params k,
        (completedWordRightAdjoint params family k xs gs)ᴴ *
          completedWordRightAdjoint params family k xs gs) =
        ∑ gs : GHatTupleOutcome params k,
          rightTensor (ι₁ := ι)
            ((gHatHalfProductOutcomeOperator params family k xs gs)ᴴ *
              gHatHalfProductOutcomeOperator params family k xs gs) := by
            apply Finset.sum_congr rfl
            intro gs _
            simp only [completedWordRightAdjoint, rightTensor_conjTranspose]
            exact rightTensor_mul_rightTensor _ _
      _ = rightTensor (ι₁ := ι)
          (∑ gs : GHatTupleOutcome params k,
            (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ *
              gHatHalfProductOutcomeOperator params family k xs gs) := by
            exact rightTensor_finset_sum _ _
      _ = 1 := by
        rw [gHatHalfProduct_adjoint_square_sum_eq_one params family k xs]
        exact rightTensor_one
  unfold averagedOperatorNormSq
  apply Eq.trans (avgOver_congr _ _ _ (fun xs => by
    rw [← ev_finset_sum, hpoint xs]))
  rw [avgOver_const_of_isProbability _
    (uniformDistribution_isProbability (PointTuple params k))]
  exact ev_one_of_isNormalized ψ hψ

/-- Adjoint word placement has the same average squared distance as the
original mirror placement. -/
theorem completedWordAdjoint_distance_eq_energy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) :
    averagedOperatorNormSq ψ (uniformDistribution (PointTuple params k))
      (fun xs gs => completedWordLeftAdjoint params family k xs gs -
        completedWordRightAdjoint params family k xs gs) =
      ev ψ (randomWordMirrorEnergy params family k) := by
  rw [← completedWord_distance_eq_energy params family k ψ]
  unfold averagedOperatorNormSq
  apply avgOver_congr
  intro xs
  rw [← ev_finset_sum, ← ev_finset_sum]
  congr 1
  simpa [completedWordLeftAdjoint, completedWordRightAdjoint,
    completedWordLeft, completedWordRight, wordMirrorDifference] using
    wordMirrorEnergy_adjoint_eq
      (fun gs : GHatTupleOutcome params k =>
        gHatHalfProductOutcomeOperator params family k xs gs)
      (gHatHalfProduct_adjoint_square_sum_eq_one params family k xs)
      (gHatHalfProduct_square_adjoint_sum_eq_one params family k xs)

/-- A second-register completed word leaves a first-register effect's
expectation unchanged after summing its outcomes. -/
theorem completedWordRightAdjoint_leftEffect_mass
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (M : MIPStarRE.Quantum.Op ι) :
    averagedSandwichMass ψ (uniformDistribution (PointTuple params k))
      (leftTensor (ι₂ := ι) M) (completedWordRightAdjoint params family k) =
        ev ψ (leftTensor (ι₂ := ι) M) := by
  have hpoint (xs : PointTuple params k) :
      (∑ gs : GHatTupleOutcome params k,
        (completedWordRightAdjoint params family k xs gs)ᴴ *
          leftTensor (ι₂ := ι) M *
            completedWordRightAdjoint params family k xs gs) =
        leftTensor (ι₂ := ι) M := by
    have hterm (gs : GHatTupleOutcome params k) :
        (completedWordRightAdjoint params family k xs gs)ᴴ *
            leftTensor (ι₂ := ι) M *
              completedWordRightAdjoint params family k xs gs =
          leftTensor (ι₂ := ι) M *
            rightTensor (ι₁ := ι)
              ((gHatHalfProductOutcomeOperator params family k xs gs)ᴴ *
                gHatHalfProductOutcomeOperator params family k xs gs) := by
      let W := gHatHalfProductOutcomeOperator params family k xs gs
      have hcomm :
          rightTensor (ι₁ := ι) Wᴴ * leftTensor (ι₂ := ι) M =
            leftTensor (ι₂ := ι) M * rightTensor (ι₁ := ι) Wᴴ := by
        rw [rightTensor_mul_leftTensor_eq_opTensor,
          leftTensor_mul_rightTensor_eq_opTensor]
      simp only [completedWordRightAdjoint, rightTensor_conjTranspose]
      rw [hcomm, mul_assoc]
      exact congrArg (leftTensor (ι₂ := ι) M * ·)
        (rightTensor_mul_rightTensor Wᴴ W)
    calc
      (∑ gs : GHatTupleOutcome params k,
        (completedWordRightAdjoint params family k xs gs)ᴴ *
          leftTensor (ι₂ := ι) M *
            completedWordRightAdjoint params family k xs gs) =
        ∑ gs : GHatTupleOutcome params k,
          leftTensor (ι₂ := ι) M *
            rightTensor (ι₁ := ι)
              ((gHatHalfProductOutcomeOperator params family k xs gs)ᴴ *
                gHatHalfProductOutcomeOperator params family k xs gs) := by
            exact Finset.sum_congr rfl fun gs _ => hterm gs
      _ = leftTensor (ι₂ := ι) M *
          rightTensor (ι₁ := ι)
            (∑ gs : GHatTupleOutcome params k,
              (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ *
                gHatHalfProductOutcomeOperator params family k xs gs) := by
            rw [← rightTensor_finset_sum, Finset.mul_sum]
      _ = leftTensor (ι₂ := ι) M := by
        rw [gHatHalfProduct_adjoint_square_sum_eq_one params family k xs]
        simp [rightTensor_one]
  unfold averagedSandwichMass
  apply Eq.trans (avgOver_congr _ _ _ (fun xs => by
    rw [← ev_finset_sum, hpoint xs]))
  exact avgOver_const_of_isProbability _
    (uniformDistribution_isProbability (PointTuple params k)) _

/-- The adjoint completed word changes the expectation of a first-register
effect by at most the linear mirror-energy square root. -/
theorem completedWordAdjoint_leftEffect_marginal_stability
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (M : MIPStarRE.Quantum.Op ι) (hM : 0 ≤ M) (hMle : M ≤ 1)
    (zeta : Error)
    (hsc : SDDRel ψ (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    |averagedSandwichMass ψ (uniformDistribution (PointTuple params k))
        (leftTensor (ι₂ := ι) M) (completedWordLeftAdjoint params family k) -
      ev ψ (leftTensor (ι₂ := ι) M)| ≤
        Real.sqrt ((k : Error) * (2 * zeta)) := by
  have hgap := averagedSandwichMass_gap_le_sqrt ψ
    (uniformDistribution (PointTuple params k))
    (leftTensor (ι₂ := ι) M) (leftTensor_nonneg hM) (leftTensor_le_one hMle)
    (completedWordLeftAdjoint params family k)
    (completedWordRightAdjoint params family k)
    (completedWordLeftAdjoint_norm_one params family k ψ hψ)
    (completedWordRightAdjoint_norm_one params family k ψ hψ)
  rw [completedWordRightAdjoint_leftEffect_mass,
    completedWordAdjoint_distance_eq_energy] at hgap
  exact hgap.trans (Real.sqrt_le_sqrt
    (ev_randomWordMirrorEnergy_le params family ψ zeta k hsc))

end MIPStarRE.LDT.Pasting
