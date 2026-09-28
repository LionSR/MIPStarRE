import MIPStarRE.LDT.Pasting.Simplified.MarginalStability

/-!
# Marginal stability of completed measurement words

The two tensor placements of a completed word each form a normalized
operator family. Their squared distance is the random-word mirror energy,
so the general effect-stability inequality applies without a loss in the
number of word outcomes.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `lem:sequential-bot-marginal`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A completed word acting on the first register. -/
noncomputable def completedWordLeft
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι) (gHatHalfProductOutcomeOperator params family k xs gs)

/-- The adjoint completed word acting on the second register. -/
noncomputable def completedWordRight
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  rightTensor (ι₁ := ι)
    (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ

/-- Both placed word families have unit state-dependent norm after averaging
uniform question tuples. -/
theorem completedWordLeft_norm_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized) :
    averagedOperatorNormSq ψ (uniformDistribution (PointTuple params k))
      (completedWordLeft params family k) = 1 := by
  have hpoint (xs : PointTuple params k) :
      (∑ gs : GHatTupleOutcome params k,
        (completedWordLeft params family k xs gs)ᴴ *
          completedWordLeft params family k xs gs) = 1 := by
    calc
      (∑ gs : GHatTupleOutcome params k,
        (completedWordLeft params family k xs gs)ᴴ *
          completedWordLeft params family k xs gs) =
        ∑ gs : GHatTupleOutcome params k,
          leftTensor (ι₂ := ι)
            ((gHatHalfProductOutcomeOperator params family k xs gs)ᴴ *
              gHatHalfProductOutcomeOperator params family k xs gs) := by
            refine Finset.sum_congr rfl ?_
            intro gs _
            simp only [completedWordLeft, leftTensor_conjTranspose]
            exact leftTensor_mul_leftTensor _ _
      _ = leftTensor (ι₂ := ι)
          (∑ gs : GHatTupleOutcome params k,
            (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ *
              gHatHalfProductOutcomeOperator params family k xs gs) := by
            exact leftTensor_finset_sum _ _
      _ = 1 := by
        rw [gHatHalfProduct_adjoint_square_sum_eq_one params family k xs]
        exact leftTensor_one
  unfold averagedOperatorNormSq
  apply Eq.trans (avgOver_congr _ _ _ (fun xs => by
    rw [← ev_finset_sum, hpoint xs]))
  rw [avgOver_const_of_isProbability _
    (uniformDistribution_isProbability (PointTuple params k))]
  exact ev_one_of_isNormalized ψ hψ

/-- Unit norm of the adjoint words on the second register. -/
theorem completedWordRight_norm_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized) :
    averagedOperatorNormSq ψ (uniformDistribution (PointTuple params k))
      (completedWordRight params family k) = 1 := by
  have hpoint (xs : PointTuple params k) :
      (∑ gs : GHatTupleOutcome params k,
        (completedWordRight params family k xs gs)ᴴ *
          completedWordRight params family k xs gs) = 1 := by
    calc
      (∑ gs : GHatTupleOutcome params k,
        (completedWordRight params family k xs gs)ᴴ *
          completedWordRight params family k xs gs) =
        ∑ gs : GHatTupleOutcome params k,
          rightTensor (ι₁ := ι)
            (gHatHalfProductOutcomeOperator params family k xs gs *
              (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ) := by
            refine Finset.sum_congr rfl ?_
            intro gs _
            simp only [completedWordRight, rightTensor_conjTranspose,
              Matrix.conjTranspose_conjTranspose]
            exact rightTensor_mul_rightTensor _ _
      _ = rightTensor (ι₁ := ι)
          (∑ gs : GHatTupleOutcome params k,
            gHatHalfProductOutcomeOperator params family k xs gs *
              (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ) := by
            exact rightTensor_finset_sum _ _
      _ = 1 := by
        rw [gHatHalfProduct_square_adjoint_sum_eq_one params family k xs]
        exact rightTensor_one
  unfold averagedOperatorNormSq
  apply Eq.trans (avgOver_congr _ _ _ (fun xs => by
    rw [← ev_finset_sum, hpoint xs]))
  rw [avgOver_const_of_isProbability _
    (uniformDistribution_isProbability (PointTuple params k))]
  exact ev_one_of_isNormalized ψ hψ

/-- The family squared distance is the random-word mirror energy. -/
theorem completedWord_distance_eq_energy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) :
    averagedOperatorNormSq ψ (uniformDistribution (PointTuple params k))
      (fun xs gs => completedWordLeft params family k xs gs -
        completedWordRight params family k xs gs) =
      ev ψ (randomWordMirrorEnergy params family k) := by
  unfold randomWordMirrorEnergy
  rw [ev_averageOperatorOverDistribution]
  unfold averagedOperatorNormSq
  apply avgOver_congr
  intro xs
  rw [ev_finset_sum]
  rfl

/-- Any effect sees at most the square root of the random-word mirror energy
when the completed word is moved between the two registers. -/
theorem completedWord_effect_gap_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (M : MIPStarRE.Quantum.Op (ι × ι))
    (hM : 0 ≤ M) (hMle : M ≤ 1) :
    |averagedSandwichMass ψ (uniformDistribution (PointTuple params k)) M
        (completedWordLeft params family k) -
      averagedSandwichMass ψ (uniformDistribution (PointTuple params k)) M
        (completedWordRight params family k)| ≤
      Real.sqrt (ev ψ (randomWordMirrorEnergy params family k)) := by
  have h := averagedSandwichMass_gap_le_sqrt ψ
    (uniformDistribution (PointTuple params k)) M hM hMle
    (completedWordLeft params family k) (completedWordRight params family k)
    (completedWordLeft_norm_one params family k ψ hψ)
    (completedWordRight_norm_one params family k ψ hψ)
  rwa [completedWord_distance_eq_energy] at h

/-- A word on the second register leaves the expectation of a first-register
effect unchanged after its outcomes are summed. -/
theorem completedWordRight_leftEffect_mass
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) (M : MIPStarRE.Quantum.Op ι) :
    averagedSandwichMass ψ (uniformDistribution (PointTuple params k))
      (leftTensor (ι₂ := ι) M) (completedWordRight params family k) =
        ev ψ (leftTensor (ι₂ := ι) M) := by
  have hpoint (xs : PointTuple params k) :
      (∑ gs : GHatTupleOutcome params k,
        (completedWordRight params family k xs gs)ᴴ *
          leftTensor (ι₂ := ι) M *
            completedWordRight params family k xs gs) =
        leftTensor (ι₂ := ι) M := by
    have hterm (gs : GHatTupleOutcome params k) :
        (completedWordRight params family k xs gs)ᴴ *
            leftTensor (ι₂ := ι) M *
              completedWordRight params family k xs gs =
          leftTensor (ι₂ := ι) M *
            rightTensor (ι₁ := ι)
              (gHatHalfProductOutcomeOperator params family k xs gs *
                (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ) := by
      let W := gHatHalfProductOutcomeOperator params family k xs gs
      have hcomm :
          rightTensor (ι₁ := ι) W * leftTensor (ι₂ := ι) M =
            leftTensor (ι₂ := ι) M * rightTensor (ι₁ := ι) W := by
        rw [rightTensor_mul_leftTensor_eq_opTensor,
          leftTensor_mul_rightTensor_eq_opTensor]
      simp only [completedWordRight, rightTensor_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      rw [hcomm, mul_assoc]
      exact congrArg (leftTensor (ι₂ := ι) M * ·)
        (rightTensor_mul_rightTensor W Wᴴ)
    calc
      (∑ gs : GHatTupleOutcome params k,
        (completedWordRight params family k xs gs)ᴴ *
          leftTensor (ι₂ := ι) M *
            completedWordRight params family k xs gs) =
          ∑ gs : GHatTupleOutcome params k,
            leftTensor (ι₂ := ι) M *
              rightTensor (ι₁ := ι)
                (gHatHalfProductOutcomeOperator params family k xs gs *
                  (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ) := by
            exact Finset.sum_congr rfl fun gs _ => hterm gs
      _ = leftTensor (ι₂ := ι) M *
          rightTensor (ι₁ := ι)
            (∑ gs : GHatTupleOutcome params k,
              gHatHalfProductOutcomeOperator params family k xs gs *
                (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ) := by
            rw [← rightTensor_finset_sum, Finset.mul_sum]
      _ = leftTensor (ι₂ := ι) M := by
        rw [gHatHalfProduct_square_adjoint_sum_eq_one params family k xs]
        simp [rightTensor_one]
  unfold averagedSandwichMass
  apply Eq.trans (avgOver_congr _ _ _ (fun xs => by
    rw [← ev_finset_sum, hpoint xs]))
  exact avgOver_const_of_isProbability _
    (uniformDistribution_isProbability (PointTuple params k)) _

/-- The expectation of a first-register effect after a random completed word
changes by at most the square root of the linear mirror-energy budget. -/
theorem completedWord_leftEffect_marginal_stability
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
        (leftTensor (ι₂ := ι) M) (completedWordLeft params family k) -
      ev ψ (leftTensor (ι₂ := ι) M)| ≤
        Real.sqrt ((k : Error) * (2 * zeta)) := by
  have hgap := completedWord_effect_gap_le params family k ψ hψ
    (leftTensor (ι₂ := ι) M)
    (leftTensor_nonneg hM) (leftTensor_le_one hMle)
  rw [completedWordRight_leftEffect_mass] at hgap
  exact hgap.trans (Real.sqrt_le_sqrt
    (ev_randomWordMirrorEnergy_le params family ψ zeta k hsc))

end MIPStarRE.LDT.Pasting
