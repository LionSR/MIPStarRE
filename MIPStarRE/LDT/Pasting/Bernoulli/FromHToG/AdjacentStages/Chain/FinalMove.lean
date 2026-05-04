import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.AdjacentStages.Chain.HalfSandwich

/-!
# Section 12 pasting: from-H-to-G final move-right chain

Definition for `M₄` and the final move-right rewrite lemmas
connecting `M₃ → M₄`.

The preceding half-sandwich chain `M₁ → M₂ → M₃` lives in `Chain.HalfSandwich`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- Pointwise rewrite of `M₃` to the left-action shape for the final move-right step. -/
lemma fromHToGAdjacentStageM3_pointwise_finalLeftShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
          leftTensor (ι₂ := ι) U) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_moveRight_final_left_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₄` to the right-action shape for the final move-right step. -/
lemma fromHToGAdjacentStageM4_pointwise_finalRightShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
          rightTensor (ι₁ := ι) U) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_moveRight_final_right_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- The paper endpoint intermediate `M₄`: the head completed-slice outcome has
moved to the right tensor factor. -/
noncomputable def fromHToGAdjacentStageM4
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) : Error :=
  let n := k - (ℓ + 1)
  ∑ b : Bool,
    ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U * U))

/-- Global rewrite of `M₃` to the left-action shape for the final move-right step. -/
lemma fromHToGAdjacentStageM3_eq_finalLeftShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM3 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
            leftTensor (ι₂ := ι) U) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM3
  simpa using
    (fromHToGAdjacentStage_globalize_pointwiseShape (params := params) (n := n)
      (source := fun b τ x xs =>
        ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
          ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
              gHatTupleType gs = τ,
            let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
            let U := (gHatIdxMeas params family x).outcome g
            let T := gHatHalfProductOutcomeOperator params family n xs gs
            ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
              rightTensor (ι₁ := ι) (S * U)))
      (target := fun x xs =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
            leftTensor (ι₂ := ι) U))
      (hpoint := fun x xs =>
        fromHToGAdjacentStageM3_pointwise_finalLeftShape params ψbi family ℓ n x xs))

/-- Global rewrite of `M₄` to the right-action shape for the final move-right step. -/
lemma fromHToGAdjacentStageM4_eq_finalRightShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM4 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
            rightTensor (ι₁ := ι) U) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM4
  simpa using
    (fromHToGAdjacentStage_globalize_pointwiseShape (params := params) (n := n)
      (source := fun b τ x xs =>
        ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
          ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
              gHatTupleType gs = τ,
            let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
            let U := (gHatIdxMeas params family x).outcome g
            let T := gHatHalfProductOutcomeOperator params family n xs gs
            ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
              rightTensor (ι₁ := ι) (S * U * U)))
      (target := fun x xs =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
            rightTensor (ι₁ := ι) U))
      (hpoint := fun x xs =>
        fromHToGAdjacentStageM4_pointwise_finalRightShape params ψbi family ℓ n x xs))

end MIPStarRE.LDT.Pasting
