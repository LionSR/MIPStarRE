import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.AdjacentStages.StageA0M1

/-!
# Section 12 pasting: from-H-to-G half-sandwich chain

Definitions for `M₂` and `M₃`, and the half-sandwich rewrite lemmas
connecting `M₁ → M₂ → M₃` via approximate commutation of the G-half sandwich.

The final move-right chain `M₃ → M₄` lives in `Chain.FinalMove`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- The paper's second adjacent-stage intermediate scalar `M₂`: after the first
half-sandwich commutation. -/
noncomputable def fromHToGAdjacentStageM2
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
              ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))

/-- The paper's third adjacent-stage intermediate scalar `M₃`: after the second
half-sandwich commutation. -/
noncomputable def fromHToGAdjacentStageM3
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
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                rightTensor (ι₁ := ι) (S * U))

/-- Pointwise rewrite of `M₁` to the half-sandwich source shape. -/
lemma fromHToGAdjacentStageM1_pointwise_halfSandwichLeftShape
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
          ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi (leftTensor (ι₂ := ι) (U * T) *
          (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_halfSandwich_left_context_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₂` to the half-sandwich target shape. -/
lemma fromHToGAdjacentStageM2_pointwise_halfSandwichRightShape
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
          ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi (leftTensor (ι₂ := ι) (T * U) *
          (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_halfSandwich_right_context_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₂` to the adjoint half-sandwich source shape. -/
lemma fromHToGAdjacentStageM2_pointwise_halfSandwichRightAdjointShape
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
          ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi (leftTensor (ι₂ := ι) T *
          (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_halfSandwich_adjoint_right_context_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₃` to the adjoint half-sandwich target shape. -/
lemma fromHToGAdjacentStageM3_pointwise_halfSandwichLeftAdjointShape
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
        ev ψbi (leftTensor (ι₂ := ι) T *
          (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_halfSandwich_adjoint_left_context_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₂` to the left-action adjoint half-sandwich shape. -/
lemma fromHToGAdjacentStageM2_pointwise_halfSandwichRightAdjointLeftActionShape
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
          ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
          leftTensor (ι₂ := ι) (U * Tᴴ)) := by
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U)))
        = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family x).outcome g
            let T := gHatHalfProductOutcomeOperator params family n xs gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))) :=
          fromHToGAdjacentStageM2_pointwise_halfSandwichRightAdjointShape
            params ψbi family ℓ n x xs
    _ = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
          leftTensor (ι₂ := ι) (U * Tᴴ)) := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          exact congrArg (ev ψbi)
            (fromHToG_halfSandwich_adjoint_right_leftAction_term
              ((gHatIdxMeas params family x).outcome g)
              (gHatHalfProductOutcomeOperator params family n xs gs)
              (fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₃` to the left-action adjoint half-sandwich shape. -/
lemma fromHToGAdjacentStageM3_pointwise_halfSandwichLeftAdjointLeftActionShape
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
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
          leftTensor (ι₂ := ι) (Tᴴ * U)) := by
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
            rightTensor (ι₁ := ι) (S * U)))
        = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family x).outcome g
            let T := gHatHalfProductOutcomeOperator params family n xs gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))) :=
          fromHToGAdjacentStageM3_pointwise_halfSandwichLeftAdjointShape
            params ψbi family ℓ n x xs
    _ = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
          leftTensor (ι₂ := ι) (Tᴴ * U)) := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          exact congrArg (ev ψbi)
            (fromHToG_halfSandwich_adjoint_left_leftAction_term
              ((gHatIdxMeas params family x).outcome g)
              (gHatHalfProductOutcomeOperator params family n xs gs)
              (fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Global rewrite of `M₁` to the half-sandwich source shape. -/
lemma fromHToGAdjacentStageM1_eq_halfSandwichLeftShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM1 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi (leftTensor (ι₂ := ι) (U * T) *
            (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM1
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                      rightTensor (ι₁ := ι) (S * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM1_pointwise_halfSandwichLeftShape
            params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) (U * T) *
              (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)))) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) (U * T) *
                  (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))).symm

/-- Global rewrite of `M₂` to the half-sandwich target shape. -/
lemma fromHToGAdjacentStageM2_eq_halfSandwichRightShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM2 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi (leftTensor (ι₂ := ι) (T * U) *
            (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM2
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                      rightTensor (ι₁ := ι) (S * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM2_pointwise_halfSandwichRightShape
            params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) (T * U) *
              (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)))) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) (T * U) *
                  (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))).symm

/-- Global rewrite of `M₂` to the adjoint half-sandwich source shape. -/
lemma fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM2 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi (leftTensor (ι₂ := ι) T *
            (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM2
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                      rightTensor (ι₁ := ι) (S * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) T *
                (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM2_pointwise_halfSandwichRightAdjointShape
            params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U)))) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) T *
                  (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))))).symm

/-- Global rewrite of `M₃` to the adjoint half-sandwich target shape. -/
lemma fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointShape
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
          ev ψbi (leftTensor (ι₂ := ι) T *
            (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM3
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                rightTensor (ι₁ := ι) (S * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                rightTensor (ι₁ := ι) (S * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                      rightTensor (ι₁ := ι) (S * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) T *
                (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM3_pointwise_halfSandwichLeftAdjointShape
            params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U)))) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) T *
                  (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))))).symm

/-- Global rewrite of `M₂` to the left-action adjoint half-sandwich source shape. -/
lemma fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointLeftActionShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM2 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            leftTensor (ι₂ := ι) (U * Tᴴ)) := by
  classical
  intro n
  calc
    fromHToGAdjacentStageM2 params ψbi family k ℓ =
        avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))) := by
          simpa [n] using
            fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointShape params ψbi family k ℓ
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) (U * Tᴴ)) := by
          refine avgOver_congr _ _ _ ?_
          intro q
          refine Finset.sum_congr rfl ?_
          intro g _hg
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          exact congrArg (ev ψbi)
            (fromHToG_halfSandwich_adjoint_right_leftAction_term
              ((gHatIdxMeas params family q.1).outcome g)
              (gHatHalfProductOutcomeOperator params family n q.2 gs)
              (fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Global rewrite of `M₃` to the left-action adjoint half-sandwich target shape. -/
lemma fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointLeftActionShape
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
          ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            leftTensor (ι₂ := ι) (Tᴴ * U)) := by
  classical
  intro n
  calc
    fromHToGAdjacentStageM3 params ψbi family k ℓ =
        avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))) := by
          simpa [n] using
            fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointShape params ψbi family k ℓ
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) (Tᴴ * U)) := by
          refine avgOver_congr _ _ _ ?_
          intro q
          refine Finset.sum_congr rfl ?_
          intro g _hg
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          exact congrArg (ev ψbi)
            (fromHToG_halfSandwich_adjoint_left_leftAction_term
              ((gHatIdxMeas params family q.1).outcome g)
              (gHatHalfProductOutcomeOperator params family n q.2 gs)
              (fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs)))).symm


end MIPStarRE.LDT.Pasting
