import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.MoveLemmas

/-!
# Section 12 pasting: from-H-to-G adjacent-stage scalars

Definitions for the adjacent paper chain `M₁ → M₂ → M₃ → M₄` and the exact
rewrites connecting its endpoints to the Lean stage masses.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def fromHToGAdjacentStageA0
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
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                rightTensor (ι₁ := ι) S)

/-- A nonterminal Lean stage is exactly the paper's adjacent-stage source scalar. -/
lemma fromHToGStageMass_eq_adjacentStageA0
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    {k ℓ : ℕ} (hℓ : ℓ < k) :
    fromHToGStageMass params ψbi family k ℓ =
      fromHToGAdjacentStageA0 params ψbi family k ℓ := by
  classical
  let n := k - (ℓ + 1)
  calc
    fromHToGStageMass params ψbi family k ℓ
        = ∑ p : Bool × GHatType n,
            fromHToGTailStageMass params ψbi family ℓ (prependTypeBit p.1 p.2) := by
            simpa [n] using fromHToGStageMass_split_succ params ψbi family hℓ
    _ = ∑ b : Bool, ∑ τ : GHatType n,
          fromHToGTailStageMass params ψbi family ℓ (prependTypeBit b τ) := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ b : Bool, ∑ τ : GHatType n,
          avgOver (uniformDistribution (Fq params)) fun x =>
            avgOver (uniformDistribution (PointTuple params n)) fun xs =>
              ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                    gHatTupleType gs = τ,
                  let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                  let U := (gHatIdxMeas params family x).outcome g
                  let T := gHatHalfProductOutcomeOperator params family n xs gs
                  ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                    rightTensor (ι₁ := ι) S) := by
          refine Finset.sum_congr rfl ?_
          intro b _hb
          refine Finset.sum_congr rfl ?_
          intro τ _hτ
          exact fromHToGTailStageMass_cons_eq_adjacentStageA0_branch
            params ψbi family ℓ n b τ
    _ = fromHToGAdjacentStageA0 params ψbi family k ℓ := by
          unfold fromHToGAdjacentStageA0
          change (∑ b : Bool, ∑ τ : GHatType n, _) =
            (let n := k - (ℓ + 1); ∑ b : Bool, ∑ τ : GHatType n, _)
          rfl

/-- The paper's first adjacent-stage intermediate scalar `M₁`: the head
completed-slice outcome has been moved to the right tensor factor. -/
noncomputable def fromHToGAdjacentStageM1
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
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))

/-- Algebra for the left-action term in the first move-right estimate. -/
lemma fromHToG_moveRight_left_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
        leftTensor (ι₂ := ι) U =
      leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S := by
  calc
    (leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
        leftTensor (ι₂ := ι) U
        = leftTensor (ι₂ := ι) (U * T * Tᴴ) *
            (rightTensor (ι₁ := ι) S * leftTensor (ι₂ := ι) U) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) (U * T * Tᴴ) *
          (leftTensor (ι₂ := ι) U * rightTensor (ι₁ := ι) S) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
    _ = (leftTensor (ι₂ := ι) (U * T * Tᴴ) * leftTensor (ι₂ := ι) U) *
          rightTensor (ι₁ := ι) S := by
          rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) ((U * T * Tᴴ) * U) * rightTensor (ι₁ := ι) S := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S := by
          rw [mul_assoc]

/-- Algebra for the right-action term in the first move-right estimate. -/
lemma fromHToG_moveRight_right_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
        rightTensor (ι₁ := ι) U =
      leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    (leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
        rightTensor (ι₁ := ι) U
        = leftTensor (ι₂ := ι) (U * T * Tᴴ) *
            (rightTensor (ι₁ := ι) S * rightTensor (ι₁ := ι) U) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [rightTensor_mul_rightTensor]

/-- Algebra for the left-action term in the final move-right estimate. -/
lemma fromHToG_moveRight_final_left_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) U =
      leftTensor (ι₂ := ι) (T * Tᴴ * U) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) U
        = leftTensor (ι₂ := ι) (T * Tᴴ) *
            (rightTensor (ι₁ := ι) (S * U) * leftTensor (ι₂ := ι) U) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) (T * Tᴴ) *
          (leftTensor (ι₂ := ι) U * rightTensor (ι₁ := ι) (S * U)) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
    _ = (leftTensor (ι₂ := ι) (T * Tᴴ) * leftTensor (ι₂ := ι) U) *
          rightTensor (ι₁ := ι) (S * U) := by
          rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) ((T * Tᴴ) * U) * rightTensor (ι₁ := ι) (S * U) := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (T * Tᴴ * U) * rightTensor (ι₁ := ι) (S * U) := by
          rw [mul_assoc]

/-- Algebra for the right-action term in the final move-right estimate. -/
lemma fromHToG_moveRight_final_right_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
        rightTensor (ι₁ := ι) U =
      leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U * U) := by
  calc
    (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
        rightTensor (ι₁ := ι) U
        = leftTensor (ι₂ := ι) (T * Tᴴ) *
            (rightTensor (ι₁ := ι) (S * U) * rightTensor (ι₁ := ι) U) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) ((S * U) * U) := by
          rw [rightTensor_mul_rightTensor]
    _ = leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U * U) := by
          rw [mul_assoc]

/-- Algebra for the `M₁` half-sandwich commutation source term. -/
lemma fromHToG_halfSandwich_left_context_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) (U * T) *
        (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)) =
      leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    leftTensor (ι₂ := ι) (U * T) *
        (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))
        = (leftTensor (ι₂ := ι) (U * T) * leftTensor (ι₂ := ι) Tᴴ) *
            rightTensor (ι₁ := ι) (S * U) := by
            rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) ((U * T) * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [mul_assoc]

/-- Algebra for the `M₂` half-sandwich commutation target term. -/
lemma fromHToG_halfSandwich_right_context_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) (T * U) *
        (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)) =
      leftTensor (ι₂ := ι) (T * U * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    leftTensor (ι₂ := ι) (T * U) *
        (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))
        = (leftTensor (ι₂ := ι) (T * U) * leftTensor (ι₂ := ι) Tᴴ) *
            rightTensor (ι₁ := ι) (S * U) := by
            rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) ((T * U) * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (T * U * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [mul_assoc]

/-- Algebra for the `M₂` adjoint half-sandwich commutation source term. -/
lemma fromHToG_halfSandwich_adjoint_right_context_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) =
      leftTensor (ι₂ := ι) (T * U * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))
        = (leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) (U * Tᴴ)) *
            rightTensor (ι₁ := ι) (S * U) := by
            rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) (T * (U * Tᴴ)) * rightTensor (ι₁ := ι) (S * U) := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (T * U * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [mul_assoc]

/-- Algebra for the `M₃` adjoint half-sandwich commutation target term. -/
lemma fromHToG_halfSandwich_adjoint_left_context_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U)) =
      leftTensor (ι₂ := ι) (T * Tᴴ * U) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))
        = (leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) (Tᴴ * U)) *
            rightTensor (ι₁ := ι) (S * U) := by
            rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) (T * (Tᴴ * U)) * rightTensor (ι₁ := ι) (S * U) := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (T * Tᴴ * U) * rightTensor (ι₁ := ι) (S * U) := by
          rw [mul_assoc]

/-- Normalize the `M₂` adjoint half-sandwich source to `C * A` form. -/
lemma fromHToG_halfSandwich_adjoint_right_leftAction_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) (U * Tᴴ) =
      leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) := by
  calc
    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) (U * Tᴴ)
        = leftTensor (ι₂ := ι) T *
            (rightTensor (ι₁ := ι) (S * U) * leftTensor (ι₂ := ι) (U * Tᴴ)) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) T *
          (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]

/-- Normalize the `M₃` adjoint half-sandwich target to `C * B` form. -/
lemma fromHToG_halfSandwich_adjoint_left_leftAction_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) (Tᴴ * U) =
      leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U)) := by
  calc
    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) (Tᴴ * U)
        = leftTensor (ι₂ := ι) T *
            (rightTensor (ι₁ := ι) (S * U) * leftTensor (ι₂ := ι) (Tᴴ * U)) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) T *
          (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U)) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]

/-- Pointwise rewrite of `A0` to the left-action shape used by `closenessOfIP`. -/
lemma fromHToGAdjacentStageA0_pointwise_leftShape
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
          ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
            rightTensor (ι₁ := ι) S)) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
          leftTensor (ι₂ := ι) U) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_moveRight_left_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₁` to the right-action shape used by `closenessOfIP`. -/
lemma fromHToGAdjacentStageM1_pointwise_rightShape
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
        ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
          rightTensor (ι₁ := ι) U) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_moveRight_right_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Global rewrite of `A0` to the left-action shape used by `closenessOfIP`. -/
lemma fromHToGAdjacentStageA0_eq_leftShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageA0 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
            leftTensor (ι₂ := ι) U) := by
  classical
  intro n
  unfold fromHToGAdjacentStageA0
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                rightTensor (ι₁ := ι) S)) = _
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
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                rightTensor (ι₁ := ι) S))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                      rightTensor (ι₁ := ι) S))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
                leftTensor (ι₂ := ι) U))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageA0_pointwise_leftShape params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
              leftTensor (ι₂ := ι) U)) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
                  leftTensor (ι₂ := ι) U))).symm

/-- Global rewrite of `M₁` to the right-action shape used by `closenessOfIP`. -/
lemma fromHToGAdjacentStageM1_eq_rightShape
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
          ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
            rightTensor (ι₁ := ι) U) := by
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
              ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
                rightTensor (ι₁ := ι) U))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM1_pointwise_rightShape params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
              rightTensor (ι₁ := ι) U)) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
                  rightTensor (ι₁ := ι) U))).symm

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
              ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
                leftTensor (ι₂ := ι) U))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM3_pointwise_finalLeftShape params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) U)) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
                  leftTensor (ι₂ := ι) U))).symm

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
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U * U))) = _
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
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                      rightTensor (ι₁ := ι) (S * U * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
                rightTensor (ι₁ := ι) U))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM4_pointwise_finalRightShape params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
              rightTensor (ι₁ := ι) U)) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
                  rightTensor (ι₁ := ι) U))).symm

end MIPStarRE.LDT.Pasting
