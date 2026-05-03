import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.AdjacentStages

/-!
# Section 12 pasting: from-H-to-G S U S context-average bounds

Sandwich-sum identities and the `S U S` context-average bound used in the
second half-sandwich and final move-right Cauchy--Schwarz steps.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The total mass of the tail sandwich family is the identity. -/
lemma fromHToG_gHatSandwichFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (xs : PointTuple params n) :
    (gHatSandwichFamily params family n xs).total = 1 := by
  simp [gHatSandwichFamily, gHatHalfProductTotalOperator_eq_one]

/-- The tail sandwich outcomes sum to the identity. -/
lemma fromHToG_gHatSandwichFamily_sum_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (xs : PointTuple params n) :
    (∑ gs : GHatTupleOutcome params n,
      (gHatSandwichFamily params family n xs).outcome gs) = 1 := by
  rw [(gHatSandwichFamily params family n xs).sum_eq_total]
  exact fromHToG_gHatSandwichFamily_total_eq_one params family n xs

/-- The total operator of a fixed-type averaged tail sandwich. -/
noncomputable def fromHToGAveragedSandwichByTypeTotal
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (τ : GHatType n) :
    MIPStarRE.Quantum.Op ι :=
  (averagedSandwichByTypeSubMeas params family n τ).total

/-- Expectation-level branch sum with an `S · U · S` sandwich. -/
lemma fromHToG_ev_sum_isSome_sandwich_weight
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (x : Fq params)
    (b : Bool) (A S : MIPStarRE.Quantum.Op ι) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ev ψbi (leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * (gHatIdxMeas params family x).outcome g * S))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι)
          (S * (if b then (completePartSubMeas params family x).total
            else (incompletePartSubMeas params family x).total) * S)) := by
  classical
  rw [← ev_finset_sum]
  congr 1
  cases b
  · calc
      (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
          leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              (S * (gHatIdxMeas params family x).outcome g * S))
        = leftTensor (ι₂ := ι) A *
            (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
              rightTensor (ι₁ := ι)
                (S * (gHatIdxMeas params family x).outcome g * S)) := by
            rw [Finset.mul_sum]
      _ = leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
                S * (gHatIdxMeas params family x).outcome g * S) := by
            rw [rightTensor_finset_sum]
      _ = leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              ((∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
                  S * (gHatIdxMeas params family x).outcome g) * S) := by
            rw [Finset.sum_mul]
      _ = leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              (S * (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
                  (gHatIdxMeas params family x).outcome g) * S) := by
            rw [Finset.mul_sum]
      _ = leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              (S * (incompletePartSubMeas params family x).total * S) := by
            rw [fromHToG_gHatIdxMeas_sum_isSome_false]
      _ = leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              (S * (if false then (completePartSubMeas params family x).total
                else (incompletePartSubMeas params family x).total) * S) := by simp
  · calc
      (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
          leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              (S * (gHatIdxMeas params family x).outcome g * S))
        = leftTensor (ι₂ := ι) A *
            (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
              rightTensor (ι₁ := ι)
                (S * (gHatIdxMeas params family x).outcome g * S)) := by
            rw [Finset.mul_sum]
      _ = leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
                S * (gHatIdxMeas params family x).outcome g * S) := by
            rw [rightTensor_finset_sum]
      _ = leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              ((∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
                  S * (gHatIdxMeas params family x).outcome g) * S) := by
            rw [Finset.sum_mul]
      _ = leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              (S * (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
                  (gHatIdxMeas params family x).outcome g) * S) := by
            rw [Finset.mul_sum]
      _ = leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              (S * (completePartSubMeas params family x).total * S) := by
            rw [fromHToG_gHatIdxMeas_sum_isSome_true]
      _ = leftTensor (ι₂ := ι) A *
            rightTensor (ι₁ := ι)
              (S * (if true then (completePartSubMeas params family x).total
                else (incompletePartSubMeas params family x).total) * S) := by simp

/-- Fold a head-point scalar average with an `S · F x · S` sandwich into the
right tensor factor. -/
lemma fromHToG_avgOver_head_ev_sandwich
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (A S : MIPStarRE.Quantum.Op ι) (F : Fq params → MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (Fq params)) (fun x =>
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) (S * F x * S))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι)
          (S * averageOperatorOverDistribution (uniformDistribution (Fq params)) F * S)) := by
  have havg :
      averageOperatorOverDistribution (uniformDistribution (Fq params)) (fun x => F x * S) =
        averageOperatorOverDistribution (uniformDistribution (Fq params)) F * S := by
    unfold averageOperatorOverDistribution
    calc
      ∑ x ∈ (uniformDistribution (Fq params)).support,
          (uniformDistribution (Fq params)).weight x • (F x * S)
        = ∑ x ∈ (uniformDistribution (Fq params)).support,
            ((uniformDistribution (Fq params)).weight x • F x) * S := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              rw [smul_mul_assoc]
      _ = (∑ x ∈ (uniformDistribution (Fq params)).support,
            (uniformDistribution (Fq params)).weight x • F x) * S := by
              rw [Finset.sum_mul]
  calc
    avgOver (uniformDistribution (Fq params)) (fun x =>
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) (S * F x * S)))
      = avgOver (uniformDistribution (Fq params)) (fun x =>
          ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) (S * (F x * S)))) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            simp [mul_assoc]
    _ = ev ψbi (leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * averageOperatorOverDistribution (uniformDistribution (Fq params))
              (fun x => F x * S))) := by
            simpa [mul_assoc] using fromHToG_avgOver_head_ev params ψbi A S (fun x => F x * S)
    _ = ev ψbi (leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * averageOperatorOverDistribution (uniformDistribution (Fq params)) F * S)) := by
            simp [havg, mul_assoc]

/-- Fold the complete/incomplete head branch average with an `S · B · S`
sandwich into the stored exact branch averages. -/
lemma fromHToG_avgOver_head_branch_ev_sandwich
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (b : Bool) (A S : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (Fq params)) (fun x =>
      let B := if b then (completePartSubMeas params family x).total
        else (incompletePartSubMeas params family x).total
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) (S * B * S))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι)
          (S * (if b then family.averagedSubMeas.total
            else 1 - family.averagedSubMeas.total) * S)) := by
  cases b
  · rw [fromHToG_avgOver_head_ev_sandwich]
    simp only [Bool.false_eq_true, if_false]
    rw [hincomplete]
  · rw [fromHToG_avgOver_head_ev_sandwich]
    simp only [if_true]
    rw [hcomplete]

/-- Summing the per-type averaged sandwich totals gives the full tail sandwich
total, hence the identity. -/
lemma fromHToG_sum_averagedSandwichByType_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) :
    (∑ τ : GHatType n,
      (averagedSandwichByTypeSubMeas params family n τ).total) = 1 := by
  classical
  calc
    (∑ τ : GHatType n, (averagedSandwichByTypeSubMeas params family n τ).total)
      = ∑ τ : GHatType n,
          ∑ xs ∈ (uniformDistribution (PointTuple params n)).support,
            (uniformDistribution (PointTuple params n)).weight xs •
              (∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
                (gHatSandwichFamily params family n xs).outcome gs) := by
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            rw [fromHToG_averagedSandwichByType_total_eq_type_sum params family n τ]
    _ = ∑ xs ∈ (uniformDistribution (PointTuple params n)).support,
          ∑ τ : GHatType n,
            (uniformDistribution (PointTuple params n)).weight xs •
              (∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
                (gHatSandwichFamily params family n xs).outcome gs) := by
            rw [Finset.sum_comm]
    _ = ∑ xs ∈ (uniformDistribution (PointTuple params n)).support,
          (uniformDistribution (PointTuple params n)).weight xs •
            (∑ τ : GHatType n,
              ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
                (gHatSandwichFamily params family n xs).outcome gs) := by
            refine Finset.sum_congr rfl ?_
            intro xs _hxs
            rw [Finset.smul_sum]
    _ = ∑ xs ∈ (uniformDistribution (PointTuple params n)).support,
          (uniformDistribution (PointTuple params n)).weight xs •
            (∑ gs : GHatTupleOutcome params n,
              (gHatSandwichFamily params family n xs).outcome gs) := by
            refine Finset.sum_congr rfl ?_
            intro xs _hxs
            exact congrArg
              ((uniformDistribution (PointTuple params n)).weight xs • ·)
              (fromHToG_type_filtered_outcome_sum params
                (fun τ gs => (gHatSandwichFamily params family n xs).outcome gs))
    _ = ∑ xs ∈ (uniformDistribution (PointTuple params n)).support,
          (uniformDistribution (PointTuple params n)).weight xs • (1 : MIPStarRE.Quantum.Op ι) := by
            refine Finset.sum_congr rfl ?_
            intro xs _hxs
            rw [fromHToG_gHatSandwichFamily_sum_eq_one params family n xs]
    _ = 1 := by
          simpa [averageOperatorOverDistribution] using
            (fromHToG_averageOperator_uniform_const_one (ι := ι) (α := PointTuple params n))

set_option maxHeartbeats 1000000 in
-- This averaged-context bound expands nested filtered sums and tensor-product rewrites.
omit [Fintype ι] [DecidableEq ι] in
/-- Averaged first-root context bound for the `S U S` sandwich used in the
second half-sandwich and final move-right Cauchy--Schwarz steps. -/
lemma fromHToG_SUS_context_avg_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι)) (hnorm : ψbi.IsNormalized)
    -- `averagedSandwichByTypeSubMeas` fixes this family universe at `0`.
    (family : IdxPolyFamily.{_, 0} params ι)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (ℓ n : ℕ) :
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
        let U := (gHatIdxMeas params family q.1).outcome ogs.1
        let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
        ev ψbi
          ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)) ≤ 1 := by
  classical
  let F : Bool → GHatType n → Fq params → PointTuple params n → Error := fun b τ x xs =>
    ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
          (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)
  have hsplit :
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)) =
      ∑ b : Bool, ∑ τ : GHatType n,
        avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs)) := by
    calc
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
            let U := (gHatIdxMeas params family x).outcome ogs.1
            let T := gHatHalfProductOutcomeOperator params family n xs ogs.2
            ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
              (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ))) := by
            simpa using (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
              (f := fun x xs =>
                ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
                  let S := fromHToGRecurrenceWeight params family ℓ
                    (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                  let U := (gHatIdxMeas params family x).outcome ogs.1
                  let T := gHatHalfProductOutcomeOperator params family n xs ogs.2
                  ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
                    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)))
      _ = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                F b τ x xs)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              refine avgOver_congr _ _ _ ?_
              intro xs
              rw [(fromHToG_sum_product (fun g gs =>
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
                  (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ))).symm]
              symm
              exact fromHToG_bool_type_filtered_outcome_sum params
                (fun b τ g gs =>
                  let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                  let U := (gHatIdxMeas params family x).outcome g
                  let T := gHatHalfProductOutcomeOperator params family n xs gs
                  ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
                    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ))
      _ = ∑ b : Bool, ∑ τ : GHatType n,
            avgOver (uniformDistribution (Fq params)) (fun x =>
              avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs)) := by
              symm
              exact fromHToG_sum₂_avgOver₂
                (uniformDistribution (Fq params))
                (uniformDistribution (PointTuple params n)) F
  let branchRhs : Bool → GHatType n → Error := fun b τ =>
    ev ψbi (leftTensor (ι₂ := ι) (averagedSandwichByTypeSubMeas params family n τ).total *
      rightTensor (ι₁ := ι)
        (if b then family.averagedSubMeas.total else 1 - family.averagedSubMeas.total))
  have hbranchSum : ∀ b : Bool,
      ∑ τ : GHatType n,
        avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs)) ≤
      ∑ τ : GHatType n, branchRhs b τ := by
    intro b
    refine Finset.sum_le_sum ?_
    intro τ _hτ
    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
    let Aτ := (averagedSandwichByTypeSubMeas params family n τ).total
    change avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs)) ≤
      branchRhs b τ
    have hrew :
        avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs)) =
        avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
              ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                  gHatTupleType gs = τ,
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U * S)))) := by
      refine avgOver_congr _ _ _ ?_
      intro x
      refine avgOver_congr _ _ _ ?_
      intro xs
      dsimp [F, S]
      refine Finset.sum_congr rfl ?_
      intro g _hg
      refine Finset.sum_congr rfl ?_
      intro gs _hgs
      let U := (gHatIdxMeas params family x).outcome g
      let T := gHatHalfProductOutcomeOperator params family n xs gs
      have hUherm : Uᴴ = U := by
        simpa [U] using fromHToG_gHatIdxMeas_outcome_isHermitian params family x g
      have hUproj : U * U = U := by
        simpa [U] using fromHToG_gHatIdxMeas_proj params family x g
      have hSherm : Sᴴ = S :=
        fromHToGRecurrenceWeight_isHermitian params family ℓ (prependTypeBit b τ)
      calc
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)
          = ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
              rightTensor (ι₁ := ι) ((S * U) * (Uᴴ * Sᴴ))) := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
              rw [conjTranspose_opTensor, opTensor_mul, Matrix.conjTranspose_mul]
              rw [show leftTensor (ι₂ := ι) (T * Tᴴ) *
                  rightTensor (ι₁ := ι) ((S * U) * (Uᴴ * Sᴴ)) =
                    opTensor (T * Tᴴ) ((S * U) * (Uᴴ * Sᴴ)) by
                rw [leftTensor_mul_rightTensor_eq_opTensor]]
        _ = ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U * S)) := by
              have hright : (S * U) * (Uᴴ * Sᴴ) = S * U * S := by
                calc
                  (S * U) * (Uᴴ * Sᴴ) = S * U * (U * S) := by rw [hUherm, hSherm]
                  _ = S * (U * U) * S := by simp [mul_assoc]
                  _ = S * U * S := by rw [hUproj]
              simp [hright]
    rw [hrew]
    calc
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U * S))))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                  gHatTupleType gs = τ,
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                let B := if b then (completePartSubMeas params family x).total
                  else (incompletePartSubMeas params family x).total
                ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * B * S)))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              refine avgOver_congr _ _ _ ?_
              intro xs
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro gs _hgs
              simpa [S] using
                (fromHToG_ev_sum_isSome_sandwich_weight params ψbi family x b
                  (gHatHalfProductOutcomeOperator params family n xs gs *
                    (gHatHalfProductOutcomeOperator params family n xs gs)ᴴ) S)
      _ = avgOver (uniformDistribution (Fq params)) (fun x =>
            ev ψbi (leftTensor (ι₂ := ι) Aτ *
              rightTensor (ι₁ := ι)
                (S * (if b then (completePartSubMeas params family x).total
                  else (incompletePartSubMeas params family x).total) * S))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              simpa [Aτ, S] using
                (fromHToG_avgOver_tail_type_ev_sandwich params ψbi family n τ
                  (S * (if b then (completePartSubMeas params family x).total
                    else (incompletePartSubMeas params family x).total) * S))
      _ = ev ψbi (leftTensor (ι₂ := ι) Aτ *
            rightTensor (ι₁ := ι)
              (S * (if b then family.averagedSubMeas.total
                else 1 - family.averagedSubMeas.total) * S)) := by
              simpa [Aτ, S] using
                (fromHToG_avgOver_head_branch_ev_sandwich params ψbi family
                  hcomplete hincomplete b Aτ S)
      _ ≤ ev ψbi (leftTensor (ι₂ := ι) Aτ *
            rightTensor (ι₁ := ι)
              (if b then family.averagedSubMeas.total else 1 - family.averagedSubMeas.total)) := by
              have hAτ_nonneg : 0 ≤ Aτ := by
                simpa [Aτ] using
                  (averagedSandwichByTypeSubMeas params family n τ).total_nonneg
              cases b
              · simpa [S] using
                  fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left ψbi hAτ_nonneg
                    (fromHToGRecurrenceWeight_sandwich_one_sub_base_le params family ℓ
                      (τtail := prependTypeBit false τ))
              · simpa [S] using
                  fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left ψbi hAτ_nonneg
                    (fromHToGRecurrenceWeight_sandwich_base_le params family ℓ
                      (τtail := prependTypeBit true τ))
      _ = branchRhs b τ := by rfl
  rw [hsplit]
  calc
    ∑ b : Bool, ∑ τ : GHatType n,
        avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs))
      ≤ ∑ b : Bool, ∑ τ : GHatType n, branchRhs b τ := by
            refine Finset.sum_le_sum ?_
            intro b _hb
            exact hbranchSum b
    _ = ∑ τ : GHatType n, ∑ b : Bool, branchRhs b τ := by
            rw [Finset.sum_comm]
    _ = ∑ τ : GHatType n,
          ev ψbi (leftTensor (ι₂ := ι)
            (averagedSandwichByTypeSubMeas params family n τ).total *
            rightTensor (ι₁ := ι)
              (family.averagedSubMeas.total + (1 - family.averagedSubMeas.total))) := by
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            rw [Fintype.sum_bool]
            dsimp [branchRhs]
            rw [← ev_add]
            apply congrArg (ev ψbi)
            calc
              leftTensor (ι₂ := ι)
                (averagedSandwichByTypeSubMeas params family n τ).total *
                  rightTensor (ι₁ := ι) family.averagedSubMeas.total +
                leftTensor (ι₂ := ι)
                  (averagedSandwichByTypeSubMeas params family n τ).total *
                  rightTensor (ι₁ := ι) (1 - family.averagedSubMeas.total)
                = leftTensor (ι₂ := ι)
                    (averagedSandwichByTypeSubMeas params family n τ).total *
                    (rightTensor (ι₁ := ι) family.averagedSubMeas.total +
                      rightTensor (ι₁ := ι) (1 - family.averagedSubMeas.total)) := by
                        rw [← mul_add]
              _ = leftTensor (ι₂ := ι)
                    (averagedSandwichByTypeSubMeas params family n τ).total *
                    rightTensor (ι₁ := ι)
                      (family.averagedSubMeas.total + (1 - family.averagedSubMeas.total)) := by
                        rw [fromHToG_rightTensor_add]
    _ = ∑ τ : GHatType n,
          ev ψbi (leftTensor (ι₂ := ι)
            (averagedSandwichByTypeSubMeas params family n τ).total) := by
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            have hone : family.averagedSubMeas.total +
                (1 - family.averagedSubMeas.total) = (1 : MIPStarRE.Quantum.Op ι) := by
              simp
            rw [hone, rightTensor_one, mul_one]
    _ = ev ψbi (leftTensor (ι₂ := ι)
          (∑ τ : GHatType n,
            (averagedSandwichByTypeSubMeas params family n τ).total)) := by
            rw [← ev_sum]
            rw [leftTensor_finset_sum]
    _ = ev ψbi (leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
          rw [fromHToG_sum_averagedSandwichByType_total_eq_one params family n]
    _ = 1 := by simpa [leftTensor] using ev_one_of_isNormalized ψbi hnorm

end MIPStarRE.LDT.Pasting
