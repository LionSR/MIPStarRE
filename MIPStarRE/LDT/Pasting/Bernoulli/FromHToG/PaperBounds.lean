import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.AdjacentStages
import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.PaperBounds.ContextBounds

/-!
# Section 12 pasting: from-H-to-G collapsed bounds

Collapses the paper endpoint `M₄` to the next Lean stage and records the scalar
bounds used by the final telescope.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def fromHToGAdjacentStageCollapsed
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) : Error :=
  let n := k - (ℓ + 1)
  ∑ τ : GHatType n,
    ev ψbi (leftTensor (ι₂ := ι) (averagedSandwichByTypeSubMeas params family n τ).total *
      rightTensor (ι₁ := ι)
        (fromHToGRecurrenceWeight params family ℓ (prependTypeBit true τ) *
            family.averagedSubMeas.total +
          fromHToGRecurrenceWeight params family ℓ (prependTypeBit false τ) *
            (1 - family.averagedSubMeas.total)))

/-- The collapsed branch expression is exactly the next Lean stage. -/
lemma fromHToGAdjacentStageCollapsed_eq_stage_succ
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k ℓ : ℕ) :
    fromHToGAdjacentStageCollapsed params ψbi family k ℓ =
      fromHToGStageMass params ψbi family k (ℓ + 1) := by
  classical
  unfold fromHToGAdjacentStageCollapsed fromHToGStageMass
  refine Finset.sum_congr rfl ?_
  intro τ _hτ
  exact (hstageExact.tailWeightRecurrence ℓ τ).symm

/-- `M₄` collapses exactly to the branch-averaged recurrence expression. -/
lemma fromHToGAdjacentStageM4_eq_collapsed
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (k ℓ : ℕ) :
    fromHToGAdjacentStageM4 params ψbi family k ℓ =
      fromHToGAdjacentStageCollapsed params ψbi family k ℓ := by
  classical
  let n := k - (ℓ + 1)
  unfold fromHToGAdjacentStageM4 fromHToGAdjacentStageCollapsed
  change
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
                rightTensor (ι₁ := ι) (S * U * U))) =
      ∑ τ : GHatType n,
        ev ψbi (leftTensor (ι₂ := ι)
          (averagedSandwichByTypeSubMeas params family n τ).total *
            rightTensor (ι₁ := ι)
              (fromHToGRecurrenceWeight params family ℓ (prependTypeBit true τ) *
                  family.averagedSubMeas.total +
                fromHToGRecurrenceWeight params family ℓ (prependTypeBit false τ) *
                  (1 - family.averagedSubMeas.total)))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro τ _hτ
  let Aτ := (averagedSandwichByTypeSubMeas params family n τ).total
  let Strue := fromHToGRecurrenceWeight params family ℓ (prependTypeBit true τ)
  let Sfalse := fromHToGRecurrenceWeight params family ℓ (prependTypeBit false τ)
  have htrue :
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (Strue * U * U)))) =
        ev ψbi (leftTensor (ι₂ := ι) Aτ *
          rightTensor (ι₁ := ι) (Strue * family.averagedSubMeas.total)) := by
    calc
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (Strue * U * U))))
          = avgOver (uniformDistribution (Fq params)) (fun x =>
              avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
                ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                    gHatTupleType gs = τ,
                  let T := gHatHalfProductOutcomeOperator params family n xs gs
                  ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                    rightTensor (ι₁ := ι)
                      (Strue * (completePartSubMeas params family x).total)))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              refine avgOver_congr _ _ _ ?_
              intro xs
              simpa [Strue] using
                (fromHToGAdjacentStageM4_head_sum params ψbi family ℓ n true τ x xs)
      _ = avgOver (uniformDistribution (Fq params)) (fun x =>
              ev ψbi (leftTensor (ι₂ := ι) Aτ *
                rightTensor (ι₁ := ι)
                  (Strue * (completePartSubMeas params family x).total))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              simpa [Aτ, Strue] using
                (fromHToG_avgOver_tail_type_ev params ψbi family n τ
                  (Strue * (completePartSubMeas params family x).total))
      _ = ev ψbi (leftTensor (ι₂ := ι) Aτ *
            rightTensor (ι₁ := ι) (Strue * family.averagedSubMeas.total)) := by
              simpa [Aτ, Strue] using
                (fromHToG_avgOver_head_branch_ev params ψbi family hcomplete hincomplete
                  true Aτ Strue)
  have hfalse :
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (Sfalse * U * U)))) =
        ev ψbi (leftTensor (ι₂ := ι) Aτ *
          rightTensor (ι₁ := ι) (Sfalse * (1 - family.averagedSubMeas.total))) := by
    calc
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (Sfalse * U * U))))
          = avgOver (uniformDistribution (Fq params)) (fun x =>
              avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
                ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                    gHatTupleType gs = τ,
                  let T := gHatHalfProductOutcomeOperator params family n xs gs
                  ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                    rightTensor (ι₁ := ι)
                      (Sfalse * (incompletePartSubMeas params family x).total)))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              refine avgOver_congr _ _ _ ?_
              intro xs
              simpa [Sfalse] using
                (fromHToGAdjacentStageM4_head_sum params ψbi family ℓ n false τ x xs)
      _ = avgOver (uniformDistribution (Fq params)) (fun x =>
              ev ψbi (leftTensor (ι₂ := ι) Aτ *
                rightTensor (ι₁ := ι)
                  (Sfalse * (incompletePartSubMeas params family x).total))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              simpa [Aτ, Sfalse] using
                (fromHToG_avgOver_tail_type_ev params ψbi family n τ
                  (Sfalse * (incompletePartSubMeas params family x).total))
      _ = ev ψbi (leftTensor (ι₂ := ι) Aτ *
            rightTensor (ι₁ := ι) (Sfalse * (1 - family.averagedSubMeas.total))) := by
              simpa [Aτ, Sfalse] using
                (fromHToG_avgOver_head_branch_ev params ψbi family hcomplete hincomplete
                  false Aτ Sfalse)
  rw [Fintype.sum_bool, htrue, hfalse]
  rw [← ev_add]
  congr 1
  rw [← mul_add]
  congr 1
  exact (fromHToG_rightTensor_add
    (Strue * family.averagedSubMeas.total)
    (Sfalse * (1 - family.averagedSubMeas.total))).symm

/-- Raw `qSDDCore` form of the half-sandwich commutation hypothesis after
splitting a nonempty sandwich into its head and tail, with the error weakened to
the ambient length `k`. -/
lemma fromHToG_headTail_qSDDCore_bound
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    {n k : ℕ} (hn : 2 ≤ n + 1) (hnk : n + 1 ≤ k) :
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      qSDDCore ψbi
        (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
          leftTensor (ι₂ := ι)
            ((gHatIdxMeas params family q.1).outcome ogs.1 *
              gHatHalfProductOutcomeOperator params family n q.2 ogs.2))
        (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
              (gHatIdxMeas params family q.1).outcome ogs.1))) ≤
      commuteGHalfSandwichError params gamma zeta k := by
  have hsplit : SDDOpRel ψbi
      (uniformDistribution (Fq params × PointTuple params n))
      (headTailOrderedFamily params family n)
      (headTailRotatedFamily params family n)
      (commuteGHalfSandwichError params gamma zeta (n + 1)) := by
    exact (commuteGHalfSandwich_split_iff params ψbi family n
      (commuteGHalfSandwichError params gamma zeta (n + 1))).1
      (hhalf (n + 1) hn).repeatedCommutation
  have hcore :
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        qSDDCore ψbi
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              ((gHatIdxMeas params family q.1).outcome ogs.1 *
                gHatHalfProductOutcomeOperator params family n q.2 ogs.2))
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              (gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
                (gHatIdxMeas params family q.1).outcome ogs.1))) ≤
        commuteGHalfSandwichError params gamma zeta (n + 1) := by
    simpa [sddErrorOp, qSDDOp, headTailOrderedFamily, headTailRotatedFamily,
      leftTensor_mul_leftTensor] using hsplit.squaredDistanceBound
  exact le_trans hcore
    (commuteGHalfSandwichError_mono_length params gamma zeta hgamma_nonneg hzeta_nonneg hnk)

/-- The completed self-consistency estimate used in the first and final move-right
steps, after adjoining an irrelevant uniform suffix-question register. -/
lemma fromHToG_selfConsistency_qSDDCore_bound
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcompleted :
      SDDRel ψbi
        (uniformDistribution (SliceQuestion params))
        (gHatSelfConsistencyLeftFamily params family)
        (gHatSelfConsistencyRightFamily params family)
        (gHatSelfConsistencyError zeta))
    {n : ℕ} :
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      qSDDCore ψbi
        (fun g : GHatOutcome params =>
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g))
        (fun g : GHatOutcome params =>
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g))) ≤
      2 * zeta := by
  have hscOp := gHatSelfConsistency_sddOpRel params ψbi family zeta hcompleted
  have hprod := sddOpRel_uniform_fst
    (α := SliceQuestion params) (β := PointTuple params n) (Outcome := GHatOutcome params)
    (ι := ι) (ψ := ψbi)
    (A := IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
    (B := IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
    (δ := gHatSelfConsistencyError zeta) hscOp
  simpa [SliceQuestion, sddErrorOp, qSDDOp, qSDDCore, IdxSubMeas.toIdxOpFamily,
    SubMeas.toOpFamily, gHatSelfConsistencyLeftFamily, gHatSelfConsistencyRightFamily,
    gHatSelfConsistencyError, leftPlacedSubMeas, rightPlacedSubMeas] using
      hprod.squaredDistanceBound

/-- Adjoint-oriented raw `qSDDCore` form of the half-sandwich commutation
hypothesis.  This is the orientation used by the paper's Cauchy--Schwarz
decompositions in `eq:call-this-later` and `eq:call-again-later-part-dos`. -/
lemma fromHToG_headTail_adjoint_qSDDCore_bound
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    {n k : ℕ} (hn : 2 ≤ n + 1) (hnk : n + 1 ≤ k) :
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      qSDDCore ψbi
        (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
          leftTensor (ι₂ := ι)
            ((gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
              (gHatIdxMeas params family q.1).outcome ogs.1))
        (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
          leftTensor (ι₂ := ι)
            ((gHatIdxMeas params family q.1).outcome ogs.1 *
              (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))) ≤
      commuteGHalfSandwichError params gamma zeta k := by
  let eQ : (Fq params × PointTuple params n) ≃ (Fq params × PointTuple params n) :=
    { toFun := fun q => (q.1, (fromHToGPointTupleReverseEquiv params n) q.2)
      invFun := fun q => (q.1, (fromHToGPointTupleReverseEquiv params n) q.2)
      left_inv := by
        rintro ⟨x, xs⟩
        simp [fromHToGPointTupleReverseEquiv]
      right_inv := by
        rintro ⟨x, xs⟩
        simp [fromHToGPointTupleReverseEquiv] }
  let eO : (GHatOutcome params × GHatTupleOutcome params n) ≃
      (GHatOutcome params × GHatTupleOutcome params n) :=
    { toFun := fun ogs => (ogs.1, (fromHToGGHatTupleOutcomeReverseEquiv params n) ogs.2)
      invFun := fun ogs => (ogs.1, (fromHToGGHatTupleOutcomeReverseEquiv params n) ogs.2)
      left_inv := by
        rintro ⟨g, gs⟩
        simp [fromHToGGHatTupleOutcomeReverseEquiv]
      right_inv := by
        rintro ⟨g, gs⟩
        simp [fromHToGGHatTupleOutcomeReverseEquiv] }
  let baseIntegrand := fun q : Fq params × PointTuple params n =>
    qSDDCore ψbi
      (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
        leftTensor (ι₂ := ι)
          ((gHatIdxMeas params family q.1).outcome ogs.1 *
            gHatHalfProductOutcomeOperator params family n q.2 ogs.2))
      (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
        leftTensor (ι₂ := ι)
          (gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
            (gHatIdxMeas params family q.1).outcome ogs.1))
  have hbase := fromHToG_headTail_qSDDCore_bound params ψbi family gamma zeta
    hgamma_nonneg hzeta_nonneg hhalf (n := n) (k := k) hn hnk
  have hbase_reindexed :
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        qSDDCore ψbi
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              ((gHatIdxMeas params family q.1).outcome ogs.1 *
                gHatHalfProductOutcomeOperator params family n
                  ((fromHToGPointTupleReverseEquiv params n) q.2) ogs.2))
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              (gHatHalfProductOutcomeOperator params family n
                  ((fromHToGPointTupleReverseEquiv params n) q.2) ogs.2 *
                (gHatIdxMeas params family q.1).outcome ogs.1))) ≤
        commuteGHalfSandwichError params gamma zeta k := by
    calc
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        qSDDCore ψbi
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              ((gHatIdxMeas params family q.1).outcome ogs.1 *
                gHatHalfProductOutcomeOperator params family n
                  ((fromHToGPointTupleReverseEquiv params n) q.2) ogs.2))
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              (gHatHalfProductOutcomeOperator params family n
                  ((fromHToGPointTupleReverseEquiv params n) q.2) ogs.2 *
                (gHatIdxMeas params family q.1).outcome ogs.1)))
        = avgOver (uniformDistribution (Fq params × PointTuple params n)) baseIntegrand := by
            simpa [baseIntegrand, eQ] using
              (avgOver_uniform_equiv eQ baseIntegrand).symm
      _ ≤ commuteGHalfSandwichError params gamma zeta k := hbase
  have hsymm :
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        qSDDCore ψbi
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              ((gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                (gHatIdxMeas params family q.1).outcome ogs.1))
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              ((gHatIdxMeas params family q.1).outcome ogs.1 *
                (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))) =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        qSDDCore ψbi
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              ((gHatIdxMeas params family q.1).outcome ogs.1 *
                (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              ((gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                (gHatIdxMeas params family q.1).outcome ogs.1))) := by
    refine avgOver_congr _ _ _ ?_
    intro q
    exact fromHToG_qSDDCore_symm ψbi _ _
  have hrev :
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        qSDDCore ψbi
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              ((gHatIdxMeas params family q.1).outcome ogs.1 *
                (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              ((gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                (gHatIdxMeas params family q.1).outcome ogs.1))) =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        qSDDCore ψbi
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              ((gHatIdxMeas params family q.1).outcome ogs.1 *
                gHatHalfProductOutcomeOperator params family n
                  ((fromHToGPointTupleReverseEquiv params n) q.2) ogs.2))
          (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
            leftTensor (ι₂ := ι)
              (gHatHalfProductOutcomeOperator params family n
                  ((fromHToGPointTupleReverseEquiv params n) q.2) ogs.2 *
                (gHatIdxMeas params family q.1).outcome ogs.1))) := by
    refine avgOver_congr _ _ _ ?_
    intro q
    unfold qSDDCore
    exact Fintype.sum_equiv eO.symm
      (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
        let U := (gHatIdxMeas params family q.1).outcome ogs.1
        let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
        ev ψbi (((leftTensor (ι₂ := ι) (U * Tᴴ) - leftTensor (ι₂ := ι) (Tᴴ * U))ᴴ) *
          (leftTensor (ι₂ := ι) (U * Tᴴ) - leftTensor (ι₂ := ι) (Tᴴ * U))))
      (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
        let U := (gHatIdxMeas params family q.1).outcome ogs.1
        let T := gHatHalfProductOutcomeOperator params family n
          ((fromHToGPointTupleReverseEquiv params n) q.2) ogs.2
        ev ψbi (((leftTensor (ι₂ := ι) (U * T) - leftTensor (ι₂ := ι) (T * U))ᴴ) *
          (leftTensor (ι₂ := ι) (U * T) - leftTensor (ι₂ := ι) (T * U))))
      (by
        rintro ⟨g, gs⟩
        let U := (gHatIdxMeas params family q.1).outcome g
        have hT :
            gHatHalfProductOutcomeOperator params family n
                ((fromHToGPointTupleReverseEquiv params n) q.2)
                ((fromHToGGHatTupleOutcomeReverseEquiv params n) gs) =
              (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ := by
          simpa using fromHToG_gHatHalfProduct_reverse_eq_adjoint params family n q.2 gs
        let F := fun T : MIPStarRE.Quantum.Op ι =>
          ev ψbi (((leftTensor (ι₂ := ι) (U * T) - leftTensor (ι₂ := ι) (T * U))ᴴ) *
            (leftTensor (ι₂ := ι) (U * T) - leftTensor (ι₂ := ι) (T * U)))
        simpa [F, U, eO] using congrArg F hT.symm)
  calc
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      qSDDCore ψbi
        (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
          leftTensor (ι₂ := ι)
            ((gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
              (gHatIdxMeas params family q.1).outcome ogs.1))
        (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
          leftTensor (ι₂ := ι)
            ((gHatIdxMeas params family q.1).outcome ogs.1 *
              (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ)))
      = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          qSDDCore ψbi
            (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
              leftTensor (ι₂ := ι)
                ((gHatIdxMeas params family q.1).outcome ogs.1 *
                  (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))
            (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
              leftTensor (ι₂ := ι)
                ((gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                  (gHatIdxMeas params family q.1).outcome ogs.1))) := hsymm
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          qSDDCore ψbi
            (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
              leftTensor (ι₂ := ι)
                ((gHatIdxMeas params family q.1).outcome ogs.1 *
                  gHatHalfProductOutcomeOperator params family n
                    ((fromHToGPointTupleReverseEquiv params n) q.2) ogs.2))
            (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
              leftTensor (ι₂ := ι)
                (gHatHalfProductOutcomeOperator params family n
                    ((fromHToGPointTupleReverseEquiv params n) q.2) ogs.2 *
                  (gHatIdxMeas params family q.1).outcome ogs.1))) := hrev
    _ ≤ commuteGHalfSandwichError params gamma zeta k := hbase_reindexed
end MIPStarRE.LDT.Pasting
