import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.Definitions
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.SumBounds

/-!
# Section 12 pasting: commute G half-sandwich move lemmas

This module contains the move-chain lemmas for the half-sandwich commutation
chain.  The split reindexing lemmas and the two-term base case are kept in
`StepLemmas.Split`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gHatSelfConsistency_sddOpRel_quadThird
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) (r : ℕ)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params ×
        SliceQuestion params × PointTuple params r))
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.2.2.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.2.2.1)
      (gHatSelfConsistencyError zeta) := by
  have hfst :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params ×
          (SliceQuestion params × SliceQuestion params × PointTuple params r)))
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
        (gHatSelfConsistencyError zeta) :=
    sddOpRel_uniform_fst ψbi
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
      (gHatSelfConsistencyError zeta)
      (gHatSelfConsistency_sddOpRel params ψbi family zeta hsc)
  simpa [thirdSliceFrontEquiv] using
    (sddOpRel_uniform_equiv (thirdSliceFrontEquiv params r).symm ψbi
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
      (gHatSelfConsistencyError zeta)).1 hfst

lemma commuteGHalfSandwich_step_commute
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (r : ℕ)
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveFamily params family r)
      (commuteGHalfSandwich_commuteFamily params family r)
      (gHatCommutationError params gamma zeta) := by
  let C : (SliceQuestion params × SliceQuestion params × PointTuple params r) →
      (GHatOutcome params × GHatOutcome params) → GHatTupleOutcome params r →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ gt => rightTensor (ι₁ := ι)
      (gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)
  have hC :
      ∀ q a,
        ∑ gt : GHatTupleOutcome params r, (C q a gt)ᴴ * C q a gt ≤ 1 := by
    intro q a
    calc
      ∑ gt : GHatTupleOutcome params r, (C q a gt)ᴴ * C q a gt
        = ∑ gt : GHatTupleOutcome params r,
            rightTensor (ι₁ := ι)
              (((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt) := by
                  refine Finset.sum_congr rfl ?_
                  intro gt _
                  rw [show (rightTensor (ι₁ := ι)
                      (gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))ᴴ =
                      rightTensor (ι₁ := ι)
                        ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) by
                    simpa [rightTensor, opTensor] using
                      (conjTranspose_opTensor (1 : MIPStarRE.Quantum.Op ι)
                        (gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))]
                  simp [C, rightTensor_mul_rightTensor]
      _ = rightTensor (ι₁ := ι)
            (∑ gt : GHatTupleOutcome params r,
              ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt) := by
                  simpa using (rightTensor_finset_sum (ι₁ := ι) Finset.univ
                    (fun gt => ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                      gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))
      _ ≤ 1 := by
            exact rightTensor_le_one (ι₁ := ι)
              (A := ∑ gt : GHatTupleOutcome params r,
                ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                  gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)
              (gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2)
  let rawSource : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r =>
          C q ag.1 ag.2 * (gHatPairProductLeft params family (q.1, q.2.1)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r,
          C q ag.1 ag.2 * (gHatPairProductLeft params family (q.1, q.2.1)).outcome ag.1 }
  let rawTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r =>
          C q ag.1 ag.2 * (gHatPairProductRight params family (q.1, q.2.1)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r,
          C q ag.1 ag.2 * (gHatPairProductRight params family (q.1, q.2.1)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => gHatPairProductLeft params family (q.1, q.2.1))
      (fun q => gHatPairProductRight params family (q.1, q.2.1))
      C (gHatCommutationError params gamma zeta)
      (gHatPairProduct_sddOpRel_triple params ψbi family gamma zeta r hcom)
      hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (pairTailOutcomeEquiv params r)
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    rawSource rawTarget (gHatCommutationError params gamma zeta) hcab
  let reindexedSource :
      IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((pairTailOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget :
      IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((pairTailOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveFamily params family r)
    (commuteGHalfSandwich_commuteFamily params family r)
    (gHatCommutationError params gamma zeta)
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
      calc
        (reindexedSource q).outcome ogs
          = rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) (A * B) := by
              simp [reindexedSource, rawSource, pairTailOutcomeEquiv, C,
                gHatPairProductLeft, orderedProductOpFamily, OpFamily.leftPlacedOpFamily,
                A, B, T]
        _ = opTensor (A * B) T := by
              rw [rightTensor_mul_leftTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) (A * B) * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_leftTensor]
        _ = (commuteGHalfSandwich_moveFamily params family r q).outcome ogs := by
              simp [commuteGHalfSandwich_moveFamily, A, B, T, mul_assoc]
    )
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
      calc
        (reindexedTarget q).outcome ogs
          = rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) (B * A) := by
              simp [reindexedTarget, rawTarget, pairTailOutcomeEquiv, C,
                gHatPairProductRight, reversedProductOpFamily, OpFamily.leftPlacedOpFamily,
                A, B, T]
        _ = opTensor (B * A) T := by
              rw [rightTensor_mul_leftTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) (B * A) * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) B * leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_leftTensor]
        _ = (commuteGHalfSandwich_commuteFamily params family r q).outcome ogs := by
              simp [commuteGHalfSandwich_commuteFamily, A, B, T, mul_assoc]
    )
    hreindex

lemma commuteGHalfSandwich_prefixFirstSliceLeft_move
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params ×
        SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepSourceFamily params family r)
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution ((SliceQuestion params × SliceQuestion params ×
          PointTuple params r) × SliceQuestion params))
        (fun q => commuteGHalfSandwich_moveSourceFamily params family r q.1)
        (fun q => commuteGHalfSandwich_moveFamily params family r q.1)
        δ :=
    sddOpRel_uniform_fst ψbi
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      δ hAB
  have hABquad :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params ×
          SliceQuestion params × PointTuple params r))
        (fun q => commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
        (fun q => commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
        δ :=
    (sddOpRel_uniform_equiv (firstSliceBackQuestionEquiv params r) ψbi
      (fun q => commuteGHalfSandwich_moveSourceFamily params family r q.1)
      (fun q => commuteGHalfSandwich_moveFamily params family r q.1)
      δ).1 hABfst
  let C : (SliceQuestion params × SliceQuestion params × SliceQuestion params ×
      PointTuple params r) →
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) → GHatOutcome params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ g₁ => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g₁)
  have hC :
      ∀ q a,
        ∑ g₁ : GHatOutcome params, (C q a g₁)ᴴ * C q a g₁ ≤ 1 := by
    intro q a
    calc
      ∑ g₁ : GHatOutcome params, (C q a g₁)ᴴ * C q a g₁
        = ∑ g₁ : GHatOutcome params,
            leftTensor (ι₂ := ι)
              ((((gHatIdxMeas params family q.1).outcome g₁)ᴴ) *
                (gHatIdxMeas params family q.1).outcome g₁) := by
                  refine Finset.sum_congr rfl ?_
                  intro g₁ _
                  rw [show (leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g₁))ᴴ =
                      leftTensor (ι₂ := ι) (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) by
                    simpa [leftTensor, opTensor] using
                      (conjTranspose_opTensor ((gHatIdxMeas params family q.1).outcome g₁)
                        (1 : MIPStarRE.Quantum.Op ι))]
                  simp [C, leftTensor_mul_leftTensor]
      _ = leftTensor (ι₂ := ι)
            (∑ g₁ : GHatOutcome params,
              (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) *
                (gHatIdxMeas params family q.1).outcome g₁) := by
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ ≤ 1 := by
            have hinner :
                ∑ g₁ : GHatOutcome params,
                    (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) *
                      (gHatIdxMeas params family q.1).outcome g₁ ≤ 1 :=
              CommutativityPoints.subMeas_sum_adjoint_mul_le_one
                ((gHatIdxMeas params family q.1).toSubMeas)
            exact leftTensor_le_one (ι₂ := ι) (A := _ ) hinner
  let rawSource : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1,
              q.2.2.2)).outcome ag.1
        total := ∑ ag :
            (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) ×
              GHatOutcome params,
          C q ag.1 ag.2 *
            (commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1,
                q.2.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2)).outcome ag.1
        total := ∑ ag :
            (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) ×
              GHatOutcome params,
          C q ag.1 ag.2 *
            (commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1,
                q.2.2.2)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
      (fun q => commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
      C δ hABquad hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (firstSliceBackOutcomeEquiv params r)
    ψbi
    (uniformDistribution
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((firstSliceBackOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((firstSliceBackOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveStepSourceFamily params family r)
    (commuteGHalfSandwich_moveStepMidFamily params family r)
    δ
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      calc
        (reindexedSource q).outcome ogs
          = leftTensor (ι₂ := ι) A *
              (leftTensor (ι₂ := ι) ((B * G) *
                  gHatHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)) := by
                simp [reindexedSource, rawSource, firstSliceBackOutcomeEquiv, C,
                  commuteGHalfSandwich_moveSourceFamily, A, B, G,
                  leftTensor_mul_leftTensor, mul_assoc]
        _ = (commuteGHalfSandwich_moveStepSourceFamily params family r q).outcome ogs := by
              simp [commuteGHalfSandwich_moveStepSourceFamily, A, B, G,
                 mul_assoc, leftTensor_mul_leftTensor]
    )
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      calc
        (reindexedTarget q).outcome ogs
          = leftTensor (ι₂ := ι) A * (leftTensor (ι₂ := ι) B * (leftTensor (ι₂ := ι) G
              * rightTensor (ι₁ := ι) T)) := by
                simp [reindexedTarget, rawTarget, firstSliceBackOutcomeEquiv, C,
                  commuteGHalfSandwich_moveFamily, A, B, G, T, mul_assoc]
        _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
              calc
                leftTensor (ι₂ := ι) A *
                    (leftTensor (ι₂ := ι) B *
                      (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T))
                  = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * leftTensor (ι₂ := ι) G) *
                      rightTensor (ι₁ := ι) T := by
                        simp [mul_assoc]
                _ =
                    (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G) *
                      rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
                      symm
                      calc
                        (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs
                          =
                            (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
                              leftTensor (ι₂ := ι) G) *
                              rightTensor (ι₁ := ι) T := by
                                simp [commuteGHalfSandwich_moveStepMidFamily, A, B, G, T, mul_assoc]
                        _ = (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G)
                            * rightTensor (ι₁ := ι) T := by
                              rw [leftTensor_mul_leftTensor]
                        _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                              rw [leftTensor_mul_leftTensor]
                        _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                              simp [mul_assoc]
    )
    hreindex

lemma commuteGHalfSandwich_moveStepMid_toTarget
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) (r : ℕ)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      (commuteGHalfSandwich_moveStepTargetFamily params family r)
      (gHatSelfConsistencyError zeta) := by
  let Q := SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r
  let Aop : IdxOpFamily Q (GHatOutcome params) (ι × ι) :=
    fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.2.2.1
  let Bop : IdxOpFamily Q (GHatOutcome params) (ι × ι) :=
    fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.2.2.1
  let C : Q → GHatOutcome params → ((GHatOutcome params × GHatOutcome params) ×
      GHatTupleOutcome params r) →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ ag =>
      leftTensor (ι₂ := ι)
          (((gHatIdxMeas params family q.1).outcome ag.1.1) *
            ((gHatIdxMeas params family q.2.1).outcome ag.1.2)) *
        rightTensor (ι₁ := ι)
          (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ag.2)
  have hAB :
      SDDOpRel ψbi
        (uniformDistribution Q)
        Aop Bop
        (gHatSelfConsistencyError zeta) :=
    gHatSelfConsistency_sddOpRel_quadThird params ψbi family zeta r hsc
  have hC :
      ∀ q a,
        ∑ ag : ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r),
            (C q a ag)ᴴ * C q a ag ≤ 1 := by
    intro q a
    let pairProd : GHatOutcome params × GHatOutcome params → MIPStarRE.Quantum.Op ι :=
      fun og => ((gHatIdxMeas params family q.1).outcome og.1) *
        ((gHatIdxMeas params family q.2.1).outcome og.2)
    let tailOp : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
      fun gs => gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 gs
    have hpair :
        ∑ og : GHatOutcome params × GHatOutcome params,
            (pairProd og)ᴴ * pairProd og ≤ 1 := by
      simpa [pairProd] using
        gHatPairPrefix_sum_adjoint_mul_le_one params family (q.1, q.2.1)
    have htail :
        ∑ gs : GHatTupleOutcome params r,
            (tailOp gs)ᴴ * tailOp gs ≤ 1 := by
      simpa [tailOp] using
        gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2.2
    simpa [C, pairProd, tailOp] using
      (leftTensor_rightTensor_sum_adjoint_mul_le_one
        (ι := ι) (prefixOp := pairProd) (tailOp := tailOp) hpair htail)
  let rawSource : IdxOpFamily Q
      (GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r))
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (Aop q).outcome ag.1
        total := ∑ ag : GHatOutcome params × ((GHatOutcome params × GHatOutcome params) ×
            GHatTupleOutcome params r),
          C q ag.1 ag.2 * (Aop q).outcome ag.1 }
  let rawTarget : IdxOpFamily Q
      (GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r))
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (Bop q).outcome ag.1
        total := ∑ ag : GHatOutcome params × ((GHatOutcome params × GHatOutcome params) ×
            GHatTupleOutcome params r),
          C q ag.1 ag.2 * (Bop q).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution Q) Aop Bop C (gHatSelfConsistencyError zeta) hAB hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (thirdSliceFrontOutcomeEquiv params r)
    ψbi (uniformDistribution Q) rawSource rawTarget (gHatSelfConsistencyError zeta) hcab
  let reindexedSource : IdxOpFamily Q
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
          GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((thirdSliceFrontOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily Q
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
          GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((thirdSliceFrontOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution Q)
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveStepMidFamily params family r)
    (commuteGHalfSandwich_moveStepTargetFamily params family r)
    (gHatSelfConsistencyError zeta)
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      have hAop : (Aop q).outcome ogs.2.2.1 = leftTensor (ι₂ := ι) G := by
        rfl
      have hcomm : rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) G =
          leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T := by
        rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
      calc
        (reindexedSource q).outcome ogs =
            leftTensor (ι₂ := ι) (A * B) *
              (rightTensor (ι₁ := ι) T * (Aop q).outcome ogs.2.2.1) := by
              simp [reindexedSource, rawSource, thirdSliceFrontOutcomeEquiv, C, A, B, T, mul_assoc]
        _ =
            leftTensor (ι₂ := ι) (A * B) *
              (rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) G) := by
              rw [hAop]
        _ =
            leftTensor (ι₂ := ι) (A * B) *
              (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T) := by
              rw [hcomm]
        _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
              calc
                leftTensor (ι₂ := ι) (A * B) *
                    (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T)
                  =
                    (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G) *
                      rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
                      simp [commuteGHalfSandwich_moveStepMidFamily, A, B, G, T,
                        leftTensor_mul_leftTensor, mul_assoc]
    )
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      have hBop : (Bop q).outcome ogs.2.2.1 = rightTensor (ι₁ := ι) G := by
        rfl
      calc
        (reindexedTarget q).outcome ogs
          = leftTensor (ι₂ := ι) (A * B) *
              (rightTensor (ι₁ := ι) T * (Bop q).outcome ogs.2.2.1) := by
                simp [reindexedTarget, rawTarget, thirdSliceFrontOutcomeEquiv, C, A, B, T,
                    mul_assoc]
        _ = leftTensor (ι₂ := ι) (A * B) *
              (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
                rw [hBop]
        _ = (commuteGHalfSandwich_moveStepTargetFamily params family r q).outcome ogs := by
              symm
              calc
                (commuteGHalfSandwich_moveStepTargetFamily params family r q).outcome ogs
                  = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
                      (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
                        simp [commuteGHalfSandwich_moveStepTargetFamily, A, B, G, T, mul_assoc]
                _ =
                    leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
                      rightTensor (ι₁ := ι) (T * G) := by
                      rw [rightTensor_mul_rightTensor]
                _ = leftTensor (ι₂ := ι) (A * B) * rightTensor (ι₁ := ι) (T * G) := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * B) *
                      (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
                        rw [rightTensor_mul_rightTensor]
    )
    hreindex


end MIPStarRE.LDT.Pasting
