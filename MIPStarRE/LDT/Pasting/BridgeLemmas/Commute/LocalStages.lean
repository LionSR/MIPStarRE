import MIPStarRE.LDT.Pasting.BridgeLemmas.Commute.Setup

/-!
# Section 12 pasting: bridge local commute stages

Local move and commute stages for the half-sandwich bridge before the recursive lift.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def splitQuestionEquiv (params : Parameters) (r : ℕ) :
    ((SliceQuestion params × PointTuple params r) × SliceQuestion params) ≃
      (SliceQuestion params × SliceQuestion params × PointTuple params r) where
  toFun q := (q.1.1, q.2, q.1.2)
  invFun q := ((q.1, q.2.2), q.2.1)
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

def prefixTripleOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.1.1, og.2, og.1.2)
  invFun og := ((og.1, og.2.2), og.2.1)
  left_inv og := by cases og; rfl
  right_inv og := by cases og; rfl

def pairTailOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.1.1, og.1.2, og.2)
  invFun og := ((og.1, og.2.1), og.2.2)
  left_inv og := by cases og; rfl
  right_inv og := by cases og; rfl

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
  let reindexedSource : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((pairTailOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
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
                A, B, T, leftTensor_mul_leftTensor, mul_assoc]
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
                A, B, T, leftTensor_mul_leftTensor, mul_assoc]
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

def splitSuccQuestionEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × PointTuple params (r + 1)) ≃
      (SliceQuestion params × SliceQuestion params × PointTuple params r) where
  toFun q := (q.1, q.2 0, pointTupleTail q.2)
  invFun q := (q.1, Fin.cons q.2.1 q.2.2)
  left_inv q := by
    rcases q with ⟨x, xs⟩
    change (x, Fin.cons (xs 0) (pointTupleTail xs)) = (x, xs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv q := by
    cases q
    rfl

def splitSuccOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × GHatTupleOutcome params (r + 1)) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.1, og.2 0, gHatTupleOutcomeTail og.2)
  invFun og := (og.1, Fin.cons og.2.1 og.2.2)
  left_inv og := by
    rcases og with ⟨g, gs⟩
    change (g, Fin.cons (gs 0) (gHatTupleOutcomeTail gs)) = (g, gs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv og := by
    cases og
    rfl

def moveTailQuestionEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) where
  toFun q := (q.1, q.2.1, q.2.2 0, pointTupleTail q.2.2)
  invFun q := (q.1, q.2.1, Fin.cons q.2.2.1 q.2.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, xs⟩
    change (x₁, x₂, Fin.cons (xs 0) (pointTupleTail xs)) = (x₁, x₂, xs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv q := by
    cases q
    rfl

def moveTailOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.1, og.2.1, og.2.2 0, gHatTupleOutcomeTail og.2.2)
  invFun og := (og.1, og.2.1, Fin.cons og.2.2.1 og.2.2.2)
  left_inv og := by
    rcases og with ⟨g₁, g₂, gs⟩
    change (g₁, g₂, Fin.cons (gs 0) (gHatTupleOutcomeTail gs)) = (g₁, g₂, gs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv og := by
    cases og
    rfl

def swappedFrontQuestionEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) where
  toFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  invFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl
  right_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl

def swappedFrontOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.2.1, og.1, og.2.2.1, og.2.2.2)
  invFun og := (og.2.1, og.1, og.2.2.1, og.2.2.2)
  left_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl
  right_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl

def moveTailSwappedFrontQuestionEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) :=
  (moveTailQuestionEquiv params r).trans (swappedFrontQuestionEquiv params r)

def moveTailSwappedFrontOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :=
  (moveTailOutcomeEquiv params r).trans (swappedFrontOutcomeEquiv params r)

def firstSliceBackQuestionEquiv (params : Parameters) (r : ℕ) :
    ((SliceQuestion params × SliceQuestion params × PointTuple params r) × SliceQuestion params) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) where
  toFun q := (q.2, q.1.1, q.1.2.1, q.1.2.2)
  invFun q := ((q.2.1, q.2.2.1, q.2.2.2), q.1)
  left_inv q := by
    rcases q with ⟨⟨x₂, x₃, xs⟩, x₁⟩
    rfl
  right_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl

def firstSliceBackOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.2, og.1.1, og.1.2.1, og.1.2.2)
  invFun og := ((og.2.1, og.2.2.1, og.2.2.2), og.1)
  left_inv og := by
    rcases og with ⟨⟨g₂, g₃, gs⟩, g₁⟩
    rfl
  right_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl

noncomputable def commuteGHalfSandwich_moveStepSourceFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).total) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2.2) }

noncomputable def commuteGHalfSandwich_moveStepTargetFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          rightTensor (ι₁ := ι)
            (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2) *
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.2.2.1).total) *
          rightTensor (ι₁ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2.2) }

noncomputable def commuteGHalfSandwich_moveStepMidFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1) *
          rightTensor (ι₁ := ι)
            (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).total) *
          rightTensor (ι₁ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2.2) }

noncomputable def commuteGHalfSandwich_moveSourceFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2) }

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
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepSourceFamily params family r)
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution
          ((SliceQuestion params × SliceQuestion params × PointTuple params r) × SliceQuestion params))
        (fun q => commuteGHalfSandwich_moveSourceFamily params family r q.1)
        (fun q => commuteGHalfSandwich_moveFamily params family r q.1)
        δ :=
    sddOpRel_uniform_fst ψbi
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      δ hAB
  have hABquad :
      SDDOpRel ψbi
        (uniformDistribution
          (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
        (fun q => commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
        (fun q => commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
        δ :=
    (sddOpRel_uniform_equiv (firstSliceBackQuestionEquiv params r) ψbi
      (fun q => commuteGHalfSandwich_moveSourceFamily params family r q.1)
      (fun q => commuteGHalfSandwich_moveFamily params family r q.1)
      δ).1 hABfst
  let C : (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) →
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
          (commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 *
            (commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 *
            (commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2)).outcome ag.1 }
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
              (leftTensor (ι₂ := ι) ((B * G) * gHatHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)) := by
                simp [reindexedSource, rawSource, firstSliceBackOutcomeEquiv, C,
                  commuteGHalfSandwich_moveSourceFamily, A, B, G,
                  leftTensor_mul_leftTensor, mul_assoc]
        _ = (commuteGHalfSandwich_moveStepSourceFamily params family r q).outcome ogs := by
              simp [commuteGHalfSandwich_moveStepSourceFamily, A, B, G,
                gHatHalfProductOutcomeOperator, mul_assoc, leftTensor_mul_leftTensor]
    )
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      calc
        (reindexedTarget q).outcome ogs
          = leftTensor (ι₂ := ι) A * (leftTensor (ι₂ := ι) B * (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T)) := by
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
                _ = (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G) * rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
                      symm
                      calc
                        (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs
                          = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * leftTensor (ι₂ := ι) G) *
                              rightTensor (ι₁ := ι) T := by
                                simp [commuteGHalfSandwich_moveStepMidFamily, A, B, G, T, mul_assoc]
                        _ = (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G) * rightTensor (ι₁ := ι) T := by
                              rw [leftTensor_mul_leftTensor]
                        _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                              rw [leftTensor_mul_leftTensor]
                        _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                              simp [mul_assoc]
    )
    hreindex

end MIPStarRE.LDT.Pasting
