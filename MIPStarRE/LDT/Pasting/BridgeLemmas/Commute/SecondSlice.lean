import MIPStarRE.LDT.Pasting.BridgeLemmas.Commute.RecursiveLift

/-!
# Section 12 pasting: bridge second-slice transport

Second-slice lifting and move-back transport steps for the half-sandwich chain.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma commuteGHalfSandwich_prefixSecondSliceLeftLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (A B : IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r A)
      (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r B)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution ((SliceQuestion params × PointTuple params r) × SliceQuestion params))
        (fun q => A q.1)
        (fun q => B q.1)
        δ :=
    sddOpRel_uniform_fst ψbi A B δ hAB
  have hABtriple :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        (fun q => A (q.1, q.2.2))
        (fun q => B (q.1, q.2.2))
        δ :=
    (sddOpRel_uniform_equiv (splitQuestionEquiv params r) ψbi
      (fun q => A q.1)
      (fun q => B q.1)
      δ).1 hABfst
  let C : (SliceQuestion params × SliceQuestion params × PointTuple params r) →
      (GHatOutcome params × GHatTupleOutcome params r) → GHatOutcome params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ gy => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome gy)
  have hC :
      ∀ q a,
        ∑ gy : GHatOutcome params, (C q a gy)ᴴ * C q a gy ≤ 1 := by
    intro q a
    calc
      ∑ gy : GHatOutcome params, (C q a gy)ᴴ * C q a gy
        = ∑ gy : GHatOutcome params,
            leftTensor (ι₂ := ι)
              ((((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) *
                (gHatIdxMeas params family q.2.1).outcome gy) := by
                  refine Finset.sum_congr rfl ?_
                  intro gy _
                  rw [show (leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome gy))ᴴ =
                      leftTensor (ι₂ := ι) (((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) by
                    simpa [leftTensor, opTensor] using
                      (conjTranspose_opTensor ((gHatIdxMeas params family q.2.1).outcome gy)
                        (1 : MIPStarRE.Quantum.Op ι))]
                  simp [C, leftTensor_mul_leftTensor]
      _ = leftTensor (ι₂ := ι)
            (∑ gy : GHatOutcome params,
              (((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) *
                (gHatIdxMeas params family q.2.1).outcome gy) := by
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ ≤ leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) := by
            simpa using
              opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
                (CommutativityPoints.subMeas_sum_adjoint_mul_le_one
                  ((gHatIdxMeas params family q.2.1).toSubMeas))
                (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one)
      _ = 1 := by simp [leftTensor]
  let rawSource : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (A (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (A (q.1, q.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (B (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (B (q.1, q.2.2)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => A (q.1, q.2.2))
      (fun q => B (q.1, q.2.2))
      C δ hABtriple hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (prefixTripleOutcomeEquiv params r)
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((prefixTripleOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((prefixTripleOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r A)
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r B)
    δ
    (fun q ogs => by
      simp [reindexedSource, rawSource, commuteGHalfSandwich_prefixSecondSliceLeftFamily,
        prefixTripleOutcomeEquiv, C])
    (fun q ogs => by
      simp [reindexedTarget, rawTarget, commuteGHalfSandwich_prefixSecondSliceLeftFamily,
        prefixTripleOutcomeEquiv, C])
    hreindex

noncomputable def commuteGHalfSandwich_secondSliceLiftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).total }

lemma commuteGHalfSandwich_splitSuccLift_moveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_splitSuccLiftFamily params r
      (commuteGHalfSandwich_moveSourceFamily params family r) q).outcome ogs =
      (headTailOrderedFamily params family (r + 1) q).outcome ogs := by
  simpa [commuteGHalfSandwich_splitSuccLiftFamily, splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
    commuteGHalfSandwich_moveSource_eq_split params family r
      ((splitSuccQuestionEquiv params r) q)
      ((splitSuccOutcomeEquiv params r) ogs)

lemma commuteGHalfSandwich_splitSuccLift_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_splitSuccLiftFamily params r
      (commuteGHalfSandwich_recursiveTargetFamily params family r) q).outcome ogs =
      (headTailRotatedFamily params family (r + 1) q).outcome ogs := by
  simpa [commuteGHalfSandwich_splitSuccLiftFamily, splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
    commuteGHalfSandwich_recursiveTarget_eq_split params family r
      ((splitSuccQuestionEquiv params r) q)
      ((splitSuccOutcomeEquiv params r) ogs)

lemma commuteGHalfSandwich_prefixSecondSliceLeftFamily_ordered
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r
      (headTailOrderedFamily params family r) q).outcome ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family r q).outcome ogs := by
  rfl

lemma commuteGHalfSandwich_prefixSecondSliceLeftFamily_rotated
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r
      (headTailRotatedFamily params family r) q).outcome ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs := by
  rfl

lemma commuteGHalfSandwich_secondSliceLift_moveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveSourceFamily params family r) q).outcome ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_secondSliceLiftFamily,
    commuteGHalfSandwich_recursiveSourceFamily, commuteGHalfSandwich_moveSourceFamily,
    headTailOrderedFamily, gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι))
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
      (commuteGHalfSandwich_splitSuccLiftFamily params r F) q).outcome ogs =
      (commuteGHalfSandwich_secondSliceLiftFamily params family r F q).outcome ogs := by
  simp [commuteGHalfSandwich_prefixSecondSliceLeftFamily,
    commuteGHalfSandwich_splitSuccLiftFamily,
    commuteGHalfSandwich_secondSliceLiftFamily,
    splitSuccQuestionEquiv, splitSuccOutcomeEquiv, leftTensor_mul_leftTensor, mul_assoc]

def commuteGHalfSandwich_postMoveFlatLength : ℕ → ℕ
  | 0 => 1
  | r + 1 => commuteGHalfSandwich_postMoveFlatLength r + 2

noncomputable def commuteGHalfSandwich_postMoveFlatFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (r : ℕ) → Fin (commuteGHalfSandwich_postMoveFlatLength r + 1) → IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)
  | 0, i =>
      if i.1 = 0 then
        commuteGHalfSandwich_moveFamily params family 0
      else
        commuteGHalfSandwich_recursiveTargetFamily params family 0
  | r + 1, i =>
      if i.1 = 0 then
        commuteGHalfSandwich_moveFamily params family (r + 1)
      else if i.1 = 1 then
        commuteGHalfSandwich_commuteFamily params family (r + 1)
      else
        commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
          (commuteGHalfSandwich_splitSuccLiftFamily params r
            ((commuteGHalfSandwich_postMoveFlatFamily params family r)
              ⟨i.1 - 2, by
                have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 3 := by
                  simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
                omega⟩))

lemma commuteGHalfSandwich_postMoveFlatLength_pos
    (r : ℕ) :
    1 ≤ commuteGHalfSandwich_postMoveFlatLength r := by
  induction r with
  | zero => simp [commuteGHalfSandwich_postMoveFlatLength]
  | succ r ih =>
      simpa [commuteGHalfSandwich_postMoveFlatLength] using Nat.le_trans (by decide : 1 ≤ 3) ih

noncomputable def commuteGHalfSandwich_postMoveFlatError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) :
    (r : ℕ) → Fin (commuteGHalfSandwich_postMoveFlatLength r) → Error
  | 0, _ => gHatCommutationError params gamma zeta
  | r + 1, i =>
      if hi0 : i.1 = 0 then
        gHatCommutationError params gamma zeta
      else if hi1 : i.1 = 1 then
        gHatSelfConsistencyError zeta
      else
        commuteGHalfSandwich_postMoveFlatError params gamma zeta r
          ⟨i.1 - 2, by
            have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
              simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
            omega⟩

lemma commuteGHalfSandwich_postMoveFlatError_sum
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) :
    ∀ r,
      ∑ i : Fin (commuteGHalfSandwich_postMoveFlatLength r),
        commuteGHalfSandwich_postMoveFlatError params gamma zeta r i =
          (2 : Error) * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta
  | 0 => by
      simp [commuteGHalfSandwich_postMoveFlatLength, commuteGHalfSandwich_postMoveFlatError]
  | r + 1 => by
      have hone_lt : 1 < commuteGHalfSandwich_postMoveFlatLength (r + 1) := by
        simp [commuteGHalfSandwich_postMoveFlatLength, commuteGHalfSandwich_postMoveFlatLength_pos]
      change ∑ i : Fin (commuteGHalfSandwich_postMoveFlatLength r + 2),
        commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1) i = _
      rw [Fin.sum_univ_succ]
      rw [Fin.sum_univ_succ]
      simp [commuteGHalfSandwich_postMoveFlatError,
        commuteGHalfSandwich_postMoveFlatError_sum params gamma zeta r,
        gHatSelfConsistencyError, Nat.mod_eq_of_lt hone_lt]
      ring

def commuteGHalfSandwich_flatChainLength (r : ℕ) : ℕ :=
  r + commuteGHalfSandwich_postMoveFlatLength r

noncomputable def commuteGHalfSandwich_flatChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    Fin (commuteGHalfSandwich_flatChainLength r + 1) → IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)
  | i =>
      if hi : i.1 < r + 1 then
        commuteGHalfSandwich_moveChainFamily params family r ⟨i.1, hi⟩
      else
        commuteGHalfSandwich_postMoveFlatFamily params family r
          ⟨i.1 - r, by
            have hi_lt : i.1 < r + commuteGHalfSandwich_postMoveFlatLength r + 1 := i.2
            omega⟩

noncomputable def commuteGHalfSandwich_flatChainError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) (r : ℕ) :
    Fin (commuteGHalfSandwich_flatChainLength r) → Error
  | i =>
      if hi : i.1 < r then
        gHatSelfConsistencyError zeta
      else
        commuteGHalfSandwich_postMoveFlatError params gamma zeta r
          ⟨i.1 - r, by
            have hi_lt : i.1 < r + commuteGHalfSandwich_postMoveFlatLength r := i.2
            omega⟩

lemma commuteGHalfSandwich_flatChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (r : ℕ) (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_flatChainFamily params family r 0 q).outcome ogs =
      (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs := by
  simp [commuteGHalfSandwich_flatChainFamily,
    commuteGHalfSandwich_moveChainFamily_zero params family r]

lemma commuteGHalfSandwich_flatChainError_sum
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) :
    ∀ r,
      ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
        commuteGHalfSandwich_flatChainError params gamma zeta r i =
          4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta
  | 0 => by
      simp [commuteGHalfSandwich_flatChainLength, commuteGHalfSandwich_flatChainError,
        commuteGHalfSandwich_postMoveFlatError,
        commuteGHalfSandwich_postMoveFlatLength]
  | r + 1 => by
      have hhead : ∀ x : Fin (r + 1), (x : ℕ) ≤ r := by
        intro x
        exact Nat.le_of_lt_succ x.is_lt
      have htail : ∀ x : Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1)),
          ¬ r + 1 + (x : ℕ) ≤ r := by
        intro x
        omega
      change ∑ i : Fin ((r + 1) + commuteGHalfSandwich_postMoveFlatLength (r + 1)),
        commuteGHalfSandwich_flatChainError params gamma zeta (r + 1) i = _
      rw [Fin.sum_univ_add]
      simp [commuteGHalfSandwich_flatChainError,
        commuteGHalfSandwich_postMoveFlatError_sum params gamma zeta (r + 1),
        gHatSelfConsistencyError, hhead, htail]
      ring

lemma commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params 0)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params 0) :
    (commuteGHalfSandwich_commuteFamily params family 0 q).outcome ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family 0 q).outcome ogs := by
  simp [commuteGHalfSandwich_commuteFamily, commuteGHalfSandwich_recursiveTargetFamily,
    headTailRotatedFamily, gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator,
    rightTensor_one,
    gHatRotatedHalfProductOutcomeOperator, leftTensor_mul_leftTensor,
    rightTensor_mul_rightTensor, mul_assoc]

lemma commuteGHalfSandwich_postMoveFlatLength_eq
    (r : ℕ) :
    commuteGHalfSandwich_postMoveFlatLength r = 2 * r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [commuteGHalfSandwich_postMoveFlatLength, ih, Nat.mul_add, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm]

lemma commuteGHalfSandwich_secondSliceLift_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_recursiveTargetFamily params family r) q).outcome ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_secondSliceLiftFamily,
    commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
    gHatHalfProductOutcomeOperator, gHatRotatedHalfProductOutcomeOperator,
    leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_postMoveFlatFamily_zero_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_postMoveFlatFamily params family r 0 q).outcome ogs =
        (commuteGHalfSandwich_moveFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily, commuteGHalfSandwich_moveFamily,
        commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
        gHatHalfProductOutcomeOperator, gHatRotatedHalfProductOutcomeOperator,
        leftTensor_mul_leftTensor, rightTensor_mul_rightTensor, mul_assoc]
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily]

lemma commuteGHalfSandwich_postMoveFlatFamily_one_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
      ⟨1, by
        rw [commuteGHalfSandwich_postMoveFlatLength_eq]
        omega⟩ q).outcome ogs =
      (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_postMoveFlatFamily]

lemma commuteGHalfSandwich_postMoveFlatFamily_last_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_postMoveFlatFamily params family r
          (Fin.last (commuteGHalfSandwich_postMoveFlatLength r)) q).outcome ogs =
        (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily, commuteGHalfSandwich_postMoveFlatLength,
        commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
        commuteGHalfSandwich_moveFamily, gHatHalfProductOutcomeOperator,
        gHatRotatedHalfProductOutcomeOperator, leftTensor_mul_leftTensor,
        rightTensor_mul_rightTensor, mul_assoc]
  | r + 1, q, ogs => by
      let q' : SliceQuestion params × PointTuple params (r + 1) := (q.1, q.2.2)
      let ogs' : GHatOutcome params × GHatTupleOutcome params (r + 1) := (ogs.1, ogs.2.2)
      let q'' : SliceQuestion params × SliceQuestion params × PointTuple params r :=
        (splitSuccQuestionEquiv params r) q'
      let ogs'' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r :=
        (splitSuccOutcomeEquiv params r) ogs'
      have hsmall :
          (commuteGHalfSandwich_postMoveFlatFamily params family r
              (Fin.last (commuteGHalfSandwich_postMoveFlatLength r)) q'').outcome ogs'' =
            (commuteGHalfSandwich_recursiveTargetFamily params family r
              q'').outcome ogs'' := by
        simpa using commuteGHalfSandwich_postMoveFlatFamily_last_active params family r
          q'' ogs''
      have hsmall' :
          (commuteGHalfSandwich_postMoveFlatFamily params family r
              ⟨2 * (r + 1) - 1, by
                rw [commuteGHalfSandwich_postMoveFlatLength_eq]
                omega⟩ q'').outcome ogs'' =
            (commuteGHalfSandwich_recursiveTargetFamily params family r q'').outcome ogs'' := by
        have hlast_idx :
            (⟨2 * (r + 1) - 1, by
                have hlt : 2 * (r + 1) - 1 < commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                  rw [commuteGHalfSandwich_postMoveFlatLength_eq]
                  omega
                exact hlt⟩ : Fin (commuteGHalfSandwich_postMoveFlatLength r + 1)) =
              Fin.last (commuteGHalfSandwich_postMoveFlatLength r) := by
          ext
          simp [Fin.last, commuteGHalfSandwich_postMoveFlatLength_eq, Nat.mul_add, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm]
        simpa [hlast_idx] using hsmall
      calc
        (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
            (Fin.last (commuteGHalfSandwich_postMoveFlatLength (r + 1))) q).outcome ogs
          = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
              (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_postMoveFlatFamily params family r
                  ⟨2 * (r + 1) - 1, by
                    have hlt : 2 * (r + 1) - 1 < commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                      rw [commuteGHalfSandwich_postMoveFlatLength_eq]
                      omega
                    exact hlt⟩)) q).outcome ogs := by
                simp [commuteGHalfSandwich_postMoveFlatFamily, commuteGHalfSandwich_postMoveFlatLength_eq]
        _ = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
              (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_recursiveTargetFamily params family r)) q).outcome ogs := by
                change leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                    ((commuteGHalfSandwich_postMoveFlatFamily params family r
                        ⟨2 * (r + 1) - 1, by
                          have hlt : 2 * (r + 1) - 1 < commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                            rw [commuteGHalfSandwich_postMoveFlatLength_eq]
                            omega
                          exact hlt⟩ q'').outcome ogs'') =
                  leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                    ((commuteGHalfSandwich_recursiveTargetFamily params family r q'').outcome ogs'')
                exact congrArg
                  (fun X => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) * X)
                  hsmall'
        _ = (commuteGHalfSandwich_recursiveTargetFamily params family (r + 1) q).outcome ogs := by
              exact (commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift params family r
                (commuteGHalfSandwich_recursiveTargetFamily params family r) q ogs).trans
                  (commuteGHalfSandwich_secondSliceLift_recursiveTarget params family r q ogs)

lemma commuteGHalfSandwich_flatChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (r : ℕ) (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_flatChainFamily params family r
      (Fin.last (commuteGHalfSandwich_flatChainLength r)) q).outcome ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs := by
  have hnot : ¬ (commuteGHalfSandwich_flatChainLength r : ℕ) < r + 1 := by
    unfold commuteGHalfSandwich_flatChainLength
    rw [commuteGHalfSandwich_postMoveFlatLength_eq]
    omega
  have hidx :
      (⟨commuteGHalfSandwich_flatChainLength r - r, by
          unfold commuteGHalfSandwich_flatChainLength
          rw [commuteGHalfSandwich_postMoveFlatLength_eq]
          omega⟩ : Fin (commuteGHalfSandwich_postMoveFlatLength r + 1)) =
        Fin.last (commuteGHalfSandwich_postMoveFlatLength r) := by
    ext
    simp [Fin.last, commuteGHalfSandwich_flatChainLength,
      commuteGHalfSandwich_postMoveFlatLength_eq]
  calc
    (commuteGHalfSandwich_flatChainFamily params family r
        (Fin.last (commuteGHalfSandwich_flatChainLength r)) q).outcome ogs
      = (commuteGHalfSandwich_postMoveFlatFamily params family r
          (Fin.last (commuteGHalfSandwich_postMoveFlatLength r)) q).outcome ogs := by
            simp [commuteGHalfSandwich_flatChainFamily, hnot, hidx]
    _ = (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs := by
          exact commuteGHalfSandwich_postMoveFlatFamily_last_active params family r q ogs

lemma commuteGHalfSandwich_secondSliceLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (A B : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_secondSliceLiftFamily params family r A)
      (commuteGHalfSandwich_secondSliceLiftFamily params family r B)
      δ := by
  let eQ :
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) ≃
        (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) :=
    { toFun := fun q => (q.2.1, q.1, q.2.2)
      invFun := fun q => (q.2.1, q.1, q.2.2)
      left_inv := by
        intro q
        rcases q with ⟨x₁, x₂, xs⟩
        rfl
      right_inv := by
        intro q
        rcases q with ⟨x₁, x₂, xs⟩
        rfl }
  let eO :
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) ≃
        (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :=
    { toFun := fun ogs => (ogs.2.1, ogs.1, ogs.2.2)
      invFun := fun ogs => (ogs.2.1, ogs.1, ogs.2.2)
      left_inv := by
        intro ogs
        rcases ogs with ⟨g₁, g₂, gs⟩
        rfl
      right_inv := by
        intro ogs
        rcases ogs with ⟨g₁, g₂, gs⟩
        rfl }
  have hlift :=
    commuteGHalfSandwich_moveChainLift params ψbi family r A B δ hAB
  have hswapQ :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (fun q =>
          commuteGHalfSandwich_moveChainLiftFamily params family r A (eQ.symm q))
        (fun q =>
          commuteGHalfSandwich_moveChainLiftFamily params family r B (eQ.symm q))
        δ :=
    (sddOpRel_uniform_equiv eQ ψbi
      (commuteGHalfSandwich_moveChainLiftFamily params family r A)
      (commuteGHalfSandwich_moveChainLiftFamily params family r B)
      δ).1 hlift
  have hreindex := CommutativityPoints.sddOpRel_reindex eO
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    (fun q =>
      commuteGHalfSandwich_moveChainLiftFamily params family r A (eQ.symm q))
    (fun q =>
      commuteGHalfSandwich_moveChainLiftFamily params family r B (eQ.symm q))
    δ hswapQ
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    _ _
    (commuteGHalfSandwich_secondSliceLiftFamily params family r A)
    (commuteGHalfSandwich_secondSliceLiftFamily params family r B)
    δ
    (fun q ogs => by
      simp [eQ, eO, commuteGHalfSandwich_moveChainLiftFamily,
        commuteGHalfSandwich_secondSliceLiftFamily])
    (fun q ogs => by
      simp [eQ, eO, commuteGHalfSandwich_moveChainLiftFamily,
        commuteGHalfSandwich_secondSliceLiftFamily])
    hreindex

noncomputable def commuteGHalfSandwich_moveBackChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    Fin (r + 1) → IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι)
  | i =>
      commuteGHalfSandwich_secondSliceLiftFamily params family r
        ((commuteGHalfSandwich_moveChainFamily params family r)
          ⟨r - i.1, by omega⟩)

lemma commuteGHalfSandwich_moveBackChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_moveBackChainFamily params family r (Fin.last r) q).outcome ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
  let q' : SliceQuestion params × SliceQuestion params × PointTuple params r :=
    (q.1, q.2.2 0, pointTupleTail q.2.2)
  let ogs' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r :=
    (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
  have hzero :
      (commuteGHalfSandwich_secondSliceLiftFamily params family r
        ((commuteGHalfSandwich_moveChainFamily params family r) 0) q).outcome ogs =
        (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
    calc
      (commuteGHalfSandwich_secondSliceLiftFamily params family r
        ((commuteGHalfSandwich_moveChainFamily params family r) 0) q).outcome ogs
        = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
            (commuteGHalfSandwich_moveSourceFamily params family r q').outcome ogs' := by
              simpa [commuteGHalfSandwich_secondSliceLiftFamily, q', ogs'] using
                congrArg
                  (fun X =>
                    leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) * X)
                  (commuteGHalfSandwich_moveChainFamily_zero params family r q' ogs')
      _ = (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
            exact commuteGHalfSandwich_secondSliceLift_moveSource params family r q ogs
  simpa [commuteGHalfSandwich_moveBackChainFamily] using hzero

lemma commuteGHalfSandwich_secondSliceLift_moveFamily_eq_swappedFrontMoveStepMid
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs =
      (commuteGHalfSandwich_moveStepMidFamily params family r
        ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
        ((moveTailSwappedFrontOutcomeEquiv params r) ogs) := by
  let A := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let B := (gHatIdxMeas params family q.1).outcome ogs.1
  let G := (gHatIdxMeas params family (q.2.2 0)).outcome (ogs.2.2 0)
  let T := gHatReverseHalfProductOutcomeOperator params family r
    (pointTupleTail q.2.2) (gHatTupleOutcomeTail ogs.2.2)
  calc
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs
      = leftTensor (ι₂ := ι) A *
          (leftTensor (ι₂ := ι) (B * G) * rightTensor (ι₁ := ι) T) := by
            simp [commuteGHalfSandwich_secondSliceLiftFamily, commuteGHalfSandwich_moveFamily,
              A, B, G, T, leftTensor_mul_leftTensor, mul_assoc]
    _ = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (B * G)) * rightTensor (ι₁ := ι) T := by
          simp [mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
          rw [leftTensor_mul_leftTensor]
    _ = (commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
          ((moveTailSwappedFrontOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepMidFamily,
              moveTailSwappedFrontQuestionEquiv, moveTailSwappedFrontOutcomeEquiv,
              moveTailQuestionEquiv, moveTailOutcomeEquiv,
              swappedFrontQuestionEquiv, swappedFrontOutcomeEquiv,
              A, B, G, T, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_commute_eq_swappedFrontMoveStepTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs =
      (commuteGHalfSandwich_moveStepTargetFamily params family r
        ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
        ((moveTailSwappedFrontOutcomeEquiv params r) ogs) := by
  simp [commuteGHalfSandwich_commuteFamily,
    moveTailSwappedFrontQuestionEquiv, moveTailSwappedFrontOutcomeEquiv,
    moveTailQuestionEquiv, moveTailOutcomeEquiv,
    swappedFrontQuestionEquiv, swappedFrontOutcomeEquiv,
    commuteGHalfSandwich_moveStepTargetFamily,
    gHatReverseHalfProductOutcomeOperator, leftTensor_mul_leftTensor,
    rightTensor_mul_rightTensor, mul_assoc]

lemma commuteGHalfSandwich_moveBackChain_step
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    ∀ i : Fin r,
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.succ)
        (gHatSelfConsistencyError zeta)
  | i => by
      let j : Fin r := ⟨r - i.1 - 1, by omega⟩
      have hstep := commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc r j
      have hlift := commuteGHalfSandwich_secondSliceLift params ψbi family r
        ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc)
        ((commuteGHalfSandwich_moveChainFamily params family r) j.succ)
        (gHatSelfConsistencyError zeta)
        hstep
      have hsymm := Preliminaries.sddOpRel_symm ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.succ))
        (gHatSelfConsistencyError zeta)
        hlift
      have hsrc : (⟨r - i.1, by omega⟩ : Fin (r + 1)) = j.succ := by
        apply Fin.ext
        dsimp [j]
        omega
      have htgt : (⟨r - (i.1 + 1), by omega⟩ : Fin (r + 1)) = j.castSucc := by
        apply Fin.ext
        dsimp [j]
        omega
      exact CommutativityPoints.sddOpRel_congr_outcome ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.succ))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc))
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.succ)
        (gHatSelfConsistencyError zeta)
        (fun q ogs => by
          simpa [commuteGHalfSandwich_moveBackChainFamily, j, hsrc])
        (fun q ogs => by
          simpa [commuteGHalfSandwich_moveBackChainFamily, j, htgt])
        hsymm

lemma commuteGHalfSandwich_commute_to_moveBackChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) {r : ℕ}
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_commuteFamily params family (r + 1))
      ((commuteGHalfSandwich_moveBackChainFamily params family r) 0)
      (gHatSelfConsistencyError zeta) := by
  have htargetMid :
      SDDOpRel ψbi
        (uniformDistribution
          (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
        (commuteGHalfSandwich_moveStepTargetFamily params family r)
        (commuteGHalfSandwich_moveStepMidFamily params family r)
        (gHatSelfConsistencyError zeta) :=
    Preliminaries.sddOpRel_symm ψbi
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      (commuteGHalfSandwich_moveStepTargetFamily params family r)
      (gHatSelfConsistencyError zeta)
      (commuteGHalfSandwich_moveStepMid_toTarget params ψbi family zeta r hsc)
  have hq :=
    (sddOpRel_uniform_equiv (moveTailSwappedFrontQuestionEquiv params r).symm ψbi
      (commuteGHalfSandwich_moveStepTargetFamily params family r)
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      (gHatSelfConsistencyError zeta)).1 htargetMid
  have ho := CommutativityPoints.sddOpRel_reindex (moveTailSwappedFrontOutcomeEquiv params r).symm
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
      ((moveTailSwappedFrontQuestionEquiv params r) q))
    (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
      ((moveTailSwappedFrontQuestionEquiv params r) q))
    (gHatSelfConsistencyError zeta)
    hq
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    _ _
    (commuteGHalfSandwich_commuteFamily params family (r + 1))
    ((commuteGHalfSandwich_moveBackChainFamily params family r) 0)
    (gHatSelfConsistencyError zeta)
    (fun q ogs => by
      simpa using
        (commuteGHalfSandwich_commute_eq_swappedFrontMoveStepTarget params family r q ogs).symm)
    (fun q ogs => by
      let q' : SliceQuestion params × SliceQuestion params × PointTuple params r :=
        (q.1, q.2.2 0, pointTupleTail q.2.2)
      let ogs' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r :=
        (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      have hlast :
          (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs =
            (commuteGHalfSandwich_secondSliceLiftFamily params family r
              (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
        calc
          (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs
            = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                (commuteGHalfSandwich_moveFamily params family r q').outcome ogs' := by
                  simpa [commuteGHalfSandwich_moveBackChainFamily, q', ogs'] using
                    congrArg
                      (fun X =>
                        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) * X)
                      (commuteGHalfSandwich_moveChainFamily_last params family r q' ogs')
          _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
                rfl
      calc
        (commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
          ((moveTailSwappedFrontOutcomeEquiv params r) ogs)
            = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
                  exact (commuteGHalfSandwich_secondSliceLift_moveFamily_eq_swappedFrontMoveStepMid
                    params family r q ogs).symm
        _ = (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs := by
              simpa using hlast.symm)
    ho

lemma commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs =
      (commuteGHalfSandwich_secondSliceLiftFamily params family r
        (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
  let q' : SliceQuestion params × SliceQuestion params × PointTuple params r :=
    (q.1, q.2.2 0, pointTupleTail q.2.2)
  let ogs' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r :=
    (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
  calc
    (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs
      = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (commuteGHalfSandwich_moveFamily params family r q').outcome ogs' := by
            simpa [commuteGHalfSandwich_moveBackChainFamily, q', ogs'] using
              congrArg
                (fun X => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) * X)
                (commuteGHalfSandwich_moveChainFamily_last params family r q' ogs')
    _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
          (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
            rfl

end MIPStarRE.LDT.Pasting
