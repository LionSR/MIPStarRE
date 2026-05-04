import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.Base

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ## Lifting families for the half-sandwich chain

Lifting constructions: swapped-front equivalences, `splitSuccLiftFamily`,
`prefixSecondSliceLeftFamily`, `secondSliceLiftFamily`, and the
`moveChainLift` construction that lifts an `r`-step chain to `r+1`.
-/
def swappedFrontQuestionEquiv (params : Parameters) (r : ℕ) :
    (MoveTailQ params r) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params ×
          PointTuple params r) where
  toFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  invFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl
  right_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl

def swappedFrontOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (MoveTailO params r) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
          GHatTupleOutcome params r) where
  toFun og := (og.2.1, og.1, og.2.2.1, og.2.2.2)
  invFun og := (og.2.1, og.1, og.2.2.1, og.2.2.2)
  left_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl
  right_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl

def moveTailSwappedFrontQuestionEquiv (params : Parameters) (r : ℕ) :
    (MoveQ params (r + 1)) ≃
      (MoveTailQ params r) :=
  (moveTailQuestionEquiv params r).trans (swappedFrontQuestionEquiv params r)

def moveTailSwappedFrontOutcomeEquiv
    (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (MoveO params (r + 1)) ≃
      (MoveTailO params r) :=
  (moveTailOutcomeEquiv params r).trans (swappedFrontOutcomeEquiv params r)

noncomputable def commuteGHalfSandwich_splitSuccLiftFamily
    (params : Parameters) [FieldModel params.q]
    (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        (F ((splitSuccQuestionEquiv params r) q)).outcome ((splitSuccOutcomeEquiv params r) ogs)
      total := (F ((splitSuccQuestionEquiv params r) q)).total }

noncomputable def commuteGHalfSandwich_prefixSecondSliceLeftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)) :
    IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          (F (q.1, q.2.2)).total }

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
      (uniformDistribution (MoveQ params r))
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
        (uniformDistribution (MoveQ params r))
        (fun q => A (q.1, q.2.2))
        (fun q => B (q.1, q.2.2))
        δ :=
    (sddOpRel_uniform_equiv (splitQuestionEquiv params r) ψbi
      (fun q => A q.1)
      (fun q => B q.1)
      δ).1 hABfst
  let C : (MoveQ params r) →
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
                  rw [show
                      (leftTensor (ι₂ := ι)
                        ((gHatIdxMeas params family q.2.1).outcome gy))ᴴ =
                        leftTensor (ι₂ := ι)
                          (show MIPStarRE.Quantum.Op ι from
                            ((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) by
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
  let rawSource : IdxOpFamily (MoveQ params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (A (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (A (q.1, q.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily (MoveQ params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (B (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (B (q.1, q.2.2)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (MoveQ params r))
      (fun q => A (q.1, q.2.2))
      (fun q => B (q.1, q.2.2))
      C δ hABtriple hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (prefixTripleOutcomeEquiv params r)
    ψbi
    (uniformDistribution (MoveQ params r))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily (SliceQuestion params × SliceQuestion params ×
      PointTuple params r)
      (MoveO params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((prefixTripleOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params ×
      PointTuple params r)
      (MoveO params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((prefixTripleOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (MoveQ params r))
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

lemma commuteGHalfSandwich_splitSuccLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (r : ℕ)
    (A B : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (MoveQ params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_splitSuccLiftFamily params r A)
      (commuteGHalfSandwich_splitSuccLiftFamily params r B)
      δ := by
  let A' : IdxOpFamily
      (MoveQ params r)
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun ogs => A q |>.outcome ((splitSuccOutcomeEquiv params r) ogs)
        total := (A q).total }
  let B' : IdxOpFamily
      (MoveQ params r)
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun ogs => B q |>.outcome ((splitSuccOutcomeEquiv params r) ogs)
        total := (B q).total }
  have ho := CommutativityPoints.sddOpRel_reindex (splitSuccOutcomeEquiv params r).symm
    ψbi
    (uniformDistribution (MoveQ params r))
    A B δ hAB
  have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (MoveQ params r))
    _ _
    A' B'
    δ
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    ho
  let A'' : IdxOpFamily
      (SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q => A' ((splitSuccQuestionEquiv params r) q)
  let B'' : IdxOpFamily
      (SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q => B' ((splitSuccQuestionEquiv params r) q)
  have hsplit :=
    (sddOpRel_uniform_equiv (splitSuccQuestionEquiv params r) ψbi A'' B'' δ).2 hq
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
    A'' B''
    (commuteGHalfSandwich_splitSuccLiftFamily params r A)
    (commuteGHalfSandwich_splitSuccLiftFamily params r B)
    δ
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    hsplit

lemma commuteGHalfSandwich_splitSuccLift_moveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_splitSuccLiftFamily params r
      (commuteGHalfSandwich_moveSourceFamily params family r) q).outcome
        ogs =
      (headTailOrderedFamily params family (r + 1) q).outcome ogs := by
  simpa [commuteGHalfSandwich_splitSuccLiftFamily, splitSuccQuestionEquiv,
      splitSuccOutcomeEquiv] using
    commuteGHalfSandwich_moveSource_eq_split params family r
      ((splitSuccQuestionEquiv params r) q)
      ((splitSuccOutcomeEquiv params r) ogs)

noncomputable def commuteGHalfSandwich_secondSliceLiftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)) :
    IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).total }

lemma commuteGHalfSandwich_secondSliceLift_moveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveSourceFamily params family r) q).outcome
        ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_secondSliceLiftFamily,
    commuteGHalfSandwich_recursiveSourceFamily, commuteGHalfSandwich_moveSourceFamily,
    headTailOrderedFamily, gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι))
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
      (commuteGHalfSandwich_splitSuccLiftFamily params r F) q).outcome
        ogs =
      (commuteGHalfSandwich_secondSliceLiftFamily params family r F q).outcome ogs := by
  simp [commuteGHalfSandwich_prefixSecondSliceLeftFamily,
    commuteGHalfSandwich_splitSuccLiftFamily,
    commuteGHalfSandwich_secondSliceLiftFamily,
    splitSuccQuestionEquiv, splitSuccOutcomeEquiv]

lemma commuteGHalfSandwich_moveFamily_eq_moveStepTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome
      ogs =
      (commuteGHalfSandwich_moveStepTargetFamily params family r
        ((moveTailQuestionEquiv params r) q)).outcome
        ((moveTailOutcomeEquiv params r) ogs) := by
  let A := (gHatIdxMeas params family q.1).outcome ogs.1
  let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let T := gHatReverseHalfProductOutcomeOperator params family r
    (pointTupleTail q.2.2) (gHatTupleOutcomeTail ogs.2.2)
  let G := (gHatIdxMeas params family (q.2.2 0)).outcome (ogs.2.2 0)
  calc
    (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs
      = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
          rightTensor (ι₁ := ι) (T * G) := by
          simp [commuteGHalfSandwich_moveFamily,
            A, B, T, G, gHatReverseHalfProductOutcomeOperator, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
          (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
            rw [rightTensor_mul_rightTensor]
    _ = (commuteGHalfSandwich_moveStepTargetFamily params family r
          ((moveTailQuestionEquiv params r) q)).outcome
          ((moveTailOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepTargetFamily, moveTailQuestionEquiv,
              moveTailOutcomeEquiv, A, B, T, G, mul_assoc]

def commuteGHalfSandwich_moveChainLiftQuestionEquiv (params : Parameters) (r : ℕ) :
    ((MoveQ params r) × SliceQuestion params) ≃
      (MoveQ params (r + 1)) :=
  (firstSliceBackQuestionEquiv params r).trans (moveTailQuestionEquiv params r).symm

def commuteGHalfSandwich_moveChainLiftOutcomeEquiv
    (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((MoveO params r) × GHatOutcome params) ≃
      (MoveO params (r + 1)) :=
  (firstSliceBackOutcomeEquiv params r).trans (moveTailOutcomeEquiv params r).symm

noncomputable def commuteGHalfSandwich_moveChainLiftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)) :
    IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          (F (q.2.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.2.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          (F (q.2.1, q.2.2 0, pointTupleTail q.2.2)).total }

lemma commuteGHalfSandwich_moveChainLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (A B : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (MoveQ params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (MoveQ params (r + 1)))
      (commuteGHalfSandwich_moveChainLiftFamily params family r A)
      (commuteGHalfSandwich_moveChainLiftFamily params family r B)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution (MoveQ params r × SliceQuestion params))
        (fun q => A q.1)
        (fun q => B q.1)
        δ :=
    sddOpRel_uniform_fst ψbi A B δ hAB
  have hABlift :
      SDDOpRel ψbi
        (uniformDistribution (MoveQ params (r + 1)))
        (fun q => A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
        (fun q => B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
        δ :=
    (sddOpRel_uniform_equiv (commuteGHalfSandwich_moveChainLiftQuestionEquiv params r) ψbi
      (fun q => A q.1)
      (fun q => B q.1)
      δ).1 hABfst
  let C : (MoveQ params (r + 1)) →
      (MoveO params r) → GHatOutcome params →
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
                  rw [show
                      (leftTensor (ι₂ := ι)
                        ((gHatIdxMeas params family q.1).outcome g₁))ᴴ =
                        leftTensor (ι₂ := ι)
                        (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) by
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
            exact leftTensor_le_one (ι₂ := ι) (A := _) hinner
  let rawSource : IdxOpFamily
      (MoveQ params (r + 1))
      ((MoveO params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1
        total := ∑ ag :
          ((MoveO params r) ×
              GHatOutcome params),
          C q ag.1 ag.2 *
            (A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome
                ag.1 }
  let rawTarget : IdxOpFamily
      (MoveQ params (r + 1))
      ((MoveO params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1
        total := ∑ ag :
          ((MoveO params r) ×
              GHatOutcome params),
          C q ag.1 ag.2 *
            (B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome
                ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (MoveQ params (r + 1)))
      (fun q => A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
      (fun q => B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
      C δ hABlift hC
  have hreindex := CommutativityPoints.sddOpRel_reindex
    (commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r)
    ψbi
    (uniformDistribution (MoveQ params (r + 1)))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun a' =>
          (rawSource q).outcome ((commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun a' =>
          (rawTarget q).outcome ((commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (MoveQ params (r + 1)))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveChainLiftFamily params family r A)
    (commuteGHalfSandwich_moveChainLiftFamily params family r B)
    δ
    (fun q ogs => by
      simp [reindexedSource, rawSource, commuteGHalfSandwich_moveChainLiftOutcomeEquiv,
        commuteGHalfSandwich_moveChainLiftQuestionEquiv, C,
        commuteGHalfSandwich_moveChainLiftFamily, moveTailQuestionEquiv, moveTailOutcomeEquiv,
        firstSliceBackQuestionEquiv, firstSliceBackOutcomeEquiv])
    (fun q ogs => by
      simp [reindexedTarget, rawTarget, commuteGHalfSandwich_moveChainLiftOutcomeEquiv,
        commuteGHalfSandwich_moveChainLiftQuestionEquiv, C,
        commuteGHalfSandwich_moveChainLiftFamily, moveTailQuestionEquiv, moveTailOutcomeEquiv,
        firstSliceBackQuestionEquiv, firstSliceBackOutcomeEquiv])
    hreindex

lemma commuteGHalfSandwich_moveChainLift_moveFamily_eq_moveStepMid
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveChainLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome
        ogs =
      (commuteGHalfSandwich_moveStepMidFamily params family r
        ((moveTailQuestionEquiv params r) q)).outcome
        ((moveTailOutcomeEquiv params r) ogs) := by
  let A := (gHatIdxMeas params family q.1).outcome ogs.1
  let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let G := (gHatIdxMeas params family (q.2.2 0)).outcome (ogs.2.2 0)
  let T := gHatReverseHalfProductOutcomeOperator params family r
    (pointTupleTail q.2.2) (gHatTupleOutcomeTail ogs.2.2)
  calc
    (commuteGHalfSandwich_moveChainLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs
      = leftTensor (ι₂ := ι) A *
          (leftTensor (ι₂ := ι) (B * G) * rightTensor (ι₁ := ι) T) := by
            simp [commuteGHalfSandwich_moveChainLiftFamily, commuteGHalfSandwich_moveFamily,
              A, B, G, T,
              leftTensor_mul_leftTensor]
    _ =
        (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (B * G)) *
          rightTensor (ι₁ := ι) T := by
          simp [mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
          rw [leftTensor_mul_leftTensor]
    _ = (commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailQuestionEquiv params r) q)).outcome
          ((moveTailOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepMidFamily, moveTailQuestionEquiv,
              moveTailOutcomeEquiv, A, B, G, T, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_moveChainLift_moveFamily_last
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
      (uniformDistribution (MoveQ params (r + 1)))
      (commuteGHalfSandwich_moveChainLiftFamily params family r
        (commuteGHalfSandwich_moveFamily params family r))
      (commuteGHalfSandwich_moveFamily params family (r + 1))
      (gHatSelfConsistencyError zeta) := by
  have hmid :
      SDDOpRel ψbi
        (uniformDistribution (MoveQ params (r + 1)))
        (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailQuestionEquiv params r) q))
        (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
          ((moveTailQuestionEquiv params r) q))
        (gHatSelfConsistencyError zeta) :=
    (sddOpRel_uniform_equiv (moveTailQuestionEquiv params r) ψbi
      (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
        ((moveTailQuestionEquiv params r) q))
      (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
        ((moveTailQuestionEquiv params r) q))
      (gHatSelfConsistencyError zeta)).2
      (commuteGHalfSandwich_moveStepMid_toTarget params ψbi family zeta r hsc)
  have hreindex := CommutativityPoints.sddOpRel_reindex (moveTailOutcomeEquiv params r).symm
    ψbi
    (uniformDistribution (MoveQ params (r + 1)))
    (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
      ((moveTailQuestionEquiv params r) q))
    (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
      ((moveTailQuestionEquiv params r) q))
    (gHatSelfConsistencyError zeta)
    hmid
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (MoveQ params (r + 1)))
    _ _
    (commuteGHalfSandwich_moveChainLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r))
    (commuteGHalfSandwich_moveFamily params family (r + 1))
    (gHatSelfConsistencyError zeta)
    (fun q ogs => by
      simpa [moveTailQuestionEquiv, moveTailOutcomeEquiv] using
        (commuteGHalfSandwich_moveChainLift_moveFamily_eq_moveStepMid params family r q ogs).symm)
    (fun q ogs => by
      simpa [moveTailQuestionEquiv, moveTailOutcomeEquiv] using
        (commuteGHalfSandwich_moveFamily_eq_moveStepTarget params family r q ogs).symm)
    hreindex



end MIPStarRE.LDT.Pasting
