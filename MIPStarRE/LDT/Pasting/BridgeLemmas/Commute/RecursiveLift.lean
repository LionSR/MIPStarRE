import MIPStarRE.LDT.Pasting.BridgeLemmas.Commute.MoveToTarget

/-!
# Section 12 pasting: bridge recursive lift

Recursive lift machinery that turns local commute stages into the inductive split form.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def commuteGHalfSandwich_recursiveSourceFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (headTailOrderedFamily params family r (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total := 0 }

noncomputable def commuteGHalfSandwich_recursiveTargetFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (headTailRotatedFamily params family r (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total := 0 }

lemma commuteGHalfSandwich_moveBack_eq_recursiveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_moveBackFamily params family r q).outcome ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family r q).outcome ogs := by
  simp [commuteGHalfSandwich_moveBackFamily, commuteGHalfSandwich_recursiveSourceFamily,
    headTailOrderedFamily, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_recursiveTarget_eq_split
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs =
      (headTailRotatedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
        (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
  let A := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let T := gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
  let G := (gHatIdxMeas params family q.1).outcome ogs.1
  have htail :
      T = gHatHalfProductOutcomeOperator params family r
        (pointTupleTail (Fin.cons q.2.1 q.2.2))
        (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)) := by
    rfl
  calc
    (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs
      = leftTensor (ι₂ := ι) (A * (T * G)) := by
          simp [commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
            A, T, G, leftTensor_mul_leftTensor, mul_assoc]
    _ = leftTensor (ι₂ := ι)
          (A * (gHatHalfProductOutcomeOperator params family r
            (pointTupleTail (Fin.cons q.2.1 q.2.2))
            (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)) * G)) := by
              exact congrArg (fun X => leftTensor (ι₂ := ι) (A * (X * G))) htail.symm
    _ = (headTailRotatedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
          (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
            simp [headTailRotatedFamily, A, G, gHatHalfProductOutcomeOperator,
              gHatRotatedHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_moveSource_eq_moveStepSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_moveSourceFamily params family (r + 1) q).outcome ogs =
      (commuteGHalfSandwich_moveStepSourceFamily params family r
        ((moveTailQuestionEquiv params r) q)).outcome
        ((moveTailOutcomeEquiv params r) ogs) := by
  simp [moveTailQuestionEquiv, moveTailOutcomeEquiv,
    commuteGHalfSandwich_moveSourceFamily, commuteGHalfSandwich_moveStepSourceFamily,
    gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_moveFamily_eq_moveStepTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs =
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
      = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) (T * G) := by
          simp [commuteGHalfSandwich_moveFamily, moveTailQuestionEquiv, moveTailOutcomeEquiv,
            A, B, T, G, gHatReverseHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]
    _ = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
          (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
            rw [rightTensor_mul_rightTensor]
    _ = (commuteGHalfSandwich_moveStepTargetFamily params family r
          ((moveTailQuestionEquiv params r) q)).outcome
          ((moveTailOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepTargetFamily, moveTailQuestionEquiv,
              moveTailOutcomeEquiv, A, B, T, G, mul_assoc]

def commuteGHalfSandwich_moveChainLiftQuestionEquiv (params : Parameters) (r : ℕ) :
    ((SliceQuestion params × SliceQuestion params × PointTuple params r) × SliceQuestion params) ≃
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) :=
  (firstSliceBackQuestionEquiv params r).trans (moveTailQuestionEquiv params r).symm

def commuteGHalfSandwich_moveChainLiftOutcomeEquiv
    (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :=
  (firstSliceBackOutcomeEquiv params r).trans (moveTailOutcomeEquiv params r).symm

noncomputable def commuteGHalfSandwich_moveChainLiftFamily
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
      (commuteGHalfSandwich_moveChainLiftFamily params family r A)
      (commuteGHalfSandwich_moveChainLiftFamily params family r B)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution
          (((SliceQuestion params × SliceQuestion params × PointTuple params r)) ×
            SliceQuestion params))
        (fun q => A q.1)
        (fun q => B q.1)
        δ :=
    sddOpRel_uniform_fst ψbi A B δ hAB
  have hABlift :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (fun q => A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
        (fun q => B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
        δ :=
    (sddOpRel_uniform_equiv (commuteGHalfSandwich_moveChainLiftQuestionEquiv params r) ψbi
      (fun q => A q.1)
      (fun q => B q.1)
      δ).1 hABfst
  let C : (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) →
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
            exact leftTensor_le_one (ι₂ := ι) (A := _) hinner
  let rawSource : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1
        total := ∑ ag :
          ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params),
          C q ag.1 ag.2 *
            (A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1 }
  let rawTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1
        total := ∑ ag :
          ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params),
          C q ag.1 ag.2 *
            (B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
      (fun q => A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
      (fun q => B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
      C δ hABlift hC
  have hreindex := CommutativityPoints.sddOpRel_reindex
    (commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r)
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun a' =>
          (rawSource q).outcome ((commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun a' =>
          (rawTarget q).outcome ((commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
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
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_moveChainLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs =
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
              A, B, G, T, gHatReverseHalfProductOutcomeOperator,
              leftTensor_mul_leftTensor, mul_assoc]
    _ = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (B * G)) * rightTensor (ι₁ := ι) T := by
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
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_moveChainLiftFamily params family r
        (commuteGHalfSandwich_moveFamily params family r))
      (commuteGHalfSandwich_moveFamily params family (r + 1))
      (gHatSelfConsistencyError zeta) := by
  have hmid :
      SDDOpRel ψbi
        (uniformDistribution
          (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
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
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
      ((moveTailQuestionEquiv params r) q))
    (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
      ((moveTailQuestionEquiv params r) q))
    (gHatSelfConsistencyError zeta)
    hmid
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
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

noncomputable def commuteGHalfSandwich_moveChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (r : ℕ) → Fin (r + 1) → IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)
  | 0, _ => commuteGHalfSandwich_moveSourceFamily params family 0
  | r + 1, i =>
      if hi : i.1 < r + 1 then
        commuteGHalfSandwich_moveChainLiftFamily params family r
          (commuteGHalfSandwich_moveChainFamily params family r ⟨i.1, hi⟩)
      else
        commuteGHalfSandwich_moveFamily params family (r + 1)

lemma commuteGHalfSandwich_moveChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_moveChainFamily params family r 0 q).outcome ogs =
        (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs
  | 0, q, ogs => by rfl
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily, commuteGHalfSandwich_moveChainLiftFamily,
        commuteGHalfSandwich_moveSourceFamily,
        commuteGHalfSandwich_moveChainFamily_zero params family r,
        gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_moveChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_moveChainFamily params family r (Fin.last r) q).outcome ogs =
        (commuteGHalfSandwich_moveFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily,
        commuteGHalfSandwich_moveSourceFamily, commuteGHalfSandwich_moveFamily,
        gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator]
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily]

lemma commuteGHalfSandwich_moveChain_step
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    ∀ r (i : Fin r),
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        ((commuteGHalfSandwich_moveChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_moveChainFamily params family r) i.succ)
        (gHatSelfConsistencyError zeta)
  | 0, i => Fin.elim0 i
  | r + 1, i => by
      by_cases hi : i.1 < r
      · have hsmall := commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc r ⟨i.1, hi⟩
        let j : Fin r := ⟨i.1, hi⟩
        have hsrc : i.1 < r + 1 := Nat.lt_trans hi (Nat.lt_succ_self r)
        simpa [commuteGHalfSandwich_moveChainFamily, hi,
          hsrc, Nat.succ_lt_succ hi] using
          commuteGHalfSandwich_moveChainLift params ψbi family r
            ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc)
            ((commuteGHalfSandwich_moveChainFamily params family r) j.succ)
            (gHatSelfConsistencyError zeta)
            hsmall
      · have hilast : i.1 = r := by omega
        have hi_last : i = Fin.last r := Fin.ext hilast
        cases hi_last
        have hlast := commuteGHalfSandwich_moveChainLift_moveFamily_last params ψbi family zeta r hsc
        simpa [commuteGHalfSandwich_moveChainFamily] using
          (CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
            (commuteGHalfSandwich_moveChainLiftFamily params family r
              (commuteGHalfSandwich_moveFamily params family r))
            (commuteGHalfSandwich_moveFamily params family (r + 1))
            (commuteGHalfSandwich_moveChainLiftFamily params family r
              (commuteGHalfSandwich_moveChainFamily params family r (Fin.last r)))
            (commuteGHalfSandwich_moveFamily params family (r + 1))
            (gHatSelfConsistencyError zeta)
            (fun q ogs => by
              simp [commuteGHalfSandwich_moveChainLiftFamily,
                commuteGHalfSandwich_moveChainFamily_last params family r
                  (q.2.1, q.2.2 0, pointTupleTail q.2.2)
                  (ogs.2.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)])
            (fun _ _ => rfl)
            hlast)

lemma commuteGHalfSandwich_move_chain
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (r : ℕ)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      ((r : Error) * ∑ i : Fin r, gHatSelfConsistencyError zeta) := by
  cases r with
  | zero =>
      simpa using commuteGHalfSandwich_move_recursive_zero params ψbi family
  | succ r =>
      have hchain := Preliminaries.sddOpRel_chain
        ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (r + 1)
        (commuteGHalfSandwich_moveChainFamily params family (r + 1))
        (fun _ => gHatSelfConsistencyError zeta)
        (commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc (r + 1))
      have hchain' :
          SDDOpRel ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
            (commuteGHalfSandwich_moveChainFamily params family (r + 1) 0)
            (commuteGHalfSandwich_moveChainFamily params family (r + 1) (Fin.last (r + 1)))
            (((r + 1 : Error)) * ∑ i : Fin (r + 1), gHatSelfConsistencyError zeta) := by
        simpa using hchain
      simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        (CommutativityPoints.sddOpRel_congr_outcome ψbi
          (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
          (commuteGHalfSandwich_moveChainFamily params family (r + 1) 0)
          (commuteGHalfSandwich_moveChainFamily params family (r + 1) (Fin.last (r + 1)))
          (commuteGHalfSandwich_moveSourceFamily params family (r + 1))
          (commuteGHalfSandwich_moveFamily params family (r + 1))
          (((r + 1 : Error)) * ∑ i : Fin (r + 1), gHatSelfConsistencyError zeta)
          (commuteGHalfSandwich_moveChainFamily_zero params family (r + 1))
          (commuteGHalfSandwich_moveChainFamily_last params family (r + 1))
          hchain')

lemma commuteGHalfSandwich_recursiveSource_eq_swappedFrontMoveStepSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs =
      (commuteGHalfSandwich_moveStepSourceFamily params family r
        ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
        ((moveTailSwappedFrontOutcomeEquiv params r) ogs) := by
  simp [moveTailSwappedFrontQuestionEquiv, moveTailSwappedFrontOutcomeEquiv,
    moveTailQuestionEquiv, moveTailOutcomeEquiv,
    swappedFrontQuestionEquiv, swappedFrontOutcomeEquiv,
    commuteGHalfSandwich_recursiveSourceFamily,
    commuteGHalfSandwich_moveStepSourceFamily,
    headTailOrderedFamily, gHatHalfProductOutcomeOperator,
    leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_split_succ_iff
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ) (δ : Error) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
      (headTailOrderedFamily params family (r + 1))
      (headTailRotatedFamily params family (r + 1))
      δ ↔
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ := by
  constructor
  · intro h
    have hq :=
      (sddOpRel_uniform_equiv (splitSuccQuestionEquiv params r) ψbi
        (headTailOrderedFamily params family (r + 1))
        (headTailRotatedFamily params family (r + 1)) δ).1 h
    have ho := CommutativityPoints.sddOpRel_reindex (splitSuccOutcomeEquiv params r)
      ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => headTailOrderedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      (fun q => headTailRotatedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      δ hq
    exact CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      _ _
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ
      (fun q ogs => by
        simpa [splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
          (commuteGHalfSandwich_moveSource_eq_split params family r
            q
            ogs).symm)
      (fun q ogs => by
        simpa [splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
          (commuteGHalfSandwich_recursiveTarget_eq_split params family r
            q
            ogs).symm)
      ho
  · intro h
    have ho := CommutativityPoints.sddOpRel_reindex (splitSuccOutcomeEquiv params r).symm
      ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ h
    have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      _ _
      (fun q => headTailOrderedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      (fun q => headTailRotatedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      δ
      (fun q ogs => by
        simpa [splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
          (commuteGHalfSandwich_moveSource_eq_split params family r
            q ((splitSuccOutcomeEquiv params r) ogs)))
      (fun q ogs => by
        simpa [splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
          (commuteGHalfSandwich_recursiveTarget_eq_split params family r
            q ((splitSuccOutcomeEquiv params r) ogs)))
      ho
    exact (sddOpRel_uniform_equiv (splitSuccQuestionEquiv params r) ψbi
      (headTailOrderedFamily params family (r + 1))
      (headTailRotatedFamily params family (r + 1)) δ).2 hq

lemma commuteGHalfSandwich_prefixSecondSliceLeft
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params r))
      (headTailOrderedFamily params family r)
      (headTailRotatedFamily params family r)
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_recursiveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution ((SliceQuestion params × PointTuple params r) × SliceQuestion params))
        (fun q => headTailOrderedFamily params family r q.1)
        (fun q => headTailRotatedFamily params family r q.1)
        δ :=
    sddOpRel_uniform_fst ψbi
      (headTailOrderedFamily params family r)
      (headTailRotatedFamily params family r)
      δ hAB
  have hABtriple :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        (fun q => headTailOrderedFamily params family r (q.1, q.2.2))
        (fun q => headTailRotatedFamily params family r (q.1, q.2.2))
        δ :=
    (sddOpRel_uniform_equiv (splitQuestionEquiv params r) ψbi
      (fun q => headTailOrderedFamily params family r q.1)
      (fun q => headTailRotatedFamily params family r q.1)
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
      { outcome := fun ag => C q ag.1 ag.2 * (headTailOrderedFamily params family r (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (headTailOrderedFamily params family r (q.1, q.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (headTailRotatedFamily params family r (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (headTailRotatedFamily params family r (q.1, q.2.2)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => headTailOrderedFamily params family r (q.1, q.2.2))
      (fun q => headTailRotatedFamily params family r (q.1, q.2.2))
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
    (commuteGHalfSandwich_recursiveSourceFamily params family r)
    (commuteGHalfSandwich_recursiveTargetFamily params family r)
    δ
    (fun q ogs => by
      simp [reindexedSource, rawSource, commuteGHalfSandwich_recursiveSourceFamily,
        prefixTripleOutcomeEquiv, C])
    (fun q ogs => by
      simp [reindexedTarget, rawTarget, commuteGHalfSandwich_recursiveTargetFamily,
        prefixTripleOutcomeEquiv, C])
    hreindex

noncomputable def commuteGHalfSandwich_splitSuccLiftFamily
    (params : Parameters) [FieldModel params.q]
    (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
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
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          (F (q.1, q.2.2)).total }

lemma commuteGHalfSandwich_splitSuccLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (r : ℕ)
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
      (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_splitSuccLiftFamily params r A)
      (commuteGHalfSandwich_splitSuccLiftFamily params r B)
      δ := by
  let A' : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun ogs => A q |>.outcome ((splitSuccOutcomeEquiv params r) ogs)
        total := (A q).total }
  let B' : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun ogs => B q |>.outcome ((splitSuccOutcomeEquiv params r) ogs)
        total := (B q).total }
  have ho := CommutativityPoints.sddOpRel_reindex (splitSuccOutcomeEquiv params r).symm
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    A B δ hAB
  have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
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

end MIPStarRE.LDT.Pasting
