import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Recursive source/target families and the split-succ equivalence

These are the basic building blocks for the half-sandwich commutation chain:
type abbreviations, the recursive source and target families, and the
split-succ equivalence (`split_succ_iff`) plus the prefix-second-slice-left lemma.
-/
abbrev MoveQ (params : Parameters) (r : ℕ) :=
  SliceQuestion params × SliceQuestion params × PointTuple params r

abbrev MoveO (params : Parameters) [FieldModel params.q] (r : ℕ) :=
  GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r

abbrev MoveTailQ (params : Parameters) (r : ℕ) :=
  SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r

abbrev MoveTailO (params : Parameters) [FieldModel params.q] (r : ℕ) :=
  GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r

noncomputable def commuteGHalfSandwich_recursiveSourceFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily (MoveQ params r)
      (MoveO params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (headTailOrderedFamily params family r (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total := 0 }

noncomputable def commuteGHalfSandwich_recursiveTargetFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily (MoveQ params r)
      (MoveO params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (headTailRotatedFamily params family r (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total := 0 }

lemma commuteGHalfSandwich_moveBack_eq_recursiveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_moveBackFamily params family r q).outcome
      ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family r q).outcome ogs := by
  simp [commuteGHalfSandwich_moveBackFamily, commuteGHalfSandwich_recursiveSourceFamily,
    headTailOrderedFamily, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_recursiveTarget_eq_split
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome
      ogs =
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
            A, T, G, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι)
          (A * (gHatHalfProductOutcomeOperator params family r
            (pointTupleTail (Fin.cons q.2.1 q.2.2))
            (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)) * G)) := by
              exact congrArg (fun X => leftTensor (ι₂ := ι) (A * (X * G))) htail.symm
    _ = (headTailRotatedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
          (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
            simp [headTailRotatedFamily, A, G, gHatHalfProductOutcomeOperator,
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
      (uniformDistribution (MoveQ params r))
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
      (uniformDistribution (MoveQ params r))
      (fun q =>
        headTailOrderedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      (fun q =>
        headTailRotatedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      δ hq
    exact CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (MoveQ params r))
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
      (uniformDistribution (MoveQ params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ h
    have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (MoveQ params r))
      _ _
      (fun q =>
        headTailOrderedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      (fun q =>
        headTailRotatedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
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
      (uniformDistribution (MoveQ params r))
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
        (uniformDistribution (MoveQ params r))
        (fun q => headTailOrderedFamily params family r (q.1, q.2.2))
        (fun q => headTailRotatedFamily params family r (q.1, q.2.2))
        δ :=
    (sddOpRel_uniform_equiv (splitQuestionEquiv params r) ψbi
      (fun q => headTailOrderedFamily params family r q.1)
      (fun q => headTailRotatedFamily params family r q.1)
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
                        (((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) by
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
      { outcome := fun ag => C q ag.1 ag.2 * (headTailOrderedFamily params family r (q.1,
          q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (headTailOrderedFamily params family r (q.1, q.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily (MoveQ params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (headTailRotatedFamily params family r (q.1,
          q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (headTailRotatedFamily params family r (q.1, q.2.2)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (MoveQ params r))
      (fun q => headTailOrderedFamily params family r (q.1, q.2.2))
      (fun q => headTailRotatedFamily params family r (q.1, q.2.2))
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

end MIPStarRE.LDT.Pasting
