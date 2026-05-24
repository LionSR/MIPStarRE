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

end MIPStarRE.LDT.Pasting
