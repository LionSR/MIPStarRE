import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.Chain

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ## Move-back chain

The `moveBackChainFamily` and its endpoint lemmas reverse the commutation to
bring the leading `Ĝ` back into position.
-/

noncomputable def commuteGHalfSandwich_moveBackChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    Fin (r + 1) → IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι)
  | i =>
      commuteGHalfSandwich_secondSliceLiftFamily params family r
        ((commuteGHalfSandwich_moveChainFamily params family r)
          ⟨r - i.1, by omega⟩)

lemma commuteGHalfSandwich_secondSliceLift_moveFamily_eq_swappedFrontMoveStepMid
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome
        ogs =
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
              A, B, G, T, leftTensor_mul_leftTensor]
    _ =
        (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (B * G)) *
          rightTensor (ι₁ := ι) T := by
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
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome
      ogs =
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
      (uniformDistribution (MoveQ params (r + 1)))
      (commuteGHalfSandwich_commuteFamily params family (r + 1))
      ((commuteGHalfSandwich_moveBackChainFamily params family r) 0)
      (gHatSelfConsistencyError zeta) := by
  have htargetMid :
      SDDOpRel ψbi
        (uniformDistribution (MoveTailQ params r))
        (commuteGHalfSandwich_moveStepTargetFamily params family r)
        (commuteGHalfSandwich_moveStepMidFamily params family r)
        (gHatSelfConsistencyError zeta) :=
    Preliminaries.sddOpRel_symm ψbi
      (uniformDistribution (MoveTailQ params r))
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
    (uniformDistribution (MoveQ params (r + 1)))
    (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
      ((moveTailSwappedFrontQuestionEquiv params r) q))
    (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
      ((moveTailSwappedFrontQuestionEquiv params r) q))
    (gHatSelfConsistencyError zeta)
    hq
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (MoveQ params (r + 1)))
    _ _
    (commuteGHalfSandwich_commuteFamily params family (r + 1))
    ((commuteGHalfSandwich_moveBackChainFamily params family r) 0)
    (gHatSelfConsistencyError zeta)
    (fun q ogs => by
      simpa using
        (commuteGHalfSandwich_commute_eq_swappedFrontMoveStepTarget params family r q ogs).symm)
    (fun q ogs => by
      let q' : MoveQ params r :=
        (q.1, q.2.2 0, pointTupleTail q.2.2)
      let ogs' : MoveO params r :=
        (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      have hlast :
          (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome
            ogs =
            (commuteGHalfSandwich_secondSliceLiftFamily params family r
              (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
        calc
          (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs
            = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                (commuteGHalfSandwich_moveFamily params family r q').outcome ogs' := by
                  simpa [commuteGHalfSandwich_moveBackChainFamily, q', ogs'] using
                    congrArg
                      (fun X =>
                        let G := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
                        leftTensor (ι₂ := ι) G * X)
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
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome
      ogs =
      (commuteGHalfSandwich_secondSliceLiftFamily params family r
        (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
  let q' : MoveQ params r :=
    (q.1, q.2.2 0, pointTupleTail q.2.2)
  let ogs' : MoveO params r :=
    (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
  calc
    (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs
      = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (commuteGHalfSandwich_moveFamily params family r q').outcome ogs' := by
            simpa [commuteGHalfSandwich_moveBackChainFamily, q', ogs'] using
              congrArg
                (fun X =>
                  leftTensor (ι₂ := ι)
                      ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                    X)
                (commuteGHalfSandwich_moveChainFamily_last params family r q' ogs')
    _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
          (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
            rfl



end MIPStarRE.LDT.Pasting
