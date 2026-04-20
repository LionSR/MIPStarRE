import MIPStarRE.LDT.Pasting.BridgeLemmas.Commute.GlobalChain

/-!
# Section 12 pasting: bridge commute theorem

Final assembly of the `commuteGHalfSandwich` theorem from the staged chain bounds.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma commuteGHalfSandwich_split_succ_via_stage
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (δmove δcomm δmoveBack δrecursive : Error)
    (hmove : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      δmove)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveFamily params family r)
      (commuteGHalfSandwich_commuteFamily params family r)
      δcomm)
    (hmoveBack : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_commuteFamily params family r)
      (commuteGHalfSandwich_moveBackFamily params family r)
      δmoveBack)
    (hrecursive : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_recursiveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      δrecursive) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
      (headTailOrderedFamily params family (r + 1))
      (headTailRotatedFamily params family (r + 1))
      ((5 : Error) * (δmove + δcomm + δmoveBack + δrecursive)) := by
  exact (commuteGHalfSandwich_split_succ_iff params ψbi family r
    ((5 : Error) * (δmove + δcomm + δmoveBack + δrecursive))).2
      (commuteGHalfSandwich_successor_stage_chain params ψbi family r
        δmove δcomm δmoveBack δrecursive hmove hcomm hmoveBack hrecursive)

lemma commuteGHalfSandwich_globalChain_step
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta))
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    ∀ r (i : Fin (commuteGHalfSandwich_globalChainLength r)),
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × PointTuple params r))
        ((commuteGHalfSandwich_globalChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_globalChainFamily params family r) i.succ)
        ((commuteGHalfSandwich_globalChainError params gamma zeta r) i)
  | 0, i => Fin.elim0 i
  | 1, i => by
      have hsplit :
          SDDOpRel ψbi
            (uniformDistribution (SliceQuestion params × PointTuple params 1))
            (headTailOrderedFamily params family 1)
            (headTailRotatedFamily params family 1)
            (gHatCommutationError params gamma zeta) :=
        (commuteGHalfSandwich_split_one_iff params ψbi family
          (gHatCommutationError params gamma zeta)).2 hcom
      fin_cases i
      simpa [commuteGHalfSandwich_globalChainFamily,
        commuteGHalfSandwich_globalChainError, commuteGHalfSandwich_globalChainLength] using hsplit
  | r + 2, i => by
      by_cases himove : i.1 < r + 1
      · let j : Fin (r + 1) := ⟨i.1, himove⟩
        have hstep := commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc (r + 1) j
        have hlift := commuteGHalfSandwich_splitSuccLift params ψbi (r + 1)
          ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) j.castSucc)
          ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) j.succ)
          (gHatSelfConsistencyError zeta)
          hstep
        have hsrc : i.1 < r + 2 := Nat.lt_trans himove (Nat.lt_succ_self (r + 1))
        have htgt : i.1 + 1 < r + 2 := Nat.succ_lt_succ himove
        simpa [commuteGHalfSandwich_globalChainFamily,
          commuteGHalfSandwich_globalChainError, himove, hsrc, htgt, j] using hlift
      · have hnot_move : ¬ i.1 < r + 1 := himove
        by_cases hicomm : i.1 = r + 1
        · have hcommute := commuteGHalfSandwich_splitSuccLift params ψbi (r + 1)
            (commuteGHalfSandwich_moveFamily params family (r + 1))
            (commuteGHalfSandwich_commuteFamily params family (r + 1))
            (gHatCommutationError params gamma zeta)
            (commuteGHalfSandwich_step_commute params ψbi family gamma zeta (r + 1) hcom)
          have hsrc_eq :
              ∀ q ogs,
                (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                  (commuteGHalfSandwich_moveFamily params family (r + 1)) q).outcome ogs =
                ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.castSucc q).outcome ogs := by
            intro q ogs
            have hlast_idx : (Fin.last (r + 1) : Fin (r + 2)) = ⟨r + 1, by simp⟩ := by
              apply Fin.ext
              simp
            calc
              (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                  (commuteGHalfSandwich_moveFamily params family (r + 1)) q).outcome ogs
                = (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                    ((commuteGHalfSandwich_moveChainFamily params family (r + 1))
                      (Fin.last (r + 1))) q).outcome ogs := by
                        symm
                        simp [commuteGHalfSandwich_splitSuccLiftFamily,
                          commuteGHalfSandwich_moveChainFamily_last params family (r + 1)]
              _ = (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                    ((commuteGHalfSandwich_moveChainFamily params family (r + 1))
                      ⟨r + 1, by simp⟩) q).outcome ogs := by
                    rw [hlast_idx]
              _ = ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.castSucc q).outcome ogs := by
                    simp [commuteGHalfSandwich_globalChainFamily, hicomm]
          have htgt_eq :
              ∀ q ogs,
                (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                  (commuteGHalfSandwich_commuteFamily params family (r + 1)) q).outcome ogs =
                ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ q).outcome ogs := by
            intro q ogs
            have hstage_zero :
                (commuteGHalfSandwich_moveBackStageFamily params family r 0) =
                  commuteGHalfSandwich_commuteFamily params family (r + 1) := by
              rfl
            have htgt_formula :
                ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ q).outcome ogs =
                  (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                    ((commuteGHalfSandwich_moveBackStageFamily params family r) 0) q).outcome ogs := by
              have hnot_move_succ : ¬ i.1 + 1 < r + 2 := by omega
              have hstage_succ : i.1 + 1 < 2 * (r + 1) + 1 := by omega
              have hsub_zero : i.1 + 1 - (r + 2) = 0 := by omega
              simp [commuteGHalfSandwich_globalChainFamily, hnot_move_succ, hstage_succ, hsub_zero]
            calc
              (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                  (commuteGHalfSandwich_commuteFamily params family (r + 1)) q).outcome ogs
                = (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                    ((commuteGHalfSandwich_moveBackStageFamily params family r) 0) q).outcome ogs := by
                      rw [hstage_zero.symm]
              _ = ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ q).outcome ogs := by
                    simpa using htgt_formula.symm
          have hbridge := CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × PointTuple params (r + 2)))
            (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
              (commuteGHalfSandwich_moveFamily params family (r + 1)))
            (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
              (commuteGHalfSandwich_commuteFamily params family (r + 1)))
            ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.castSucc)
            ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ)
            (gHatCommutationError params gamma zeta)
            hsrc_eq htgt_eq hcommute
          simpa [commuteGHalfSandwich_globalChainError, hnot_move, hicomm] using hbridge
        · have hnot_comm : i.1 ≠ r + 1 := hicomm
          by_cases hiback : i.1 < 2 * (r + 1) + 1
          · by_cases hlast_back : i.1 = 2 * (r + 1)
            · let j : Fin (r + 1) := ⟨r, by simp⟩
              have hstage := commuteGHalfSandwich_moveBackStage_step params ψbi family zeta
                  (r := r) hsc j
              have hlift := commuteGHalfSandwich_splitSuccLift params ψbi (r + 1)
                ((commuteGHalfSandwich_moveBackStageFamily params family r) j.castSucc)
                ((commuteGHalfSandwich_moveBackStageFamily params family r) j.succ)
                (gHatSelfConsistencyError zeta)
                hstage
              have hsrc_eq :
                  ∀ q ogs,
                    (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                      ((commuteGHalfSandwich_moveBackStageFamily params family r) j.castSucc) q).outcome ogs =
                    ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.castSucc q).outcome ogs := by
                intro q ogs
                have hsrc_formula :
                    ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.castSucc q).outcome ogs =
                      (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                        ((commuteGHalfSandwich_moveBackStageFamily params family r) j.castSucc) q).outcome ogs := by
                  have hnot_move_src : ¬ i.1 < r + 2 := by omega
                  have hstage_src : i.1 < 2 * (r + 1) + 1 := by omega
                  have hsub_src : i.1 - (r + 2) = r := by omega
                  have hjcast : j.castSucc = ⟨r, by simp⟩ := by
                    ext
                    simp [j]
                  simp [commuteGHalfSandwich_globalChainFamily, hnot_move_src, hstage_src, hsub_src, j, hjcast]
                simpa using hsrc_formula.symm
              have htgt_eq :
                  ∀ q ogs,
                    (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                      ((commuteGHalfSandwich_moveBackStageFamily params family r) j.succ) q).outcome ogs =
                    ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ q).outcome ogs := by
                intro q ogs
                let q' : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1) :=
                  (splitSuccQuestionEquiv params (r + 1)) q
                let ogs' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1) :=
                  (splitSuccOutcomeEquiv params (r + 1)) ogs
                have hlast_stage :
                    ((commuteGHalfSandwich_moveBackStageFamily params family r) j.succ q').outcome ogs' =
                      (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q').outcome ogs' := by
                  simpa [commuteGHalfSandwich_moveBackStageFamily, j] using
                    commuteGHalfSandwich_moveBackChainFamily_last params family r q' ogs'
                have hzero_small :
                    ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) 0
                        (q'.1, q'.2.2)).outcome (ogs'.1, ogs'.2.2) =
                      (headTailOrderedFamily params family (r + 1)
                        (q'.1, q'.2.2)).outcome (ogs'.1, ogs'.2.2) := by
                  exact commuteGHalfSandwich_globalChainFamily_zero params family (r + 1)
                    (q'.1, q'.2.2) (ogs'.1, ogs'.2.2)
                have hrec_to_zero :
                    (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                        (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1)) q).outcome ogs =
                      (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                        (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                          ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) 0)) q).outcome ogs := by
                  change
                    (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q').outcome ogs' =
                      (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                        ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) 0) q').outcome ogs'
                  calc
                    (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q').outcome ogs'
                      = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                          (headTailOrderedFamily params family (r + 1)) q').outcome ogs' := by
                            rfl
                    _ = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                          ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) 0) q').outcome ogs' := by
                        exact (congrArg
                          (fun X => leftTensor (ι₂ := ι)
                            ((gHatIdxMeas params family q'.2.1).outcome ogs'.2.1) * X)
                          hzero_small).symm
                have htgt_formula :
                    ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ q).outcome ogs =
                      (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                        (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                          ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) 0)) q).outcome ogs := by
                  have hnot_move_tgt : ¬ i.1 + 1 < r + 2 := by omega
                  have hnot_stage_tgt : ¬ i.1 + 1 < 2 * (r + 1) + 1 := by omega
                  have hsub_zero : i.1 + 1 - (2 * (r + 1) + 1) = 0 := by omega
                  simp [commuteGHalfSandwich_globalChainFamily, hnot_move_tgt, hnot_stage_tgt,
                    hsub_zero]
                calc
                  (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                      ((commuteGHalfSandwich_moveBackStageFamily params family r) j.succ) q).outcome ogs
                    = (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                        (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1)) q).outcome ogs := by
                          simpa [commuteGHalfSandwich_splitSuccLiftFamily, q', ogs'] using hlast_stage
                  _ = (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                        (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                          ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) 0)) q).outcome ogs := hrec_to_zero
                  _ = ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ q).outcome ogs := by
                        simpa using htgt_formula.symm
              have hbridge := CommutativityPoints.sddOpRel_congr_outcome ψbi
                (uniformDistribution (SliceQuestion params × PointTuple params (r + 2)))
                (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                  ((commuteGHalfSandwich_moveBackStageFamily params family r) j.castSucc))
                (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                  ((commuteGHalfSandwich_moveBackStageFamily params family r) j.succ))
                ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.castSucc)
                ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ)
                (gHatSelfConsistencyError zeta)
                hsrc_eq htgt_eq hlift
              simpa [commuteGHalfSandwich_globalChainError, hnot_move, hicomm, hiback] using hbridge
            · let j : Fin (r + 1) := ⟨i.1 - (r + 2), by omega⟩
              have hstage := commuteGHalfSandwich_moveBackStage_step params ψbi family zeta
                (r := r) hsc j
              have hlift := commuteGHalfSandwich_splitSuccLift params ψbi (r + 1)
                ((commuteGHalfSandwich_moveBackStageFamily params family r) j.castSucc)
                ((commuteGHalfSandwich_moveBackStageFamily params family r) j.succ)
                (gHatSelfConsistencyError zeta)
                hstage
              have hsrc_eq :
                  ∀ q ogs,
                    (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                      ((commuteGHalfSandwich_moveBackStageFamily params family r) j.castSucc) q).outcome ogs =
                    ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.castSucc q).outcome ogs := by
                intro q ogs
                have hnot_move_src : ¬ i.1 < r + 2 := by omega
                simpa [commuteGHalfSandwich_globalChainFamily, hnot_move_src, hiback, j]
              have htgt_eq :
                  ∀ q ogs,
                    (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                      ((commuteGHalfSandwich_moveBackStageFamily params family r) j.succ) q).outcome ogs =
                    ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ q).outcome ogs := by
                intro q ogs
                have hnot_move_tgt : ¬ i.1 + 1 < r + 2 := by omega
                have htgt_stage : i.1 + 1 < 2 * (r + 1) + 1 := by omega
                have hj_succ_norm :
                    (j.succ : Fin (r + 2)) = ⟨i.1 - (r + 1), by omega⟩ := by
                  ext
                  dsimp [j]
                  omega
                simpa [commuteGHalfSandwich_globalChainFamily, hnot_move_tgt, htgt_stage, j, hj_succ_norm]
              have hbridge := CommutativityPoints.sddOpRel_congr_outcome ψbi
                (uniformDistribution (SliceQuestion params × PointTuple params (r + 2)))
                (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                  ((commuteGHalfSandwich_moveBackStageFamily params family r) j.castSucc))
                (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                  ((commuteGHalfSandwich_moveBackStageFamily params family r) j.succ))
                ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.castSucc)
                ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ)
                (gHatSelfConsistencyError zeta)
                hsrc_eq htgt_eq hlift
              simpa [commuteGHalfSandwich_globalChainError, hnot_move, hicomm, hiback] using hbridge
          · let j : Fin (commuteGHalfSandwich_globalChainLength (r + 1)) :=
              ⟨i.1 - (2 * (r + 1) + 1), by
                have hi_lt : i.1 <
                    commuteGHalfSandwich_globalChainLength (r + 1) + (2 * (r + 1) + 1) := by
                  simpa [commuteGHalfSandwich_globalChainLength, Nat.add_assoc,
                    Nat.add_left_comm, Nat.add_comm] using i.2
                omega⟩
            have hrec := commuteGHalfSandwich_globalChain_step params ψbi family gamma zeta
              hsc hcom (r + 1) j
            have hprefix := commuteGHalfSandwich_prefixSecondSliceLeftLift params ψbi family (r + 1)
              ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j.castSucc)
              ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j.succ)
              ((commuteGHalfSandwich_globalChainError params gamma zeta (r + 1)) j)
              hrec
            have hlift := commuteGHalfSandwich_splitSuccLift params ψbi (r + 1)
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j.castSucc))
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j.succ))
              ((commuteGHalfSandwich_globalChainError params gamma zeta (r + 1)) j)
              hprefix
            have hsrc_eq :
                ∀ q ogs,
                  (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                      ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j.castSucc)) q).outcome ogs =
                  ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.castSucc q).outcome ogs := by
              intro q ogs
              have hnot_move_src : ¬ i.1 < r + 2 := by omega
              have hnot_stage_src : ¬ i.1 < 2 * (r + 1) + 1 := hiback
              simpa [commuteGHalfSandwich_globalChainFamily, hnot_move_src, hnot_stage_src, j]
            have htgt_eq :
                ∀ q ogs,
                  (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                      ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j.succ)) q).outcome ogs =
                  ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ q).outcome ogs := by
              intro q ogs
              have hnot_move_tgt : ¬ i.1 + 1 < r + 2 := by omega
              have hnot_stage_tgt : ¬ i.1 + 1 < 2 * (r + 1) + 1 := by omega
              have hj_succ_norm :
                  (j.succ : Fin (commuteGHalfSandwich_globalChainLength (r + 1) + 1)) =
                    ⟨i.1 - 2 * (r + 1), by
                      have hjlt : j.1 < commuteGHalfSandwich_globalChainLength (r + 1) := j.2
                      dsimp [j] at hjlt
                      omega⟩ := by
                ext
                dsimp [j]
                omega
              simpa [commuteGHalfSandwich_globalChainFamily, hnot_move_tgt, hnot_stage_tgt, j, hj_succ_norm]
            simpa [commuteGHalfSandwich_globalChainError, hnot_move, hicomm, hiback] using
              (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × PointTuple params (r + 2)))
              (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                  ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j.castSucc)))
              (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
                (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                  ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j.succ)))
              ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.castSucc)
              ((commuteGHalfSandwich_globalChainFamily params family (r + 2)) i.succ)
              ((commuteGHalfSandwich_globalChainError params gamma zeta (r + 1)) j)
              hsrc_eq htgt_eq hlift)

lemma commuteGHalfSandwich_core_three
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hzeta_le : zeta ≤ 1)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta))
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params 3))
      (gHatHalfSandwichLeft params family 3)
      (gHatHalfSandwichRight params family 3)
      (commuteGHalfSandwichError params gamma zeta 3) := by
  have hmove :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 1))
        (commuteGHalfSandwich_moveSourceFamily params family 1)
        (commuteGHalfSandwich_moveFamily params family 1)
        ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) := by
    simpa using commuteGHalfSandwich_move_chain params ψbi family zeta 1 hsc
  have hmoveBackRec :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 1))
        (commuteGHalfSandwich_commuteFamily params family 1)
        (commuteGHalfSandwich_recursiveSourceFamily params family 1)
        ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) := by
    simpa using commuteGHalfSandwich_moveBack_chain params ψbi family zeta (r := 0) hsc
  have hmoveBack :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 1))
        (commuteGHalfSandwich_commuteFamily params family 1)
        (commuteGHalfSandwich_moveBackFamily params family 1)
        ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) := by
    exact CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 1))
      (commuteGHalfSandwich_commuteFamily params family 1)
      (commuteGHalfSandwich_recursiveSourceFamily params family 1)
      (commuteGHalfSandwich_commuteFamily params family 1)
      (commuteGHalfSandwich_moveBackFamily params family 1)
      (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta))
      (fun _ _ => rfl)
      (fun q ogs => by
        simpa using (commuteGHalfSandwich_moveBack_eq_recursiveSource params family 1 q ogs).symm)
      hmoveBackRec
  have htail :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 1))
        (commuteGHalfSandwich_recursiveSourceFamily params family 1)
        (commuteGHalfSandwich_recursiveTargetFamily params family 1)
        (gHatCommutationError params gamma zeta) := by
    have hsplit1 :
        SDDOpRel ψbi
          (uniformDistribution (SliceQuestion params × PointTuple params 1))
          (headTailOrderedFamily params family 1)
          (headTailRotatedFamily params family 1)
          (gHatCommutationError params gamma zeta) :=
      (commuteGHalfSandwich_split_one_iff params ψbi family
        (gHatCommutationError params gamma zeta)).2 hcom
    exact commuteGHalfSandwich_prefixSecondSliceLeft params ψbi family 1
      (gHatCommutationError params gamma zeta) hsplit1
  have hsplit2 :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × PointTuple params 2))
        (headTailOrderedFamily params family 2)
        (headTailRotatedFamily params family 2)
        ((5 : Error) *
          (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
            gHatCommutationError params gamma zeta +
            ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
            gHatCommutationError params gamma zeta)) := by
    exact commuteGHalfSandwich_split_succ_via_stage params ψbi family 1
      (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta))
      (gHatCommutationError params gamma zeta)
      (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta))
      (gHatCommutationError params gamma zeta)
      hmove
      (commuteGHalfSandwich_step_commute params ψbi family gamma zeta 1 hcom)
      hmoveBack
      htail
  have hpoint :
      SDDOpRel ψbi
        (uniformDistribution (PointTuple params 3))
        (gHatHalfSandwichLeft params family 3)
        (gHatHalfSandwichRight params family 3)
        ((5 : Error) *
          (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
            gHatCommutationError params gamma zeta +
            ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
            gHatCommutationError params gamma zeta)) := by
    exact (commuteGHalfSandwich_split_iff params ψbi family 2
      ((5 : Error) *
        (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
          gHatCommutationError params gamma zeta +
          ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
          gHatCommutationError params gamma zeta))).2 hsplit2
  rcases hsc with ⟨hν2⟩
  have hν2_nonneg : 0 ≤ gHatSelfConsistencyError zeta := by
    exact le_trans
      (avgOver_nonneg (uniformDistribution (SliceQuestion params))
        (fun q => qSDD ψbi (gHatSelfConsistencyLeftFamily params family q)
          (gHatSelfConsistencyRightFamily params family q))
        (fun q => qSDD_nonneg ψbi _ _))
      hν2
  have hzeta_nonneg : 0 ≤ zeta := by
    simpa [gHatSelfConsistencyError] using hν2_nonneg
  rcases hcom with ⟨hν3⟩
  have hν3_nonneg : 0 ≤ gHatCommutationError params gamma zeta := by
    exact le_trans
      (avgOver_nonneg (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi (gHatPairProductLeft params family q) (gHatPairProductRight params family q))
        (fun q => Preliminaries.qSDDOp_nonneg ψbi _ _))
      hν3
  have hbound_raw :
      ((5 : Error) *
          (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
            gHatCommutationError params gamma zeta +
            ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
            gHatCommutationError params gamma zeta))
        ≤ 3 * (3 : Error) * (4 * (3 : Error) * zeta + (3 : Error) * gHatCommutationError params gamma zeta) := by
    simp [gHatSelfConsistencyError]
    nlinarith
  have hbound :
      ((5 : Error) *
          (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
            gHatCommutationError params gamma zeta +
            ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
            gHatCommutationError params gamma zeta))
        ≤ commuteGHalfSandwichError params gamma zeta 3 := by
    let S : Error :=
      Real.rpow gamma (1 / (16 : Error)) +
        Real.rpow zeta (1 / (16 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
    have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
    have hm : 0 < (params.m : Error) := by exact_mod_cast params.hm
    have hm_pos : 0 < (138 : Error) * (params.m : Error) := by positivity
    have hS_nonneg : 0 ≤ S := by
      unfold gHatCommutationError at hν3_nonneg
      nlinarith [hν3_nonneg, hm_pos]
    have hzeta_to_S : zeta ≤ (params.m : Error) * S := by
      have hzeta_to_rpow : zeta ≤ Real.rpow zeta (1 / (16 : Error)) := by
        have hpow : (1 / (16 : Error)) ≤ (1 : Error) := by norm_num
        simpa [Real.rpow_one] using
          (Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le (by norm_num) hpow)
      have hγterm_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : Error)) := by
        by_cases hγ : 0 ≤ gamma
        · exact Real.rpow_nonneg hγ _
        · have hγlt : gamma < 0 := lt_of_not_ge hγ
          have hnegexpr : 0 ≤ gamma ^ (1 / (16 : Error)) := by
            rw [Real.rpow_def_of_neg hγlt]
            refine mul_nonneg (by positivity) ?_
            have hcos_pos : 0 < Real.cos ((1 / (16 : Error)) * Real.pi) := by
              apply Real.cos_pos_of_mem_Ioo
              constructor <;> nlinarith [Real.pi_pos]
            simpa [mul_comm] using hcos_pos.le
          simpa using hnegexpr
      have hratio_base_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
      have hratio_nonneg : 0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
        exact Real.rpow_nonneg hratio_base_nonneg _
      have hroot_le : Real.rpow zeta (1 / (16 : Error)) ≤ S := by
        have hsum1 :
            Real.rpow zeta (1 / (16 : Error)) ≤
              Real.rpow zeta (1 / (16 : Error)) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
          nlinarith [hratio_nonneg]
        have hsum2 :
            Real.rpow zeta (1 / (16 : Error)) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) ≤ S := by
          have :
              Real.rpow zeta (1 / (16 : Error)) +
                  Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) ≤
                Real.rpow gamma (1 / (16 : Error)) +
                  (Real.rpow zeta (1 / (16 : Error)) +
                    Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))) := by
            nlinarith [hγterm_nonneg]
          simpa [S, add_assoc, add_left_comm, add_comm] using this
        exact le_trans hsum1 hsum2
      have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
        exact_mod_cast (Nat.succ_le_of_lt params.hm)
      have hmul : S ≤ (params.m : Error) * S := by nlinarith
      exact le_trans hzeta_to_rpow (le_trans hroot_le hmul)
    have hmain :
        ((5 : Error) *
            (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
              gHatCommutationError params gamma zeta +
              ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
              gHatCommutationError params gamma zeta))
          ≤ 20 * ((params.m : Error) * S) + 10 * gHatCommutationError params gamma zeta := by
      have :
          ((5 : Error) *
              (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
                gHatCommutationError params gamma zeta +
                ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
                gHatCommutationError params gamma zeta))
            = 20 * zeta + 10 * gHatCommutationError params gamma zeta := by
              simp [gHatSelfConsistencyError]
              ring
      rw [this]
      nlinarith [hzeta_to_S]
    have hcomm_to_error :
        20 * ((params.m : Error) * S) + 10 * gHatCommutationError params gamma zeta
          ≤ commuteGHalfSandwichError params gamma zeta 3 := by
      have :
          20 * ((params.m : Error) * S) + 10 * gHatCommutationError params gamma zeta
            = (1400 : Error) * (params.m : Error) * S := by
              simp [gHatCommutationError, S]
              ring
      rw [this]
      have :
          (1400 : Error) * (params.m : Error) * S ≤
            426 * ((3 : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by
              nlinarith [hm_nonneg, hS_nonneg]
      simpa [commuteGHalfSandwichError, S] using this
    exact le_trans hmain hcomm_to_error
  exact Preliminaries.sddOpRel_mono ψbi
    (uniformDistribution (PointTuple params 3))
    (gHatHalfSandwichLeft params family 3)
    (gHatHalfSandwichRight params family 3)
    ((5 : Error) *
      (((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
        gHatCommutationError params gamma zeta +
        ((1 : Error) * ∑ i : Fin 1, gHatSelfConsistencyError zeta) +
        gHatCommutationError params gamma zeta))
    (commuteGHalfSandwichError params gamma zeta 3)
    hpoint hbound

lemma commuteGHalfSandwich_core
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta))
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft params family k)
      (gHatHalfSandwichRight params family k)
      (commuteGHalfSandwichError params gamma zeta k) := by
  by_cases hk2 : k = 2
  · subst hk2
    exact commuteGHalfSandwich_core_two params ψbi family gamma zeta hcom
  · have hk3 : 3 ≤ k := by omega
    by_cases hk3eq : k = 3
    · subst hk3eq
      exact commuteGHalfSandwich_core_three params ψbi family gamma zeta hzeta_le hsc hcom
    · have hk4 : 4 ≤ k := by omega
      let r : ℕ := k - 2
      have hk_eq : k = r + 2 := by
        dsimp [r]
        omega
      have hsc0 := hsc
      have hcom0 := hcom
      rcases hsc with ⟨hν2⟩
      have hν2_nonneg : 0 ≤ gHatSelfConsistencyError zeta := by
        exact le_trans
          (avgOver_nonneg (uniformDistribution (SliceQuestion params))
            (fun q => qSDD ψbi (gHatSelfConsistencyLeftFamily params family q)
              (gHatSelfConsistencyRightFamily params family q))
            (fun q => qSDD_nonneg ψbi _ _))
          hν2
      have hzeta_nonneg : 0 ≤ zeta := by
        simpa [gHatSelfConsistencyError] using hν2_nonneg
      rcases hcom with ⟨hν3⟩
      have hν3_nonneg : 0 ≤ gHatCommutationError params gamma zeta := by
        exact le_trans
          (avgOver_nonneg (uniformDistribution (SlicePairQuestion params))
            (fun q => qSDDOp ψbi (gHatPairProductLeft params family q) (gHatPairProductRight params family q))
            (fun q => Preliminaries.qSDDOp_nonneg ψbi _ _))
          hν3
      have hchain := Preliminaries.sddOpRel_chain
        ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        (commuteGHalfSandwich_flatChainLength r)
        (commuteGHalfSandwich_flatChainFamily params family r)
        (commuteGHalfSandwich_flatChainError params gamma zeta r)
        (commuteGHalfSandwich_flatChainStep params ψbi family gamma zeta hsc0 hcom0 r)
      have hsplit :
          SDDOpRel ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
            (commuteGHalfSandwich_moveSourceFamily params family r)
            (commuteGHalfSandwich_recursiveTargetFamily params family r)
            (((commuteGHalfSandwich_flatChainLength r : Error)) *
              ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
                commuteGHalfSandwich_flatChainError params gamma zeta r i) := by
        exact CommutativityPoints.sddOpRel_congr_outcome ψbi
          (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
          ((commuteGHalfSandwich_flatChainFamily params family r) 0)
          ((commuteGHalfSandwich_flatChainFamily params family r)
            (Fin.last (commuteGHalfSandwich_flatChainLength r)))
          (commuteGHalfSandwich_moveSourceFamily params family r)
          (commuteGHalfSandwich_recursiveTargetFamily params family r)
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i)
          (fun q ogs => by simpa using (commuteGHalfSandwich_flatChainFamily_zero params family r q ogs))
          (fun q ogs => by simpa using (commuteGHalfSandwich_flatChainFamily_last params family r q ogs))
          hchain
      have hsplitOrdered :
          SDDOpRel ψbi
            (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
            (headTailOrderedFamily params family (r + 1))
            (headTailRotatedFamily params family (r + 1))
            (((commuteGHalfSandwich_flatChainLength r : Error)) *
              ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
                commuteGHalfSandwich_flatChainError params gamma zeta r i) :=
        (commuteGHalfSandwich_split_succ_iff params ψbi family r
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i)).2 hsplit
      have hpoint :
          SDDOpRel ψbi
            (uniformDistribution (PointTuple params k))
            (gHatHalfSandwichLeft params family k)
            (gHatHalfSandwichRight params family k)
            (((commuteGHalfSandwich_flatChainLength r : Error)) *
              ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
                commuteGHalfSandwich_flatChainError params gamma zeta r i) := by
        rw [hk_eq]
        exact (commuteGHalfSandwich_split_iff params ψbi family (r + 1)
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i)).2 hsplitOrdered
      have hkR : (k : Error) = (r : Error) + 2 := by
        exact_mod_cast hk_eq
      have hsum :
          ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i =
            4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta :=
        commuteGHalfSandwich_flatChainError_sum params gamma zeta r
      have hlen_le : ((commuteGHalfSandwich_flatChainLength r : ℕ) : Error) ≤ 3 * (k : Error) := by
        have hflat : ((commuteGHalfSandwich_flatChainLength r : ℕ) : Error) = 3 * (r : Error) + 1 := by
          rw [commuteGHalfSandwich_flatChainLength, commuteGHalfSandwich_postMoveFlatLength_eq]
          norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
          ring
        rw [hflat, hkR]
        nlinarith
      have hsum_le :
          4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta
            ≤ 4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta := by
        rw [hkR]
        have hζextra : 0 ≤ 8 * zeta := by nlinarith [hzeta_nonneg]
        have hνextra : 0 ≤ gHatCommutationError params gamma zeta := hν3_nonneg
        have hcast_r1 : (((r + 1 : ℕ) : Error)) = (r : Error) + 1 := by
          norm_num [Nat.cast_add, Nat.cast_one]
        have hrewrite :
            4 * ((r : Error) + 2) * zeta + ((r : Error) + 2) * gHatCommutationError params gamma zeta =
              4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta +
                (8 * zeta + gHatCommutationError params gamma zeta) := by
          rw [hcast_r1]
          ring
        nlinarith [hrewrite, hζextra, hνextra]
      have hsum_nonneg :
          0 ≤ 4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta := by
        nlinarith [hzeta_nonneg, hν3_nonneg]
      have hraw_bound :
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
              ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
                commuteGHalfSandwich_flatChainError params gamma zeta r i)
            ≤ 3 * (k : Error) *
                (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta) := by
        rw [hsum]
        gcongr
      exact Preliminaries.sddOpRel_mono ψbi
        (uniformDistribution (PointTuple params k))
        (gHatHalfSandwichLeft params family k)
        (gHatHalfSandwichRight params family k)
        (((commuteGHalfSandwich_flatChainLength r : Error)) *
          ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
            commuteGHalfSandwich_flatChainError params gamma zeta r i)
        (commuteGHalfSandwichError params gamma zeta k)
        hpoint
        (le_trans hraw_bound (commuteGHalfSandwich_error_bound params gamma zeta k hzeta_nonneg hzeta_le))

/-- `lem:commute-g-half-sandwich`. -/
lemma commuteGHalfSandwich
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta) :
    CommuteGHalfSandwichStatement params ψbi family gamma zeta k := by
  exact ⟨commuteGHalfSandwich_core params ψbi family gamma zeta k hk
    hzeta_le hfacts.completedSelfConsistency hfacts.completedCommutation⟩

end MIPStarRE.LDT.Pasting
