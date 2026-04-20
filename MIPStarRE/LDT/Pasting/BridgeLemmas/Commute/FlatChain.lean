import MIPStarRE.LDT.Pasting.BridgeLemmas.Commute.SecondSlice

/-!
# Section 12 pasting: bridge flat chain

Flattens the staged move/commute/move-back process into a uniform chain estimate.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma commuteGHalfSandwich_postMoveFlatStep
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
    ∀ r (i : Fin (commuteGHalfSandwich_postMoveFlatLength r)),
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        ((commuteGHalfSandwich_postMoveFlatFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_postMoveFlatFamily params family r) i.succ)
        ((commuteGHalfSandwich_postMoveFlatError params gamma zeta r) i)
  | 0, i => by
      fin_cases i
      have hcomm0 := commuteGHalfSandwich_step_commute params ψbi family gamma zeta 0 hcom
      exact CommutativityPoints.sddOpRel_congr_outcome ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 0))
        (commuteGHalfSandwich_moveFamily params family 0)
        (commuteGHalfSandwich_commuteFamily params family 0)
        (commuteGHalfSandwich_moveFamily params family 0)
        (commuteGHalfSandwich_recursiveTargetFamily params family 0)
        (gHatCommutationError params gamma zeta)
        (fun _ _ => rfl)
        (fun q ogs => commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget params family q ogs)
        hcomm0
  | r + 1, i => by
      by_cases hi0 : i.1 = 0
      · have hcomm1 := commuteGHalfSandwich_step_commute params ψbi family gamma zeta (r + 1) hcom
        have hsrc_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc q).outcome ogs =
                (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs := by
          intro q ogs
          simpa [commuteGHalfSandwich_postMoveFlatFamily, hi0]
        have htgt_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ q).outcome ogs =
                (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
          intro q ogs
          have hi1 : i.1 + 1 = 1 := by omega
          simpa [commuteGHalfSandwich_postMoveFlatFamily, hi0, hi1]
        simpa [commuteGHalfSandwich_postMoveFlatError, hi0] using
          (CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
            (commuteGHalfSandwich_moveFamily params family (r + 1))
            (commuteGHalfSandwich_commuteFamily params family (r + 1))
            ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc)
            ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ)
            (gHatCommutationError params gamma zeta)
            (fun q ogs => (hsrc_eq q ogs).symm)
            (fun q ogs => (htgt_eq q ogs).symm)
            hcomm1)
      · by_cases hi1 : i.1 = 1
        · have hzero := commuteGHalfSandwich_commute_to_moveBackChainFamily_zero params ψbi family zeta (r := r) hsc
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc q).outcome ogs =
                  (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            simpa [commuteGHalfSandwich_postMoveFlatFamily, hi0, hi1]
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ q).outcome ogs =
                  ((commuteGHalfSandwich_moveBackChainFamily params family r) 0 q).outcome ogs := by
            intro q ogs
            have hi2 : i.1 + 1 ≠ 0 := by omega
            have hi2' : i.1 + 1 ≠ 1 := by omega
            have hinner0_nat : i.1 - 1 = 0 := by omega
            have hinner0 :
                (⟨i.1 - 1, by
                    have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                      simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
                    omega⟩ : Fin (commuteGHalfSandwich_postMoveFlatLength r + 1)) = 0 := by
              apply Fin.ext
              simp [hinner0_nat]
            let q' : SliceQuestion params × SliceQuestion params × PointTuple params r :=
              (q.1, q.2.2 0, pointTupleTail q.2.2)
            let ogs' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r :=
              (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
            have hzero_active :
                ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0 q').outcome ogs' =
                  (commuteGHalfSandwich_moveFamily params family r q').outcome ogs' :=
              commuteGHalfSandwich_postMoveFlatFamily_zero_active params family r q' ogs'
            have hsecond_eq :
                (commuteGHalfSandwich_secondSliceLiftFamily params family r
                  ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0) q).outcome ogs =
                  (commuteGHalfSandwich_secondSliceLiftFamily params family r
                    (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
              simpa [commuteGHalfSandwich_secondSliceLiftFamily, q', ogs'] using
                congrArg
                  (fun X =>
                    leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) * X)
                  hzero_active
            calc
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ q).outcome ogs
                = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      (commuteGHalfSandwich_postMoveFlatFamily params family r 0)) q).outcome ogs := by
                        conv_lhs => simp [commuteGHalfSandwich_postMoveFlatFamily, hi2, hi2']
                        simpa [hi0, hinner0]
              _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                    ((commuteGHalfSandwich_moveFamily params family r)) q).outcome ogs := by
                    calc
                      (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                        (commuteGHalfSandwich_splitSuccLiftFamily params r
                          (commuteGHalfSandwich_postMoveFlatFamily params family r 0)) q).outcome ogs
                          = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                              ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0) q).outcome ogs := by
                                rw [commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift]
                      _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                            (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := hsecond_eq
              _ = ((commuteGHalfSandwich_moveBackChainFamily params family r) 0 q).outcome ogs := by
                    simpa using
                      (commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily
                        params family r q ogs).symm
          simpa [commuteGHalfSandwich_postMoveFlatError, hi0, hi1] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
              (commuteGHalfSandwich_commuteFamily params family (r + 1))
              ((commuteGHalfSandwich_moveBackChainFamily params family r) 0)
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ)
              (gHatSelfConsistencyError zeta)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hzero)
        · let j : Fin (commuteGHalfSandwich_postMoveFlatLength r) :=
            ⟨i.1 - 2, by
              have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
              omega⟩
          have hsmall := commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc hcom r j
          have hprefix := commuteGHalfSandwich_prefixSecondSliceLeftLift params ψbi family (r + 1)
            (commuteGHalfSandwich_splitSuccLiftFamily params r
              ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc))
            (commuteGHalfSandwich_splitSuccLiftFamily params r
              ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ))
            ((commuteGHalfSandwich_postMoveFlatError params gamma zeta r) j)
            (commuteGHalfSandwich_splitSuccLift params ψbi r
              ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc)
              ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ)
              ((commuteGHalfSandwich_postMoveFlatError params gamma zeta r) j)
              hsmall)
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc q).outcome ogs =
                  (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc)) q).outcome ogs := by
            intro q ogs
            have hsrc_not0 : i.1 ≠ 0 := hi0
            have hsrc_not1 : i.1 ≠ 1 := hi1
            simp [commuteGHalfSandwich_postMoveFlatFamily, hsrc_not0, hsrc_not1, j]
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ q).outcome ogs =
                  (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ)) q).outcome ogs := by
            intro q ogs
            have htgt_not0 : i.1 + 1 ≠ 0 := by omega
            have htgt_not1 : i.1 + 1 ≠ 1 := by omega
            have hj_succ :
                (j.succ : Fin (commuteGHalfSandwich_postMoveFlatLength r + 1)) =
                  ⟨i.1 - 1, by
                    have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                      simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
                    omega⟩ := by
              apply Fin.ext
              dsimp [j]
              omega
            calc
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ q).outcome ogs
                = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r)
                        ⟨i.1 - 1, by
                          have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                            simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
                          omega⟩)) q).outcome ogs := by
                        conv_lhs => simp [commuteGHalfSandwich_postMoveFlatFamily, htgt_not0, htgt_not1]
                        simpa [hi0]
              _ = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ)) q).outcome ogs := by
                        have hidx :
                            ((commuteGHalfSandwich_postMoveFlatFamily params family r)
                              ⟨i.1 - 1, by
                                have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                                  simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
                                omega⟩) =
                              ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ) := by
                                exact congrArg
                                  (fun idx => (commuteGHalfSandwich_postMoveFlatFamily params family r) idx)
                                  hj_succ.symm
                        simpa [hidx]
          simpa [commuteGHalfSandwich_postMoveFlatError, hi0, hi1, j] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                (commuteGHalfSandwich_splitSuccLiftFamily params r
                  ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc)))
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                (commuteGHalfSandwich_splitSuccLiftFamily params r
                  ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ)))
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ)
              ((commuteGHalfSandwich_postMoveFlatError params gamma zeta r) j)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hprefix)

lemma commuteGHalfSandwich_flatChainStep
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
    ∀ r (i : Fin (commuteGHalfSandwich_flatChainLength r)),
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        ((commuteGHalfSandwich_flatChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_flatChainFamily params family r) i.succ)
        ((commuteGHalfSandwich_flatChainError params gamma zeta r) i)
  | 0, i => by
      fin_cases i
      simpa [commuteGHalfSandwich_flatChainFamily, commuteGHalfSandwich_flatChainError,
        commuteGHalfSandwich_postMoveFlatLength] using
        commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc hcom 0
          ⟨0, by simp [commuteGHalfSandwich_postMoveFlatLength]⟩
  | r + 1, i => by
      by_cases hi : i.1 < r + 1
      · let imove : Fin (r + 1) := ⟨i.1, hi⟩
        have hmove := commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc (r + 1) imove
        have hsrc_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc q).outcome ogs =
                ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.castSucc q).outcome ogs := by
          intro q ogs
          have hsrc_le : i.1 ≤ r + 1 := by omega
          conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_le]
          rfl
        have htgt_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ q).outcome ogs =
                ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.succ q).outcome ogs := by
          intro q ogs
          have htgt_le : i.1 ≤ r := by omega
          conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_le]
          rfl
        simpa [commuteGHalfSandwich_flatChainError, hi] using
          (CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
            ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.castSucc)
            ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.succ)
            ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
            ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
            (gHatSelfConsistencyError zeta)
            (fun q ogs => (hsrc_eq q ogs).symm)
            (fun q ogs => (htgt_eq q ogs).symm)
            hmove)
      · have hge : r + 1 ≤ i.1 := by omega
        by_cases hboundary : i.1 = r + 1
        · have hcomm1 := commuteGHalfSandwich_step_commute params ψbi family gamma zeta (r + 1) hcom
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc q).outcome ogs =
                  (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            have hsrc_le : i.1 ≤ r + 1 := by omega
            conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_le]
            simpa [hboundary, Fin.last] using
              commuteGHalfSandwich_moveChainFamily_last params family (r + 1) q ogs
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ q).outcome ogs =
                  (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            have htgt_not : ¬ i.1 ≤ r := by omega
            have hone_lt : 1 < commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1 := by
              rw [commuteGHalfSandwich_postMoveFlatLength_eq]
              omega
            calc
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ q).outcome ogs
                = (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
                    ⟨i.1 - r, by
                      simpa [hboundary] using hone_lt⟩ q).outcome ogs := by
                        conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_not]
              _ = (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
                    ⟨1, by
                      exact hone_lt⟩ q).outcome ogs := by
                    have hone :
                        (⟨i.1 - r, by
                            simpa [hboundary] using hone_lt⟩ : Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) =
                          ⟨1, by
                            exact hone_lt⟩ := by
                      apply Fin.ext
                      simp [hboundary]
                    exact congrArg
                      (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) idx q).outcome ogs)
                      hone
              _ = (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
                    exact commuteGHalfSandwich_postMoveFlatFamily_one_active params family (r := r) q ogs
          simpa [commuteGHalfSandwich_flatChainError, hi, hboundary,
            commuteGHalfSandwich_postMoveFlatError] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
              (commuteGHalfSandwich_moveFamily params family (r + 1))
              (commuteGHalfSandwich_commuteFamily params family (r + 1))
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
              (gHatCommutationError params gamma zeta)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hcomm1)
        · let j : Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1)) :=
            ⟨i.1 - (r + 1), by
              have hi_lt : i.1 < (r + 1) + commuteGHalfSandwich_postMoveFlatLength (r + 1) := by
                simpa [commuteGHalfSandwich_flatChainLength] using i.2
              omega⟩
          have hsmall := commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc hcom (r + 1) j
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc q).outcome ogs =
                  ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.castSucc q).outcome ogs := by
            intro q ogs
            have hsrc_not : ¬ i.1 ≤ r + 1 := by omega
            have hj_castSucc :
                (⟨i.1 - (r + 1), by
                    exact Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩ :
                  Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) = j.castSucc := by
              apply Fin.ext
              simp [j]
            conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_not]
            exact congrArg
              (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) idx q).outcome ogs)
              hj_castSucc
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ q).outcome ogs =
                  ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.succ q).outcome ogs := by
            intro q ogs
            have htgt_not : ¬ i.1 ≤ r := by omega
            have hge2 : r + 2 ≤ i.1 := by omega
            have hval : i.1 - r = (i.1 - (r + 1)) + 1 := by
              omega
            have hj_succ :
                (⟨i.1 - r, by
                    rw [hval]
                    simpa [j] using j.succ.is_lt⟩ :
                  Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) = j.succ := by
              apply Fin.ext
              simp [j, hval]
            conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_not]
            exact congrArg
              (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) idx q).outcome ogs)
              hj_succ
          simpa [commuteGHalfSandwich_flatChainError, hi, hboundary, j] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.castSucc)
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.succ)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
              ((commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1)) j)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hsmall)

noncomputable def commuteGHalfSandwich_moveBackStageFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    Fin (r + 2) → IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι)
  | ⟨0, _⟩ => commuteGHalfSandwich_commuteFamily params family (r + 1)
  | ⟨i + 1, _⟩ => commuteGHalfSandwich_moveBackChainFamily params family r ⟨i, by omega⟩

lemma commuteGHalfSandwich_moveBackStage_step
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) {r : ℕ}
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    ∀ i : Fin (r + 1),
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        ((commuteGHalfSandwich_moveBackStageFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_moveBackStageFamily params family r) i.succ)
        (gHatSelfConsistencyError zeta)
  | ⟨0, hi⟩ => by
      simpa [commuteGHalfSandwich_moveBackStageFamily] using
        commuteGHalfSandwich_commute_to_moveBackChainFamily_zero params ψbi family zeta hsc
  | ⟨i + 1, hi⟩ => by
      have hj : i < r := by omega
      simpa [commuteGHalfSandwich_moveBackStageFamily] using
        commuteGHalfSandwich_moveBackChain_step params ψbi family zeta hsc ⟨i, hj⟩

lemma commuteGHalfSandwich_moveBack_chain
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
      (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1))
      (((r + 1 : Error)) * ∑ i : Fin (r + 1), gHatSelfConsistencyError zeta) := by
  have hchain := Preliminaries.sddOpRel_chain
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    (r + 1)
    (commuteGHalfSandwich_moveBackStageFamily params family r)
    (fun _ => gHatSelfConsistencyError zeta)
    (commuteGHalfSandwich_moveBackStage_step params ψbi family zeta hsc)
  have hchain' :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (commuteGHalfSandwich_moveBackStageFamily params family r 0)
        (commuteGHalfSandwich_moveBackStageFamily params family r (Fin.last (r + 1)))
        (((r + 1 : Error)) * ∑ i : Fin (r + 1), gHatSelfConsistencyError zeta) := by
    simpa using hchain
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    (commuteGHalfSandwich_moveBackStageFamily params family r 0)
    (commuteGHalfSandwich_moveBackStageFamily params family r (Fin.last (r + 1)))
    (commuteGHalfSandwich_commuteFamily params family (r + 1))
    (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1))
    (((r + 1 : Error)) * ∑ i : Fin (r + 1), gHatSelfConsistencyError zeta)
    (fun _ _ => rfl)
    (fun q ogs => by
      simpa [commuteGHalfSandwich_moveBackStageFamily] using
        commuteGHalfSandwich_moveBackChainFamily_last params family r q ogs)
    hchain'

end MIPStarRE.LDT.Pasting
