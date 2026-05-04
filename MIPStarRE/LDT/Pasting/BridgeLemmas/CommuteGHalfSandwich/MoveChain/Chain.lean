import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.Lifting

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ## Move chain: recursive family, step lemma, and aggregate

The recursive `moveChainFamily` indexed over `Fin (r+1)`, with the step lemma
`moveChain_step` and the aggregate lemma `move_chain` that composes the
`r` self-consistency edges.
-/
noncomputable def commuteGHalfSandwich_moveChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (r : ℕ) → Fin (r + 1) → IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
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
      (commuteGHalfSandwich_moveChainFamily params family r 0 q).outcome
        ogs =
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
      (commuteGHalfSandwich_moveChainFamily params family r (Fin.last r) q).outcome
        ogs =
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
        (uniformDistribution (MoveQ params r))
        ((commuteGHalfSandwich_moveChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_moveChainFamily params family r) i.succ)
        (gHatSelfConsistencyError zeta)
  | 0, i => Fin.elim0 i
  | r + 1, i => by
      by_cases hi : i.1 < r
      · have hsmall :=
          commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc r ⟨i.1, hi⟩
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
        have hlast := commuteGHalfSandwich_moveChainLift_moveFamily_last params ψbi family zeta
            r hsc
        simpa [commuteGHalfSandwich_moveChainFamily] using
          (CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                PointTuple params (r + 1)))
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
      (uniformDistribution (MoveQ params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      ((r : Error) * ∑ _i : Fin r, gHatSelfConsistencyError zeta) := by
  cases r with
  | zero =>
      simpa using commuteGHalfSandwich_move_recursive_zero params ψbi family
  | succ r =>
      have hchain := Preliminaries.sddOpRel_chain
        ψbi
        (uniformDistribution (MoveQ params (r + 1)))
        (r + 1)
        (commuteGHalfSandwich_moveChainFamily params family (r + 1))
        (fun _ => gHatSelfConsistencyError zeta)
        (commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc (r + 1))
      have hchain' :
          SDDOpRel ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                PointTuple params (r + 1)))
            (commuteGHalfSandwich_moveChainFamily params family (r + 1) 0)
            (commuteGHalfSandwich_moveChainFamily params family (r + 1) (Fin.last (r + 1)))
            (((r + 1 : Error)) * ∑ i : Fin (r + 1), gHatSelfConsistencyError zeta) := by
        simpa using hchain
      simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        (CommutativityPoints.sddOpRel_congr_outcome ψbi
          (uniformDistribution (MoveQ params (r + 1)))
          (commuteGHalfSandwich_moveChainFamily params family (r + 1) 0)
          (commuteGHalfSandwich_moveChainFamily params family (r + 1) (Fin.last (r + 1)))
          (commuteGHalfSandwich_moveSourceFamily params family (r + 1))
          (commuteGHalfSandwich_moveFamily params family (r + 1))
          (((r + 1 : Error)) * ∑ i : Fin (r + 1), gHatSelfConsistencyError zeta)
          (commuteGHalfSandwich_moveChainFamily_zero params family (r + 1))
          (commuteGHalfSandwich_moveChainFamily_last params family (r + 1))
          hchain')



end MIPStarRE.LDT.Pasting
