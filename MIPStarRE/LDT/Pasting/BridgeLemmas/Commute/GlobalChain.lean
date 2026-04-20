import MIPStarRE.LDT.Pasting.BridgeLemmas.Commute.FlatChain

/-!
# Section 12 pasting: bridge global chain

Assembles the recursive flat-chain pieces into the global chain used by the final sandwich theorem.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def commuteGHalfSandwich_globalChainLength : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | r + 2 => commuteGHalfSandwich_globalChainLength (r + 1) + (2 * (r + 1) + 1)

noncomputable def commuteGHalfSandwich_globalChainError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) :
    (r : ℕ) → Fin (commuteGHalfSandwich_globalChainLength r) → Error
  | 0, i => Fin.elim0 i
  | 1, _ => gHatCommutationError params gamma zeta
  | r + 2, i =>
      if himove : i.1 < r + 1 then
        gHatSelfConsistencyError zeta
      else if hicomm : i.1 = r + 1 then
        gHatCommutationError params gamma zeta
      else if hiback : i.1 < 2 * (r + 1) + 1 then
        gHatSelfConsistencyError zeta
      else
        commuteGHalfSandwich_globalChainError params gamma zeta (r + 1)
          ⟨i.1 - (2 * (r + 1) + 1), by
            have hi_lt : i.1 < commuteGHalfSandwich_globalChainLength (r + 1) + (2 * (r + 1) + 1) :=
              i.2
            omega⟩

noncomputable def commuteGHalfSandwich_globalChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (r : ℕ) → Fin (commuteGHalfSandwich_globalChainLength r + 1) → IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)
  | 0, _ => headTailOrderedFamily params family 0
  | 1, i =>
      if i.1 = 0 then
        headTailOrderedFamily params family 1
      else
        headTailRotatedFamily params family 1
  | r + 2, i =>
      if himove : i.1 < r + 2 then
        commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
          ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) ⟨i.1, himove⟩)
      else if hstage : i.1 < 2 * (r + 1) + 1 then
        commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
          ((commuteGHalfSandwich_moveBackStageFamily params family r)
            ⟨i.1 - (r + 2), by omega⟩)
      else
        commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
          (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
            ((commuteGHalfSandwich_globalChainFamily params family (r + 1))
              ⟨i.1 - (2 * (r + 1) + 1), by
                have hi_lt :
                    i.1 < commuteGHalfSandwich_globalChainLength (r + 1) +
                      (2 * (r + 1) + 1) + 1 := by
                  simpa [commuteGHalfSandwich_globalChainLength, Nat.add_assoc,
                    Nat.add_left_comm, Nat.add_comm] using i.2
                omega⟩))

lemma commuteGHalfSandwich_globalChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_globalChainFamily params family r 0 q).outcome ogs =
        (headTailOrderedFamily params family r q).outcome ogs
  | 0, q, ogs => rfl
  | 1, q, ogs => by
      simp [commuteGHalfSandwich_globalChainFamily]
  | r + 2, q, ogs => by
      calc
        (commuteGHalfSandwich_globalChainFamily params family (r + 2) 0 q).outcome ogs
          = (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
              ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) 0) q).outcome ogs := by
                simp [commuteGHalfSandwich_globalChainFamily]
        _ = (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
              (commuteGHalfSandwich_moveSourceFamily params family (r + 1)) q).outcome ogs := by
                simp [commuteGHalfSandwich_splitSuccLiftFamily,
                  commuteGHalfSandwich_moveChainFamily_zero params family (r + 1)]
        _ = (headTailOrderedFamily params family (r + 2) q).outcome ogs := by
              exact commuteGHalfSandwich_splitSuccLift_moveSource params family (r + 1) q ogs

lemma commuteGHalfSandwich_globalChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_globalChainFamily params family r
          (Fin.last (commuteGHalfSandwich_globalChainLength r)) q).outcome ogs =
        (headTailRotatedFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_globalChainFamily, headTailOrderedFamily, headTailRotatedFamily,
        gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]
  | 1, q, ogs => by
      simp [commuteGHalfSandwich_globalChainFamily, commuteGHalfSandwich_globalChainLength]
  | r + 2, q, ogs => by
      let N := commuteGHalfSandwich_globalChainLength (r + 1)
      let j : Fin (N + 1) := ⟨N, by simp [N]⟩
      have htail :
          (commuteGHalfSandwich_globalChainFamily params family (r + 2)
              (Fin.last (commuteGHalfSandwich_globalChainLength (r + 2))) q).outcome ogs =
            (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j)) q).outcome ogs := by
        have hnot_move : ¬ N + (2 * (r + 1) + 1) < r + 2 := by
          omega
        have hnot_stage : ¬ N + (2 * (r + 1) + 1) < 2 * (r + 1) + 1 := by
          omega
        simp [commuteGHalfSandwich_globalChainFamily, commuteGHalfSandwich_globalChainLength,
          N, j, hnot_move, hnot_stage]
      have htail_rotated :
          (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j)) q).outcome ogs =
            (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                (headTailRotatedFamily params family (r + 1))) q).outcome ogs := by
        let q' : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1) :=
          (splitSuccQuestionEquiv params (r + 1)) q
        let ogs' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1) :=
          (splitSuccOutcomeEquiv params (r + 1)) ogs
        have hlast_small :
            ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j
                (q'.1, q'.2.2)).outcome (ogs'.1, ogs'.2.2) =
              (headTailRotatedFamily params family (r + 1)
                (q'.1, q'.2.2)).outcome (ogs'.1, ogs'.2.2) := by
          simpa [j, N] using
            commuteGHalfSandwich_globalChainFamily_last params family (r + 1)
              (q'.1, q'.2.2) (ogs'.1, ogs'.2.2)
        change
          (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
              ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j) q').outcome ogs' =
            (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
              (headTailRotatedFamily params family (r + 1)) q').outcome ogs'
        exact congrArg
          (fun X =>
            leftTensor (ι₂ := ι) ((gHatIdxMeas params family q'.2.1).outcome ogs'.2.1) * X)
          hlast_small
      calc
        (commuteGHalfSandwich_globalChainFamily params family (r + 2)
            (Fin.last (commuteGHalfSandwich_globalChainLength (r + 2))) q).outcome ogs
          = (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                ((commuteGHalfSandwich_globalChainFamily params family (r + 1)) j)) q).outcome ogs :=
              htail
        _ = (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                (headTailRotatedFamily params family (r + 1))) q).outcome ogs := htail_rotated
        _ = (commuteGHalfSandwich_splitSuccLiftFamily params (r + 1)
              (commuteGHalfSandwich_recursiveTargetFamily params family (r + 1)) q).outcome ogs := by
                simp [commuteGHalfSandwich_splitSuccLiftFamily,
                  commuteGHalfSandwich_prefixSecondSliceLeftFamily_rotated]
        _ = (headTailRotatedFamily params family (r + 2) q).outcome ogs := by
              exact commuteGHalfSandwich_splitSuccLift_recursiveTarget params family (r + 1) q ogs

 /-- Bridge: the staged move-commute-move chain for `commuteGHalfSandwich`.

Constructs the sequence of `3k` intermediate bipartite operator families
that arise from repeatedly moving `Ĝ₁` through the product
`Ĝ₁ · Ĝ₂ · ⋯ · Ĝₖ` using self-consistency (move to right tensor,
error `2ζ`) and pairwise commutation (swap past neighbor, error `ν₃`),
then composes them via `sddOpRel_chain`.

Paper reference: `lem:commute-g-half-sandwich` computation in
`ld-pasting.tex` lines 881–914. -/
noncomputable def commuteGHalfSandwichSuccessorStageFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    Fin 6 → IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)
  | ⟨0, _⟩ => commuteGHalfSandwich_moveSourceFamily params family r
  | ⟨1, _⟩ => commuteGHalfSandwich_moveFamily params family r
  | ⟨2, _⟩ => commuteGHalfSandwich_commuteFamily params family r
  | ⟨3, _⟩ => commuteGHalfSandwich_moveBackFamily params family r
  | ⟨4, _⟩ => commuteGHalfSandwich_recursiveSourceFamily params family r
  | ⟨_, _⟩ => commuteGHalfSandwich_recursiveTargetFamily params family r

def commuteGHalfSandwichSuccessorStageError
    (δmove δcomm δmoveBack δrecursive : Error) :
    Fin 5 → Error
  | ⟨0, _⟩ => δmove
  | ⟨1, _⟩ => δcomm
  | ⟨2, _⟩ => δmoveBack
  | ⟨3, _⟩ => 0
  | ⟨_, _⟩ => δrecursive

lemma commuteGHalfSandwich_moveBack_to_recursiveSource
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveBackFamily params family r)
      (commuteGHalfSandwich_recursiveSourceFamily params family r)
      0 := by
  refine ⟨?_⟩
  unfold sddErrorOp
  refine le_of_eq ?_
  calc
    avgOver
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        (fun q =>
          qSDDOp ψbi
            (commuteGHalfSandwich_moveBackFamily params family r q)
            (commuteGHalfSandwich_recursiveSourceFamily params family r q))
      = avgOver
          (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
          (fun _ => (0 : Error)) := by
            apply avgOver_congr
            intro q
            unfold qSDDOp qSDDCore
            refine Finset.sum_eq_zero ?_
            intro ogs _
            rw [commuteGHalfSandwich_moveBack_eq_recursiveSource params family r q ogs]
            simp [ev_zero]
    _ = 0 := by
          simpa using avgOver_uniform_const
            (α := SliceQuestion params × SliceQuestion params × PointTuple params r)
            (c := (0 : Error))

lemma commuteGHalfSandwich_successor_stage_chain
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
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      ((5 : Error) * (δmove + δcomm + δmoveBack + δrecursive)) := by
  have hsteps : ∀ i : Fin 5,
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        ((commuteGHalfSandwichSuccessorStageFamily params family r) i.castSucc)
        ((commuteGHalfSandwichSuccessorStageFamily params family r) i.succ)
        ((commuteGHalfSandwichSuccessorStageError δmove δcomm δmoveBack δrecursive) i) := by
    intro i
    fin_cases i
    · simpa [commuteGHalfSandwichSuccessorStageFamily, commuteGHalfSandwichSuccessorStageError] using hmove
    · simpa [commuteGHalfSandwichSuccessorStageFamily, commuteGHalfSandwichSuccessorStageError] using hcomm
    · simpa [commuteGHalfSandwichSuccessorStageFamily, commuteGHalfSandwichSuccessorStageError] using hmoveBack
    · simpa [commuteGHalfSandwichSuccessorStageFamily, commuteGHalfSandwichSuccessorStageError] using
        commuteGHalfSandwich_moveBack_to_recursiveSource params ψbi family r
    · simpa [commuteGHalfSandwichSuccessorStageFamily, commuteGHalfSandwichSuccessorStageError] using
        hrecursive
  have hchain := Preliminaries.sddOpRel_chain
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    5 (commuteGHalfSandwichSuccessorStageFamily params family r)
    (commuteGHalfSandwichSuccessorStageError δmove δcomm δmoveBack δrecursive) hsteps
  have hsum :
      ∑ x : Fin 5,
        commuteGHalfSandwichSuccessorStageError δmove δcomm δmoveBack δrecursive x =
          δmove + δcomm + δmoveBack + δrecursive := by
    rw [Fin.sum_univ_five]
    simp [commuteGHalfSandwichSuccessorStageError]
  simpa [commuteGHalfSandwichSuccessorStageFamily, hsum] using hchain

end MIPStarRE.LDT.Pasting
