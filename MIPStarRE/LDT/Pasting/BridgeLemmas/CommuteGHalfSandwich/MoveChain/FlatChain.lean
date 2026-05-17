import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.Chain

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ## Post-move flat chain and flat-chain definitions

The post-move flat chain (`postMoveFlatFamily`, `postMoveFlatError`) and the
combined flat chain (`flatChainFamily`, `flatChainError`) together with their
endpoint and summation lemmas.
-/
def commuteGHalfSandwich_postMoveFlatLength : ℕ → ℕ
  | 0 => 1
  | r + 1 => commuteGHalfSandwich_postMoveFlatLength r + 2

lemma commuteGHalfSandwich_postMoveFlatLength_pos
    (r : ℕ) :
    1 ≤ commuteGHalfSandwich_postMoveFlatLength r := by
  induction r with
  | zero => simp [commuteGHalfSandwich_postMoveFlatLength]
  | succ r ih =>
      simp [commuteGHalfSandwich_postMoveFlatLength]

noncomputable def commuteGHalfSandwich_postMoveFlatFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (r : ℕ) → Fin (commuteGHalfSandwich_postMoveFlatLength r + 1) → IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
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
                    exact i.2
                  omega⟩))

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
              exact i.2
            omega⟩

lemma commuteGHalfSandwich_postMoveFlatError_sum
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) :
    ∀ r,
      ∑ i : Fin (commuteGHalfSandwich_postMoveFlatLength r),
        commuteGHalfSandwich_postMoveFlatError params gamma zeta r i =
          (2 : Error) * (r : Error) * zeta + ((r + 1 : ℕ) : Error)
              * gHatCommutationError params gamma zeta
  | 0 => by
      simp [commuteGHalfSandwich_postMoveFlatLength, commuteGHalfSandwich_postMoveFlatError]
  | r + 1 => by
      have hone_lt : 1 < commuteGHalfSandwich_postMoveFlatLength (r + 1) := by
        simp [commuteGHalfSandwich_postMoveFlatLength]
      change ∑ i : Fin (commuteGHalfSandwich_postMoveFlatLength r + 2),
        commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1) i = _
      rw [Fin.sum_univ_succ]
      rw [Fin.sum_univ_succ]
      simp [commuteGHalfSandwich_postMoveFlatError,
        commuteGHalfSandwich_postMoveFlatError_sum params gamma zeta r,
        gHatSelfConsistencyError]
      ring

def commuteGHalfSandwich_flatChainLength (r : ℕ) : ℕ :=
  r + commuteGHalfSandwich_postMoveFlatLength r

noncomputable def commuteGHalfSandwich_flatChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    Fin (commuteGHalfSandwich_flatChainLength r + 1) → IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
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

lemma commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params 0)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params 0) :
    (commuteGHalfSandwich_commuteFamily params family 0 q).outcome
      ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family 0 q).outcome ogs := by
  simp [commuteGHalfSandwich_commuteFamily, commuteGHalfSandwich_recursiveTargetFamily,
    headTailRotatedFamily, gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator,
    rightTensor_one,
    leftTensor_mul_leftTensor]

lemma commuteGHalfSandwich_postMoveFlatLength_eq
    (r : ℕ) :
    commuteGHalfSandwich_postMoveFlatLength r = 2 * r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [commuteGHalfSandwich_postMoveFlatLength, ih, Nat.mul_add,
        Nat.add_left_comm, Nat.add_comm]

lemma commuteGHalfSandwich_secondSliceLift_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_recursiveTargetFamily params family r) q).outcome
        ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_secondSliceLiftFamily,
    commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
    gHatHalfProductOutcomeOperator,
    leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_postMoveFlatFamily_zero_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_postMoveFlatFamily params family r 0 q).outcome
        ogs =
        (commuteGHalfSandwich_moveFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily, commuteGHalfSandwich_moveFamily,
        leftTensor_mul_leftTensor]
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily]

lemma commuteGHalfSandwich_postMoveFlatFamily_one_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
      ⟨1, by
        rw [commuteGHalfSandwich_postMoveFlatLength_eq]
        omega⟩ q).outcome
          ogs =
      (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_postMoveFlatFamily]

lemma commuteGHalfSandwich_postMoveFlatFamily_last_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_postMoveFlatFamily params family r
          (Fin.last (commuteGHalfSandwich_postMoveFlatLength r)) q).outcome
            ogs =
        (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily, commuteGHalfSandwich_postMoveFlatLength,
        commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
        gHatHalfProductOutcomeOperator,
        leftTensor_mul_leftTensor]
  | r + 1, q, ogs => by
      let q' : SliceQuestion params × PointTuple params (r + 1) := (q.1, q.2.2)
      let ogs' : GHatOutcome params × GHatTupleOutcome params (r + 1) := (ogs.1, ogs.2.2)
      let q'' : MoveQ params r :=
        (splitSuccQuestionEquiv params r) q'
      let ogs'' : MoveO params r :=
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
          simp [Fin.last, commuteGHalfSandwich_postMoveFlatLength_eq, Nat.mul_add,
             Nat.add_comm]
        simpa [hlast_idx] using hsmall
      calc
        (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
            (Fin.last (commuteGHalfSandwich_postMoveFlatLength (r + 1))) q).outcome ogs
          = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
              (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_postMoveFlatFamily params family r
                  ⟨2 * (r + 1) - 1, by
                    have hlt :
                        2 * (r + 1) - 1 < commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                      rw [commuteGHalfSandwich_postMoveFlatLength_eq]
                      omega
                    exact hlt⟩)) q).outcome ogs := by
                simp [commuteGHalfSandwich_postMoveFlatFamily,
                    commuteGHalfSandwich_postMoveFlatLength_eq]
        _ = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
              (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_recursiveTargetFamily params family r)) q).outcome ogs := by
                change
                  leftTensor (ι₂ := ι)
                      ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                    ((commuteGHalfSandwich_postMoveFlatFamily params family r
                        ⟨2 * (r + 1) - 1, by
                          have hlt :
                              2 * (r + 1) - 1 < commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                            rw [commuteGHalfSandwich_postMoveFlatLength_eq]
                            omega
                          exact hlt⟩ q'').outcome ogs'') =
                    leftTensor (ι₂ := ι)
                        ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                      ((commuteGHalfSandwich_recursiveTargetFamily params family r q'').outcome
                        ogs'')
                exact congrArg
                  (fun X =>
                    let G := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
                    leftTensor (ι₂ := ι) G * X)
                  hsmall'
        _ = (commuteGHalfSandwich_recursiveTargetFamily params family (r + 1) q).outcome ogs := by
              exact (commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift
                  params family r
                (commuteGHalfSandwich_recursiveTargetFamily params family r) q ogs).trans
                  (commuteGHalfSandwich_secondSliceLift_recursiveTarget params family r q ogs)

lemma commuteGHalfSandwich_flatChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (r : ℕ) (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_flatChainFamily params family r 0 q).outcome
      ogs =
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

lemma commuteGHalfSandwich_flatChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (r : ℕ) (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_flatChainFamily params family r
      (Fin.last (commuteGHalfSandwich_flatChainLength r)) q).outcome
        ogs =
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



end MIPStarRE.LDT.Pasting
