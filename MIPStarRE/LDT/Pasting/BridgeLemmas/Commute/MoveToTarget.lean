import MIPStarRE.LDT.Pasting.BridgeLemmas.Commute.LocalStages

/-!
# Section 12 pasting: bridge move-to-target

Moves the local commute stage to the recursive target form used later in the sandwich chain.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma commuteGHalfSandwich_moveSource_eq_split
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs =
      (headTailOrderedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
        (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
  let A := (gHatIdxMeas params family q.1).outcome ogs.1
  let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let T := gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
  calc
    (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs
      = leftTensor (ι₂ := ι) ((A * B) * T) := by
          simp [commuteGHalfSandwich_moveSourceFamily, A, B, T,
            leftTensor_mul_leftTensor, mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * (B * T)) := by
          simp [mul_assoc]
    _ = leftTensor (ι₂ := ι)
          (A * (B * gHatHalfProductOutcomeOperator params family r
            (pointTupleTail (Fin.cons q.2.1 q.2.2))
            (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)))) := by
              have htail :
                  T = gHatHalfProductOutcomeOperator params family r
                    (pointTupleTail (Fin.cons q.2.1 q.2.2))
                    (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)) := by
                rfl
              exact congrArg (fun t => leftTensor (ι₂ := ι) (A * (B * t))) htail
    _ = (headTailOrderedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
          (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
            simp [headTailOrderedFamily, A, B, T,
              gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_move_recursive_zero
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 0))
      (commuteGHalfSandwich_moveSourceFamily params family 0)
      (commuteGHalfSandwich_moveFamily params family 0)
      0 := by
  refine ⟨?_⟩
  unfold sddErrorOp qSDDOp qSDDCore commuteGHalfSandwich_moveSourceFamily commuteGHalfSandwich_moveFamily
  simp [gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator,
    leftTensor_mul_leftTensor,
    leftTensor_mul_rightTensor_eq_opTensor]
  have hzero :
      avgOver (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 0))
        (fun q => ((Fintype.card (Polynomial params) : Error) + 1) *
          ((Fintype.card (Polynomial params) : Error) + 1) * ev ψbi 0) = 0 := by
    simp [avgOver, uniformDistribution, ev_zero]
  nlinarith [hzero]

def pointTupleOneEquiv (params : Parameters) :
    PointTuple params 1 ≃ SliceQuestion params where
  toFun xs := xs 0
  invFun x := fun _ => x
  left_inv xs := by
    funext i
    fin_cases i
    rfl
  right_inv x := by rfl

def gHatTupleOutcomeOneEquiv (params : Parameters) [FieldModel params.q] :
    GHatTupleOutcome params 1 ≃ GHatOutcome params where
  toFun gs := gs 0
  invFun g := fun _ => g
  left_inv gs := by
    funext i
    fin_cases i
    rfl
  right_inv g := by rfl

def splitQuestionEquivOne (params : Parameters) :
    (SliceQuestion params × PointTuple params 1) ≃ SlicePairQuestion params where
  toFun q := (q.1, (pointTupleOneEquiv params) q.2)
  invFun q := (q.1, (pointTupleOneEquiv params).symm q.2)
  left_inv q := by
    rcases q with ⟨x, xs⟩
    simpa using congrArg (fun ys => (x, ys)) ((pointTupleOneEquiv params).left_inv xs)
  right_inv q := by
    rcases q with ⟨x, y⟩
    simpa using congrArg (fun ys => (x, ys)) ((pointTupleOneEquiv params).right_inv y)

def splitOutcomeEquivOne (params : Parameters) [FieldModel params.q] :
    (GHatOutcome params × GHatTupleOutcome params 1) ≃ (GHatOutcome params × GHatOutcome params) where
  toFun og := (og.1, (gHatTupleOutcomeOneEquiv params) og.2)
  invFun og := (og.1, (gHatTupleOutcomeOneEquiv params).symm og.2)
  left_inv og := by
    rcases og with ⟨g, gs⟩
    simpa using congrArg (fun hs => (g, hs)) ((gHatTupleOutcomeOneEquiv params).left_inv gs)
  right_inv og := by
    rcases og with ⟨g₁, g₂⟩
    simpa using congrArg (fun hs => (g₁, hs)) ((gHatTupleOutcomeOneEquiv params).right_inv g₂)

lemma commuteGHalfSandwich_split_one_iff
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (δ : Error) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params 1))
      (headTailOrderedFamily params family 1)
      (headTailRotatedFamily params family 1)
      δ ↔
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      δ := by
  constructor
  · intro h
    have hq :=
      (sddOpRel_uniform_equiv (splitQuestionEquivOne params) ψbi
        (headTailOrderedFamily params family 1)
        (headTailRotatedFamily params family 1) δ).1 h
    have ho := CommutativityPoints.sddOpRel_reindex (splitOutcomeEquivOne params)
      ψbi
      (uniformDistribution (SlicePairQuestion params))
      (fun q => headTailOrderedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      (fun q => headTailRotatedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      δ hq
    exact CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SlicePairQuestion params))
      _ _
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      δ
      (fun q og => by
        rcases og with ⟨g₁, g₂⟩
        simp [gHatPairProductLeft, headTailOrderedFamily,
          splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
          gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
          orderedProductOpFamily, OpFamily.leftPlacedOpFamily,
          leftTensor_mul_leftTensor, mul_assoc])
      (fun q og => by
        rcases og with ⟨g₁, g₂⟩
        simp [gHatPairProductRight, headTailRotatedFamily,
          splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
          gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
          gHatRotatedHalfProductOutcomeOperator, reversedProductOpFamily,
          OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc])
      ho
  · intro h
    have ho := CommutativityPoints.sddOpRel_reindex (splitOutcomeEquivOne params).symm
      ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      δ h
    have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SlicePairQuestion params))
      _ _
      (fun q => headTailOrderedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      (fun q => headTailRotatedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      δ
      (fun q og => by
        rcases og with ⟨g₁, g₂⟩
        simp [gHatPairProductLeft, headTailOrderedFamily,
          splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
          gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
          orderedProductOpFamily, OpFamily.leftPlacedOpFamily,
          leftTensor_mul_leftTensor, mul_assoc])
      (fun q og => by
        rcases og with ⟨g₁, g₂⟩
        simp [gHatPairProductRight, headTailRotatedFamily,
          splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
          gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
          gHatRotatedHalfProductOutcomeOperator, reversedProductOpFamily,
          OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc])
      ho
    exact (sddOpRel_uniform_equiv (splitQuestionEquivOne params) ψbi
      (headTailOrderedFamily params family 1)
      (headTailRotatedFamily params family 1) δ).2 hq

lemma commuteGHalfSandwich_core_two
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params 2))
      (gHatHalfSandwichLeft params family 2)
      (gHatHalfSandwichRight params family 2)
      (commuteGHalfSandwichError params gamma zeta 2) := by
  have hsplit : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params 1))
      (headTailOrderedFamily params family 1)
      (headTailRotatedFamily params family 1)
      (gHatCommutationError params gamma zeta) :=
    (commuteGHalfSandwich_split_one_iff params ψbi family (gHatCommutationError params gamma zeta)).2 hcom
  have hpoint : SDDOpRel ψbi
      (uniformDistribution (PointTuple params 2))
      (gHatHalfSandwichLeft params family 2)
      (gHatHalfSandwichRight params family 2)
      (gHatCommutationError params gamma zeta) :=
    (commuteGHalfSandwich_split_iff params ψbi family 1 (gHatCommutationError params gamma zeta)).2 hsplit
  rcases hcom with ⟨hν3⟩
  have hν3_nonneg : 0 ≤ gHatCommutationError params gamma zeta := by
    exact le_trans
      (avgOver_nonneg (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi (gHatPairProductLeft params family q) (gHatPairProductRight params family q))
        (fun q => Preliminaries.qSDDOp_nonneg ψbi _ _))
      hν3
  have hS_nonneg :
      0 ≤ Real.rpow gamma (1 / (16 : Error)) +
            Real.rpow zeta (1 / (16 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    unfold gHatCommutationError at hν3_nonneg
    have hm : 0 < (params.m : Error) := by exact_mod_cast params.hm
    have hm_pos : 0 < (138 : Error) * (params.m : Error) := by positivity
    nlinarith
  have hbound :
      gHatCommutationError params gamma zeta ≤ commuteGHalfSandwichError params gamma zeta 2 := by
    let S : Error :=
      Real.rpow gamma (1 / (16 : Error)) +
        Real.rpow zeta (1 / (16 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
    have : 138 * (params.m : Error) * S ≤ 426 * ((2 : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by
      have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
      have hS' : 0 ≤ S := by simpa [S] using hS_nonneg
      nlinarith
    simpa [gHatCommutationError, commuteGHalfSandwichError, S] using this
  exact Preliminaries.sddOpRel_mono ψbi
    (uniformDistribution (PointTuple params 2))
    (gHatHalfSandwichLeft params family 2)
    (gHatHalfSandwichRight params family 2)
    (gHatCommutationError params gamma zeta)
    (commuteGHalfSandwichError params gamma zeta 2)
    hpoint hbound

def thirdSliceFrontOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r)) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.2.1.1, og.2.1.2, og.1, og.2.2)
  invFun og := (og.2.2.1, ((og.1, og.2.1), og.2.2.2))
  left_inv og := by
    rcases og with ⟨g₃, ⟨⟨g₁, g₂⟩, gs⟩⟩
    rfl
  right_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl

lemma gHatPairPrefix_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (q : SlicePairQuestion params) :
    ∑ og : GHatOutcome params × GHatOutcome params,
        ((((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2))ᴴ) *
          (((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2)) ≤ 1 := by
  let xs : PointTuple params 2 := Fin.cons q.1 (fun _ => q.2)
  have hsum := gHatHalfProduct_sum_adjoint_mul_le_one params family 2 xs
  have hEq :
      (∑ gs : GHatTupleOutcome params 2,
          (gHatHalfProductOutcomeOperator params family 2 xs gs)ᴴ *
            gHatHalfProductOutcomeOperator params family 2 xs gs) =
        ∑ og : GHatOutcome params × GHatOutcome params,
          ((((gHatIdxMeas params family q.1).outcome og.1) *
              ((gHatIdxMeas params family q.2).outcome og.2))ᴴ) *
            (((gHatIdxMeas params family q.1).outcome og.1) *
              ((gHatIdxMeas params family q.2).outcome og.2)) := by
    exact Fintype.sum_equiv
      ((gHatTupleOutcomeConsEquiv' params 1).trans (splitOutcomeEquivOne params))
      (fun gs : GHatTupleOutcome params 2 =>
        (gHatHalfProductOutcomeOperator params family 2 xs gs)ᴴ *
          gHatHalfProductOutcomeOperator params family 2 xs gs)
      (fun og : GHatOutcome params × GHatOutcome params =>
        ((((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2))ᴴ) *
          (((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2)))
      (by
        intro gs
        simp [xs, gHatHalfProductOutcomeOperator, splitOutcomeEquivOne,
          gHatTupleOutcomeOneEquiv, pointTupleTail, gHatTupleOutcomeTail,
          gHatTupleOutcomeConsEquiv'])
  rw [hEq] at hsum
  exact hsum

lemma commuteGHalfSandwich_moveStepMid_toTarget
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
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      (commuteGHalfSandwich_moveStepTargetFamily params family r)
      (gHatSelfConsistencyError zeta) := by
  let Q := SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r
  let Aop : IdxOpFamily Q (GHatOutcome params) (ι × ι) :=
    fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.2.2.1
  let Bop : IdxOpFamily Q (GHatOutcome params) (ι × ι) :=
    fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.2.2.1
  let C : Q → GHatOutcome params → ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ ag =>
      leftTensor (ι₂ := ι)
          (((gHatIdxMeas params family q.1).outcome ag.1.1) *
            ((gHatIdxMeas params family q.2.1).outcome ag.1.2)) *
        rightTensor (ι₁ := ι)
          (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ag.2)
  have hAB :
      SDDOpRel ψbi
        (uniformDistribution Q)
        Aop Bop
        (gHatSelfConsistencyError zeta) :=
    gHatSelfConsistency_sddOpRel_quadThird params ψbi family zeta r hsc
  have hC :
      ∀ q a,
        ∑ ag : ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r),
            (C q a ag)ᴴ * C q a ag ≤ 1 := by
    intro q a
    let pairProd : GHatOutcome params × GHatOutcome params → MIPStarRE.Quantum.Op ι :=
      fun og => ((gHatIdxMeas params family q.1).outcome og.1) *
        ((gHatIdxMeas params family q.2.1).outcome og.2)
    let pairTerm : GHatOutcome params × GHatOutcome params → MIPStarRE.Quantum.Op ι :=
      fun og => (pairProd og)ᴴ * pairProd og
    let tailOp : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
      fun gs => gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 gs
    let tailTerm : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
      fun gs => (tailOp gs)ᴴ * tailOp gs
    have hpair : ∑ og : GHatOutcome params × GHatOutcome params, pairTerm og ≤ 1 := by
      simpa [pairProd, pairTerm] using
        gHatPairPrefix_sum_adjoint_mul_le_one params family (q.1, q.2.1)
    have htail : ∑ gs : GHatTupleOutcome params r, tailTerm gs ≤ 1 := by
      simpa [tailOp, tailTerm] using
        gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2.2
    calc
      ∑ ag : ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r),
          (C q a ag)ᴴ * C q a ag
        = ∑ og : GHatOutcome params × GHatOutcome params,
            ∑ gs : GHatTupleOutcome params r,
              leftTensor (ι₂ := ι) (pairTerm og) * rightTensor (ι₁ := ι) (tailTerm gs) := by
                rw [← Finset.univ_product_univ, Finset.sum_product]
                refine Finset.sum_congr rfl ?_
                intro og _
                refine Finset.sum_congr rfl ?_
                intro gs _
                have hmul :
                    leftTensor (ι₂ := ι) (pairProd og) * rightTensor (ι₁ := ι) (tailOp gs) =
                      opTensor (pairProd og) (tailOp gs) := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor]
                have hCeq : C q a (og, gs) = opTensor (pairProd og) (tailOp gs) := by
                  simpa [C] using hmul
                calc
                  (C q a (og, gs))ᴴ * C q a (og, gs)
                    = (opTensor (pairProd og) (tailOp gs))ᴴ * opTensor (pairProd og) (tailOp gs) := by
                        rw [hCeq]
                  _ = opTensor ((pairProd og)ᴴ) ((tailOp gs)ᴴ) * opTensor (pairProd og) (tailOp gs) := by
                        rw [conjTranspose_opTensor]
                  _ = leftTensor (ι₂ := ι) (pairTerm og) * rightTensor (ι₁ := ι) (tailTerm gs) := by
                        simp [pairTerm, tailTerm, opTensor_mul, leftTensor_mul_rightTensor_eq_opTensor]
      _ = ∑ og : GHatOutcome params × GHatOutcome params,
            leftTensor (ι₂ := ι) (pairTerm og) *
              rightTensor (ι₁ := ι) (∑ gs : GHatTupleOutcome params r, tailTerm gs) := by
                refine Finset.sum_congr rfl ?_
                intro og _
                rw [← rightTensor_finset_sum (ι₁ := ι) Finset.univ tailTerm, ← Finset.mul_sum]
      _ ≤ ∑ og : GHatOutcome params × GHatOutcome params, leftTensor (ι₂ := ι) (pairTerm og) := by
            refine Finset.sum_le_sum ?_
            intro og _
            have hpair_nonneg : 0 ≤ pairTerm og := by
              change 0 ≤ star (pairProd og) * pairProd og
              exact (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨pairProd og, rfl⟩
            calc
              leftTensor (ι₂ := ι) (pairTerm og) *
                  rightTensor (ι₁ := ι) (∑ gs : GHatTupleOutcome params r, tailTerm gs)
                = opTensor (pairTerm og) (∑ gs : GHatTupleOutcome params r, tailTerm gs) := by
                    rw [leftTensor_mul_rightTensor_eq_opTensor]
              _ ≤ leftTensor (ι₂ := ι) (pairTerm og) := by
                    exact opTensor_le_leftTensor hpair_nonneg htail
      _ = leftTensor (ι₂ := ι)
            (∑ og : GHatOutcome params × GHatOutcome params, pairTerm og) := by
              rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ pairTerm]
      _ ≤ 1 := by
            exact leftTensor_le_one (ι₂ := ι) (A := _) hpair
  let rawSource : IdxOpFamily Q
      (GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r))
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (Aop q).outcome ag.1
        total := ∑ ag : GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r),
          C q ag.1 ag.2 * (Aop q).outcome ag.1 }
  let rawTarget : IdxOpFamily Q
      (GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r))
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (Bop q).outcome ag.1
        total := ∑ ag : GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r),
          C q ag.1 ag.2 * (Bop q).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution Q) Aop Bop C (gHatSelfConsistencyError zeta) hAB hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (thirdSliceFrontOutcomeEquiv params r)
    ψbi (uniformDistribution Q) rawSource rawTarget (gHatSelfConsistencyError zeta) hcab
  let reindexedSource : IdxOpFamily Q
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((thirdSliceFrontOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily Q
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((thirdSliceFrontOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution Q)
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveStepMidFamily params family r)
    (commuteGHalfSandwich_moveStepTargetFamily params family r)
    (gHatSelfConsistencyError zeta)
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      have hAop : (Aop q).outcome ogs.2.2.1 = leftTensor (ι₂ := ι) G := by
        rfl
      have hcomm : rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) G =
          leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T := by
        rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
      calc
        (reindexedSource q).outcome ogs
          = leftTensor (ι₂ := ι) (A * B) * (rightTensor (ι₁ := ι) T * (Aop q).outcome ogs.2.2.1) := by
              simp [reindexedSource, rawSource, thirdSliceFrontOutcomeEquiv, C, A, B, T, mul_assoc]
        _ = leftTensor (ι₂ := ι) (A * B) * (rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) G) := by
              rw [hAop]
        _ = leftTensor (ι₂ := ι) (A * B) * (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T) := by
              rw [hcomm]
        _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
              calc
                leftTensor (ι₂ := ι) (A * B) * (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T)
                  = (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G) * rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
                      simp [commuteGHalfSandwich_moveStepMidFamily, A, B, G, T,
                        leftTensor_mul_leftTensor, mul_assoc]
    )
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      have hBop : (Bop q).outcome ogs.2.2.1 = rightTensor (ι₁ := ι) G := by
        rfl
      calc
        (reindexedTarget q).outcome ogs
          = leftTensor (ι₂ := ι) (A * B) *
              (rightTensor (ι₁ := ι) T * (Bop q).outcome ogs.2.2.1) := by
                simp [reindexedTarget, rawTarget, thirdSliceFrontOutcomeEquiv, C, A, B, T, mul_assoc]
        _ = leftTensor (ι₂ := ι) (A * B) *
              (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
                rw [hBop]
        _ = (commuteGHalfSandwich_moveStepTargetFamily params family r q).outcome ogs := by
              symm
              calc
                (commuteGHalfSandwich_moveStepTargetFamily params family r q).outcome ogs
                  = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
                      (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
                        simp [commuteGHalfSandwich_moveStepTargetFamily, A, B, G, T, mul_assoc]
                _ = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) (T * G) := by
                      rw [rightTensor_mul_rightTensor]
                _ = leftTensor (ι₂ := ι) (A * B) * rightTensor (ι₁ := ι) (T * G) := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * B) *
                      (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
                        rw [rightTensor_mul_rightTensor]
    )
    hreindex

end MIPStarRE.LDT.Pasting
