import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup

/-!
# Section 12 pasting: commute G half-sandwich move chain

Recursive move, commute, move-back, and flat-chain construction for the half-sandwich bridge.

The generic branch uses the paper's single flat chain. For `r = k - 2`, the first
`r` edges move the leading `Ĝ` across the tail by self-consistency, and the
post-move suffix contributes `2r + 1` further edges: one outer pairwise
commutation, `r` recursively lifted commutations, and `r` move-back
self-consistency edges. Thus the composed chain has `3r + 1 = 3k - 5` edges
and total elementary error `4r * ζ + (r + 1) * ν₃`, matching the bookkeeping in
`lem:commute-g-half-sandwich`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev MoveQ (params : Parameters) (r : ℕ) :=
  SliceQuestion params × SliceQuestion params × PointTuple params r

private abbrev MoveO (params : Parameters) [FieldModel params.q] (r : ℕ) :=
  GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r

private abbrev MoveTailQ (params : Parameters) (r : ℕ) :=
  SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r

private abbrev MoveTailO (params : Parameters) [FieldModel params.q] (r : ℕ) :=
  GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r

private noncomputable def commuteGHalfSandwich_recursiveSourceFamily
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

private noncomputable def commuteGHalfSandwich_recursiveTargetFamily
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

private lemma commuteGHalfSandwich_moveBack_eq_recursiveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_moveBackFamily params family r q).outcome
      ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family r q).outcome ogs := by
  simp [commuteGHalfSandwich_moveBackFamily, commuteGHalfSandwich_recursiveSourceFamily,
    headTailOrderedFamily, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_recursiveTarget_eq_split
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

private lemma commuteGHalfSandwich_split_succ_iff
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

/- private lemma commuteGHalfSandwich_recursiveTarget_eq_rotated
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
      = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (T * G) := by
          rw [show (headTailRotatedFamily params family r (q.1, q.2.2)).outcome (ogs.1, ogs.2.2) =
              leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) G by
            simp [headTailRotatedFamily, T, G]]
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (A * (T * G)) := by
          rw [leftTensor_mul_leftTensor]
          rfl
    _ = (headTailRotatedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
          (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
            rw [htail]
            simp [headTailRotatedFamily, A, T, G,
              gHatHalfProductOutcomeOperator, gHatRotatedHalfProductOutcomeOperator,
              pointTupleTail, gHatTupleOutcomeTail, leftTensor_mul_leftTensor, mul_assoc]
-/

private lemma commuteGHalfSandwich_prefixSecondSliceLeft
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

private def swappedFrontQuestionEquiv (params : Parameters) (r : ℕ) :
    (MoveTailQ params r) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params ×
          PointTuple params r) where
  toFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  invFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl
  right_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl

private def swappedFrontOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (MoveTailO params r) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
          GHatTupleOutcome params r) where
  toFun og := (og.2.1, og.1, og.2.2.1, og.2.2.2)
  invFun og := (og.2.1, og.1, og.2.2.1, og.2.2.2)
  left_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl
  right_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl

private def moveTailSwappedFrontQuestionEquiv (params : Parameters) (r : ℕ) :
    (MoveQ params (r + 1)) ≃
      (MoveTailQ params r) :=
  (moveTailQuestionEquiv params r).trans (swappedFrontQuestionEquiv params r)

private def moveTailSwappedFrontOutcomeEquiv
    (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (MoveO params (r + 1)) ≃
      (MoveTailO params r) :=
  (moveTailOutcomeEquiv params r).trans (swappedFrontOutcomeEquiv params r)

private noncomputable def commuteGHalfSandwich_splitSuccLiftFamily
    (params : Parameters) [FieldModel params.q]
    (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        (F ((splitSuccQuestionEquiv params r) q)).outcome ((splitSuccOutcomeEquiv params r) ogs)
      total := (F ((splitSuccQuestionEquiv params r) q)).total }

private noncomputable def commuteGHalfSandwich_prefixSecondSliceLeftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)) :
    IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          (F (q.1, q.2.2)).total }

private lemma commuteGHalfSandwich_prefixSecondSliceLeftLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (A B : IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (MoveQ params r))
      (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r A)
      (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r B)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution ((SliceQuestion params × PointTuple params r) × SliceQuestion params))
        (fun q => A q.1)
        (fun q => B q.1)
        δ :=
    sddOpRel_uniform_fst ψbi A B δ hAB
  have hABtriple :
      SDDOpRel ψbi
        (uniformDistribution (MoveQ params r))
        (fun q => A (q.1, q.2.2))
        (fun q => B (q.1, q.2.2))
        δ :=
    (sddOpRel_uniform_equiv (splitQuestionEquiv params r) ψbi
      (fun q => A q.1)
      (fun q => B q.1)
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
                          (show MIPStarRE.Quantum.Op ι from
                            ((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) by
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
      { outcome := fun ag => C q ag.1 ag.2 * (A (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (A (q.1, q.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily (MoveQ params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (B (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (B (q.1, q.2.2)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (MoveQ params r))
      (fun q => A (q.1, q.2.2))
      (fun q => B (q.1, q.2.2))
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
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r A)
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r B)
    δ
    (fun q ogs => by
      simp [reindexedSource, rawSource, commuteGHalfSandwich_prefixSecondSliceLeftFamily,
        prefixTripleOutcomeEquiv, C])
    (fun q ogs => by
      simp [reindexedTarget, rawTarget, commuteGHalfSandwich_prefixSecondSliceLeftFamily,
        prefixTripleOutcomeEquiv, C])
    hreindex

private lemma commuteGHalfSandwich_splitSuccLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (r : ℕ)
    (A B : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (MoveQ params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_splitSuccLiftFamily params r A)
      (commuteGHalfSandwich_splitSuccLiftFamily params r B)
      δ := by
  let A' : IdxOpFamily
      (MoveQ params r)
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun ogs => A q |>.outcome ((splitSuccOutcomeEquiv params r) ogs)
        total := (A q).total }
  let B' : IdxOpFamily
      (MoveQ params r)
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun ogs => B q |>.outcome ((splitSuccOutcomeEquiv params r) ogs)
        total := (B q).total }
  have ho := CommutativityPoints.sddOpRel_reindex (splitSuccOutcomeEquiv params r).symm
    ψbi
    (uniformDistribution (MoveQ params r))
    A B δ hAB
  have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (MoveQ params r))
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

private lemma commuteGHalfSandwich_splitSuccLift_moveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_splitSuccLiftFamily params r
      (commuteGHalfSandwich_moveSourceFamily params family r) q).outcome
        ogs =
      (headTailOrderedFamily params family (r + 1) q).outcome ogs := by
  simpa [commuteGHalfSandwich_splitSuccLiftFamily, splitSuccQuestionEquiv,
      splitSuccOutcomeEquiv] using
    commuteGHalfSandwich_moveSource_eq_split params family r
      ((splitSuccQuestionEquiv params r) q)
      ((splitSuccOutcomeEquiv params r) ogs)

private noncomputable def commuteGHalfSandwich_secondSliceLiftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)) :
    IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).total }

private lemma commuteGHalfSandwich_secondSliceLift_moveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveSourceFamily params family r) q).outcome
        ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_secondSliceLiftFamily,
    commuteGHalfSandwich_recursiveSourceFamily, commuteGHalfSandwich_moveSourceFamily,
    headTailOrderedFamily, gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι))
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
      (commuteGHalfSandwich_splitSuccLiftFamily params r F) q).outcome
        ogs =
      (commuteGHalfSandwich_secondSliceLiftFamily params family r F q).outcome ogs := by
  simp [commuteGHalfSandwich_prefixSecondSliceLeftFamily,
    commuteGHalfSandwich_splitSuccLiftFamily,
    commuteGHalfSandwich_secondSliceLiftFamily,
    splitSuccQuestionEquiv, splitSuccOutcomeEquiv]

private lemma commuteGHalfSandwich_moveFamily_eq_moveStepTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome
      ogs =
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
      = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
          rightTensor (ι₁ := ι) (T * G) := by
          simp [commuteGHalfSandwich_moveFamily,
            A, B, T, G, gHatReverseHalfProductOutcomeOperator, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
          (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
            rw [rightTensor_mul_rightTensor]
    _ = (commuteGHalfSandwich_moveStepTargetFamily params family r
          ((moveTailQuestionEquiv params r) q)).outcome
          ((moveTailOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepTargetFamily, moveTailQuestionEquiv,
              moveTailOutcomeEquiv, A, B, T, G, mul_assoc]

private def commuteGHalfSandwich_moveChainLiftQuestionEquiv (params : Parameters) (r : ℕ) :
    ((MoveQ params r) × SliceQuestion params) ≃
      (MoveQ params (r + 1)) :=
  (firstSliceBackQuestionEquiv params r).trans (moveTailQuestionEquiv params r).symm

private def commuteGHalfSandwich_moveChainLiftOutcomeEquiv
    (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((MoveO params r) × GHatOutcome params) ≃
      (MoveO params (r + 1)) :=
  (firstSliceBackOutcomeEquiv params r).trans (moveTailOutcomeEquiv params r).symm

private noncomputable def commuteGHalfSandwich_moveChainLiftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι)) :
    IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          (F (q.2.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.2.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          (F (q.2.1, q.2.2 0, pointTupleTail q.2.2)).total }

private lemma commuteGHalfSandwich_moveChainLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (A B : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (MoveQ params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (MoveQ params (r + 1)))
      (commuteGHalfSandwich_moveChainLiftFamily params family r A)
      (commuteGHalfSandwich_moveChainLiftFamily params family r B)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution (MoveQ params r × SliceQuestion params))
        (fun q => A q.1)
        (fun q => B q.1)
        δ :=
    sddOpRel_uniform_fst ψbi A B δ hAB
  have hABlift :
      SDDOpRel ψbi
        (uniformDistribution (MoveQ params (r + 1)))
        (fun q => A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
        (fun q => B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
        δ :=
    (sddOpRel_uniform_equiv (commuteGHalfSandwich_moveChainLiftQuestionEquiv params r) ψbi
      (fun q => A q.1)
      (fun q => B q.1)
      δ).1 hABfst
  let C : (MoveQ params (r + 1)) →
      (MoveO params r) → GHatOutcome params →
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
                  rw [show
                      (leftTensor (ι₂ := ι)
                        ((gHatIdxMeas params family q.1).outcome g₁))ᴴ =
                        leftTensor (ι₂ := ι)
                        (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) by
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
      (MoveQ params (r + 1))
      ((MoveO params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1
        total := ∑ ag :
          ((MoveO params r) ×
              GHatOutcome params),
          C q ag.1 ag.2 *
            (A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome
                ag.1 }
  let rawTarget : IdxOpFamily
      (MoveQ params (r + 1))
      ((MoveO params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1
        total := ∑ ag :
          ((MoveO params r) ×
              GHatOutcome params),
          C q ag.1 ag.2 *
            (B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome
                ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (MoveQ params (r + 1)))
      (fun q => A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
      (fun q => B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
      C δ hABlift hC
  have hreindex := CommutativityPoints.sddOpRel_reindex
    (commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r)
    ψbi
    (uniformDistribution (MoveQ params (r + 1)))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun a' =>
          (rawSource q).outcome ((commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily
      (MoveQ params (r + 1))
      (MoveO params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun a' =>
          (rawTarget q).outcome ((commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (MoveQ params (r + 1)))
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

private lemma commuteGHalfSandwich_moveChainLift_moveFamily_eq_moveStepMid
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveChainLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome
        ogs =
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
              A, B, G, T,
              leftTensor_mul_leftTensor]
    _ =
        (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (B * G)) *
          rightTensor (ι₁ := ι) T := by
          simp [mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
          rw [leftTensor_mul_leftTensor]
    _ = (commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailQuestionEquiv params r) q)).outcome
          ((moveTailOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepMidFamily, moveTailQuestionEquiv,
              moveTailOutcomeEquiv, A, B, G, T, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_moveChainLift_moveFamily_last
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
      (uniformDistribution (MoveQ params (r + 1)))
      (commuteGHalfSandwich_moveChainLiftFamily params family r
        (commuteGHalfSandwich_moveFamily params family r))
      (commuteGHalfSandwich_moveFamily params family (r + 1))
      (gHatSelfConsistencyError zeta) := by
  have hmid :
      SDDOpRel ψbi
        (uniformDistribution (MoveQ params (r + 1)))
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
    (uniformDistribution (MoveQ params (r + 1)))
    (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
      ((moveTailQuestionEquiv params r) q))
    (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
      ((moveTailQuestionEquiv params r) q))
    (gHatSelfConsistencyError zeta)
    hmid
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (MoveQ params (r + 1)))
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

private noncomputable def commuteGHalfSandwich_moveChainFamily
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

private lemma commuteGHalfSandwich_moveChainFamily_zero
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

private lemma commuteGHalfSandwich_moveChainFamily_last
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

private lemma commuteGHalfSandwich_moveChain_step
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

private lemma commuteGHalfSandwich_move_chain
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

private lemma commuteGHalfSandwich_secondSliceLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (A B : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (MoveQ params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (MoveQ params (r + 1)))
      (commuteGHalfSandwich_secondSliceLiftFamily params family r A)
      (commuteGHalfSandwich_secondSliceLiftFamily params family r B)
      δ := by
  let eQ :
      (MoveQ params (r + 1)) ≃
        (MoveQ params (r + 1)) :=
    { toFun := fun q => (q.2.1, q.1, q.2.2)
      invFun := fun q => (q.2.1, q.1, q.2.2)
      left_inv := by
        intro q
        rcases q with ⟨x₁, x₂, xs⟩
        rfl
      right_inv := by
        intro q
        rcases q with ⟨x₁, x₂, xs⟩
        rfl }
  let eO :
      (MoveO params (r + 1)) ≃
        (MoveO params (r + 1)) :=
    { toFun := fun ogs => (ogs.2.1, ogs.1, ogs.2.2)
      invFun := fun ogs => (ogs.2.1, ogs.1, ogs.2.2)
      left_inv := by
        intro ogs
        rcases ogs with ⟨g₁, g₂, gs⟩
        rfl
      right_inv := by
        intro ogs
        rcases ogs with ⟨g₁, g₂, gs⟩
        rfl }
  have hlift :=
    commuteGHalfSandwich_moveChainLift params ψbi family r A B δ hAB
  have hswapQ :
      SDDOpRel ψbi
        (uniformDistribution (MoveQ params (r + 1)))
        (fun q =>
          commuteGHalfSandwich_moveChainLiftFamily params family r A (eQ.symm q))
        (fun q =>
          commuteGHalfSandwich_moveChainLiftFamily params family r B (eQ.symm q))
        δ :=
    (sddOpRel_uniform_equiv eQ ψbi
      (commuteGHalfSandwich_moveChainLiftFamily params family r A)
      (commuteGHalfSandwich_moveChainLiftFamily params family r B)
      δ).1 hlift
  have hreindex := CommutativityPoints.sddOpRel_reindex eO
    ψbi
    (uniformDistribution (MoveQ params (r + 1)))
    (fun q =>
      commuteGHalfSandwich_moveChainLiftFamily params family r A (eQ.symm q))
    (fun q =>
      commuteGHalfSandwich_moveChainLiftFamily params family r B (eQ.symm q))
    δ hswapQ
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (MoveQ params (r + 1)))
    _ _
    (commuteGHalfSandwich_secondSliceLiftFamily params family r A)
    (commuteGHalfSandwich_secondSliceLiftFamily params family r B)
    δ
    (fun q ogs => by
      simp [eQ, eO, commuteGHalfSandwich_moveChainLiftFamily,
        commuteGHalfSandwich_secondSliceLiftFamily])
    (fun q ogs => by
      simp [eQ, eO, commuteGHalfSandwich_moveChainLiftFamily,
        commuteGHalfSandwich_secondSliceLiftFamily])
    hreindex

private noncomputable def commuteGHalfSandwich_moveBackChainFamily
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

private lemma commuteGHalfSandwich_moveBackChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveBackChainFamily params family r (Fin.last r) q).outcome
      ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
  let q' : MoveQ params r :=
    (q.1, q.2.2 0, pointTupleTail q.2.2)
  let ogs' : MoveO params r :=
    (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
  have hzero :
      (commuteGHalfSandwich_secondSliceLiftFamily params family r
        ((commuteGHalfSandwich_moveChainFamily params family r) 0) q).outcome
          ogs =
        (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
    calc
      (commuteGHalfSandwich_secondSliceLiftFamily params family r
        ((commuteGHalfSandwich_moveChainFamily params family r) 0) q).outcome ogs
        = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
            (commuteGHalfSandwich_moveSourceFamily params family r q').outcome ogs' := by
              simpa [commuteGHalfSandwich_secondSliceLiftFamily, q', ogs'] using
                congrArg
                  (fun X =>
                    leftTensor (ι₂ := ι)
                        ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                      X)
                  (commuteGHalfSandwich_moveChainFamily_zero params family r q' ogs')
      _ = (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
            exact commuteGHalfSandwich_secondSliceLift_moveSource params family r q ogs
  simpa [commuteGHalfSandwich_moveBackChainFamily] using hzero

private lemma commuteGHalfSandwich_secondSliceLift_moveFamily_eq_swappedFrontMoveStepMid
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

private lemma commuteGHalfSandwich_commute_eq_swappedFrontMoveStepTarget
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

private lemma commuteGHalfSandwich_moveBackChain_step
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    ∀ i : Fin r,
      SDDOpRel ψbi
        (uniformDistribution (MoveQ params (r + 1)))
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.succ)
        (gHatSelfConsistencyError zeta)
  | i => by
      let j : Fin r := ⟨r - i.1 - 1, by omega⟩
      have hstep := commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc r j
      have hlift := commuteGHalfSandwich_secondSliceLift params ψbi family r
        ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc)
        ((commuteGHalfSandwich_moveChainFamily params family r) j.succ)
        (gHatSelfConsistencyError zeta)
        hstep
      have hsymm := Preliminaries.sddOpRel_symm ψbi
        (uniformDistribution (MoveQ params (r + 1)))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.succ))
        (gHatSelfConsistencyError zeta)
        hlift
      have hsrc : (⟨r - i.1, by omega⟩ : Fin (r + 1)) = j.succ := by
        apply Fin.ext
        dsimp [j]
        omega
      have htgt : (⟨r - (i.1 + 1), by omega⟩ : Fin (r + 1)) = j.castSucc := by
        apply Fin.ext
        dsimp [j]
        omega
      exact CommutativityPoints.sddOpRel_congr_outcome ψbi
        (uniformDistribution (MoveQ params (r + 1)))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.succ))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc))
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.succ)
        (gHatSelfConsistencyError zeta)
        (fun q ogs => by
          simp [commuteGHalfSandwich_moveBackChainFamily, j, hsrc])
        (fun q ogs => by
          simp [commuteGHalfSandwich_moveBackChainFamily, j, htgt])
        hsymm

private lemma commuteGHalfSandwich_commute_to_moveBackChainFamily_zero
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

private lemma commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily
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

private def commuteGHalfSandwich_postMoveFlatLength : ℕ → ℕ
  | 0 => 1
  | r + 1 => commuteGHalfSandwich_postMoveFlatLength r + 2

private lemma commuteGHalfSandwich_postMoveFlatLength_pos
    (r : ℕ) :
    1 ≤ commuteGHalfSandwich_postMoveFlatLength r := by
  induction r with
  | zero => simp [commuteGHalfSandwich_postMoveFlatLength]
  | succ r ih =>
      simp [commuteGHalfSandwich_postMoveFlatLength]

private noncomputable def commuteGHalfSandwich_postMoveFlatFamily
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

private noncomputable def commuteGHalfSandwich_postMoveFlatError
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

private lemma commuteGHalfSandwich_postMoveFlatError_sum
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
        gHatSelfConsistencyError, Nat.mod_eq_of_lt hone_lt]
      ring

private def commuteGHalfSandwich_flatChainLength (r : ℕ) : ℕ :=
  r + commuteGHalfSandwich_postMoveFlatLength r

private noncomputable def commuteGHalfSandwich_flatChainFamily
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

private noncomputable def commuteGHalfSandwich_flatChainError
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

private lemma commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget
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

private lemma commuteGHalfSandwich_postMoveFlatLength_eq
    (r : ℕ) :
    commuteGHalfSandwich_postMoveFlatLength r = 2 * r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [commuteGHalfSandwich_postMoveFlatLength, ih, Nat.mul_add,
        Nat.add_left_comm, Nat.add_comm]

private lemma commuteGHalfSandwich_secondSliceLift_recursiveTarget
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

private lemma commuteGHalfSandwich_postMoveFlatFamily_zero_active
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

private lemma commuteGHalfSandwich_postMoveFlatFamily_one_active
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

private lemma commuteGHalfSandwich_postMoveFlatFamily_last_active
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

private lemma commuteGHalfSandwich_flatChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (r : ℕ) (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_flatChainFamily params family r 0 q).outcome
      ogs =
      (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs := by
  simp [commuteGHalfSandwich_flatChainFamily,
    commuteGHalfSandwich_moveChainFamily_zero params family r]

private lemma commuteGHalfSandwich_flatChainError_sum
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

private lemma commuteGHalfSandwich_flatChainFamily_last
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

private lemma commuteGHalfSandwich_postMoveFlatStep
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
        (uniformDistribution (MoveQ params r))
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
        (fun q ogs => commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget params family
            q ogs)
        hcomm0
  | r + 1, i => by
      by_cases hi0 : i.1 = 0
      · have hcomm1 := commuteGHalfSandwich_step_commute
            params ψbi family gamma zeta (r + 1) hcom
        have hsrc_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.castSucc q).outcome
                ogs =
                (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs := by
          intro q ogs
          simp [commuteGHalfSandwich_postMoveFlatFamily, hi0]
        have htgt_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.succ q).outcome
                ogs =
                (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
          intro q ogs
          simp [commuteGHalfSandwich_postMoveFlatFamily, hi0]
        simpa [commuteGHalfSandwich_postMoveFlatError, hi0] using
          (CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                PointTuple params (r + 1)))
            (commuteGHalfSandwich_moveFamily params family (r + 1))
            (commuteGHalfSandwich_commuteFamily params family (r + 1))
            ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc)
            ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ)
            (gHatCommutationError params gamma zeta)
            (fun q ogs => (hsrc_eq q ogs).symm)
            (fun q ogs => (htgt_eq q ogs).symm)
            hcomm1)
      · by_cases hi1 : i.1 = 1
        · have hzero := commuteGHalfSandwich_commute_to_moveBackChainFamily_zero params ψbi
            family zeta (r := r) hsc
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.castSucc q).outcome
                  ogs =
                  (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            simp [commuteGHalfSandwich_postMoveFlatFamily, hi1]
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.succ q).outcome
                  ogs =
                  ((commuteGHalfSandwich_moveBackChainFamily params family r) 0 q).outcome
                    ogs := by
            intro q ogs
            have hi2 : i.1 + 1 ≠ 0 := by omega
            have hi2' : i.1 + 1 ≠ 1 := by omega
            have hinner0_nat : i.1 - 1 = 0 := by omega
            have hinner0 :
                (⟨i.1 - 1, by
                    have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                      exact i.2
                    omega⟩ : Fin (commuteGHalfSandwich_postMoveFlatLength r + 1)) = 0 := by
              apply Fin.ext
              simp [hinner0_nat]
            let q' : MoveQ params r :=
              (q.1, q.2.2 0, pointTupleTail q.2.2)
            let ogs' : MoveO params r :=
              (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
            have hzero_active :
                ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0 q').outcome ogs' =
                  (commuteGHalfSandwich_moveFamily params family r q').outcome ogs' :=
              commuteGHalfSandwich_postMoveFlatFamily_zero_active params family r q' ogs'
            have hsecond_eq :
                (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                  (commuteGHalfSandwich_splitSuccLiftFamily params r
                    ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0)) q).outcome
                      ogs =
                  (commuteGHalfSandwich_secondSliceLiftFamily params family r
                    (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
              calc
                (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                  (commuteGHalfSandwich_splitSuccLiftFamily params r
                    ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0)) q).outcome ogs
                    = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                        ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0)
                          q).outcome ogs := by
                          rw [
                  commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift
                          ]
                _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                      (commuteGHalfSandwich_moveFamily params family r)
                      q).outcome ogs := by
                    change leftTensor (ι₂ := ι)
                      ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                        (((commuteGHalfSandwich_postMoveFlatFamily params family r) 0
                          q').outcome ogs') = _
                    exact congrArg
                      (fun X =>
                        let G := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
                        leftTensor (ι₂ := ι) G * X)
                      hzero_active
            calc
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.succ q).outcome ogs
                = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0)) q).outcome
                    ogs := by
                        conv_lhs => simp [commuteGHalfSandwich_postMoveFlatFamily, hi2, hi2']
                        simp [hi0, hinner0]
              _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                    (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := hsecond_eq
              _ = ((commuteGHalfSandwich_moveBackChainFamily params family r) 0 q).outcome
                    ogs := by
                    simpa using
                      (commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily
                        params family r q ogs).symm
          simpa [commuteGHalfSandwich_postMoveFlatError, hi0, hi1] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                  PointTuple params (r + 1)))
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
                exact i.2
              omega⟩
          have hsmall := commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc
              hcom r j
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
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.castSucc q).outcome
                  ogs =
                  (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc))
                        q).outcome ogs := by
            intro q ogs
            have hsrc_not0 : i.1 ≠ 0 := hi0
            have hsrc_not1 : i.1 ≠ 1 := hi1
            simp [commuteGHalfSandwich_postMoveFlatFamily, hsrc_not0, hsrc_not1, j]
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.succ q).outcome
                  ogs =
                  (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ))
                        q).outcome ogs := by
            intro q ogs
            have htgt_not0 : i.1 + 1 ≠ 0 := by omega
            have htgt_not1 : i.1 + 1 ≠ 1 := by omega
            have hj_succ :
                (j.succ : Fin (commuteGHalfSandwich_postMoveFlatLength r + 1)) =
                  ⟨i.1 - 1, by
                    have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                      exact i.2
                    omega⟩ := by
              apply Fin.ext
              dsimp [j]
              omega
            calc
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.succ q).outcome ogs
                = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r)
                        ⟨i.1 - 1, by
                          have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                            exact i.2
                          omega⟩)) q).outcome ogs := by
                        conv_lhs => simp [commuteGHalfSandwich_postMoveFlatFamily, htgt_not0,
                            htgt_not1]
                        simp [hi0]
              _ = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ))
                        q).outcome ogs := by
                        have hidx :
                            ((commuteGHalfSandwich_postMoveFlatFamily params family r)
                              ⟨i.1 - 1, by
                                have hi_lt :
                                    i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                                  exact i.2
                                omega⟩) =
                              ((commuteGHalfSandwich_postMoveFlatFamily params family r)
                                j.succ) := by
                                exact congrArg
                                  (fun idx =>
                                    (commuteGHalfSandwich_postMoveFlatFamily params family r) idx)
                                  hj_succ.symm
                        simp [hidx]
          simpa [commuteGHalfSandwich_postMoveFlatError, hi0, hi1, j] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                  PointTuple params (r + 1)))
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

private lemma commuteGHalfSandwich_flatChainStep
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
        (uniformDistribution (MoveQ params r))
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
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.castSucc q).outcome
                ogs =
                ((commuteGHalfSandwich_moveChainFamily params family (r + 1))
                  imove.castSucc q).outcome ogs := by
          intro q ogs
          have hsrc_le : i.1 ≤ r + 1 := by omega
          conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_le]
          rfl
        have htgt_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome
                ogs =
                ((commuteGHalfSandwich_moveChainFamily params family (r + 1))
                  imove.succ q).outcome ogs := by
          intro q ogs
          have htgt_le : i.1 ≤ r := by omega
          conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_le]
          rfl
        simpa [commuteGHalfSandwich_flatChainError, hi] using
          (CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                PointTuple params (r + 1)))
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
        · have hcomm1 := commuteGHalfSandwich_step_commute
            params ψbi family gamma zeta (r + 1) hcom
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.castSucc q).outcome
                  ogs =
                  (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            have hsrc_le : i.1 ≤ r + 1 := by omega
            conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_le]
            simpa [hboundary, Fin.last] using
              commuteGHalfSandwich_moveChainFamily_last params family (r + 1) q ogs
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome
                  ogs =
                  (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            have htgt_not : ¬ i.1 ≤ r := by omega
            have hone_lt : 1 < commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1 := by
              rw [commuteGHalfSandwich_postMoveFlatLength_eq]
              omega
            calc
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome ogs
                = (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
                    ⟨i.1 - r, by
                      simpa [hboundary] using hone_lt⟩ q).outcome ogs := by
                        conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_not]
              _ = (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
                    ⟨1, by exact hone_lt⟩ q).outcome ogs := by
                    have hone :
                        (⟨i.1 - r, by simpa [hboundary] using hone_lt⟩ :
                          Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) =
                          ⟨1, by exact hone_lt⟩ := by
                      apply Fin.ext
                      simp [hboundary]
                    exact congrArg
                      (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  idx q).outcome ogs)
                      hone
                  _ = (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome
                    ogs := by
                    exact
                      commuteGHalfSandwich_postMoveFlatFamily_one_active
                        params family (r := r) q ogs
          simpa [commuteGHalfSandwich_flatChainError, hi, hboundary,
            commuteGHalfSandwich_postMoveFlatError] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                  PointTuple params (r + 1)))
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
                exact i.2
              omega⟩
          have hsmall := commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc
              hcom (r + 1) j
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.castSucc q).outcome
                  ogs =
                  ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  j.castSucc q).outcome ogs := by
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
              (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  idx q).outcome ogs)
              hj_castSucc
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome
                  ogs =
                  ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                    j.succ q).outcome ogs := by
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
              (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  idx q).outcome ogs)
              hj_succ
          simpa [commuteGHalfSandwich_flatChainError, hi, hboundary, j] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                  PointTuple params (r + 1)))
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.castSucc)
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.succ)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
              ((commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1)) j)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hsmall)

/-- Bridge: the staged move-commute-move chain for `commuteGHalfSandwich`.

Constructs the sequence of `3k - 4` intermediate bipartite operator families
joined by `3k - 5` elementary edges. These edges repeatedly move `Ĝ₁` through
the product `Ĝ₁ · Ĝ₂ · ⋯ · Ĝₖ` using self-consistency (move to right tensor,
error `2ζ`) and pairwise commutation (swap past neighbor, error `ν₃`), then
compose them in one call to `sddOpRel_chain`, avoiding the exponential loss from
recursive macro-chain composition.

Paper reference: `lem:commute-g-half-sandwich` computation in
`ld-pasting.tex` lines 881–914. -/
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
          (fun q => qSDDOp ψbi (gHatPairProductLeft params family q)
            (gHatPairProductRight params family q))
          (fun q => Preliminaries.qSDDOp_nonneg ψbi _ _))
        hν3
    have hchain := Preliminaries.sddOpRel_chain
      ψbi
      (uniformDistribution (MoveQ params r))
      (commuteGHalfSandwich_flatChainLength r)
      (commuteGHalfSandwich_flatChainFamily params family r)
      (commuteGHalfSandwich_flatChainError params gamma zeta r)
      (commuteGHalfSandwich_flatChainStep params ψbi family gamma zeta hsc0 hcom0 r)
    have hsplit :
        SDDOpRel ψbi
          (uniformDistribution (MoveQ params r))
          (commuteGHalfSandwich_moveSourceFamily params family r)
          (commuteGHalfSandwich_recursiveTargetFamily params family r)
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i) := by
      exact CommutativityPoints.sddOpRel_congr_outcome ψbi
        (uniformDistribution (MoveQ params r))
        ((commuteGHalfSandwich_flatChainFamily params family r) 0)
        ((commuteGHalfSandwich_flatChainFamily params family r)
          (Fin.last (commuteGHalfSandwich_flatChainLength r)))
        (commuteGHalfSandwich_moveSourceFamily params family r)
        (commuteGHalfSandwich_recursiveTargetFamily params family r)
        (((commuteGHalfSandwich_flatChainLength r : Error)) *
          ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
            commuteGHalfSandwich_flatChainError params gamma zeta r i)
        (fun q ogs => by
          simpa using commuteGHalfSandwich_flatChainFamily_zero params family r q ogs)
        (fun q ogs => by
          simpa using commuteGHalfSandwich_flatChainFamily_last params family r q ogs)
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
          4 * (r : Error) * zeta +
            ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta :=
      commuteGHalfSandwich_flatChainError_sum params gamma zeta r
    have hlen_le :
        ((commuteGHalfSandwich_flatChainLength r : ℕ) : Error) ≤ 3 * (k : Error) := by
      have hflat :
          ((commuteGHalfSandwich_flatChainLength r : ℕ) : Error) =
            3 * (r : Error) + 1 := by
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
          4 * ((r : Error) + 2) * zeta + ((r : Error) + 2)
              * gHatCommutationError params gamma zeta =
            4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error)
                * gHatCommutationError params gamma zeta +
              (8 * zeta + gHatCommutationError params gamma zeta) := by
        rw [hcast_r1]
        ring
      nlinarith [hrewrite, hζextra, hνextra]
    have hsum_nonneg :
        0 ≤
          4 * (r : Error) * zeta +
            ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta := by
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
      (le_trans hraw_bound
        (commuteGHalfSandwich_error_bound params gamma zeta k hzeta_nonneg hzeta_le))

end MIPStarRE.LDT.Pasting
