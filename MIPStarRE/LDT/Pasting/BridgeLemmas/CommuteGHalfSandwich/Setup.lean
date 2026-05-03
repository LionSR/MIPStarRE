import MIPStarRE.LDT.CommutativityPoints.SharedHelpers.Core
import MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPStarRE.LDT.Pasting.BridgeLemmas.Common

/-!
# Section 12 pasting: commute G half-sandwich setup

Tuple equivalences, split families, base cases, and local step lemmas for the half-sandwich
commutation chain.

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

/-! ### Bridge lemmas for the sandwich chain

These lemmas capture the infrastructure needed for the `lem:commute-g-half-sandwich`
through `cor:h-a-consistency` chain in `ld-pasting.tex` §9.3.

The n-step SDDOpRel composition lemma (`sddOpRel_chain`) now lives in
`Preliminaries.Theorems` alongside `sddOpRel_triangle`, since it is a
general-purpose result used by multiple chapters. -/

def pointTupleConsEquiv (params : Parameters) (k : ℕ) :
    PointTuple params (k + 1) ≃ SliceQuestion params × PointTuple params k where
  toFun xs := (xs 0, pointTupleTail xs)
  invFun p := Fin.cons p.1 p.2
  left_inv xs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    rfl

def gHatTupleOutcomeConsEquiv' (params : Parameters) [FieldModel params.q] (k : ℕ) :
    GHatTupleOutcome params (k + 1) ≃ GHatOutcome params × GHatTupleOutcome params k where
  toFun gs := (gs 0, gHatTupleOutcomeTail gs)
  invFun p := Fin.cons p.1 p.2
  left_inv gs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    rfl

omit [DecidableEq ι] in
lemma conjTranspose_mul_mono_local
    {X Y Z : MIPStarRE.Quantum.Op ι}
    (hXY : X ≤ Y) :
    Zᴴ * X * Z ≤ Zᴴ * Y * Z := by
  apply sub_nonneg.mp
  have hnonneg : 0 ≤ Zᴴ * (Y - X) * Z := by
    simpa [Matrix.conjTranspose_conjTranspose] using
      (Matrix.PosSemidef.mul_mul_conjTranspose_same
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hXY))
        Zᴴ).nonneg
  simpa [mul_sub, sub_mul, Matrix.conjTranspose_conjTranspose, mul_assoc] using hnonneg

noncomputable def gHatReverseHalfProductOutcomeOperator
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      gHatReverseHalfProductOutcomeOperator params family k
          (pointTupleTail xs) (gHatTupleOutcomeTail gs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0)

noncomputable def headTailOrderedFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family r q.2 ogs.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) (gHatHalfProductTotalOperator params family r q.2) }

noncomputable def headTailRotatedFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι)
          (gHatHalfProductOutcomeOperator params family r q.2 ogs.2) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1)
      total :=
        leftTensor (ι₂ := ι) (gHatHalfProductTotalOperator params family r q.2) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) }

noncomputable def commuteGHalfSandwich_moveFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          rightTensor (ι₁ := ι)
            (gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          rightTensor (ι₁ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2) }

noncomputable def commuteGHalfSandwich_commuteFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          rightTensor (ι₁ := ι)
            (gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          rightTensor (ι₁ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2) }

noncomputable def commuteGHalfSandwich_moveBackFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2) }

lemma gHatHalfSandwichLeft_split_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1))
    (gs : GHatTupleOutcome params (k + 1)) :
    (gHatHalfSandwichLeft params family (k + 1) xs).outcome gs =
      (headTailOrderedFamily params family k ((pointTupleConsEquiv params k) xs)).outcome
        ((gHatTupleOutcomeConsEquiv' params k) gs) := by
  simp [gHatHalfSandwichLeft, headTailOrderedFamily,
    pointTupleConsEquiv, gHatTupleOutcomeConsEquiv',
    gHatHalfProductOutcomeOperator, OpFamily.leftPlacedOpFamily,
    leftTensor_mul_leftTensor]

lemma gHatHalfSandwichLeft_split_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1)) :
    (gHatHalfSandwichLeft params family (k + 1) xs).total =
      (headTailOrderedFamily params family k ((pointTupleConsEquiv params k) xs)).total := by
  simp [gHatHalfSandwichLeft, headTailOrderedFamily,
    pointTupleConsEquiv, gHatHalfProductTotalOperator,
    OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor]

lemma gHatHalfSandwichRight_split_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1))
    (gs : GHatTupleOutcome params (k + 1)) :
    (gHatHalfSandwichRight params family (k + 1) xs).outcome gs =
      (headTailRotatedFamily params family k ((pointTupleConsEquiv params k) xs)).outcome
        ((gHatTupleOutcomeConsEquiv' params k) gs) := by
  simp [gHatHalfSandwichRight, headTailRotatedFamily,
    pointTupleConsEquiv, gHatTupleOutcomeConsEquiv',
    gHatRotatedHalfProductOutcomeOperator, OpFamily.leftPlacedOpFamily,
    leftTensor_mul_leftTensor]

lemma gHatHalfSandwichRight_split_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1)) :
    (gHatHalfSandwichRight params family (k + 1) xs).total =
      (headTailRotatedFamily params family k ((pointTupleConsEquiv params k) xs)).total := by
  simp [gHatHalfSandwichRight, headTailRotatedFamily,
    pointTupleConsEquiv, gHatRotatedHalfProductTotalOperator,
    OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor]

lemma sddOpRel_uniform_equiv
    {α β Outcome : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    (e : α ≃ β)
    (ψ : QuantumState (ι × ι))
    (A B : IdxOpFamily α Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψ (uniformDistribution α) A B δ ↔
      SDDOpRel ψ (uniformDistribution β)
        (fun b => A (e.symm b))
        (fun b => B (e.symm b))
        δ := by
  constructor
  · intro ⟨h⟩
    constructor
    unfold sddErrorOp at *
    calc
      avgOver (uniformDistribution β) (fun b => qSDDOp ψ (A (e.symm b)) (B (e.symm b)))
        = avgOver (uniformDistribution α) (fun a => qSDDOp ψ (A a) (B a)) := by
            simpa using (avgOver_uniform_equiv e (fun a => qSDDOp ψ (A a) (B a))).symm
      _ ≤ δ := h
  · intro ⟨h⟩
    constructor
    unfold sddErrorOp at *
    calc
      avgOver (uniformDistribution α) (fun a => qSDDOp ψ (A a) (B a))
        = avgOver (uniformDistribution β) (fun b => qSDDOp ψ (A (e.symm b)) (B (e.symm b))) := by
            simpa using (avgOver_uniform_equiv e (fun a => qSDDOp ψ (A a) (B a)))
      _ ≤ δ := h

lemma commuteGHalfSandwich_split_iff
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k : ℕ) (δ : Error) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params (k + 1)))
      (gHatHalfSandwichLeft params family (k + 1))
      (gHatHalfSandwichRight params family (k + 1))
      δ ↔
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      (headTailOrderedFamily params family k)
      (headTailRotatedFamily params family k)
      δ := by
  constructor
  · intro h
    have hq :=
      (sddOpRel_uniform_equiv (pointTupleConsEquiv params k) ψbi
        (gHatHalfSandwichLeft params family (k + 1))
        (gHatHalfSandwichRight params family (k + 1)) δ).1 h
    have ho := CommutativityPoints.sddOpRel_reindex (gHatTupleOutcomeConsEquiv' params k)
      ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      (fun q => gHatHalfSandwichLeft params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      (fun q => gHatHalfSandwichRight params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      δ hq
    exact CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      _ _
      (headTailOrderedFamily params family k)
      (headTailRotatedFamily params family k)
      δ
      (fun q ogs => by
        simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
          gHatHalfSandwichLeft_split_outcome params family k
            ((pointTupleConsEquiv params k).symm q)
            ((gHatTupleOutcomeConsEquiv' params k).symm ogs))
      (fun q ogs => by
        simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
          gHatHalfSandwichRight_split_outcome params family k
            ((pointTupleConsEquiv params k).symm q)
            ((gHatTupleOutcomeConsEquiv' params k).symm ogs))
      ho
  · intro h
    have ho := CommutativityPoints.sddOpRel_reindex (gHatTupleOutcomeConsEquiv' params k).symm
      ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      (headTailOrderedFamily params family k)
      (headTailRotatedFamily params family k)
      δ h
    have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      _ _
      (fun q => gHatHalfSandwichLeft params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      (fun q => gHatHalfSandwichRight params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      δ
      (fun q gs => by
        simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
          (gHatHalfSandwichLeft_split_outcome params family k
            ((pointTupleConsEquiv params k).symm q) gs).symm)
      (fun q gs => by
        simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
          (gHatHalfSandwichRight_split_outcome params family k
            ((pointTupleConsEquiv params k).symm q) gs).symm)
      ho
    exact (sddOpRel_uniform_equiv (pointTupleConsEquiv params k) ψbi
      (gHatHalfSandwichLeft params family (k + 1))
      (gHatHalfSandwichRight params family (k + 1)) δ).2 hq

lemma commuteGHalfSandwich_split_zero
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params 0))
      (headTailOrderedFamily params family 0)
      (headTailRotatedFamily params family 0)
      0 := by
  refine ⟨?_⟩
  unfold sddErrorOp qSDDOp qSDDCore headTailOrderedFamily headTailRotatedFamily
  simp [gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor]
  have hzero :
      avgOver (uniformDistribution (SliceQuestion params × PointTuple params 0))
        (fun q => ((Fintype.card (Polynomial params) : Error) + 1) * ev ψbi 0) = 0 := by
    simp [avgOver, uniformDistribution, ev_zero]
  nlinarith [hzero]

lemma gHatSelfConsistency_sddOpRel
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
      (gHatSelfConsistencyError zeta) := by
  rcases hsc with ⟨h⟩
  exact ⟨by simpa [sddError, sddErrorOp, qSDD, qSDDOp] using h⟩

lemma sddOpRel_uniform_fst
    {α β Outcome : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : IdxOpFamily α Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψ (uniformDistribution α) A B δ →
      SDDOpRel ψ (uniformDistribution (α × β))
        (fun ab => A ab.1)
        (fun ab => B ab.1)
        δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => qSDDOp ψ (A ab.1) (B ab.1))
      = avgOver (uniformDistribution α) (fun a => qSDDOp ψ (A a) (B a)) := by
          exact avgOver_uniform_fst (fun a => qSDDOp ψ (A a) (B a))
    _ ≤ δ := h

lemma gHatSelfConsistency_sddOpRel_triple
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
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
      (gHatSelfConsistencyError zeta) := by
  exact sddOpRel_uniform_fst ψbi
    (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
    (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
    (gHatSelfConsistencyError zeta)
    (gHatSelfConsistency_sddOpRel params ψbi family zeta hsc)

lemma gHatPairProduct_sddOpRel_triple
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (r : ℕ)
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => gHatPairProductLeft params family (q.1, q.2.1))
      (fun q => gHatPairProductRight params family (q.1, q.2.1))
      (gHatCommutationError params gamma zeta) := by
  have hfst :
      SDDOpRel ψbi
        (uniformDistribution (SlicePairQuestion params × PointTuple params r))
        (fun q => gHatPairProductLeft params family q.1)
        (fun q => gHatPairProductRight params family q.1)
        (gHatCommutationError params gamma zeta) := (sddOpRel_uniform_fst
    (α := SlicePairQuestion params)
    (β := PointTuple params r)
    ψbi
    (gHatPairProductLeft params family)
    (gHatPairProductRight params family)
    (gHatCommutationError params gamma zeta)
    hcom)
  exact (sddOpRel_uniform_equiv
    (Equiv.prodAssoc (SliceQuestion params) (SliceQuestion params) (PointTuple params r))
    ψbi
    (fun q => gHatPairProductLeft params family q.1)
    (fun q => gHatPairProductRight params family q.1)
    (gHatCommutationError params gamma zeta)).1 hfst

lemma gHatIdxMeas_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    (gHatIdxMeas params family x).outcome g * (gHatIdxMeas params family x).outcome g =
      (gHatIdxMeas params family x).outcome g := by
  cases g with
  | none =>
      let T := (family.meas x).total
      change (1 - T) * (1 - T) = 1 - T
      have hTT : T * T = T := by
        simpa [T] using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x)
      calc
        (1 - T) * (1 - T) = 1 - T - T + T * T := by
          noncomm_ring
        _ = 1 - T := by
          rw [hTT]
          abel
  | some p =>
      simp [gHatIdxMeas, completeSubMeas, (family.meas x).proj p]

lemma gHatHalfProduct_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r (xs : PointTuple params r),
      ∑ gs : GHatTupleOutcome params r,
          (gHatHalfProductOutcomeOperator params family r xs gs)ᴴ *
            gHatHalfProductOutcomeOperator params family r xs gs ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro xs
      simp [gHatHalfProductOutcomeOperator]
  | succ r ihr =>
      intro xs
      let G : GHatOutcome params → MIPStarRE.Quantum.Op ι :=
        fun g => (gHatIdxMeas params family (xs 0)).outcome g
      let T : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
        fun gs => gHatHalfProductOutcomeOperator params family r (pointTupleTail xs) gs
      have hsplit :
          (∑ gs : GHatTupleOutcome params (r + 1),
              (gHatHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
                gHatHalfProductOutcomeOperator params family (r + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              ((G p.1 * T p.2)ᴴ) * (G p.1 * T p.2) := by
        exact Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r)
          (fun gs : GHatTupleOutcome params (r + 1) =>
            (gHatHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
              gHatHalfProductOutcomeOperator params family (r + 1) xs gs)
          (fun p : GHatOutcome params × GHatTupleOutcome params r =>
            ((G p.1 * T p.2)ᴴ) * (G p.1 * T p.2))
          (by
            intro gs
            rfl)
      rw [hsplit, ← Finset.univ_product_univ, Finset.sum_product]
      calc
        ∑ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params r, ((G g * T gs)ᴴ) * (G g * T gs)
          = ∑ gs : GHatTupleOutcome params r,
              ∑ g : GHatOutcome params, (T gs)ᴴ * G g * T gs := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl ?_
                intro gs _
                refine Finset.sum_congr rfl ?_
                intro g _
                calc
                  ((G g * T gs)ᴴ) * (G g * T gs)
                    = (T gs)ᴴ * ((G g)ᴴ * G g) * T gs := by
                        simp [Matrix.conjTranspose_mul, mul_assoc]
                  _ = (T gs)ᴴ * G g * T gs := by
                        have hherm : (G g)ᴴ = G g := by
                          simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
                        have hproj : G g * G g = G g := by
                          simpa [G] using gHatIdxMeas_proj params family (xs 0) g
                        simp [hherm, hproj, mul_assoc]
        _ = ∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * (∑ g : GHatOutcome params, G g) * T gs := by
              refine Finset.sum_congr rfl ?_
              intro gs _
              rw [← Finset.sum_mul, ← Matrix.mul_sum]
        _ = ∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs := by
              refine Finset.sum_congr rfl ?_
              intro gs _
              rw [(gHatIdxMeas params family (xs 0)).sum_eq_total]
              rw [(gHatIdxMeas params family (xs 0)).total_eq_one]
              simp
        _ ≤ 1 := by
              simpa [T] using ihr (pointTupleTail xs)

lemma gHatReverseHalfProduct_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r (xs : PointTuple params r),
      ∑ gs : GHatTupleOutcome params r,
          (gHatReverseHalfProductOutcomeOperator params family r xs gs)ᴴ *
            gHatReverseHalfProductOutcomeOperator params family r xs gs ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro xs
      simp [gHatReverseHalfProductOutcomeOperator]
  | succ r ihr =>
      intro xs
      let T : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
        fun gs => gHatReverseHalfProductOutcomeOperator params family r (pointTupleTail xs) gs
      let G : GHatOutcome params → MIPStarRE.Quantum.Op ι :=
        fun g => ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome g
      have hsplit :
          (∑ gs : GHatTupleOutcome params (r + 1),
              (gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
                gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              ((T p.2 * G p.1)ᴴ) * (T p.2 * G p.1) := by
        exact Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r)
          (fun gs : GHatTupleOutcome params (r + 1) =>
            (gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
              gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs)
          (fun p : GHatOutcome params × GHatTupleOutcome params r =>
            ((T p.2 * G p.1)ᴴ) * (T p.2 * G p.1))
          (by intro gs; rfl)
      rw [hsplit, ← Finset.univ_product_univ, Finset.sum_product]
      calc
        ∑ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params r, ((T gs * G g)ᴴ) * (T gs * G g)
          = ∑ g : GHatOutcome params,
              G g * (∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs) * G g := by
                refine Finset.sum_congr rfl ?_
                intro g _
                calc
                  ∑ gs : GHatTupleOutcome params r, ((T gs * G g)ᴴ) * (T gs * G g)
                    = ∑ gs : GHatTupleOutcome params r, G g * ((T gs)ᴴ * T gs) * G g := by
                        refine Finset.sum_congr rfl ?_
                        intro gs _
                        have hherm : (G g)ᴴ = G g := by
                          simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
                        calc
                          ((T gs * G g)ᴴ) * (T gs * G g)
                            = (G g)ᴴ * ((T gs)ᴴ * T gs) * G g := by
                                simp [Matrix.conjTranspose_mul, mul_assoc]
                          _ = G g * ((T gs)ᴴ * T gs) * G g := by
                                simp [hherm]
                  _ = G g * (∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs) * G g := by
                        rw [← Finset.sum_mul, ← Matrix.mul_sum]
        _ ≤ ∑ g : GHatOutcome params, G g * (1 : MIPStarRE.Quantum.Op ι) * G g := by
              refine Finset.sum_le_sum ?_
              intro g _
              let X : MIPStarRE.Quantum.Op ι :=
                ∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs
              have hX : X ≤ 1 := by
                simpa [X] using ihr (pointTupleTail xs)
              have hherm : (G g)ᴴ = G g := by
                simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
              simpa [X, hherm] using conjTranspose_mul_mono_local (Z := G g) hX
        _ = ∑ g : GHatOutcome params, G g := by
              refine Finset.sum_congr rfl ?_
              intro g _
              have hherm : (G g)ᴴ = G g := by
                simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
              have hproj : G g * G g = G g := by
                simpa [G] using gHatIdxMeas_proj params family (xs 0) g
              simp [hproj]
        _ = 1 := by
              calc
                ∑ g : GHatOutcome params, G g = (gHatIdxMeas params family (xs 0)).total := by
                  simpa [G] using (gHatIdxMeas params family (xs 0)).sum_eq_total
                _ = 1 := (gHatIdxMeas params family (xs 0)).total_eq_one

def thirdSliceFrontEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) ≃
      (SliceQuestion params × (SliceQuestion params × SliceQuestion params ×
          PointTuple params r)) where
  toFun q := (q.2.2.1, (q.1, q.2.1, q.2.2.2))
  invFun q := (q.2.1, q.2.2.1, q.1, q.2.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl
  right_inv q := by
    rcases q with ⟨x₃, x₁, x₂, xs⟩
    rfl

def firstTwoSlicesFrontEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) ≃
      (SlicePairQuestion params × (SliceQuestion params × PointTuple params r)) where
  toFun q := ((q.1, q.2.1), (q.2.2.1, q.2.2.2))
  invFun q := (q.1.1, q.1.2, q.2.1, q.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl
  right_inv q := by
    rcases q with ⟨⟨x₁, x₂⟩, x₃, xs⟩
    rfl

lemma gHatSelfConsistency_sddOpRel_quadThird
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
      (uniformDistribution (SliceQuestion params × SliceQuestion params ×
        SliceQuestion params × PointTuple params r))
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.2.2.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.2.2.1)
      (gHatSelfConsistencyError zeta) := by
  have hfst :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params ×
          (SliceQuestion params × SliceQuestion params × PointTuple params r)))
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
        (gHatSelfConsistencyError zeta) :=
    sddOpRel_uniform_fst ψbi
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
      (gHatSelfConsistencyError zeta)
      (gHatSelfConsistency_sddOpRel params ψbi family zeta hsc)
  simpa [thirdSliceFrontEquiv] using
    (sddOpRel_uniform_equiv (thirdSliceFrontEquiv params r).symm ψbi
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
      (gHatSelfConsistencyError zeta)).1 hfst

/- private lemma gHatSelfConsistency_sddOpRel_quadThird
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
      (uniformDistribution (SliceQuestion params × SliceQuestion params × SliceQuestion params
      × PointTuple params r))
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.2.2.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.2.2.1)
      (gHatSelfConsistencyError zeta) := by
  have hfst :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × (SliceQuestion params × SliceQuestion
        params × PointTuple params r)))
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
        (gHatSelfConsistencyError zeta) :=
    sddOpRel_uniform_fst ψbi
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
      (gHatSelfConsistencyError zeta)
      (gHatSelfConsistency_sddOpRel params ψbi family zeta hsc)
  exact (sddOpRel_uniform_equiv (thirdSliceFrontEquiv params r) ψbi
    (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
    (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
    (gHatSelfConsistencyError zeta)).1 hfst

lemma gHatPairProduct_sddOpRel_quadFirstTwo
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (r : ℕ)
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × SliceQuestion params
      × PointTuple params r))
      (fun q => gHatPairProductLeft params family (q.1, q.2.1))
      (fun q => gHatPairProductRight params family (q.1, q.2.1))
      (gHatCommutationError params gamma zeta) := by
  have hfst :
      SDDOpRel ψbi
        (uniformDistribution (SlicePairQuestion params × (SliceQuestion params × PointTuple
        params r)))
        (fun q => gHatPairProductLeft params family q.1)
        (fun q => gHatPairProductRight params family q.1)
        (gHatCommutationError params gamma zeta) :=
    sddOpRel_uniform_fst ψbi
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)
      hcom
  exact (sddOpRel_uniform_equiv (firstTwoSlicesFrontEquiv params r) ψbi
    (fun q => gHatPairProductLeft params family q.1)
    (fun q => gHatPairProductRight params family q.1)
    (gHatCommutationError params gamma zeta)).1 hfst -/

/-- The fixed paper exponent `1/16` keeps `Real.rpow` nonnegative even on the
negative branch, because `cos (π / 16) > 0`. This lets the `commuteGHalfSandwich`
error envelopes avoid threading an extra `0 ≤ gamma` hypothesis. -/
lemma rpow_oneSixteenth_nonneg (x : Error) :
    0 ≤ Real.rpow x (1 / (16 : Error)) := by
  simpa [Real.rpow_eq_pow] using (show 0 ≤ x ^ (1 / (16 : Error)) by
    rcases le_or_gt 0 x with hx | hx
    · exact Real.rpow_nonneg hx _
    · rw [Real.rpow_def_of_neg hx]
      have hexp_nonneg : 0 ≤ Real.exp (Real.log x * (1 / (16 : Error))) := by
        exact le_of_lt (Real.exp_pos _)
      have hmem : ((1 / (16 : Error)) * Real.pi) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> have hpi_pos : 0 < Real.pi := Real.pi_pos <;> nlinarith
      have hcos_nonneg : 0 ≤ Real.cos ((1 / (16 : Error)) * Real.pi) := by
        exact le_of_lt (Real.cos_pos_of_mem_Ioo hmem)
      exact mul_nonneg hexp_nonneg hcos_nonneg)

lemma commuteGHalfSandwich_error_bound
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) (k : ℕ)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1) :
    3 * (k : Error) *
      (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta)
      ≤ commuteGHalfSandwichError params gamma zeta k := by
  let S : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  have hγterm_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : Error)) :=
    rpow_oneSixteenth_nonneg gamma
  have hS_nonneg : 0 ≤ S := by
    have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
    dsimp [S]
    exact add_nonneg
      (add_nonneg
        hγterm_nonneg
        (Real.rpow_nonneg hzeta_nonneg (1 / (16 : Error))))
      (Real.rpow_nonneg hratio_nonneg (1 / (16 : Error)))
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hzeta_to_rpow : zeta ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 : Error) := by norm_num
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le (by norm_num) hpow)
  have hzeta_term : zeta ≤ (params.m : Error) * S := by
    have hroot_le : Real.rpow zeta (1 / (16 : Error)) ≤ S := by
      have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
      have hratio_rpow_nonneg :
          0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
        exact Real.rpow_nonneg hratio_nonneg (1 / (16 : Error))
      calc
        Real.rpow zeta (1 / (16 : Error))
          ≤ Real.rpow zeta (1 / (16 : Error)) + Real.rpow gamma (1 / (16 : Error)) := by
              nlinarith
        _ ≤ Real.rpow zeta (1 / (16 : Error)) + Real.rpow gamma (1 / (16 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
              nlinarith
        _ = S := by
              simp [S, add_assoc, add_comm]
    have hm_mul : Real.rpow zeta (1 / (16 : Error)) ≤ (params.m : Error) * S := by
      have : S ≤ (params.m : Error) * S := by
        nlinarith
      exact le_trans hroot_le this
    exact le_trans hzeta_to_rpow hm_mul
  calc
    3 * (k : Error) *
      (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta)
      = 12 * ((k : Error) ^ (2 : ℕ)) * zeta +
          3 * ((k : Error) ^ (2 : ℕ)) * gHatCommutationError params gamma zeta := by ring
    _ ≤ 12 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) * S) +
          3 * ((k : Error) ^ (2 : ℕ)) * gHatCommutationError params gamma zeta := by
            gcongr
    _ = 12 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) * S) +
          3 * ((k : Error) ^ (2 : ℕ)) * (138 * (params.m : Error) * S) := by
            simp [gHatCommutationError, S]
    _ = 426 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by ring
    _ = commuteGHalfSandwichError params gamma zeta k := by
          simp [commuteGHalfSandwichError, S]

def splitQuestionEquiv (params : Parameters) (r : ℕ) :
    ((SliceQuestion params × PointTuple params r) × SliceQuestion params) ≃
      (SliceQuestion params × SliceQuestion params × PointTuple params r) where
  toFun q := (q.1.1, q.2, q.1.2)
  invFun q := ((q.1, q.2.2), q.2.1)
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

def prefixTripleOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.1.1, og.2, og.1.2)
  invFun og := ((og.1, og.2.2), og.2.1)
  left_inv og := by cases og; rfl
  right_inv og := by cases og; rfl

def pairTailOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.1.1, og.1.2, og.2)
  invFun og := ((og.1, og.2.1), og.2.2)
  left_inv og := by cases og; rfl
  right_inv og := by cases og; rfl

lemma commuteGHalfSandwich_step_commute
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (r : ℕ)
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveFamily params family r)
      (commuteGHalfSandwich_commuteFamily params family r)
      (gHatCommutationError params gamma zeta) := by
  let C : (SliceQuestion params × SliceQuestion params × PointTuple params r) →
      (GHatOutcome params × GHatOutcome params) → GHatTupleOutcome params r →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ gt => rightTensor (ι₁ := ι)
      (gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)
  have hC :
      ∀ q a,
        ∑ gt : GHatTupleOutcome params r, (C q a gt)ᴴ * C q a gt ≤ 1 := by
    intro q a
    calc
      ∑ gt : GHatTupleOutcome params r, (C q a gt)ᴴ * C q a gt
        = ∑ gt : GHatTupleOutcome params r,
            rightTensor (ι₁ := ι)
              (((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt) := by
                  refine Finset.sum_congr rfl ?_
                  intro gt _
                  rw [show (rightTensor (ι₁ := ι)
                      (gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))ᴴ =
                      rightTensor (ι₁ := ι)
                        ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) by
                    simpa [rightTensor, opTensor] using
                      (conjTranspose_opTensor (1 : MIPStarRE.Quantum.Op ι)
                        (gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))]
                  simp [C, rightTensor_mul_rightTensor]
      _ = rightTensor (ι₁ := ι)
            (∑ gt : GHatTupleOutcome params r,
              ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt) := by
                  simpa using (rightTensor_finset_sum (ι₁ := ι) Finset.univ
                    (fun gt => ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                      gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))
      _ ≤ 1 := by
            exact rightTensor_le_one (ι₁ := ι)
              (A := ∑ gt : GHatTupleOutcome params r,
                ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                  gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)
              (gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2)
  let rawSource : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r =>
          C q ag.1 ag.2 * (gHatPairProductLeft params family (q.1, q.2.1)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r,
          C q ag.1 ag.2 * (gHatPairProductLeft params family (q.1, q.2.1)).outcome ag.1 }
  let rawTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r =>
          C q ag.1 ag.2 * (gHatPairProductRight params family (q.1, q.2.1)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r,
          C q ag.1 ag.2 * (gHatPairProductRight params family (q.1, q.2.1)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => gHatPairProductLeft params family (q.1, q.2.1))
      (fun q => gHatPairProductRight params family (q.1, q.2.1))
      C (gHatCommutationError params gamma zeta)
      (gHatPairProduct_sddOpRel_triple params ψbi family gamma zeta r hcom)
      hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (pairTailOutcomeEquiv params r)
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    rawSource rawTarget (gHatCommutationError params gamma zeta) hcab
  let reindexedSource :
      IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((pairTailOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget :
      IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((pairTailOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveFamily params family r)
    (commuteGHalfSandwich_commuteFamily params family r)
    (gHatCommutationError params gamma zeta)
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
      calc
        (reindexedSource q).outcome ogs
          = rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) (A * B) := by
              simp [reindexedSource, rawSource, pairTailOutcomeEquiv, C,
                gHatPairProductLeft, orderedProductOpFamily, OpFamily.leftPlacedOpFamily,
                A, B, T]
        _ = opTensor (A * B) T := by
              rw [rightTensor_mul_leftTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) (A * B) * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_leftTensor]
        _ = (commuteGHalfSandwich_moveFamily params family r q).outcome ogs := by
              simp [commuteGHalfSandwich_moveFamily, A, B, T, mul_assoc]
    )
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
      calc
        (reindexedTarget q).outcome ogs
          = rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) (B * A) := by
              simp [reindexedTarget, rawTarget, pairTailOutcomeEquiv, C,
                gHatPairProductRight, reversedProductOpFamily, OpFamily.leftPlacedOpFamily,
                A, B, T]
        _ = opTensor (B * A) T := by
              rw [rightTensor_mul_leftTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) (B * A) * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) B * leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_leftTensor]
        _ = (commuteGHalfSandwich_commuteFamily params family r q).outcome ogs := by
              simp [commuteGHalfSandwich_commuteFamily, A, B, T, mul_assoc]
    )
    hreindex

def splitSuccQuestionEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × PointTuple params (r + 1)) ≃
      (SliceQuestion params × SliceQuestion params × PointTuple params r) where
  toFun q := (q.1, q.2 0, pointTupleTail q.2)
  invFun q := (q.1, Fin.cons q.2.1 q.2.2)
  left_inv q := by
    rcases q with ⟨x, xs⟩
    change (x, Fin.cons (xs 0) (pointTupleTail xs)) = (x, xs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv q := by
    cases q
    rfl

def splitSuccOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × GHatTupleOutcome params (r + 1)) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.1, og.2 0, gHatTupleOutcomeTail og.2)
  invFun og := (og.1, Fin.cons og.2.1 og.2.2)
  left_inv og := by
    rcases og with ⟨g, gs⟩
    change (g, Fin.cons (gs 0) (gHatTupleOutcomeTail gs)) = (g, gs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv og := by
    cases og
    rfl

def moveTailQuestionEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params ×
        PointTuple params r) where
  toFun q := (q.1, q.2.1, q.2.2 0, pointTupleTail q.2.2)
  invFun q := (q.1, q.2.1, Fin.cons q.2.2.1 q.2.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, xs⟩
    change (x₁, x₂, Fin.cons (xs 0) (pointTupleTail xs)) = (x₁, x₂, xs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv q := by
    cases q
    rfl

def moveTailOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
        GHatTupleOutcome params r) where
  toFun og := (og.1, og.2.1, og.2.2 0, gHatTupleOutcomeTail og.2.2)
  invFun og := (og.1, og.2.1, Fin.cons og.2.2.1 og.2.2.2)
  left_inv og := by
    rcases og with ⟨g₁, g₂, gs⟩
    change (g₁, g₂, Fin.cons (gs 0) (gHatTupleOutcomeTail gs)) = (g₁, g₂, gs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv og := by
    cases og
    rfl

def firstSliceBackQuestionEquiv (params : Parameters) (r : ℕ) :
    ((SliceQuestion params × SliceQuestion params × PointTuple params r) × SliceQuestion params) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params ×
        PointTuple params r) where
  toFun q := (q.2, q.1.1, q.1.2.1, q.1.2.2)
  invFun q := ((q.2.1, q.2.2.1, q.2.2.2), q.1)
  left_inv q := by
    rcases q with ⟨⟨x₂, x₃, xs⟩, x₁⟩
    rfl
  right_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl

def firstSliceBackOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
        GHatTupleOutcome params r) where
  toFun og := (og.2, og.1.1, og.1.2.1, og.1.2.2)
  invFun og := ((og.2.1, og.2.2.1, og.2.2.2), og.1)
  left_inv og := by
    rcases og with ⟨⟨g₂, g₃, gs⟩, g₁⟩
    rfl
  right_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl

noncomputable def commuteGHalfSandwich_moveStepSourceFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).total) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2.2) }

noncomputable def commuteGHalfSandwich_moveStepTargetFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          rightTensor (ι₁ := ι)
            (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2) *
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.2.2.1).total) *
          rightTensor (ι₁ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2.2) }

noncomputable def commuteGHalfSandwich_moveStepMidFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1) *
          rightTensor (ι₁ := ι)
            (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).total) *
          rightTensor (ι₁ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2.2) }

noncomputable def commuteGHalfSandwich_moveSourceFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2) }

lemma commuteGHalfSandwich_prefixFirstSliceLeft_move
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params ×
        SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepSourceFamily params family r)
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution ((SliceQuestion params × SliceQuestion params ×
          PointTuple params r) × SliceQuestion params))
        (fun q => commuteGHalfSandwich_moveSourceFamily params family r q.1)
        (fun q => commuteGHalfSandwich_moveFamily params family r q.1)
        δ :=
    sddOpRel_uniform_fst ψbi
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      δ hAB
  have hABquad :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params ×
          SliceQuestion params × PointTuple params r))
        (fun q => commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
        (fun q => commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
        δ :=
    (sddOpRel_uniform_equiv (firstSliceBackQuestionEquiv params r) ψbi
      (fun q => commuteGHalfSandwich_moveSourceFamily params family r q.1)
      (fun q => commuteGHalfSandwich_moveFamily params family r q.1)
      δ).1 hABfst
  let C : (SliceQuestion params × SliceQuestion params × SliceQuestion params ×
      PointTuple params r) →
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) → GHatOutcome params →
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
                  rw [show (leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g₁))ᴴ =
                      leftTensor (ι₂ := ι) (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) by
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
            exact leftTensor_le_one (ι₂ := ι) (A := _ ) hinner
  let rawSource : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1,
              q.2.2.2)).outcome ag.1
        total := ∑ ag :
            (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) ×
              GHatOutcome params,
          C q ag.1 ag.2 *
            (commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1,
                q.2.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2)).outcome ag.1
        total := ∑ ag :
            (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) ×
              GHatOutcome params,
          C q ag.1 ag.2 *
            (commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1,
                q.2.2.2)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
      (fun q => commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
      C δ hABquad hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (firstSliceBackOutcomeEquiv params r)
    ψbi
    (uniformDistribution
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((firstSliceBackOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((firstSliceBackOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveStepSourceFamily params family r)
    (commuteGHalfSandwich_moveStepMidFamily params family r)
    δ
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      calc
        (reindexedSource q).outcome ogs
          = leftTensor (ι₂ := ι) A *
              (leftTensor (ι₂ := ι) ((B * G) *
                  gHatHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)) := by
                simp [reindexedSource, rawSource, firstSliceBackOutcomeEquiv, C,
                  commuteGHalfSandwich_moveSourceFamily, A, B, G,
                  leftTensor_mul_leftTensor, mul_assoc]
        _ = (commuteGHalfSandwich_moveStepSourceFamily params family r q).outcome ogs := by
              simp [commuteGHalfSandwich_moveStepSourceFamily, A, B, G,
                 mul_assoc, leftTensor_mul_leftTensor]
    )
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      calc
        (reindexedTarget q).outcome ogs
          = leftTensor (ι₂ := ι) A * (leftTensor (ι₂ := ι) B * (leftTensor (ι₂ := ι) G
              * rightTensor (ι₁ := ι) T)) := by
                simp [reindexedTarget, rawTarget, firstSliceBackOutcomeEquiv, C,
                  commuteGHalfSandwich_moveFamily, A, B, G, T, mul_assoc]
        _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
              calc
                leftTensor (ι₂ := ι) A *
                    (leftTensor (ι₂ := ι) B *
                      (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T))
                  = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * leftTensor (ι₂ := ι) G) *
                      rightTensor (ι₁ := ι) T := by
                        simp [mul_assoc]
                _ =
                    (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G) *
                      rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
                      symm
                      calc
                        (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs
                          =
                            (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
                              leftTensor (ι₂ := ι) G) *
                              rightTensor (ι₁ := ι) T := by
                                simp [commuteGHalfSandwich_moveStepMidFamily, A, B, G, T, mul_assoc]
                        _ = (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G)
                            * rightTensor (ι₁ := ι) T := by
                              rw [leftTensor_mul_leftTensor]
                        _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                              rw [leftTensor_mul_leftTensor]
                        _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                              simp [mul_assoc]
    )
    hreindex

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
            simp [headTailOrderedFamily, A, B,
              gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor]

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
  unfold sddErrorOp qSDDOp qSDDCore commuteGHalfSandwich_moveSourceFamily
      commuteGHalfSandwich_moveFamily
  simp [gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator,
    leftTensor_mul_leftTensor]
  have hzero :
      avgOver (uniformDistribution (SliceQuestion params × SliceQuestion params ×
          PointTuple params 0))
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
    exact congrArg (fun ys => (x, ys)) ((pointTupleOneEquiv params).left_inv xs)
  right_inv q := by
    rcases q with ⟨x, y⟩
    exact congrArg (fun ys => (x, ys)) ((pointTupleOneEquiv params).right_inv y)

def splitOutcomeEquivOne (params : Parameters) [FieldModel params.q] :
    (GHatOutcome params × GHatTupleOutcome params 1) ≃ (GHatOutcome params ×
        GHatOutcome params) where
  toFun og := (og.1, (gHatTupleOutcomeOneEquiv params) og.2)
  invFun og := (og.1, (gHatTupleOutcomeOneEquiv params).symm og.2)
  left_inv og := by
    rcases og with ⟨g, gs⟩
    exact congrArg (fun hs => (g, hs)) ((gHatTupleOutcomeOneEquiv params).left_inv gs)
  right_inv og := by
    rcases og with ⟨g₁, g₂⟩
    exact congrArg (fun hs => (g₁, hs)) ((gHatTupleOutcomeOneEquiv params).right_inv g₂)

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
          leftTensor_mul_leftTensor])
      (fun q og => by
        rcases og with ⟨g₁, g₂⟩
        simp [gHatPairProductRight, headTailRotatedFamily,
          splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
          gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
           reversedProductOpFamily,
          OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor])
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
          leftTensor_mul_leftTensor])
      (fun q og => by
        rcases og with ⟨g₁, g₂⟩
        simp [gHatPairProductRight, headTailRotatedFamily,
          splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
          gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
           reversedProductOpFamily,
          OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor])
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
    (commuteGHalfSandwich_split_one_iff params ψbi family
      (gHatCommutationError params gamma zeta)).2 hcom
  have hpoint : SDDOpRel ψbi
      (uniformDistribution (PointTuple params 2))
      (gHatHalfSandwichLeft params family 2)
      (gHatHalfSandwichRight params family 2)
      (gHatCommutationError params gamma zeta) :=
    (commuteGHalfSandwich_split_iff params ψbi family 1
      (gHatCommutationError params gamma zeta)).2 hsplit
  rcases hcom with ⟨hν3⟩
  have hν3_nonneg : 0 ≤ gHatCommutationError params gamma zeta := by
    exact le_trans
      (avgOver_nonneg (uniformDistribution (SlicePairQuestion params))
        (fun q =>
          qSDDOp ψbi (gHatPairProductLeft params family q)
            (gHatPairProductRight params family q))
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
    have :
        138 * (params.m : Error) * S ≤
          426 * ((2 : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by
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
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
          GHatTupleOutcome params r) where
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

/-- Generic tensor-contraction bound: if `prefixOp : α → Op ι` and
`tailOp : β → Op ι` each satisfy `∑ (·)ᴴ * (·) ≤ 1`, then the joint family
`leftTensor (prefixOp a) * rightTensor (tailOp b)` on `α × β` also satisfies
`∑ (·)ᴴ * (·) ≤ 1` on the bipartite space. -/
lemma leftTensor_rightTensor_sum_adjoint_mul_le_one
    {α β : Type*}
    [Fintype α]
    [Fintype β]
    (prefixOp : α → MIPStarRE.Quantum.Op ι)
    (tailOp : β → MIPStarRE.Quantum.Op ι)
    (hprefix : ∑ a : α, (prefixOp a)ᴴ * prefixOp a ≤ 1)
    (htail : ∑ b : β, (tailOp b)ᴴ * tailOp b ≤ 1) :
    ∑ ag : α × β,
        (leftTensor (ι₂ := ι) (prefixOp ag.1) *
            rightTensor (ι₁ := ι) (tailOp ag.2))ᴴ *
          (leftTensor (ι₂ := ι) (prefixOp ag.1) *
            rightTensor (ι₁ := ι) (tailOp ag.2)) ≤ 1 := by
  classical
  let prefixTerm : α → MIPStarRE.Quantum.Op ι :=
    fun a => (prefixOp a)ᴴ * prefixOp a
  let tailTerm : β → MIPStarRE.Quantum.Op ι :=
    fun b => (tailOp b)ᴴ * tailOp b
  calc
    ∑ ag : α × β,
        (leftTensor (ι₂ := ι) (prefixOp ag.1) *
            rightTensor (ι₁ := ι) (tailOp ag.2))ᴴ *
          (leftTensor (ι₂ := ι) (prefixOp ag.1) *
            rightTensor (ι₁ := ι) (tailOp ag.2))
      = ∑ a : α, ∑ b : β,
          leftTensor (ι₂ := ι) (prefixTerm a) *
            rightTensor (ι₁ := ι) (tailTerm b) := by
              rw [← Finset.univ_product_univ, Finset.sum_product]
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro b _
              have hmul :
                  leftTensor (ι₂ := ι) (prefixOp a) *
                      rightTensor (ι₁ := ι) (tailOp b) =
                    opTensor (prefixOp a) (tailOp b) := by
                rw [leftTensor_mul_rightTensor_eq_opTensor]
              calc
                (leftTensor (ι₂ := ι) (prefixOp a) *
                    rightTensor (ι₁ := ι) (tailOp b))ᴴ *
                  (leftTensor (ι₂ := ι) (prefixOp a) *
                    rightTensor (ι₁ := ι) (tailOp b))
                  = (opTensor (prefixOp a) (tailOp b))ᴴ *
                      opTensor (prefixOp a) (tailOp b) := by
                        rw [hmul]
                _ = opTensor ((prefixOp a)ᴴ) ((tailOp b)ᴴ) *
                      opTensor (prefixOp a) (tailOp b) := by
                        rw [conjTranspose_opTensor]
                _ = leftTensor (ι₂ := ι) (prefixTerm a) *
                      rightTensor (ι₁ := ι) (tailTerm b) := by
                        simp [prefixTerm, tailTerm, opTensor_mul]
    _ = ∑ a : α,
          leftTensor (ι₂ := ι) (prefixTerm a) *
            rightTensor (ι₁ := ι) (∑ b : β, tailTerm b) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [← rightTensor_finset_sum (ι₁ := ι) Finset.univ tailTerm,
                ← Finset.mul_sum]
    _ ≤ ∑ a : α, leftTensor (ι₂ := ι) (prefixTerm a) := by
          refine Finset.sum_le_sum ?_
          intro a _
          have hprefix_nonneg : 0 ≤ prefixTerm a := by
            change 0 ≤ star (prefixOp a) * prefixOp a
            exact (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨prefixOp a, rfl⟩
          calc
            leftTensor (ι₂ := ι) (prefixTerm a) *
                rightTensor (ι₁ := ι) (∑ b : β, tailTerm b)
              = opTensor (prefixTerm a) (∑ b : β, tailTerm b) := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor]
            _ ≤ leftTensor (ι₂ := ι) (prefixTerm a) := by
                  exact opTensor_le_leftTensor hprefix_nonneg htail
    _ = leftTensor (ι₂ := ι) (∑ a : α, prefixTerm a) := by
          rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ prefixTerm]
    _ ≤ 1 := by
          exact leftTensor_le_one (ι₂ := ι) (A := _) hprefix

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
  let C : Q → GHatOutcome params → ((GHatOutcome params × GHatOutcome params) ×
      GHatTupleOutcome params r) →
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
    let tailOp : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
      fun gs => gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 gs
    have hpair :
        ∑ og : GHatOutcome params × GHatOutcome params,
            (pairProd og)ᴴ * pairProd og ≤ 1 := by
      simpa [pairProd] using
        gHatPairPrefix_sum_adjoint_mul_le_one params family (q.1, q.2.1)
    have htail :
        ∑ gs : GHatTupleOutcome params r,
            (tailOp gs)ᴴ * tailOp gs ≤ 1 := by
      simpa [tailOp] using
        gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2.2
    simpa [C, pairProd, tailOp] using
      (leftTensor_rightTensor_sum_adjoint_mul_le_one
        (ι := ι) (prefixOp := pairProd) (tailOp := tailOp) hpair htail)
  let rawSource : IdxOpFamily Q
      (GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r))
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (Aop q).outcome ag.1
        total := ∑ ag : GHatOutcome params × ((GHatOutcome params × GHatOutcome params) ×
            GHatTupleOutcome params r),
          C q ag.1 ag.2 * (Aop q).outcome ag.1 }
  let rawTarget : IdxOpFamily Q
      (GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r))
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (Bop q).outcome ag.1
        total := ∑ ag : GHatOutcome params × ((GHatOutcome params × GHatOutcome params) ×
            GHatTupleOutcome params r),
          C q ag.1 ag.2 * (Bop q).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution Q) Aop Bop C (gHatSelfConsistencyError zeta) hAB hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (thirdSliceFrontOutcomeEquiv params r)
    ψbi (uniformDistribution Q) rawSource rawTarget (gHatSelfConsistencyError zeta) hcab
  let reindexedSource : IdxOpFamily Q
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
          GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((thirdSliceFrontOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily Q
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
          GHatTupleOutcome params r) (ι × ι) :=
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
        (reindexedSource q).outcome ogs =
            leftTensor (ι₂ := ι) (A * B) *
              (rightTensor (ι₁ := ι) T * (Aop q).outcome ogs.2.2.1) := by
              simp [reindexedSource, rawSource, thirdSliceFrontOutcomeEquiv, C, A, B, T, mul_assoc]
        _ =
            leftTensor (ι₂ := ι) (A * B) *
              (rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) G) := by
              rw [hAop]
        _ =
            leftTensor (ι₂ := ι) (A * B) *
              (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T) := by
              rw [hcomm]
        _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
              calc
                leftTensor (ι₂ := ι) (A * B) *
                    (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T)
                  =
                    (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G) *
                      rightTensor (ι₁ := ι) T := by
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
                simp [reindexedTarget, rawTarget, thirdSliceFrontOutcomeEquiv, C, A, B, T,
                    mul_assoc]
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
                _ =
                    leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
                      rightTensor (ι₁ := ι) (T * G) := by
                      rw [rightTensor_mul_rightTensor]
                _ = leftTensor (ι₂ := ι) (A * B) * rightTensor (ι₁ := ι) (T * G) := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * B) *
                      (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
                        rw [rightTensor_mul_rightTensor]
    )
    hreindex

end MIPStarRE.LDT.Pasting
