import MIPStarRE.LDT.Pasting.BridgeLemmas.Common

/-!
# Section 12 pasting: bridge commute setup

Setup lemmas and first operator-family reorganizations for the `commuteGHalfSandwich` chain.
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
      gHatReverseHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs) *
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
    leftTensor_mul_leftTensor, mul_assoc]

lemma gHatHalfSandwichLeft_split_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1)) :
    (gHatHalfSandwichLeft params family (k + 1) xs).total =
      (headTailOrderedFamily params family k ((pointTupleConsEquiv params k) xs)).total := by
  simp [gHatHalfSandwichLeft, headTailOrderedFamily,
    pointTupleConsEquiv, gHatHalfProductTotalOperator,
    OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc]

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
    leftTensor_mul_leftTensor, mul_assoc]

lemma gHatHalfSandwichRight_split_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1)) :
    (gHatHalfSandwichRight params family (k + 1) xs).total =
      (headTailRotatedFamily params family k ((pointTupleConsEquiv params k) xs)).total := by
  simp [gHatHalfSandwichRight, headTailRotatedFamily,
    pointTupleConsEquiv, gHatRotatedHalfProductTotalOperator,
    OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc]

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
          gHatHalfSandwichLeft_split_outcome params family k ((pointTupleConsEquiv params k).symm q)
            ((gHatTupleOutcomeConsEquiv' params k).symm ogs))
      (fun q ogs => by
        simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
          gHatHalfSandwichRight_split_outcome params family k ((pointTupleConsEquiv params k).symm q)
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
          (gHatHalfSandwichLeft_split_outcome params family k ((pointTupleConsEquiv params k).symm q) gs).symm)
      (fun q gs => by
        simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
          (gHatHalfSandwichRight_split_outcome params family k ((pointTupleConsEquiv params k).symm q) gs).symm)
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
              simp [G, mul_assoc]
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
              simp [hherm, hproj, mul_assoc]
        _ = 1 := by
              calc
                ∑ g : GHatOutcome params, G g = (gHatIdxMeas params family (xs 0)).total := by
                  simpa [G] using (gHatIdxMeas params family (xs 0)).sum_eq_total
                _ = 1 := (gHatIdxMeas params family (xs 0)).total_eq_one

def thirdSliceFrontEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) ≃
      (SliceQuestion params × (SliceQuestion params × SliceQuestion params × PointTuple params r)) where
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
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
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

lemma commuteGHalfSandwich_error_bound
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) (k : ℕ)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1) :
    3 * (k : Error) * (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta)
      ≤ commuteGHalfSandwichError params gamma zeta k := by
  let S : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
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
      have hratio_nonneg : 0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
        exact Real.rpow_nonneg (by positivity : 0 ≤ ((params.d : Error) / (params.q : Error))) _
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
    have hm_mul : Real.rpow zeta (1 / (16 : Error)) ≤ (params.m : Error) * S := by
      have : S ≤ (params.m : Error) * S := by
        nlinarith
      exact le_trans hroot_le this
    exact le_trans hzeta_to_rpow hm_mul
  calc
    3 * (k : Error) * (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta)
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

end MIPStarRE.LDT.Pasting
