import MIPStarRE.LDT.Pasting.Defs.Families
import MIPStarRE.LDT.CommutativityPoints.Defs

/-!
# Section 12 — Sandwich constructions: switcheroo families

Switcheroo, complete-part, and half-product operator families.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyLeft {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SliceQuestion params) Outcome (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) ((M x).toSubMeas)

/-- Right tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyRight {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SliceQuestion params) Outcome (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) ((M x).toSubMeas)

/-- Concrete hypothesis family for `G^x_g M^y_o`. -/
noncomputable def switcherooPointProductLeft
    {Outcome : Type*} [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete hypothesis family for `M^y_o G^x_g` on the
`Polynomial params × Outcome` outcome type. -/
noncomputable def switcherooPointProductRight
    {Outcome : Type*} [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `G^x M^y_o`. -/
noncomputable def switcherooAggregateLeft {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.1)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `M^y_o G^x`. -/
noncomputable def switcherooAggregateRight {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((M q.2).toSubMeas)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y`. -/
noncomputable def completePartPointProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas q.1).toSubMeas)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x_g`. -/
noncomputable def completePartPointProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x G^y`. -/
noncomputable def completePartTotalProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        (completePartSubMeas params family q.1)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x`. -/
noncomputable def completePartTotalProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.2)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y_⊥`. -/
noncomputable def incompletePartPointProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas q.1).toSubMeas)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_g`. -/
noncomputable def incompletePartPointProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x_⊥ G^y_⊥`. -/
noncomputable def incompletePartTotalProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        (incompletePartSubMeas params family q.1)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_⊥`. -/
noncomputable def incompletePartTotalProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family q.2)
        (incompletePartSubMeas params family q.1)

/-- Left tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) ((gHatIdxMeas params family x).toSubMeas)

/-- Right tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) ((gHatIdxMeas params family x).toSubMeas)

/-- Concrete family for the pairwise product `\widehat G^x_g \widehat G^y_h`. -/
noncomputable def gHatPairProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- Concrete family for the reversed pairwise product `\widehat G^y_h \widehat G^x_g`. -/
noncomputable def gHatPairProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- The ordered half-product `\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductOutcomeOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0) *
        gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs)

/-- The total half-product
`\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductTotalOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → MIPStarRE.Quantum.Op ι
  | 0, _xs =>
      1
  | k + 1, xs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).total *
        gHatHalfProductTotalOperator params family k (pointTupleTail xs)

/-- The cyclically rotated half-product
`\widehat G^{x_2}_{g_2} \cdots \widehat G^{x_k}_{g_k} \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatRotatedHalfProductOutcomeOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0)

/-- The total cyclically rotated half-product. -/
noncomputable def gHatRotatedHalfProductTotalOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → MIPStarRE.Quantum.Op ι
  | 0, _xs =>
      1
  | k + 1, xs =>
      gHatHalfProductTotalOperator params family k (pointTupleTail xs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).total

private def gHatTupleOutcomeConsEquiv (params : Parameters) [FieldModel params.q] (k : ℕ) :
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

/-- The total operator of the ordered half-product is always the identity. -/
lemma gHatHalfProductTotalOperator_eq_one (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k), gHatHalfProductTotalOperator params family k xs = 1
  | 0, _xs => by
      simp [gHatHalfProductTotalOperator]
  | k + 1, xs => by
      rw [gHatHalfProductTotalOperator]
      simp [gHatIdxMeas, completeSubMeas,
        gHatHalfProductTotalOperator_eq_one params family k (pointTupleTail xs)]

/-- The total operator of the rotated half-product is always the identity. -/
lemma gHatRotatedHalfProductTotalOperator_eq_one (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k), gHatRotatedHalfProductTotalOperator params family k xs = 1
  | 0, _xs => by
      simp [gHatRotatedHalfProductTotalOperator]
  | k + 1, xs => by
      rw [gHatRotatedHalfProductTotalOperator]
      simp [gHatIdxMeas, completeSubMeas,
        gHatHalfProductTotalOperator_eq_one params family k (pointTupleTail xs)]

/-- Summing the ordered half-product over all completed outcomes gives its total operator. -/
lemma gHatHalfProduct_sum_eq_total (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k),
      (∑ gs : GHatTupleOutcome params k,
        gHatHalfProductOutcomeOperator params family k xs gs) =
          gHatHalfProductTotalOperator params family k xs
  | 0, _xs => by
      simp [gHatHalfProductOutcomeOperator, gHatHalfProductTotalOperator]
  | k + 1, xs => by
      have hsplit :
          (∑ gs : GHatTupleOutcome params (k + 1),
              gHatHalfProductOutcomeOperator params family (k + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params k,
              gHatHalfProductOutcomeOperator params family (k + 1) xs (Fin.cons p.1 p.2) := by
        symm
        exact (Fintype.sum_equiv (gHatTupleOutcomeConsEquiv params k)
          (fun gs => gHatHalfProductOutcomeOperator params family (k + 1) xs gs)
          (fun p =>
            gHatHalfProductOutcomeOperator params family (k + 1) xs (Fin.cons p.1 p.2))
          (by intro gs; rfl)).symm
      rw [hsplit]
      simp only [gHatHalfProductOutcomeOperator, Fin.cons_zero]
      rw [← Finset.univ_product_univ, Finset.sum_product]
      calc
        ∑ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params k,
              (gHatIdxMeas params family (xs 0)).outcome g *
                gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs
          = ∑ g : GHatOutcome params,
              (gHatIdxMeas params family (xs 0)).outcome g *
                ∑ gs : GHatTupleOutcome params k,
                  gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs := by
              apply Finset.sum_congr rfl
              intro g _hg
              rw [Matrix.mul_sum]
        _ = ∑ g : GHatOutcome params,
              (gHatIdxMeas params family (xs 0)).outcome g *
                gHatHalfProductTotalOperator params family k (pointTupleTail xs) := by
              apply Finset.sum_congr rfl
              intro g _hg
              rw [gHatHalfProduct_sum_eq_total params family k (pointTupleTail xs)]
        _ = (∑ g : GHatOutcome params, (gHatIdxMeas params family (xs 0)).outcome g) *
              gHatHalfProductTotalOperator params family k (pointTupleTail xs) := by
              symm
              exact
                Finset.sum_mul Finset.univ
                  (fun g => (gHatIdxMeas params family (xs 0)).outcome g)
                  (gHatHalfProductTotalOperator params family k (pointTupleTail xs))
        _ = gHatHalfProductTotalOperator params family (k + 1) xs := by
              rw [(gHatIdxMeas params family (xs 0)).sum_eq_total]
              simp [gHatHalfProductTotalOperator]

/-- Summing the rotated half-product over all completed outcomes gives its total operator. -/
lemma gHatRotatedHalfProduct_sum_eq_total (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k),
      (∑ gs : GHatTupleOutcome params k,
        gHatRotatedHalfProductOutcomeOperator params family k xs gs) =
          gHatRotatedHalfProductTotalOperator params family k xs
  | 0, _xs => by
      simp [gHatRotatedHalfProductOutcomeOperator, gHatRotatedHalfProductTotalOperator]
  | k + 1, xs => by
      have hsplit :
          (∑ gs : GHatTupleOutcome params (k + 1),
              gHatRotatedHalfProductOutcomeOperator params family (k + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params k,
              gHatRotatedHalfProductOutcomeOperator
                params family (k + 1) xs (Fin.cons p.1 p.2) := by
        symm
        exact (Fintype.sum_equiv (gHatTupleOutcomeConsEquiv params k)
          (fun gs => gHatRotatedHalfProductOutcomeOperator params family (k + 1) xs gs)
          (fun p =>
            gHatRotatedHalfProductOutcomeOperator params family (k + 1) xs (Fin.cons p.1 p.2))
          (by intro gs; rfl)).symm
      rw [hsplit]
      simp only [gHatRotatedHalfProductOutcomeOperator, Fin.cons_zero]
      rw [← Finset.univ_product_univ, Finset.sum_product]
      calc
        ∑ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params k,
              gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                (gHatIdxMeas params family (xs 0)).outcome g
          = ∑ gs : GHatTupleOutcome params k,
              ∑ g : GHatOutcome params,
                gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                  (gHatIdxMeas params family (xs 0)).outcome g := by
              rw [Finset.sum_comm]
        _ = ∑ gs : GHatTupleOutcome params k,
              gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                ∑ g : GHatOutcome params, (gHatIdxMeas params family (xs 0)).outcome g := by
              apply Finset.sum_congr rfl
              intro gs _hgs
              rw [Matrix.mul_sum]
        _ = ∑ gs : GHatTupleOutcome params k,
              gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                (gHatIdxMeas params family (xs 0)).total := by
              apply Finset.sum_congr rfl
              intro gs _hgs
              rw [(gHatIdxMeas params family (xs 0)).sum_eq_total]
        _ = (∑ gs : GHatTupleOutcome params k,
              gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs) *
                (gHatIdxMeas params family (xs 0)).total := by
              symm
              exact
                Finset.sum_mul Finset.univ
                  (fun gs =>
                    gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs)
                  ((gHatIdxMeas params family (xs 0)).total)
        _ = gHatRotatedHalfProductTotalOperator params family (k + 1) xs := by
              rw [gHatHalfProduct_sum_eq_total params family k (pointTupleTail xs)]
              simp [gHatRotatedHalfProductTotalOperator]

end MIPStarRE.LDT.Pasting
