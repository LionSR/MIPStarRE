import MIPStarRE.LDT.Pasting.Defs
set_option linter.style.longLine false

/-!
# Section 12 — Sandwich constructions

Switcheroo and sandwich operator families for the pasting argument.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyLeft {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SliceQuestion params) Outcome (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) ((M x).toSubMeas)

/-- Right tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyRight {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SliceQuestion params) Outcome (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) ((M x).toSubMeas)

/-- Concrete hypothesis family for `G^x_g M^y_o`. -/
noncomputable def switcherooPointProductLeft
    {Outcome : Type*} [Fintype Outcome] (params : Parameters)
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
    {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `G^x M^y_o`. -/
noncomputable def switcherooAggregateLeft {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.1)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `M^y_o G^x`. -/
noncomputable def switcherooAggregateRight {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((M q.2).toSubMeas)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y`. -/
noncomputable def completePartPointProductLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas q.1).toSubMeas)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x_g`. -/
noncomputable def completePartPointProductRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x G^y`. -/
noncomputable def completePartTotalProductLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        (completePartSubMeas params family q.1)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x`. -/
noncomputable def completePartTotalProductRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.2)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y_⊥`. -/
noncomputable def incompletePartPointProductLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas q.1).toSubMeas)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_g`. -/
noncomputable def incompletePartPointProductRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x_⊥ G^y_⊥`. -/
noncomputable def incompletePartTotalProductLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        (incompletePartSubMeas params family q.1)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_⊥`. -/
noncomputable def incompletePartTotalProductRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family q.2)
        (incompletePartSubMeas params family q.1)

/-- Left tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyLeftFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) ((gHatIdxMeas params family x).toSubMeas)

/-- Right tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyRightFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) ((gHatIdxMeas params family x).toSubMeas)

/-- Concrete family for the pairwise product `\widehat G^x_g \widehat G^y_h`. -/
noncomputable def gHatPairProductLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- Concrete family for the reversed pairwise product `\widehat G^y_h \widehat G^x_g`. -/
noncomputable def gHatPairProductRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- The ordered half-product `\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductOutcomeOperator (params : Parameters)
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0) *
        gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs)

/-- The total half-product
`\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductTotalOperator (params : Parameters)
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → MIPStarRE.Quantum.Op ι
  | 0, _xs =>
      1
  | k + 1, xs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).total *
        gHatHalfProductTotalOperator params family k (pointTupleTail xs)

/-- The cyclically rotated half-product
`\widehat G^{x_2}_{g_2} \cdots \widehat G^{x_k}_{g_k} \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatRotatedHalfProductOutcomeOperator (params : Parameters)
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0)

/-- The total cyclically rotated half-product. -/
noncomputable def gHatRotatedHalfProductTotalOperator (params : Parameters)
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → MIPStarRE.Quantum.Op ι
  | 0, _xs =>
      1
  | k + 1, xs =>
      gHatHalfProductTotalOperator params family k (pointTupleTail xs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).total

lemma gHatHalfProductTotalOperator_eq_one (params : Parameters)
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k), gHatHalfProductTotalOperator params family k xs = 1
  | 0, _xs => by
      simp [gHatHalfProductTotalOperator]
  | k + 1, xs => by
      rw [gHatHalfProductTotalOperator]
      simp [gHatIdxMeas, completeSubMeas,
        gHatHalfProductTotalOperator_eq_one params family k (pointTupleTail xs)]

lemma gHatRotatedHalfProductTotalOperator_eq_one (params : Parameters)
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k), gHatRotatedHalfProductTotalOperator params family k xs = 1
  | 0, _xs => by
      simp [gHatRotatedHalfProductTotalOperator]
  | k + 1, xs => by
      rw [gHatRotatedHalfProductTotalOperator]
      simp [gHatIdxMeas, completeSubMeas,
        gHatHalfProductTotalOperator_eq_one params family k (pointTupleTail xs)]

lemma gHatHalfProduct_sum_eq_total (params : Parameters)
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k),
      (∑ gs : GHatTupleOutcome params k,
        gHatHalfProductOutcomeOperator params family k xs gs) =
          gHatHalfProductTotalOperator params family k xs
  | 0, _xs => by
      simp [gHatHalfProductOutcomeOperator, gHatHalfProductTotalOperator]
  | k + 1, xs => by
      let α : Fin (k + 1) → Type := fun _ => GHatOutcome params
      have hsplit :
          (∑ gs : GHatTupleOutcome params (k + 1),
              gHatHalfProductOutcomeOperator params family (k + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params k,
              gHatHalfProductOutcomeOperator params family (k + 1) xs (Fin.cons p.1 p.2) := by
        symm
        exact Fintype.sum_equiv (Fin.consEquiv α)
          (fun p =>
            gHatHalfProductOutcomeOperator params family (k + 1) xs (Fin.cons p.1 p.2))
          (fun gs => gHatHalfProductOutcomeOperator params family (k + 1) xs gs)
          (by intro p; rfl)
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

lemma gHatRotatedHalfProduct_sum_eq_total (params : Parameters)
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k),
      (∑ gs : GHatTupleOutcome params k,
        gHatRotatedHalfProductOutcomeOperator params family k xs gs) =
          gHatRotatedHalfProductTotalOperator params family k xs
  | 0, _xs => by
      simp [gHatRotatedHalfProductOutcomeOperator, gHatRotatedHalfProductTotalOperator]
  | k + 1, xs => by
      let α : Fin (k + 1) → Type := fun _ => GHatOutcome params
      have hsplit :
          (∑ gs : GHatTupleOutcome params (k + 1),
              gHatRotatedHalfProductOutcomeOperator params family (k + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params k,
              gHatRotatedHalfProductOutcomeOperator
                params family (k + 1) xs (Fin.cons p.1 p.2) := by
        symm
        exact Fintype.sum_equiv (Fin.consEquiv α)
          (fun p =>
            gHatRotatedHalfProductOutcomeOperator params family (k + 1) xs (Fin.cons p.1 p.2))
          (fun gs => gHatRotatedHalfProductOutcomeOperator params family (k + 1) xs gs)
          (by intro p; rfl)
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

private lemma projSubMeas_outcome_mul_total_eq_outcome {α : Type*} [Fintype α]
    (A : ProjSubMeas α ι) (a : α) :
    A.outcome a * A.total = A.outcome a := by
  let P := A.outcome a
  let R := (1 : MIPStarRE.Quantum.Op ι) - A.total
  have hP_herm : Pᴴ = P := by
    simpa [P] using A.outcome_hermitian a
  have hR_nonneg : 0 ≤ R := by
    simpa [R] using sub_nonneg.mpr A.total_le_one
  have hR_le_self : R ≤ 1 - P := by
    simpa [R, P] using sub_le_sub_left (A.outcome_le_total a) (1 : MIPStarRE.Quantum.Op ι)
  have hPRP_nonneg : 0 ≤ P * R * P := by
    exact MIPStarRE.Quantum.sandwich_nonneg hR_nonneg hP_herm
  have hP_one_sub_P : P * (1 - P) * P = 0 := by
    calc
      P * (1 - P) * P = (P * 1 - P * P) * P := by rw [mul_sub]
      _ = 0 := by simp [P, A.proj a]
  have hPRP_eq_zero : P * R * P = 0 := by
    apply le_antisymm
    · calc
        P * R * P ≤ P * (1 - P) * P := by
          exact MIPStarRE.Quantum.sandwich_mono hP_herm hR_le_self
        _ = 0 := hP_one_sub_P
    · simpa using hPRP_nonneg
  have hA_total_herm : A.totalᴴ = A.total := by
    exact (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have hR_herm : Rᴴ = R := by
    simp [R, hA_total_herm]
  have hR_sq_le : R * R ≤ R := by
    have hR_le_one : R ≤ 1 := by
      simpa [R] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) A.total_nonneg
    exact MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
  have hRP_conj_mul : (R * P)ᴴ * (R * P) = P * (R * R) * P := by
    calc
      (R * P)ᴴ * (R * P) = (Pᴴ * Rᴴ) * (R * P) := by simp [Matrix.conjTranspose_mul]
      _ = P * (R * R) * P := by simp [hP_herm, hR_herm, mul_assoc]
  have hRP_eq_zero : R * P = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [hRP_conj_mul]
    apply le_antisymm
    · calc
        P * (R * R) * P ≤ P * R * P := by
          exact MIPStarRE.Quantum.sandwich_mono hP_herm hR_sq_le
        _ = 0 := hPRP_eq_zero
    · have hnonneg : 0 ≤ P * (R * R) * P := by
        exact MIPStarRE.Quantum.sandwich_nonneg
          (show 0 ≤ R * R by
            exact Commute.mul_nonneg hR_nonneg hR_nonneg (Commute.refl R))
          hP_herm
      simpa using hnonneg
  calc
    A.outcome a * A.total = P * (1 - R) := by simp [P, R, sub_eq_add_neg, add_comm, add_left_comm]
    _ = P - P * R := by rw [mul_sub, mul_one]
    _ = P := by
          have : P * R = 0 := by
            simpa [hP_herm, hR_herm] using congrArg Matrix.conjTranspose hRP_eq_zero
          simp [this]
    _ = A.outcome a := by rfl

private lemma projSubMeas_total_mul_outcome_eq_outcome {α : Type*} [Fintype α]
    (A : ProjSubMeas α ι) (a : α) :
    A.total * A.outcome a = A.outcome a := by
  have := projSubMeas_outcome_mul_total_eq_outcome (A := A) a
  exact by
    simpa [A.outcome_hermitian a,
      (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq,
      Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose this

private lemma projSubMeas_total_proj {α : Type*} [Fintype α]
    (A : ProjSubMeas α ι) :
    A.total * A.total = A.total := by
  calc
    A.total * A.total = (∑ a : α, A.outcome a) * A.total := by rw [A.sum_eq_total]
    _ = ∑ a : α, A.outcome a * A.total := by rw [Matrix.sum_mul]
    _ = ∑ a : α, A.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact projSubMeas_outcome_mul_total_eq_outcome A a
    _ = A.total := A.sum_eq_total

private lemma gHatIdxMeas_proj (params : Parameters)
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    (gHatIdxMeas params family x).outcome g * (gHatIdxMeas params family x).outcome g =
      (gHatIdxMeas params family x).outcome g := by
  cases g with
  | none =>
      let T := (family.meas x).total
      change (1 - T) * (1 - T) = 1 - T
      have hTT : T * T = T := by
        simpa [T] using projSubMeas_total_proj (family.meas x)
      calc
        (1 - T) * (1 - T) = 1 - T - T + T * T := by
          noncomm_ring
        _ = 1 - T := by
          rw [hTT]
          abel
  | some p =>
      simp [gHatIdxMeas, completeSubMeas, (family.meas x).proj p]

lemma binomialOperatorTerm_nonneg {G : MIPStarRE.Quantum.Op ι} (n r : ℕ)
    (hG : 0 ≤ G) (hGle : G ≤ 1) :
    0 ≤ (Nat.choose n r : ℂ) • (G ^ r * (1 - G) ^ (n - r)) := by
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  refine smul_nonneg ?_ ?_
  · positivity
  · have hGr : 0 ≤ G ^ r := by
      exact (Matrix.PosSemidef.pow (Matrix.nonneg_iff_posSemidef.mp hG) r).nonneg
    have hIG : 0 ≤ (1 - G) ^ (n - r) := by
      exact
        (Matrix.PosSemidef.pow
          (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hGle)) (n - r)).nonneg
    have hcommPow : Commute (G ^ r) ((1 - G) ^ (n - r)) :=
      (hcomm.pow_left r).pow_right (n - r)
    exact Commute.mul_nonneg hGr hIG hcommPow

/-- Positivity of the Bernoulli tail operator for a PSD contraction. -/
theorem bernoulliTailOperator_nonneg
    (k degree : ℕ) (G : MIPStarRE.Quantum.Op ι)
    (hG : 0 ≤ G) (hGle : G ≤ 1) :
    0 ≤ bernoulliTailOperator k degree G := by
  unfold bernoulliTailOperator
  refine Finset.sum_nonneg fun r _ => ?_
  simpa using binomialOperatorTerm_nonneg (G := G) k r hG hGle

/-- Concrete family for the full sandwich
`\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k} \cdots \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatSandwichFamily (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) ι :=
  fun xs =>
    { outcome := fun gs =>
        let half := gHatHalfProductOutcomeOperator params family k xs gs
        half * halfᴴ
      total :=
        let half := gHatHalfProductTotalOperator params family k xs
        half * halfᴴ
      outcome_pos := by
        intro gs
        simpa using
          (Matrix.posSemidef_self_mul_conjTranspose
            (gHatHalfProductOutcomeOperator params family k xs gs)).nonneg
      sum_eq_total := by
        induction k with
        | zero =>
            simp [gHatHalfProductOutcomeOperator, gHatHalfProductTotalOperator]
        | succ k ih =>
            let α : Fin (k + 1) → Type := fun _ => GHatOutcome params
            have hsplit :
                (∑ gs : GHatTupleOutcome params (k + 1),
                    let half := gHatHalfProductOutcomeOperator params family (k + 1) xs gs
                    half * halfᴴ) =
                  ∑ p : GHatOutcome params × GHatTupleOutcome params k,
                    (gHatIdxMeas params family (xs 0)).outcome p.1 *
                      (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) p.2 *
                        (gHatHalfProductOutcomeOperator
                          params family k (pointTupleTail xs) p.2)ᴴ) *
                      (gHatIdxMeas params family (xs 0)).outcome p.1 := by
              symm
              exact Fintype.sum_equiv (Fin.consEquiv α)
                (fun p =>
                  (gHatIdxMeas params family (xs 0)).outcome p.1 *
                    (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) p.2 *
                      (gHatHalfProductOutcomeOperator
                        params family k (pointTupleTail xs) p.2)ᴴ) *
                    (gHatIdxMeas params family (xs 0)).outcome p.1)
                (fun gs =>
                  let half := gHatHalfProductOutcomeOperator params family (k + 1) xs gs
                  half * halfᴴ)
                (by
                  intro p
                  have htail :
                      gHatTupleOutcomeTail ((Fin.consEquiv α) p) = p.2 := by
                    funext i
                    rfl
                  simp [gHatHalfProductOutcomeOperator, htail,
                    Matrix.conjTranspose_mul,
                    Matrix.mul_assoc, (gHatIdxMeas params family (xs 0)).outcome_hermitian])
            rw [hsplit]
            rw [← Finset.univ_product_univ, Finset.sum_product]
            calc
              ∑ g : GHatOutcome params,
                  ∑ gs : GHatTupleOutcome params k,
                    (gHatIdxMeas params family (xs 0)).outcome g *
                      (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                        (gHatHalfProductOutcomeOperator
                          params family k (pointTupleTail xs) gs)ᴴ) *
                      (gHatIdxMeas params family (xs 0)).outcome g
                = ∑ g : GHatOutcome params,
                    (gHatIdxMeas params family (xs 0)).outcome g *
                      (∑ gs : GHatTupleOutcome params k,
                        gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                          (gHatHalfProductOutcomeOperator
                            params family k (pointTupleTail xs) gs)ᴴ) *
                      (gHatIdxMeas params family (xs 0)).outcome g := by
                    refine Finset.sum_congr rfl ?_
                    intro g _hg
                    calc
                      ∑ gs : GHatTupleOutcome params k,
                          (gHatIdxMeas params family (xs 0)).outcome g *
                            (gHatHalfProductOutcomeOperator
                              params family k (pointTupleTail xs) gs *
                              (gHatHalfProductOutcomeOperator
                                params family k (pointTupleTail xs) gs)ᴴ) *
                            (gHatIdxMeas params family (xs 0)).outcome g
                        = (∑ gs : GHatTupleOutcome params k,
                            (gHatIdxMeas params family (xs 0)).outcome g *
                              (gHatHalfProductOutcomeOperator
                                params family k (pointTupleTail xs) gs *
                                (gHatHalfProductOutcomeOperator
                                  params family k (pointTupleTail xs) gs)ᴴ)) *
                            (gHatIdxMeas params family (xs 0)).outcome g := by
                              rw [Finset.sum_mul]
                        _ = (gHatIdxMeas params family (xs 0)).outcome g *
                              (∑ gs : GHatTupleOutcome params k,
                                gHatHalfProductOutcomeOperator
                                  params family k (pointTupleTail xs) gs *
                                  (gHatHalfProductOutcomeOperator
                                    params family k (pointTupleTail xs) gs)ᴴ) *
                              (gHatIdxMeas params family (xs 0)).outcome g := by
                              rw [Matrix.mul_sum]
              _ = ∑ g : GHatOutcome params,
                    (gHatIdxMeas params family (xs 0)).outcome g *
                      (gHatHalfProductTotalOperator params family k (pointTupleTail xs) *
                        (gHatHalfProductTotalOperator
                          params family k (pointTupleTail xs))ᴴ) *
                      (gHatIdxMeas params family (xs 0)).outcome g := by
                    refine Finset.sum_congr rfl ?_
                    intro g _hg
                    rw [ih (pointTupleTail xs)]
              _ = ∑ g : GHatOutcome params,
                    (gHatIdxMeas params family (xs 0)).outcome g * 1 *
                      (gHatIdxMeas params family (xs 0)).outcome g := by
                    refine Finset.sum_congr rfl ?_
                    intro g _hg
                    simp [gHatHalfProductTotalOperator_eq_one]
              _ = ∑ g : GHatOutcome params,
                    (gHatIdxMeas params family (xs 0)).outcome g *
                      (gHatIdxMeas params family (xs 0)).outcome g := by
                    simp
              _ = ∑ g : GHatOutcome params, (gHatIdxMeas params family (xs 0)).outcome g := by
                    refine Finset.sum_congr rfl ?_
                    intro g _hg
                    exact gHatIdxMeas_proj params family (xs 0) g
              _ = (gHatIdxMeas params family (xs 0)).total := by
                    rw [(gHatIdxMeas params family (xs 0)).sum_eq_total]
              _ = (1 : MIPStarRE.Quantum.Op ι) := by
                    simp [gHatIdxMeas, completeSubMeas]
              _ =
                  gHatHalfProductTotalOperator params family (k + 1) xs *
                    (gHatHalfProductTotalOperator params family (k + 1) xs)ᴴ := by
                    simp [gHatHalfProductTotalOperator_eq_one]
      total_le_one := by
        simp [gHatHalfProductTotalOperator_eq_one] }

/-- Restrict a submeasurement to the outcomes satisfying `p`, dropping all other
mass from the total operator. -/
noncomputable def restrictSubMeas {α : Type*} [Fintype α]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p] :
    SubMeas α ι :=
  open Classical in
    { outcome := fun a => if p a then A.outcome a else 0
      total := ∑ a ∈ Finset.univ.filter p, A.outcome a
      outcome_pos := by
        intro a
        by_cases ha : p a <;> simp [ha, A.outcome_pos a]
      sum_eq_total := by
        simp [Finset.sum_filter]
      total_le_one := by
        calc
          ∑ a ∈ Finset.univ.filter p, A.outcome a ≤ ∑ a : α, A.outcome a := by
            exact Finset.sum_le_univ_sum_of_nonneg
              (s := Finset.univ.filter p)
              (w := fun a => A.outcome_pos a)
          _ = A.total := by
            rw [A.sum_eq_total]
          _ ≤ 1 := A.total_le_one }

/-- Restrict the sandwiched completed-slice family to tuples with support of size at
least `d + 1`, matching the `|τ| ≥ d+1` filter in the paper before interpolation. -/
noncomputable def interpolationEligibleSandwichFamily (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) ι :=
  fun xs =>
    open Classical in
      restrictSubMeas
        (gHatSandwichFamily params family k xs)
        (InterpolationEligible params)

/-- Concrete family for the half-sandwich product of `k` completed slices. -/
noncomputable def gHatHalfSandwichLeft (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxOpFamily (PointTuple params k) (GHatTupleOutcome params k) (ι × ι) :=
  fun xs =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      { outcome := fun gs => gHatHalfProductOutcomeOperator params family k xs gs
        total := gHatHalfProductTotalOperator params family k xs
      }

/-- Concrete family for the cyclically permuted half-sandwich product. -/
noncomputable def gHatHalfSandwichRight (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxOpFamily (PointTuple params k) (GHatTupleOutcome params k) (ι × ι) :=
  fun xs =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      { outcome := fun gs => gHatRotatedHalfProductOutcomeOperator params family k xs gs
        total := gHatRotatedHalfProductTotalOperator params family k xs
      }

/-- The operator-polynomial `S_{τ≥ℓ}` from `lem:from-H-to-G` (eq:S-def):
`S_{τ≥ℓ} = ∑_{r : r + suffixWeight ≥ d+1} C(ℓ-1, r) · G^r · (I-G)^{(ℓ-1)-r}`
where `G` is the averaged total operator. -/
noncomputable def suffixBernoulliWeightOperator (params : Parameters)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) : MIPStarRE.Quantum.Op ι :=
  let G := family.averagedSubMeas.total
  let suffixWeight := (Finset.univ.filter fun i : Fin k => ℓ ≤ i.val ∧ τ i).card
  ∑ r ∈ Finset.range ℓ,
    if r + suffixWeight ≥ params.d + 1 then
      (Nat.choose (ℓ - 1) r : ℂ) • (G ^ r * (1 - G) ^ (ℓ - 1 - r))
    else 0

/-- The default type used when packaging the recurrence step at the statement level. -/
def emptyGHatType (k : ℕ) : GHatType k :=
  fun _ => false

-- MISMATCH: see #141
-- TODO: the paper's definition of `H^{x_1,\dots,x_k}_h` sums only the tuples `h_τ`
-- that are globally consistent with a single polynomial `h`; see the pasted-measurement
-- definition in `references/ldt-paper/ld-pasting.tex` around lines 474-495 and the
-- `Global_τ(x)` discussion around lines 1123-1162. The current scaffold now matches the
-- paper's `|τ| ≥ d+1` eligibility filter, but it still postprocesses every eligible tuple
-- through `interpolateCompletedSlices` instead of explicitly filtering by `h_τ`.
/-- Partial Lean model of the interpolated operator `H^{x_1,\dots,x_k}_h`. -/
noncomputable def pastedInterpolationFamily (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (Polynomial params.next) ι :=
  fun xs =>
    postprocess (interpolationEligibleSandwichFamily params family k xs)
      (interpolateCompletedSlices params k xs)

/-- The averaged sandwiched family restricted to outcome tuples of type `τ`
with `|τ| ≥ d+1`, as in `lem:over-all-outcomes`. -/
noncomputable def averagedEligibleSandwichSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    SubMeas (GHatTupleOutcome params k) ι :=
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (interpolationEligibleSandwichFamily params family k)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- The specific pasted submeasurement constructed from the sandwich/interpolation scheme. -/
noncomputable def constructedPastedSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) : SubMeas (Polynomial params.next) ι :=
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (pastedInterpolationFamily params family k)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- The distinguished fallback polynomial `h₀` that receives the completion mass. -/
noncomputable def pastedFallbackOutcome (params : Parameters) : Polynomial params.next :=
  fallbackInterpolatedPolynomial params

/-- The specific pasted measurement obtained by completing the constructed pasted submeasurement.

The paper adds all missing mass `I - H_total` to a single distinguished polynomial
outcome `h₀` (the fallback interpolant).  So the outcome operator for `h₀` becomes
`H_{h₀} + (I - H_total)` while all other outcomes keep their original operators, and
the total is genuinely the identity `I`. -/
noncomputable def constructedPastedMeasurement (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) : Measurement (Polynomial params.next) ι where
  toSubMeas := by
    classical
    let H := constructedPastedSubMeas params family k
    let h₀ := pastedFallbackOutcome params
    let completionMass := 1 - H.total
    exact
      { outcome := fun h =>
          if h = h₀ then
            H.outcome h + completionMass
          else
            H.outcome h
        total := 1
        outcome_pos := by
          intro h
          by_cases hh : h = h₀
          · simpa [hh, completionMass] using
              add_nonneg (H.outcome_pos h₀) (sub_nonneg.mpr H.total_le_one)
          · simp [hh, H.outcome_pos h]
        sum_eq_total := by
          have hsingle :
              (∑ x : Polynomial params.next,
                  if x = h₀ then completionMass else 0) = completionMass := by
            simp
          have hrewrite :
              (∑ a : Polynomial params.next,
                  if a = h₀ then H.outcome a + completionMass else H.outcome a) =
                ∑ a : Polynomial params.next,
                  (H.outcome a + if a = h₀ then completionMass else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases h : a = h₀ <;> simp [h]
          rw [hrewrite, Finset.sum_add_distrib, H.sum_eq_total, hsingle]
          simp [completionMass]
        total_le_one := by
          exact le_rfl }
  total_eq_one := rfl

/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
noncomputable def verticalLineMeasurementFamily (params : Parameters)
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    (strategy.axisParallelMeasurement ℓ).toSubMeas

/-- Explicit value extracted from the `i`-th completed slice outcome at the test point. -/
noncomputable def ldSandwichLineOnePointLeftFamily (params : Parameters)
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess (gHatSandwichFamily params family k q.2) (fun gs =>
      if h : i < k then
        Option.map (fun g => g q.1) (gs ⟨i, h⟩)
      else
        none)

/-- Explicit value extracted from the vertical line measurement `B^u` at the slice height `x_i`. -/
noncomputable def ldSandwichLineOnePointRightFamily (params : Parameters)
    (strategy : SymStrat params.next ι)
    (_family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess (verticalLineMeasurementFamily params strategy q.1) (fun f =>
      if h : i < k then
        some (f (q.2 ⟨i, h⟩))
      else
        none)

/-- Restrict a global polynomial-valued submeasurement to the vertical line through `u`. -/
noncomputable def hRestrictionToVerticalLine (params : Parameters)
    (H : SubMeas (Polynomial params.next) ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let verticalLine : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := ⟨params.m, Nat.lt_succ_self params.m⟩ }
    postprocess H (fun h => Polynomial.restrictToAxisParallelLine params.next h verticalLine)

/-- Collapse a submeasurement to its `Unit`-valued total operator. -/
noncomputable def pastedMeasurementTotal
    {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (H : SubMeas α ι) : IdxSubMeas Unit Unit ι :=
  constSubMeasFamily (postprocess H (fun _ => ()))

/-- The total operator of the specifically constructed pasted submeasurement. -/
noncomputable def constructedPastedMeasurementTotal (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  pastedMeasurementTotal (constructedPastedSubMeas params family k)

/-- The expansion over all outcome types `τ`, written as the
total mass of the averaged sandwich family restricted to `|τ| ≥ d+1`. -/
noncomputable def allOutcomesExpansionFamily (params : Parameters)
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  pastedMeasurementTotal (averagedEligibleSandwichSubMeas params family k)

/-- The Bernoulli-tail polynomial in the averaged complete operator `G = E_x \sum_g G^x_g`. -/
noncomputable def bernoulliTailFromFamily (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  constSubMeasFamily <|
    let Y := bernoulliTailOperator k params.d ((IdxPolyFamily.averagedSubMeas family).total)
    { outcome := fun _ => Y
      total := Y
      outcome_pos := by
        intro _
        let G := (IdxPolyFamily.averagedSubMeas family).total
        have hG : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
        have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
        simpa [G] using bernoulliTailOperator_nonneg k params.d G hG hGle
      sum_eq_total := by
        simp
      total_le_one := by
        -- This needs the Bernoulli-tail upper bound from the matrix Chernoff step.
        sorry }

/-- One recurrence-step left-hand family from the proof of `lem:from-H-to-G`. -/
-- MISMATCH: see #141
-- TODO: in `references/ldt-paper/ld-pasting.tex` around lines 1380-1425, the
-- recurrence is indexed by the suffix type `τ_{\ge ℓ}` and uses the operator
-- `S_{τ_{\ge ℓ}}`. The current Lean scaffold still packages the recurrence over `Unit`
-- and plugs in `emptyGHatType k`, so it forgets the τ-dependence entirely. Repairing
-- this will require threading a suffix-type index through these families and the
-- corresponding statement containers in `Pasting/Statements.lean`.
noncomputable def fromHToGRecurrenceLeftFamily (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    IdxOpFamily Unit Unit ι :=
  fun _ =>
    let base := allOutcomesExpansionFamily params strategy family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { outcome := fun _ => base.total * weight
      total := base.total * weight }

/-- One recurrence-step right-hand family from the proof of `lem:from-H-to-G`. -/
-- MISMATCH: see #141
-- TODO: mirror the `τ_{\ge ℓ}`-indexed recurrence from `ld-pasting.tex`
-- lines 1380-1425 on the right-hand side as well. The present `Unit`-indexed
-- placeholder only tracks the Bernoulli tail operator and loses the paper's
-- suffix-type bookkeeping.
noncomputable def fromHToGRecurrenceRightFamily (params : Parameters)
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    IdxOpFamily Unit Unit ι :=
  fun _ =>
    let base := bernoulliTailFromFamily params family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { outcome := fun _ => base.total * weight
      total := base.total * weight }

end MIPStarRE.LDT.Pasting
