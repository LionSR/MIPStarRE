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
noncomputable def switcherooPointProductLeft {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      orderedProductSubMeas
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete hypothesis family for `M^y_o G^x_g` on the `Polynomial params × Outcome` outcome type. -/
noncomputable def switcherooPointProductRight {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      reversedProductSubMeas
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `G^x M^y_o`. -/
noncomputable def switcherooAggregateLeft {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.1)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `M^y_o G^x`. -/
noncomputable def switcherooAggregateRight {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      multiplyByTotalOnRight
        ((M q.2).toSubMeas)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y`. -/
noncomputable def completePartPointProductLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas q.1).toSubMeas)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x_g`. -/
noncomputable def completePartPointProductRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x G^y`. -/
noncomputable def completePartTotalProductLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      multiplyByTotalOnRight
        (completePartSubMeas params family q.1)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x`. -/
noncomputable def completePartTotalProductRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.2)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y_⊥`. -/
noncomputable def incompletePartPointProductLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas q.1).toSubMeas)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_g`. -/
noncomputable def incompletePartPointProductRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x_⊥ G^y_⊥`. -/
noncomputable def incompletePartTotalProductLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      multiplyByTotalOnRight
        (incompletePartSubMeas params family q.1)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_⊥`. -/
noncomputable def incompletePartTotalProductRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
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
    IdxSubMeas (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      orderedProductSubMeas
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- Concrete family for the reversed pairwise product `\widehat G^y_h \widehat G^x_g`. -/
noncomputable def gHatPairProductRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      reversedProductSubMeas
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

/-- The total half-product `\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductTotalOperator (params : Parameters)
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → MIPStarRE.Quantum.Op ι
  | 0, _xs =>
      1
  | k + 1, xs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).total *
        gHatHalfProductTotalOperator params family k (pointTupleTail xs)

/-- The cyclically rotated half-product `\widehat G^{x_2}_{g_2} \cdots \widehat G^{x_k}_{g_k} \widehat G^{x_1}_{g_1}`. -/
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

private def gHatTupleConsEquiv (params : Parameters) (k : ℕ) :
    GHatTupleOutcome params (k + 1) ≃ (GHatOutcome params × GHatTupleOutcome params k) where
  toFun gs := (gs 0, gHatTupleOutcomeTail gs)
  invFun p := fun i => Fin.cases p.1 p.2 i
  left_inv gs := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  right_inv p := by
    cases p
    rfl

private noncomputable def gHatHalfProductSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → SubMeas (GHatTupleOutcome params k) ι
  | 0, _xs =>
      { outcome := fun _ => 1
        total := 1
        outcome_pos := by
          intro _
          simpa using (zero_le_one : (0 : MIPStarRE.Quantum.Op ι) ≤ 1)
        sum_eq_total := by
          simp
        total_le_one := by
          exact le_rfl }
  | k + 1, xs =>
      let head := ((gHatIdxMeas params family (xs 0)).toSubMeas)
      let tail := gHatHalfProductSubMeas params family k (pointTupleTail xs)
      postprocess (orderedProductSubMeas head tail) (gHatTupleConsEquiv params k).symm

private noncomputable def gHatRotatedHalfProductSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → SubMeas (GHatTupleOutcome params k) ι
  | 0, _xs =>
      { outcome := fun _ => 1
        total := 1
        outcome_pos := by
          intro _
          simpa using (zero_le_one : (0 : MIPStarRE.Quantum.Op ι) ≤ 1)
        sum_eq_total := by
          simp
        total_le_one := by
          exact le_rfl }
  | k + 1, xs =>
      let head := ((gHatIdxMeas params family (xs 0)).toSubMeas)
      let tail := gHatHalfProductSubMeas params family k (pointTupleTail xs)
      postprocess (reversedProductSubMeas head tail) (gHatTupleConsEquiv params k).symm

private lemma gHatHalfProductTotalOperator_eq_one (params : Parameters)
    (family : IdxPolyFamily params ι) :
    ∀ k xs, gHatHalfProductTotalOperator params family k xs = 1
  | 0, _xs => rfl
  | k + 1, xs => by
      rw [gHatHalfProductTotalOperator, gHatHalfProductTotalOperator_eq_one]
      simpa using (gHatIdxMeas params family (xs 0)).total_eq_one

private lemma gHatRotatedHalfProductTotalOperator_eq_one (params : Parameters)
    (family : IdxPolyFamily params ι) :
    ∀ k xs, gHatRotatedHalfProductTotalOperator params family k xs = 1
  | 0, _xs => rfl
  | k + 1, xs => by
      rw [gHatRotatedHalfProductTotalOperator, gHatHalfProductTotalOperator_eq_one]
      simpa using (gHatIdxMeas params family (xs 0)).total_eq_one

private lemma subMeas_total_nonneg {α : Type*} [Fintype α]
    (A : SubMeas α ι) : 0 ≤ A.total := by
  rw [← A.sum_eq_total]
  exact Finset.sum_nonneg fun a _ => A.outcome_pos a

private lemma psdPow {X : MIPStarRE.Quantum.Op ι} (hX : 0 ≤ X) :
    ∀ n : ℕ, 0 ≤ X ^ n
  | 0 => by
      simpa using (zero_le_one : (0 : MIPStarRE.Quantum.Op ι) ≤ 1)
  | n + 1 => by
      have hcomm : Commute (X ^ n) X := Commute.pow_self X n
      have hnonneg : 0 ≤ X ^ n * X := (commute_iff_mul_nonneg (psdPow hX n) hX).mp hcomm
      simpa [pow_succ] using hnonneg

private lemma bernoulliTermNonneg (X : MIPStarRE.Quantum.Op ι)
    (hX : 0 ≤ X) (hXle : X ≤ 1) (r k : ℕ) :
    0 ≤ (Nat.choose k r : ℂ) • (X ^ r * (1 - X) ^ (k - r)) := by
  rw [Nat.cast_smul_eq_nsmul]
  have hOneSub : 0 ≤ 1 - X := sub_nonneg.mpr hXle
  have hXcomm : Commute X (1 - X) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Commute.one_left X).sub_right (Commute.refl X)
  have hcomm : Commute (X ^ r) ((1 - X) ^ (k - r)) := hXcomm.pow_pow r (k - r)
  have hprod : 0 ≤ X ^ r * (1 - X) ^ (k - r) :=
    (commute_iff_mul_nonneg (psdPow hX r) (psdPow hOneSub (k - r))).mp hcomm
  exact nsmul_nonneg hprod _

private lemma bernoulliBinomialSumEqOne (X : MIPStarRE.Quantum.Op ι) (k : ℕ) :
    ∑ r ∈ Finset.range (k + 1), (Nat.choose k r : ℂ) • (X ^ r * (1 - X) ^ (k - r)) = 1 := by
  have hcomm : Commute X (1 - X) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Commute.one_left X).sub_right (Commute.refl X)
  calc
    ∑ r ∈ Finset.range (k + 1), (Nat.choose k r : ℂ) • (X ^ r * (1 - X) ^ (k - r))
      = ∑ r ∈ Finset.range (k + 1),
          X ^ r * (1 - X) ^ (k - r) * (Nat.choose k r : MIPStarRE.Quantum.Op ι) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul,
              (Nat.cast_commute (Nat.choose k r) (X ^ r * (1 - X) ^ (k - r))).eq]
    _ = (X + (1 - X)) ^ k := by
          simpa using (hcomm.add_pow k).symm
    _ = 1 := by
          simp

private lemma bernoulliTailOperator_nonneg (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι)
    (hX : 0 ≤ X) (hXle : X ≤ 1) :
    0 ≤ bernoulliTailOperator k degree X := by
  unfold bernoulliTailOperator
  refine Finset.sum_nonneg ?_
  intro r hr
  exact bernoulliTermNonneg X hX hXle r k

private lemma bernoulliTailOperator_le_one (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι)
    (hX : 0 ≤ X) (hXle : X ≤ 1) :
    bernoulliTailOperator k degree X ≤ 1 := by
  let term : ℕ → MIPStarRE.Quantum.Op ι :=
    fun r => (Nat.choose k r : ℂ) • (X ^ r * (1 - X) ^ (k - r))
  have hIcc :
      Finset.Icc (degree + 1) k = (Finset.Icc 0 k).filter (fun r => degree + 1 ≤ r) := by
    ext r
    simp [and_comm]
  have hRange : Finset.Icc 0 k = Finset.range (k + 1) := by
    ext r
    simp
  calc
    bernoulliTailOperator k degree X
      = ∑ r ∈ Finset.Icc 0 k, if degree + 1 ≤ r then term r else 0 := by
          unfold bernoulliTailOperator term
          rw [hIcc, Finset.sum_filter]
    _ ≤ ∑ r ∈ Finset.Icc 0 k, term r := by
          refine Finset.sum_le_sum ?_
          intro r hr
          by_cases h : degree + 1 ≤ r
          · simp [h]
          · simp [h]
            exact bernoulliTermNonneg X hX hXle r k
    _ = ∑ r ∈ Finset.range (k + 1), term r := by
          rw [hRange]
    _ = 1 := by
          simpa [term] using bernoulliBinomialSumEqOne X k

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
        sorry
      total_le_one := by
        simpa [gHatHalfProductTotalOperator_eq_one params family k xs] }

/-- Concrete family for the half-sandwich product of `k` completed slices. -/
noncomputable def gHatHalfSandwichLeft (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) (ι × ι) :=
  fun xs =>
    leftPlacedSubMeas (ιB := ι) (gHatHalfProductSubMeas params family k xs)

/-- Concrete family for the cyclically permuted half-sandwich product. -/
noncomputable def gHatHalfSandwichRight (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) (ι × ι) :=
  fun xs =>
    leftPlacedSubMeas (ιB := ι) (gHatRotatedHalfProductSubMeas params family k xs)

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

private lemma bernoulliMonomial_commute (X : MIPStarRE.Quantum.Op ι)
    (r s r' s' : ℕ) :
    Commute (X ^ r * (1 - X) ^ s) (X ^ r' * (1 - X) ^ s') := by
  have hXcomm : Commute X (1 - X) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Commute.one_left X).sub_right (Commute.refl X)
  have hleft : Commute (X ^ r * (1 - X) ^ s) (X ^ r') :=
    Commute.mul_left
      ((Commute.refl X).pow_pow r r')
      (hXcomm.pow_pow r' s).symm
  have hright : Commute (X ^ r * (1 - X) ^ s) ((1 - X) ^ s') :=
    Commute.mul_left
      (hXcomm.pow_pow r s')
      ((Commute.refl (1 - X)).pow_pow s s')
  exact hleft.mul_right hright

private lemma bernoulliTermCommute (X : MIPStarRE.Quantum.Op ι)
    (r k s l : ℕ) :
    Commute ((Nat.choose k r : ℂ) • (X ^ r * (1 - X) ^ (k - r)))
      ((Nat.choose l s : ℂ) • (X ^ s * (1 - X) ^ (l - s))) := by
  exact
    ((bernoulliMonomial_commute X r (k - r) s (l - s)).smul_left
      (Nat.choose k r : ℂ)).smul_right (Nat.choose l s : ℂ)

private lemma suffixBernoulliWeightOperator_nonneg (params : Parameters)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) :
    0 ≤ suffixBernoulliWeightOperator params family k ℓ τ := by
  let G := family.averagedSubMeas.total
  have hG : 0 ≤ G := subMeas_total_nonneg family.averagedSubMeas
  have hGle : G ≤ 1 := family.averagedSubMeas.total_le_one
  unfold suffixBernoulliWeightOperator
  refine Finset.sum_nonneg ?_
  intro r hr
  by_cases h :
      r + (Finset.univ.filter fun i : Fin k => ℓ ≤ i.val ∧ τ i).card ≥ params.d + 1
  · simp [h]
    simpa [G] using bernoulliTermNonneg G hG hGle r (ℓ - 1)
  · simp [h]

private lemma suffixBernoulliWeightOperator_le_one (params : Parameters)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) :
    suffixBernoulliWeightOperator params family k ℓ τ ≤ 1 := by
  let G := family.averagedSubMeas.total
  have hG : 0 ≤ G := subMeas_total_nonneg family.averagedSubMeas
  have hGle : G ≤ 1 := family.averagedSubMeas.total_le_one
  cases ℓ with
  | zero =>
      simp [suffixBernoulliWeightOperator]
  | succ n =>
      let term : ℕ → MIPStarRE.Quantum.Op ι :=
        fun r => (Nat.choose n r : ℂ) • (G ^ r * (1 - G) ^ (n - r))
      calc
        suffixBernoulliWeightOperator params family k (n + 1) τ
          = ∑ r ∈ Finset.range (n + 1),
              if r + (Finset.univ.filter fun i : Fin k => n + 1 ≤ i.val ∧ τ i).card ≥
                  params.d + 1 then
                term r
              else 0 := by
                  unfold suffixBernoulliWeightOperator term
        _ ≤ ∑ r ∈ Finset.range (n + 1), term r := by
              refine Finset.sum_le_sum ?_
              intro r hr
              by_cases h :
                  r + (Finset.univ.filter fun i : Fin k => n + 1 ≤ i.val ∧ τ i).card ≥
                    params.d + 1
              · simp [h]
              · simp [h]
                simpa [G, term] using bernoulliTermNonneg G hG hGle r n
        _ = 1 := by
              simpa [G, term] using bernoulliBinomialSumEqOne G n

/-- The default type used when packaging the recurrence step at the statement level. -/
def emptyGHatType (k : ℕ) : GHatType k :=
  fun _ => false

/-- Placeholder family for the interpolated operator `H^{x_1,\dots,x_k}_h`. -/
noncomputable def pastedInterpolationFamily (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (Polynomial params.next) ι :=
  fun xs =>
    postprocess (gHatSandwichFamily params family k xs)
      (interpolateCompletedSlices params k xs)

/-- The averaged sandwiched family before interpolation. -/
noncomputable def averagedSandwichSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    SubMeas (GHatTupleOutcome params k) ι :=
  MIPStarRE.LDT.Pasting.averageIdxSubMeas
    (distinctTupleDistribution params k)
    (gHatSandwichFamily params family k)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- The specific pasted submeasurement constructed from the sandwich/interpolation scheme. -/
noncomputable def constructedPastedSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) : SubMeas (Polynomial params.next) ι :=
  MIPStarRE.LDT.Pasting.averageIdxSubMeas
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
    (family : IdxPolyFamily params ι) (k : ℕ) : Measurement (Polynomial params.next) ι :=
  MIPStarRE.LDT.Preliminaries.completeAtOutcome
    (constructedPastedSubMeas params family k)
    (pastedFallbackOutcome params)

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
noncomputable def pastedMeasurementTotal {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (H : SubMeas α ι) : IdxSubMeas Unit Unit ι :=
  constSubMeasFamily (postprocess H (fun _ => ()))

/-- The total operator of the specifically constructed pasted submeasurement. -/
noncomputable def constructedPastedMeasurementTotal (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  pastedMeasurementTotal (constructedPastedSubMeas params family k)

/-- The expansion over all outcome types `τ`, written as the total mass of the averaged sandwich family. -/
noncomputable def allOutcomesExpansionFamily (params : Parameters)
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  pastedMeasurementTotal (averagedSandwichSubMeas params family k)

/-- The Bernoulli-tail polynomial in the averaged complete operator `G = E_x \sum_g G^x_g`. -/
noncomputable def bernoulliTailFromFamily (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  constSubMeasFamily <|
    let G := IdxPolyFamily.averagedSubMeas family
    let Y := bernoulliTailOperator k params.d G.total
    { outcome := fun _ => Y
      total := Y
      outcome_pos := by
        intro _
        exact bernoulliTailOperator_nonneg k params.d G.total
          (subMeas_total_nonneg G) G.total_le_one
      sum_eq_total := by
        simp
      total_le_one := by
        exact bernoulliTailOperator_le_one k params.d G.total
          (subMeas_total_nonneg G) G.total_le_one }

private lemma allOutcomesExpansionFamily_total_eq (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    (allOutcomesExpansionFamily params strategy family k ()).total =
      (∑ xs ∈ (distinctTupleDistribution params k).support,
        (distinctTupleDistribution params k).weight xs) • (1 : MIPStarRE.Quantum.Op ι) := by
  simp [allOutcomesExpansionFamily, pastedMeasurementTotal, averagedSandwichSubMeas,
    averageOperatorOverDistribution, gHatSandwichFamily,
    gHatHalfProductTotalOperator_eq_one]

private lemma bernoulliTailOperator_commute_suffixBernoulliWeightOperator (params : Parameters)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) :
    Commute (bernoulliTailOperator k params.d family.averagedSubMeas.total)
      (suffixBernoulliWeightOperator params family k ℓ τ) := by
  let G := family.averagedSubMeas.total
  let tailTerm : ℕ → MIPStarRE.Quantum.Op ι :=
    fun r => (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r))
  let weightTerm : ℕ → MIPStarRE.Quantum.Op ι :=
    fun r => (Nat.choose (ℓ - 1) r : ℂ) • (G ^ r * (1 - G) ^ (ℓ - 1 - r))
  unfold bernoulliTailOperator suffixBernoulliWeightOperator
  refine Commute.sum_right _ _ _ ?_
  intro r hr
  by_cases h :
      r + (Finset.univ.filter fun i : Fin k => ℓ ≤ i.val ∧ τ i).card ≥ params.d + 1
  · simp [h, weightTerm]
    refine Commute.sum_left _ _ _ ?_
    intro s hs
    simpa [G, tailTerm, weightTerm] using bernoulliTermCommute G s k r (ℓ - 1)
  · simp [h]

/-- One recurrence-step left-hand family from the proof of `lem:from-H-to-G`. -/
noncomputable def fromHToGRecurrenceLeftFamily (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    IdxSubMeas Unit Unit ι :=
  fun _ =>
    let base := allOutcomesExpansionFamily params strategy family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { outcome := fun _ => base.total * weight
      total := base.total * weight
      outcome_pos := by
        intro _
        let coeff : Error :=
          ∑ xs ∈ (distinctTupleDistribution params k).support,
            (distinctTupleDistribution params k).weight xs
        have hcoeff_nonneg : 0 ≤ coeff := by
          unfold coeff
          exact Finset.sum_nonneg fun xs _ => (distinctTupleDistribution params k).nonnegative xs
        have hweight_nonneg :
            0 ≤ suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k) :=
          suffixBernoulliWeightOperator_nonneg params family k ℓ (emptyGHatType k)
        rw [allOutcomesExpansionFamily_total_eq params strategy family k]
        simpa [coeff, smul_mul_assoc] using
          (smul_nonneg hcoeff_nonneg hweight_nonneg :
            0 ≤ coeff • suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k))
      sum_eq_total := by
        simp
      total_le_one := by
        let coeff : Error :=
          ∑ xs ∈ (distinctTupleDistribution params k).support,
            (distinctTupleDistribution params k).weight xs
        have hcoeff_nonneg : 0 ≤ coeff := by
          unfold coeff
          exact Finset.sum_nonneg fun xs _ => (distinctTupleDistribution params k).nonnegative xs
        have hcoeff_le_one : coeff ≤ 1 := by
          simpa [coeff] using distinctTupleDistribution_weight_sum_le_one params k
        have hweight_le_one :
            suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k) ≤ 1 :=
          suffixBernoulliWeightOperator_le_one params family k ℓ (emptyGHatType k)
        rw [allOutcomesExpansionFamily_total_eq params strategy family k]
        calc
          (coeff • (1 : MIPStarRE.Quantum.Op ι)) *
              suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
            = coeff • suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k) := by
                simp [smul_mul_assoc]
          _ ≤ coeff • (1 : MIPStarRE.Quantum.Op ι) := by
                exact smul_le_smul_of_nonneg_left hweight_le_one hcoeff_nonneg
          _ ≤ (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
                exact smul_le_smul_of_nonneg_right hcoeff_le_one zero_le_one
          _ = 1 := by
                simp }

/-- One recurrence-step right-hand family from the proof of `lem:from-H-to-G`. -/
noncomputable def fromHToGRecurrenceRightFamily (params : Parameters)
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    IdxSubMeas Unit Unit ι :=
  fun _ =>
    let base := bernoulliTailFromFamily params family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { outcome := fun _ => base.total * weight
      total := base.total * weight
      outcome_pos := by
        intro _
        let G := family.averagedSubMeas.total
        have hG : 0 ≤ G := subMeas_total_nonneg family.averagedSubMeas
        have hGle : G ≤ 1 := family.averagedSubMeas.total_le_one
        change
          0 ≤ bernoulliTailOperator k params.d G *
            suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
        unfold bernoulliTailOperator suffixBernoulliWeightOperator
        rw [Finset.sum_mul]
        refine Finset.sum_nonneg ?_
        intro s hs
        rw [Finset.mul_sum]
        refine Finset.sum_nonneg ?_
        intro r hr
        by_cases h : r + (Finset.univ.filter fun i : Fin k => ℓ ≤ i.val ∧ emptyGHatType k i).card ≥
            params.d + 1
        · simp [h]
          have hs_nonneg : 0 ≤ (Nat.choose k s : ℂ) • (G ^ s * (1 - G) ^ (k - s)) := by
            exact bernoulliTermNonneg G hG hGle s k
          have hr_nonneg : 0 ≤ (Nat.choose (ℓ - 1) r : ℂ) • (G ^ r * (1 - G) ^ (ℓ - 1 - r)) := by
            exact bernoulliTermNonneg G hG hGle r (ℓ - 1)
          exact (commute_iff_mul_nonneg hs_nonneg hr_nonneg).mp
            (by simpa [G] using bernoulliTermCommute G s k r (ℓ - 1))
        · simp [h]
      sum_eq_total := by
        simp
      total_le_one := by
        let G := family.averagedSubMeas.total
        have hG : 0 ≤ G := subMeas_total_nonneg family.averagedSubMeas
        have hGle : G ≤ 1 := family.averagedSubMeas.total_le_one
        have hbase_nonneg : 0 ≤ bernoulliTailOperator k params.d G :=
          bernoulliTailOperator_nonneg k params.d G hG hGle
        have hbase_le_one : bernoulliTailOperator k params.d G ≤ 1 :=
          bernoulliTailOperator_le_one k params.d G hG hGle
        have hweight_le_one :
            suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k) ≤ 1 :=
          suffixBernoulliWeightOperator_le_one params family k ℓ (emptyGHatType k)
        have hcomm :
            Commute (bernoulliTailOperator k params.d G)
              (suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)) := by
          simpa [G] using
            bernoulliTailOperator_commute_suffixBernoulliWeightOperator
              params family k ℓ (emptyGHatType k)
        have hcomm_sub :
            Commute (bernoulliTailOperator k params.d G)
              (1 - suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)) := by
          exact (Commute.one_right _).sub_right hcomm
        have haux :
            bernoulliTailOperator k params.d G *
                suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
              ≤ bernoulliTailOperator k params.d G := by
          have hnonneg :
              0 ≤ bernoulliTailOperator k params.d G *
                (1 - suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)) :=
            (commute_iff_mul_nonneg hbase_nonneg (sub_nonneg.mpr hweight_le_one)).mp hcomm_sub
          have hsub :
              0 ≤ bernoulliTailOperator k params.d G -
                bernoulliTailOperator k params.d G *
                  suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k) := by
            simpa [mul_sub, mul_one] using hnonneg
          exact sub_nonneg.mp hsub
        exact le_trans haux hbase_le_one }

end MIPStarRE.LDT.Pasting
