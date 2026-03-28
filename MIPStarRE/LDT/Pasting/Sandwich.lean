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
def switcherooSelfConsistencyLeft {Outcome : Type*} (params : Parameters)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SliceQuestion params) Outcome (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) ((M x).toSubMeas)

/-- Right tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyRight {Outcome : Type*} (params : Parameters)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SliceQuestion params) Outcome (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) ((M x).toSubMeas)

/-- Concrete hypothesis family for `G^x_g M^y_o`. -/
noncomputable def switcherooPointProductLeft {Outcome : Type*} (params : Parameters)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      orderedProductSubMeas
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete hypothesis family for `M^y_o G^x_g` on the `Polynomial params × Outcome` outcome type. -/
noncomputable def switcherooPointProductRight {Outcome : Type*} (params : Parameters)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      reversedProductSubMeas
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `G^x M^y_o`. -/
noncomputable def switcherooAggregateLeft {Outcome : Type*} (params : Parameters)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.1)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `M^y_o G^x`. -/
noncomputable def switcherooAggregateRight {Outcome : Type*} (params : Parameters)
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
        half * halfᴴ }

/-- Concrete family for the half-sandwich product of `k` completed slices. -/
noncomputable def gHatHalfSandwichLeft (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) (ι × ι) :=
  fun xs =>
    leftPlacedSubMeas (ιB := ι) <|
      { outcome := fun gs => gHatHalfProductOutcomeOperator params family k xs gs
        total := gHatHalfProductTotalOperator params family k xs }

/-- Concrete family for the cyclically permuted half-sandwich product. -/
noncomputable def gHatHalfSandwichRight (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) (ι × ι) :=
  fun xs =>
    leftPlacedSubMeas (ιB := ι) <|
      { outcome := fun gs => gHatRotatedHalfProductOutcomeOperator params family k xs gs
        total := gHatRotatedHalfProductTotalOperator params family k xs }

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
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (gHatSandwichFamily params family k)

/-- The specific pasted submeasurement constructed from the sandwich/interpolation scheme. -/
noncomputable def constructedPastedSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) (k : ℕ) : SubMeas (Polynomial params.next) ι :=
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (pastedInterpolationFamily params family k)

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
  toSubMeas :=
    let H := constructedPastedSubMeas params family k
    let h₀ := pastedFallbackOutcome params
    let completionMass := 1 - H.total
    { outcome := fun h => by
        classical
        exact if h = h₀ then
          H.outcome h + completionMass
        else
          H.outcome h
      total := 1 }
  -- sorry: underlying SubMeas has no PSD/summation invariant; outcome_pos needs
  -- 0 ≤ H.outcome h (+ completionMass) which requires PSD of the sandwich construction
  outcome_pos := sorry
  total_eq_one := rfl
  -- sorry: underlying SubMeas has no PSD/summation invariant; proving ∑ h, outcome h = 1
  -- requires ∑ h, H.outcome h = H.total, which SubMeas does not guarantee
  sum_eq := sorry

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
    let Y := bernoulliTailOperator k params.d ((IdxPolyFamily.averagedSubMeas family).total)
    { outcome := fun _ => Y, total := Y }

/-- One recurrence-step left-hand family from the proof of `lem:from-H-to-G`. -/
noncomputable def fromHToGRecurrenceLeftFamily (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    IdxSubMeas Unit Unit ι :=
  fun _ =>
    let base := allOutcomesExpansionFamily params strategy family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { outcome := fun _ => base.total * weight
      total := base.total * weight }

/-- One recurrence-step right-hand family from the proof of `lem:from-H-to-G`. -/
noncomputable def fromHToGRecurrenceRightFamily (params : Parameters)
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    IdxSubMeas Unit Unit ι :=
  fun _ =>
    let base := bernoulliTailFromFamily params family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { outcome := fun _ => base.total * weight
      total := base.total * weight }

end MIPStarRE.LDT.Pasting
