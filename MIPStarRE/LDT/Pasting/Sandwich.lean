import MIPStarRE.LDT.Pasting.Defs
set_option linter.style.longLine false

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints

noncomputable section

/-- Left tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyLeft {Outcome : Type*} (params : Parameters)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SliceQuestion params) Outcome :=
  fun x => leftPlacedSubMeasurement ((M x).toSubMeasurement)

/-- Right tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyRight {Outcome : Type*} (params : Parameters)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SliceQuestion params) Outcome :=
  fun x => rightPlacedSubMeasurement ((M x).toSubMeasurement)

/-- Concrete hypothesis family for `G^x_g M^y_o`. -/
def switcherooPointProductLeft {Outcome : Type*} (params : Parameters)
    (family : IndexedPolynomialFamily params)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params × Outcome) :=
  fun q =>
    leftPlacedSubMeasurement <|
      orderedProductSubMeasurement
        s!"switcheroo.point.left({params.m},{params.q},{params.d})"
        ((family.meas q.1).toSubMeasurement)
        ((M q.2).toSubMeasurement)

/-- Concrete hypothesis family for `M^y_o G^x_g` on the `Polynomial params × Outcome` outcome type. -/
def switcherooPointProductRight {Outcome : Type*} (params : Parameters)
    (family : IndexedPolynomialFamily params)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params × Outcome) :=
  fun q =>
    leftPlacedSubMeasurement <|
      reversedProductSubMeasurement
        s!"switcheroo.point.right({params.m},{params.q},{params.d})"
        ((family.meas q.1).toSubMeasurement)
        ((M q.2).toSubMeasurement)

/-- Concrete aggregate family for `G^x M^y_o`. -/
def switcherooAggregateLeft {Outcome : Type*} (params : Parameters)
    (family : IndexedPolynomialFamily params)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SlicePairQuestion params) Outcome :=
  fun q =>
    leftPlacedSubMeasurement <|
      multiplyByTotalOnLeft
        s!"switcheroo.aggregate.left({params.m},{params.q},{params.d})"
        (completePartSubMeasurement params family q.1)
        ((M q.2).toSubMeasurement)

/-- Concrete aggregate family for `M^y_o G^x`. -/
def switcherooAggregateRight {Outcome : Type*} (params : Parameters)
    (family : IndexedPolynomialFamily params)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SlicePairQuestion params) Outcome :=
  fun q =>
    leftPlacedSubMeasurement <|
      multiplyByTotalOnRight
        s!"switcheroo.aggregate.right({params.m},{params.q},{params.d})"
        ((M q.2).toSubMeasurement)
        (completePartSubMeasurement params family q.1)

/-- Concrete family for `G^x_g G^y`. -/
def completePartPointProductLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params) :=
  fun q =>
    leftPlacedSubMeasurement <|
      multiplyByTotalOnRight
        s!"complete.point.left({params.m},{params.q},{params.d})"
        ((family.meas q.1).toSubMeasurement)
        (completePartSubMeasurement params family q.2)

/-- Concrete family for `G^y G^x_g`. -/
def completePartPointProductRight (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params) :=
  fun q =>
    leftPlacedSubMeasurement <|
      multiplyByTotalOnLeft
        s!"complete.point.right({params.m},{params.q},{params.d})"
        (completePartSubMeasurement params family q.2)
        ((family.meas q.1).toSubMeasurement)

/-- Concrete family for `G^x G^y`. -/
def completePartTotalProductLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) Unit :=
  fun q =>
    leftPlacedSubMeasurement <|
      multiplyByTotalOnRight
        s!"complete.total.left({params.m},{params.q},{params.d})"
        (completePartSubMeasurement params family q.1)
        (completePartSubMeasurement params family q.2)

/-- Concrete family for `G^y G^x`. -/
def completePartTotalProductRight (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) Unit :=
  fun q =>
    leftPlacedSubMeasurement <|
      multiplyByTotalOnLeft
        s!"complete.total.right({params.m},{params.q},{params.d})"
        (completePartSubMeasurement params family q.2)
        (completePartSubMeasurement params family q.1)

/-- Concrete family for `G^x_g G^y_⊥`. -/
def incompletePartPointProductLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params) :=
  fun q =>
    leftPlacedSubMeasurement <|
      multiplyByTotalOnRight
        s!"incomplete.point.left({params.m},{params.q},{params.d})"
        ((family.meas q.1).toSubMeasurement)
        (incompletePartSubMeasurement params family q.2)

/-- Concrete family for `G^y_⊥ G^x_g`. -/
def incompletePartPointProductRight (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params) :=
  fun q =>
    leftPlacedSubMeasurement <|
      multiplyByTotalOnLeft
        s!"incomplete.point.right({params.m},{params.q},{params.d})"
        (incompletePartSubMeasurement params family q.2)
        ((family.meas q.1).toSubMeasurement)

/-- Concrete family for `G^x_⊥ G^y_⊥`. -/
def incompletePartTotalProductLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) Unit :=
  fun q =>
    leftPlacedSubMeasurement <|
      multiplyByTotalOnRight
        s!"incomplete.total.left({params.m},{params.q},{params.d})"
        (incompletePartSubMeasurement params family q.1)
        (incompletePartSubMeasurement params family q.2)

/-- Concrete family for `G^y_⊥ G^x_⊥`. -/
def incompletePartTotalProductRight (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) Unit :=
  fun q =>
    leftPlacedSubMeasurement <|
      multiplyByTotalOnLeft
        s!"incomplete.total.right({params.m},{params.q},{params.d})"
        (incompletePartSubMeasurement params family q.2)
        (incompletePartSubMeasurement params family q.1)

/-- Left tensor-placement for `\widehat G^x_g`. -/
def gHatSelfConsistencyLeftFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) (GHatOutcome params) :=
  fun x => leftPlacedSubMeasurement ((gHatIndexedMeasurement params family x).toSubMeasurement)

/-- Right tensor-placement for `\widehat G^x_g`. -/
def gHatSelfConsistencyRightFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) (GHatOutcome params) :=
  fun x => rightPlacedSubMeasurement ((gHatIndexedMeasurement params family x).toSubMeasurement)

/-- Concrete family for the pairwise product `\widehat G^x_g \widehat G^y_h`. -/
def gHatPairProductLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) :=
  fun q =>
    leftPlacedSubMeasurement <|
      orderedProductSubMeasurement
        s!"ghat.pair.left({params.m},{params.q},{params.d})"
        ((gHatIndexedMeasurement params family q.1).toSubMeasurement)
        ((gHatIndexedMeasurement params family q.2).toSubMeasurement)

/-- Concrete family for the reversed pairwise product `\widehat G^y_h \widehat G^x_g`. -/
def gHatPairProductRight (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) :=
  fun q =>
    leftPlacedSubMeasurement <|
      reversedProductSubMeasurement
        s!"ghat.pair.right({params.m},{params.q},{params.d})"
        ((gHatIndexedMeasurement params family q.1).toSubMeasurement)
        ((gHatIndexedMeasurement params family q.2).toSubMeasurement)

/-- The ordered half-product `\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
def gHatHalfProductOutcomeOperator (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Operator
  | 0, _xs, _gs =>
      identityOperator s!"ghatHalf({params.m},{params.q},{params.d},0)"
  | k + 1, xs, gs =>
      operatorMul
        (((gHatIndexedMeasurement params family (xs 0)).toSubMeasurement).outcomeOperator (gs 0))
        (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs))

/-- The total half-product `\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
def gHatHalfProductTotalOperator (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    (k : ℕ) → PointTuple params k → Operator
  | 0, _xs =>
      identityOperator s!"ghatHalfTotal({params.m},{params.q},{params.d},0)"
  | k + 1, xs =>
      operatorMul
        (((gHatIndexedMeasurement params family (xs 0)).toSubMeasurement).totalOperator)
        (gHatHalfProductTotalOperator params family k (pointTupleTail xs))

/-- The cyclically rotated half-product `\widehat G^{x_2}_{g_2} \cdots \widehat G^{x_k}_{g_k} \widehat G^{x_1}_{g_1}`. -/
def gHatRotatedHalfProductOutcomeOperator (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Operator
  | 0, _xs, _gs =>
      identityOperator s!"ghatHalfRot({params.m},{params.q},{params.d},0)"
  | k + 1, xs, gs =>
      operatorMul
        (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs))
        (((gHatIndexedMeasurement params family (xs 0)).toSubMeasurement).outcomeOperator (gs 0))

/-- The total cyclically rotated half-product. -/
def gHatRotatedHalfProductTotalOperator (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    (k : ℕ) → PointTuple params k → Operator
  | 0, _xs =>
      identityOperator s!"ghatHalfRotTotal({params.m},{params.q},{params.d},0)"
  | k + 1, xs =>
      operatorMul
        (gHatHalfProductTotalOperator params family k (pointTupleTail xs))
        (((gHatIndexedMeasurement params family (xs 0)).toSubMeasurement).totalOperator)

/-- Concrete family for the full sandwich
`\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k} \cdots \widehat G^{x_1}_{g_1}`. -/
def gHatSandwichFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) (k : ℕ) :
    IndexedSubMeasurement (PointTuple params k) (GHatTupleOutcome params k) :=
  fun xs =>
    { name := s!"ghat.sandwich({params.m},{params.q},{params.d},{k})"
      outcomeOperator := fun gs =>
        let half := gHatHalfProductOutcomeOperator params family k xs gs
        operatorMul half (operatorAdjoint half)
      totalOperator :=
        let half := gHatHalfProductTotalOperator params family k xs
        operatorMul half (operatorAdjoint half) }

/-- Concrete family for the half-sandwich product of `k` completed slices. -/
def gHatHalfSandwichLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) (k : ℕ) :
    IndexedSubMeasurement (PointTuple params k) (GHatTupleOutcome params k) :=
  fun xs =>
    leftPlacedSubMeasurement <|
      { name := s!"ghat.half.left({params.m},{params.q},{params.d},{k})"
        outcomeOperator := fun gs => gHatHalfProductOutcomeOperator params family k xs gs
        totalOperator := gHatHalfProductTotalOperator params family k xs }

/-- Concrete family for the cyclically permuted half-sandwich product. -/
def gHatHalfSandwichRight (params : Parameters)
    (family : IndexedPolynomialFamily params) (k : ℕ) :
    IndexedSubMeasurement (PointTuple params k) (GHatTupleOutcome params k) :=
  fun xs =>
    leftPlacedSubMeasurement <|
      { name := s!"ghat.half.right({params.m},{params.q},{params.d},{k})"
        outcomeOperator := fun gs => gHatRotatedHalfProductOutcomeOperator params family k xs gs
        totalOperator := gHatRotatedHalfProductTotalOperator params family k xs }

/-- TODO: this should carry the paper's operator-polynomial `S_{\tau_{\ge \ell}}` construction from `lem:from-H-to-G`. -/
def suffixBernoulliWeightOperator (params : Parameters)
    (_family : IndexedPolynomialFamily params) (k ℓ : ℕ) (_τ : GHatType k) : Operator :=
  { name := s!"S_tau>=({params.m},{params.q},{params.d},{k},{ℓ})" }

/-- The default type used when packaging the recurrence step at the statement level. -/
def emptyGHatType (k : ℕ) : GHatType k :=
  fun _ => false

/-- Placeholder family for the interpolated operator `H^{x_1,\dots,x_k}_h`. -/
def pastedInterpolationFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) (k : ℕ) :
    IndexedSubMeasurement (PointTuple params k) (Polynomial params.next) :=
  fun xs =>
    postprocess (gHatSandwichFamily params family k xs)
      (interpolateCompletedSlices params k xs)

/-- The averaged sandwiched family before interpolation. -/
def averagedSandwichSubMeasurement (params : Parameters)
    (family : IndexedPolynomialFamily params) (k : ℕ) :
    SubMeasurement (GHatTupleOutcome params k) :=
  averageIndexedSubMeasurement
    s!"ghat.sandwich.avg({params.m},{params.q},{params.d},{k})"
    (distinctTupleDistribution params k)
    (gHatSandwichFamily params family k)

/-- The specific pasted submeasurement constructed from the sandwich/interpolation scheme. -/
def constructedPastedSubMeasurement (params : Parameters)
    (family : IndexedPolynomialFamily params) (k : ℕ) : SubMeasurement (Polynomial params.next) :=
  averageIndexedSubMeasurement
    s!"Hpasted({params.m},{params.q},{params.d},{k})"
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
def constructedPastedMeasurement (params : Parameters)
    (family : IndexedPolynomialFamily params) (k : ℕ) : Measurement (Polynomial params.next) where
  toSubMeasurement :=
    let H := constructedPastedSubMeasurement params family k
    let h₀ := pastedFallbackOutcome params
    let completionMass := operatorComplement H.totalOperator
    { name := s!"{H.name}.completion"
      outcomeOperator := fun h => by
        classical
        exact if h = h₀ then
          operatorAdd (H.outcomeOperator h) completionMass
        else
          H.outcomeOperator h
      totalOperator := identityLike H.totalOperator }

/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
def verticalLineMeasurementFamily (params : Parameters)
    (strategy : SymmetricStrategy params.next) :
    IndexedSubMeasurement (VerticalLineQuestion params) (AxisLinePolynomial params.next) :=
  fun u =>
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    (strategy.axisParallelMeasurement ℓ).toSubMeasurement

/-- Explicit value extracted from the `i`-th completed slice outcome at the test point. -/
def ldSandwichLineOnePointLeftFamily (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (k i : ℕ) : IndexedSubMeasurement (SandwichedLineQuestion params k) (Option (Fq params)) :=
  fun q =>
    postprocess (gHatSandwichFamily params family k q.2) (fun gs =>
      if h : i < k then
        Option.map (fun g => g q.1) (gs ⟨i, h⟩)
      else
        none)

/-- Explicit value extracted from the vertical line measurement `B^u` at the slice height `x_i`. -/
def ldSandwichLineOnePointRightFamily (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (_family : IndexedPolynomialFamily params)
    (k i : ℕ) : IndexedSubMeasurement (SandwichedLineQuestion params k) (Option (Fq params)) :=
  fun q =>
    postprocess (verticalLineMeasurementFamily params strategy q.1) (fun f =>
      if h : i < k then
        some (f (q.2 ⟨i, h⟩))
      else
        none)

/-- Restrict a global polynomial-valued submeasurement to the vertical line through `u`. -/
def hRestrictionToVerticalLine (params : Parameters)
    (H : SubMeasurement (Polynomial params.next)) :
    IndexedSubMeasurement (VerticalLineQuestion params) (AxisLinePolynomial params.next) :=
  fun u =>
    let verticalLine : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := ⟨params.m, Nat.lt_succ_self params.m⟩ }
    postprocess H (fun h => Polynomial.restrictToAxisParallelLine params.next h verticalLine)

/-- Collapse a submeasurement to its `Unit`-valued total operator. -/
def pastedMeasurementTotal {α : Type*} (H : SubMeasurement α) : IndexedSubMeasurement Unit Unit :=
  constantSubMeasurementFamily (postprocess H (fun _ => ()))

/-- The total operator of the specifically constructed pasted submeasurement. -/
def constructedPastedMeasurementTotal (params : Parameters)
    (family : IndexedPolynomialFamily params) (k : ℕ) :
    IndexedSubMeasurement Unit Unit :=
  pastedMeasurementTotal (constructedPastedSubMeasurement params family k)

/-- The expansion over all outcome types `τ`, written as the total mass of the averaged sandwich family. -/
def allOutcomesExpansionFamily (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params) (k : ℕ) :
    IndexedSubMeasurement Unit Unit :=
  pastedMeasurementTotal (averagedSandwichSubMeasurement params family k)

/-- The Bernoulli-tail polynomial in the averaged complete operator `G = E_x \sum_g G^x_g`. -/
def bernoulliTailFromFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) (k : ℕ) :
    IndexedSubMeasurement Unit Unit :=
  constantSubMeasurementFamily <|
    bernoulliTailSubMeasurement k params.d
      ((IndexedPolynomialFamily.averagedSubMeasurement family).totalOperator)

/-- One recurrence-step left-hand family from the proof of `lem:from-H-to-G`. -/
def fromHToGRecurrenceLeftFamily (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params) (k ℓ : ℕ) :
    IndexedSubMeasurement Unit Unit :=
  fun _ =>
    let base := allOutcomesExpansionFamily params strategy family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { name := s!"fromHToG.left({params.m},{params.q},{params.d},{k},{ℓ})"
      outcomeOperator := fun _ => operatorMul base.totalOperator weight
      totalOperator := operatorMul base.totalOperator weight }

/-- One recurrence-step right-hand family from the proof of `lem:from-H-to-G`. -/
def fromHToGRecurrenceRightFamily (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params) (k ℓ : ℕ) :
    IndexedSubMeasurement Unit Unit :=
  fun _ =>
    let base := bernoulliTailFromFamily params family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { name := s!"fromHToG.right({params.m},{params.q},{params.d},{k},{ℓ})"
      outcomeOperator := fun _ => operatorMul base.totalOperator weight
      totalOperator := operatorMul base.totalOperator weight }


end

end MIPStarRE.LDT.Pasting
