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

noncomputable section

/-- Left tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyLeft {Outcome : Type*} (params : Parameters)
    (M : IdxProjSubMeas (Fq params) Outcome d) :
    IdxSubMeas (SliceQuestion params) Outcome d :=
  fun x => leftPlacedSubMeas ((M x).toSubMeas)

/-- Right tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyRight {Outcome : Type*} (params : Parameters)
    (M : IdxProjSubMeas (Fq params) Outcome d) :
    IdxSubMeas (SliceQuestion params) Outcome d :=
  fun x => rightPlacedSubMeas ((M x).toSubMeas)

/-- Concrete hypothesis family for `G^x_g M^y_o`. -/
def switcherooPointProductLeft {Outcome : Type*} (params : Parameters)
    (family : IdxPolyFamily params d)
    (M : IdxProjSubMeas (Fq params) Outcome d) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params × Outcome) d :=
  fun q =>
    leftPlacedSubMeas <|
      orderedProductSubMeas
        s!"switcheroo.point.left({params.m},{params.q},{params.d})"
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete hypothesis family for `M^y_o G^x_g` on the `Polynomial params × Outcome` outcome type. -/
def switcherooPointProductRight {Outcome : Type*} (params : Parameters)
    (family : IdxPolyFamily params d)
    (M : IdxProjSubMeas (Fq params) Outcome d) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params × Outcome) d :=
  fun q =>
    leftPlacedSubMeas <|
      reversedProductSubMeas
        s!"switcheroo.point.right({params.m},{params.q},{params.d})"
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `G^x M^y_o`. -/
def switcherooAggregateLeft {Outcome : Type*} (params : Parameters)
    (family : IdxPolyFamily params d)
    (M : IdxProjSubMeas (Fq params) Outcome d) :
    IdxSubMeas (SlicePairQuestion params) Outcome d :=
  fun q =>
    leftPlacedSubMeas <|
      multiplyByTotalOnLeft
        s!"switcheroo.aggregate.left({params.m},{params.q},{params.d})"
        (completePartSubMeas params family q.1)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `M^y_o G^x`. -/
def switcherooAggregateRight {Outcome : Type*} (params : Parameters)
    (family : IdxPolyFamily params d)
    (M : IdxProjSubMeas (Fq params) Outcome d) :
    IdxSubMeas (SlicePairQuestion params) Outcome d :=
  fun q =>
    leftPlacedSubMeas <|
      multiplyByTotalOnRight
        s!"switcheroo.aggregate.right({params.m},{params.q},{params.d})"
        ((M q.2).toSubMeas)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y`. -/
def completePartPointProductLeft (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params) d :=
  fun q =>
    leftPlacedSubMeas <|
      multiplyByTotalOnRight
        s!"complete.point.left({params.m},{params.q},{params.d})"
        ((family.meas q.1).toSubMeas)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x_g`. -/
def completePartPointProductRight (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params) d :=
  fun q =>
    leftPlacedSubMeas <|
      multiplyByTotalOnLeft
        s!"complete.point.right({params.m},{params.q},{params.d})"
        (completePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x G^y`. -/
def completePartTotalProductLeft (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SlicePairQuestion params) Unit d :=
  fun q =>
    leftPlacedSubMeas <|
      multiplyByTotalOnRight
        s!"complete.total.left({params.m},{params.q},{params.d})"
        (completePartSubMeas params family q.1)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x`. -/
def completePartTotalProductRight (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SlicePairQuestion params) Unit d :=
  fun q =>
    leftPlacedSubMeas <|
      multiplyByTotalOnLeft
        s!"complete.total.right({params.m},{params.q},{params.d})"
        (completePartSubMeas params family q.2)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y_⊥`. -/
def incompletePartPointProductLeft (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params) d :=
  fun q =>
    leftPlacedSubMeas <|
      multiplyByTotalOnRight
        s!"incomplete.point.left({params.m},{params.q},{params.d})"
        ((family.meas q.1).toSubMeas)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_g`. -/
def incompletePartPointProductRight (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SlicePairQuestion params) (Polynomial params) d :=
  fun q =>
    leftPlacedSubMeas <|
      multiplyByTotalOnLeft
        s!"incomplete.point.right({params.m},{params.q},{params.d})"
        (incompletePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x_⊥ G^y_⊥`. -/
def incompletePartTotalProductLeft (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SlicePairQuestion params) Unit d :=
  fun q =>
    leftPlacedSubMeas <|
      multiplyByTotalOnRight
        s!"incomplete.total.left({params.m},{params.q},{params.d})"
        (incompletePartSubMeas params family q.1)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_⊥`. -/
def incompletePartTotalProductRight (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SlicePairQuestion params) Unit d :=
  fun q =>
    leftPlacedSubMeas <|
      multiplyByTotalOnLeft
        s!"incomplete.total.right({params.m},{params.q},{params.d})"
        (incompletePartSubMeas params family q.2)
        (incompletePartSubMeas params family q.1)

/-- Left tensor-placement for `\widehat G^x_g`. -/
def gHatSelfConsistencyLeftFamily (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) d :=
  fun x => leftPlacedSubMeas ((gHatIdxMeas params family x).toSubMeas)

/-- Right tensor-placement for `\widehat G^x_g`. -/
def gHatSelfConsistencyRightFamily (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) d :=
  fun x => rightPlacedSubMeas ((gHatIdxMeas params family x).toSubMeas)

/-- Concrete family for the pairwise product `\widehat G^x_g \widehat G^y_h`. -/
def gHatPairProductLeft (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) d :=
  fun q =>
    leftPlacedSubMeas <|
      orderedProductSubMeas
        s!"ghat.pair.left({params.m},{params.q},{params.d})"
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- Concrete family for the reversed pairwise product `\widehat G^y_h \widehat G^x_g`. -/
def gHatPairProductRight (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) d :=
  fun q =>
    leftPlacedSubMeas <|
      reversedProductSubMeas
        s!"ghat.pair.right({params.m},{params.q},{params.d})"
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- The ordered half-product `\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
def gHatHalfProductOutcomeOperator (params : Parameters)
    (family : IdxPolyFamily params d) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Operator d
  | 0, _xs, _gs =>
      idOp s!"ghatHalf({params.m},{params.q},{params.d},0)"
  | k + 1, xs, gs =>
      opMul
        (((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0))
        (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs))

/-- The total half-product `\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
def gHatHalfProductTotalOperator (params : Parameters)
    (family : IdxPolyFamily params d) :
    (k : ℕ) → PointTuple params k → Operator d
  | 0, _xs =>
      idOp s!"ghatHalfTotal({params.m},{params.q},{params.d},0)"
  | k + 1, xs =>
      opMul
        (((gHatIdxMeas params family (xs 0)).toSubMeas).total)
        (gHatHalfProductTotalOperator params family k (pointTupleTail xs))

/-- The cyclically rotated half-product `\widehat G^{x_2}_{g_2} \cdots \widehat G^{x_k}_{g_k} \widehat G^{x_1}_{g_1}`. -/
def gHatRotatedHalfProductOutcomeOperator (params : Parameters)
    (family : IdxPolyFamily params d) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Operator d
  | 0, _xs, _gs =>
      idOp s!"ghatHalfRot({params.m},{params.q},{params.d},0)"
  | k + 1, xs, gs =>
      opMul
        (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs))
        (((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0))

/-- The total cyclically rotated half-product. -/
def gHatRotatedHalfProductTotalOperator (params : Parameters)
    (family : IdxPolyFamily params d) :
    (k : ℕ) → PointTuple params k → Operator d
  | 0, _xs =>
      idOp s!"ghatHalfRotTotal({params.m},{params.q},{params.d},0)"
  | k + 1, xs =>
      opMul
        (gHatHalfProductTotalOperator params family k (pointTupleTail xs))
        (((gHatIdxMeas params family (xs 0)).toSubMeas).total)

/-- Concrete family for the full sandwich
`\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k} \cdots \widehat G^{x_1}_{g_1}`. -/
def gHatSandwichFamily (params : Parameters)
    (family : IdxPolyFamily params d) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) d :=
  fun xs =>
    { name := s!"ghat.sandwich({params.m},{params.q},{params.d},{k})"
      outcome := fun gs =>
        let half := gHatHalfProductOutcomeOperator params family k xs gs
        opMul half (opAdj half)
      total :=
        let half := gHatHalfProductTotalOperator params family k xs
        opMul half (opAdj half) }

/-- Concrete family for the half-sandwich product of `k` completed slices. -/
def gHatHalfSandwichLeft (params : Parameters)
    (family : IdxPolyFamily params d) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) d :=
  fun xs =>
    leftPlacedSubMeas <|
      { name := s!"ghat.half.left({params.m},{params.q},{params.d},{k})"
        outcome := fun gs => gHatHalfProductOutcomeOperator params family k xs gs
        total := gHatHalfProductTotalOperator params family k xs }

/-- Concrete family for the cyclically permuted half-sandwich product. -/
def gHatHalfSandwichRight (params : Parameters)
    (family : IdxPolyFamily params d) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) d :=
  fun xs =>
    leftPlacedSubMeas <|
      { name := s!"ghat.half.right({params.m},{params.q},{params.d},{k})"
        outcome := fun gs => gHatRotatedHalfProductOutcomeOperator params family k xs gs
        total := gHatRotatedHalfProductTotalOperator params family k xs }

/-- TODO: this should carry the paper's operator-polynomial `S_{\tau_{\ge \ell}}` construction from `lem:from-H-to-G`. -/
def suffixBernoulliWeightOperator (params : Parameters)
    (_family : IdxPolyFamily params d) (k ℓ : ℕ) (_τ : GHatType k) : Operator d :=
  { name := s!"S_tau>=({params.m},{params.q},{params.d},{k},{ℓ})" }

/-- The default type used when packaging the recurrence step at the statement level. -/
def emptyGHatType (k : ℕ) : GHatType k :=
  fun _ => false

/-- Placeholder family for the interpolated operator `H^{x_1,\dots,x_k}_h`. -/
def pastedInterpolationFamily (params : Parameters)
    (family : IdxPolyFamily params d) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (Polynomial params.next) d :=
  fun xs =>
    postprocess (gHatSandwichFamily params family k xs)
      (interpolateCompletedSlices params k xs)

/-- The averaged sandwiched family before interpolation. -/
def averagedSandwichSubMeas (params : Parameters)
    (family : IdxPolyFamily params d) (k : ℕ) :
    SubMeas (GHatTupleOutcome params k) d :=
  averageIdxSubMeas
    s!"ghat.sandwich.avg({params.m},{params.q},{params.d},{k})"
    (distinctTupleDistribution params k)
    (gHatSandwichFamily params family k)

/-- The specific pasted submeasurement constructed from the sandwich/interpolation scheme. -/
def constructedPastedSubMeas (params : Parameters)
    (family : IdxPolyFamily params d) (k : ℕ) : SubMeas (Polynomial params.next) d :=
  averageIdxSubMeas
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
    (family : IdxPolyFamily params d) (k : ℕ) : Measurement (Polynomial params.next) d where
  toSubMeas :=
    let H := constructedPastedSubMeas params family k
    let h₀ := pastedFallbackOutcome params
    let completionMass := operatorComplement H.total
    { name := s!"{H.name}.completion"
      outcome := fun h => by
        classical
        exact if h = h₀ then
          opAdd (H.outcome h) completionMass
        else
          H.outcome h
      total := identityLike H.total }

/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
def verticalLineMeasurementFamily (params : Parameters)
    (strategy : SymStrat params.next d) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) d :=
  fun u =>
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    (strategy.axisParallelMeasurement ℓ).toSubMeas

/-- Explicit value extracted from the `i`-th completed slice outcome at the test point. -/
def ldSandwichLineOnePointLeftFamily (params : Parameters)
    (_strategy : SymStrat params.next d)
    (family : IdxPolyFamily params d)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) d :=
  fun q =>
    postprocess (gHatSandwichFamily params family k q.2) (fun gs =>
      if h : i < k then
        Option.map (fun g => g q.1) (gs ⟨i, h⟩)
      else
        none)

/-- Explicit value extracted from the vertical line measurement `B^u` at the slice height `x_i`. -/
def ldSandwichLineOnePointRightFamily (params : Parameters)
    (strategy : SymStrat params.next d)
    (_family : IdxPolyFamily params d)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) d :=
  fun q =>
    postprocess (verticalLineMeasurementFamily params strategy q.1) (fun f =>
      if h : i < k then
        some (f (q.2 ⟨i, h⟩))
      else
        none)

/-- Restrict a global polynomial-valued submeasurement to the vertical line through `u`. -/
def hRestrictionToVerticalLine (params : Parameters)
    (H : SubMeas (Polynomial params.next) d) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) d :=
  fun u =>
    let verticalLine : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := ⟨params.m, Nat.lt_succ_self params.m⟩ }
    postprocess H (fun h => Polynomial.restrictToAxisParallelLine params.next h verticalLine)

/-- Collapse a submeasurement to its `Unit`-valued total operator. -/
def pastedMeasurementTotal {α : Type*} {d : ℕ} [Fintype α]
    (H : SubMeas α d) : IdxSubMeas Unit Unit d :=
  constSubMeasFamily (postprocess H (fun _ => ()))

/-- The total operator of the specifically constructed pasted submeasurement. -/
def constructedPastedMeasurementTotal (params : Parameters)
    (family : IdxPolyFamily params d) (k : ℕ) :
    IdxSubMeas Unit Unit d :=
  pastedMeasurementTotal (constructedPastedSubMeas params family k)

/-- The expansion over all outcome types `τ`, written as the total mass of the averaged sandwich family. -/
def allOutcomesExpansionFamily (params : Parameters)
    (_strategy : SymStrat params.next d)
    (family : IdxPolyFamily params d) (k : ℕ) :
    IdxSubMeas Unit Unit d :=
  pastedMeasurementTotal (averagedSandwichSubMeas params family k)

/-- The Bernoulli-tail polynomial in the averaged complete operator `G = E_x \sum_g G^x_g`. -/
def bernoulliTailFromFamily (params : Parameters)
    (family : IdxPolyFamily params d) (k : ℕ) :
    IdxSubMeas Unit Unit d :=
  constSubMeasFamily <|
    bernoulliTailSubMeas k params.d
      ((IdxPolyFamily.averagedSubMeas family).total)

/-- One recurrence-step left-hand family from the proof of `lem:from-H-to-G`. -/
def fromHToGRecurrenceLeftFamily (params : Parameters)
    (strategy : SymStrat params.next d)
    (family : IdxPolyFamily params d) (k ℓ : ℕ) :
    IdxSubMeas Unit Unit d :=
  fun _ =>
    let base := allOutcomesExpansionFamily params strategy family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { name := s!"fromHToG.left({params.m},{params.q},{params.d},{k},{ℓ})"
      outcome := fun _ => opMul base.total weight
      total := opMul base.total weight }

/-- One recurrence-step right-hand family from the proof of `lem:from-H-to-G`. -/
def fromHToGRecurrenceRightFamily (params : Parameters)
    (_strategy : SymStrat params.next d)
    (family : IdxPolyFamily params d) (k ℓ : ℕ) :
    IdxSubMeas Unit Unit d :=
  fun _ =>
    let base := bernoulliTailFromFamily params family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { name := s!"fromHToG.right({params.m},{params.q},{params.d},{k},{ℓ})"
      outcome := fun _ => opMul base.total weight
      total := opMul base.total weight }


end

end MIPStarRE.LDT.Pasting
