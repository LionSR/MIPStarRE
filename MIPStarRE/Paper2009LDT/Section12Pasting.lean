import MIPStarRE.Paper2009LDT.Section11Commutativity

/-!
Matching scaffold for Section 12 of the low individual degree paper in
`references/ldt-paper/ld-pasting.tex`.

This file still uses paper-local placeholders, but the main interfaces now name the
relevant complete/incomplete parts of the slice family, the completed family
`\widehat G`, the sandwich constructions, and the displayed error formulas that drive
later pasting arguments.
-/

namespace MIPStarRE.Paper2009LDT.Section12Pasting

open MIPStarRE.Paper2009LDT
open MIPStarRE.Paper2009LDT.Section7ExpansionHypercubeGraph
open MIPStarRE.Paper2009LDT.Section10CommutativityPoints

/-- The set of `k`-tuples with distinct coordinates. -/
def distinctTuples (params : Parameters) (k : ℕ) : Set (PointTuple params k) :=
  { xs | Function.Injective xs }

/-- Placeholder distribution on distinct tuples. -/
def distinctTupleDistribution (params : Parameters) (k : ℕ) :
    Distribution (PointTuple params k) where
  name := s!"Distinct({params.q},{k})"

/-- Placeholder outcome type for the completed family `\widehat G`. -/
abbrev GHatOutcome (params : Parameters) := Option (Polynomial params)
abbrev SliceQuestion (params : Parameters) := Fq params
abbrev SlicePairQuestion (params : Parameters) := Fq params × Fq params
abbrev GHatTupleOutcome (params : Parameters) (k : ℕ) := Fin k → GHatOutcome params
abbrev GHatType (k : ℕ) := Fin k → Bool
abbrev SandwichedLineQuestion (params : Parameters) (k : ℕ) := Point params × PointTuple params k
abbrev VerticalLineQuestion (params : Parameters) := Point params

/-- Placeholder matrix-valued Bernoulli tail operator from `lem:chernoff-bernoulli-matrix`. -/
def bernoulliTailOperator (k d : ℕ) (X : Operator) : Operator :=
  { name := s!"BernoulliTail(k={k},d={d}; {X.name}^r (I-{X.name})^(k-r))" }

/-- Add a descriptive tag to a paper-local submeasurement placeholder. -/
def tagSubMeasurement {α : Type _} (tag : String) (A : SubMeasurement α) : SubMeasurement α where
  name := s!"{A.name}.{tag}"
  outcomeOperator := A.outcomeOperator
  totalOperator := A.totalOperator

/-- Multiply each outcome operator by a total operator on the right. -/
def multiplyByTotalOnRight {α β : Type _}
    (label : String) (A : SubMeasurement α) (B : SubMeasurement β) :
    SubMeasurement α where
  name := label
  outcomeOperator := fun a => formalProduct (A.outcomeOperator a) B.totalOperator
  totalOperator := formalProduct A.totalOperator B.totalOperator

/-- Multiply each outcome operator by a total operator on the left. -/
def multiplyByTotalOnLeft {α β : Type _}
    (label : String) (A : SubMeasurement α) (B : SubMeasurement β) :
    SubMeasurement β where
  name := label
  outcomeOperator := fun b => formalProduct A.totalOperator (B.outcomeOperator b)
  totalOperator := formalProduct A.totalOperator B.totalOperator

/-- Average an indexed family against a named distribution. -/
def averageIndexedSubMeasurement {Question Outcome : Type _}
    (label : String) (_𝒟 : Distribution Question) (_A : IndexedSubMeasurement Question Outcome) :
    SubMeasurement Outcome where
  name := label
  outcomeOperator := fun _ => { name := s!"{label}.avg.outcome" }
  totalOperator := { name := s!"{label}.avg.total" }

/-- Placeholder complement operator `I - X`. -/
def operatorComplement (X : Operator) : Operator :=
  { name := s!"I - {X.name}" }

/-- Regard an operator expression as a `Unit`-valued submeasurement placeholder. -/
def operatorAsSubMeasurement (X : Operator) : SubMeasurement Unit :=
  { name := s!"operator({X.name})"
    outcomeOperator := fun _ => X
    totalOperator := X }

/-- Regard the Bernoulli tail operator as a `Unit`-valued submeasurement placeholder. -/
def bernoulliTailSubMeasurement (k d : ℕ) (X : Operator) : SubMeasurement Unit :=
  operatorAsSubMeasurement (bernoulliTailOperator k d X)

/-- Record which completed-slice outcomes are genuine polynomial outcomes. -/
def gHatTupleType {params : Parameters} {k : ℕ}
    (gs : GHatTupleOutcome params k) : GHatType k :=
  fun i => Option.isSome (gs i)

/-- Remove the first coordinate from a tuple of slice questions. -/
def pointTupleTail {params : Parameters} {k : ℕ}
    (xs : PointTuple params (k + 1)) : PointTuple params k :=
  fun i => xs i.succ

/-- Remove the first coordinate from a tuple of completed slice outcomes. -/
def gHatTupleOutcomeTail {params : Parameters} {k : ℕ}
    (gs : GHatTupleOutcome params (k + 1)) : GHatTupleOutcome params k :=
  fun i => gs i.succ

/-- Fallback global polynomial used when all completed slice outcomes are `⊥`. -/
noncomputable def fallbackInterpolatedPolynomial (params : Parameters) : Polynomial params.next where
  poly := MvPolynomial.X ⟨params.m, Nat.lt_succ_self params.m⟩
  lowIndividualDegree := by
    intro i
    sorry

/-- Placeholder interpolation from completed slice outcomes to a global polynomial. -/
noncomputable def interpolateCompletedSlices (params : Parameters) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Polynomial params.next
  | 0, _xs, _gs => fallbackInterpolatedPolynomial params
  | k + 1, xs, gs =>
      match gs 0 with
      | some g => Polynomial.appendAtHeight params g (xs 0)
      | none => interpolateCompletedSlices params k (pointTupleTail xs) (gHatTupleOutcomeTail gs)

/-- Aggregate the polynomial outcomes of `G^x` into its complete part `G^x`. -/
def completePartSubMeasurement (params : Parameters)
    (family : IndexedPolynomialFamily params) (x : Fq params) : SubMeasurement Unit :=
  tagSubMeasurement "complete"
    (postprocess ((family.meas x).toSubMeasurement) (fun _ => ()))

/-- Placeholder for the incomplete part `G^x_⊥ = I - G^x`. -/
def incompletePartSubMeasurement (params : Parameters)
    (family : IndexedPolynomialFamily params) (x : Fq params) : SubMeasurement Unit :=
  operatorAsSubMeasurement (operatorComplement (completePartSubMeasurement params family x).totalOperator)

/-- Complete each projective slice submeasurement by adjoining the failure outcome. -/
def gHatIndexedMeasurement (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedMeasurement (Fq params) (GHatOutcome params) :=
  fun x => completeSubMeasurement ((family.meas x).toSubMeasurement)

/-- The submeasurement view of the completed family `\widehat G`. -/
def gHatIndexedSubMeasurement (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (Fq params) (GHatOutcome params) :=
  IndexedMeasurement.toIndexedSubMeasurement (gHatIndexedMeasurement params family)

/-- Left tensor-placement for the complete part `G^x`. -/
def completePartLeftFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) Unit :=
  fun x => leftPlacedSubMeasurement (completePartSubMeasurement params family x)

/-- Right tensor-placement for the complete part `G^x`. -/
def completePartRightFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) Unit :=
  fun x => rightPlacedSubMeasurement (completePartSubMeasurement params family x)

/-- Left tensor-placement for the incomplete part `G^x_⊥`. -/
def incompletePartLeftFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) Unit :=
  fun x => leftPlacedSubMeasurement (incompletePartSubMeasurement params family x)

/-- Right tensor-placement for the incomplete part `G^x_⊥`. -/
def incompletePartRightFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) Unit :=
  fun x => rightPlacedSubMeasurement (incompletePartSubMeasurement params family x)

/-- Left tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyLeft {Outcome : Type _} (params : Parameters)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SliceQuestion params) Outcome :=
  fun x => leftPlacedSubMeasurement ((M x).toSubMeasurement)

/-- Right tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyRight {Outcome : Type _} (params : Parameters)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SliceQuestion params) Outcome :=
  fun x => rightPlacedSubMeasurement ((M x).toSubMeasurement)

/-- Concrete hypothesis family for `G^x_g M^y_o`. -/
def switcherooPointProductLeft {Outcome : Type _} (params : Parameters)
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
def switcherooPointProductRight {Outcome : Type _} (params : Parameters)
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
def switcherooAggregateLeft {Outcome : Type _} (params : Parameters)
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
def switcherooAggregateRight {Outcome : Type _} (params : Parameters)
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
      Section7ExpansionHypercubeGraph.identityOperator s!"ghatHalf({params.m},{params.q},{params.d},0)"
  | k + 1, xs, gs =>
      formalProduct
        (((gHatIndexedMeasurement params family (xs 0)).toSubMeasurement).outcomeOperator (gs 0))
        (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs))

/-- The total half-product `\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
def gHatHalfProductTotalOperator (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    (k : ℕ) → PointTuple params k → Operator
  | 0, _xs =>
      Section7ExpansionHypercubeGraph.identityOperator s!"ghatHalfTotal({params.m},{params.q},{params.d},0)"
  | k + 1, xs =>
      formalProduct
        (((gHatIndexedMeasurement params family (xs 0)).toSubMeasurement).totalOperator)
        (gHatHalfProductTotalOperator params family k (pointTupleTail xs))

/-- The cyclically rotated half-product `\widehat G^{x_2}_{g_2} \cdots \widehat G^{x_k}_{g_k} \widehat G^{x_1}_{g_1}`. -/
def gHatRotatedHalfProductOutcomeOperator (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Operator
  | 0, _xs, _gs =>
      Section7ExpansionHypercubeGraph.identityOperator s!"ghatHalfRot({params.m},{params.q},{params.d},0)"
  | k + 1, xs, gs =>
      formalProduct
        (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs))
        (((gHatIndexedMeasurement params family (xs 0)).toSubMeasurement).outcomeOperator (gs 0))

/-- The total cyclically rotated half-product. -/
def gHatRotatedHalfProductTotalOperator (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    (k : ℕ) → PointTuple params k → Operator
  | 0, _xs =>
      Section7ExpansionHypercubeGraph.identityOperator s!"ghatHalfRotTotal({params.m},{params.q},{params.d},0)"
  | k + 1, xs =>
      formalProduct
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
        formalProduct half (formalAdjoint half)
      totalOperator :=
        let half := gHatHalfProductTotalOperator params family k xs
        formalProduct half (formalAdjoint half) }

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

/-- The type-dependent Bernoulli weight `S_{\tau_{\ge \ell}}` from `lem:from-H-to-G`. -/
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

/-- The specific pasted measurement obtained by completing the constructed pasted submeasurement. -/
def constructedPastedMeasurement (params : Parameters)
    (family : IndexedPolynomialFamily params) (k : ℕ) : Measurement (Polynomial params.next) where
  toSubMeasurement := {
    name := s!"{(constructedPastedSubMeasurement params family k).name}.completion"
    outcomeOperator := (constructedPastedSubMeasurement params family k).outcomeOperator
    totalOperator :=
      Section7ExpansionHypercubeGraph.identityOperator
        s!"{(constructedPastedSubMeasurement params family k).name}.completion" }

/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
def verticalLineMeasurementFamily (params : Parameters)
    (_strategy : SymmetricStrategy params.next) :
    IndexedSubMeasurement (VerticalLineQuestion params) (AxisLinePolynomial params.next) :=
  fun _ => { name := s!"verticalLine.B({params.m},{params.q},{params.d})" }

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
def pastedMeasurementTotal {α : Type _} (H : SubMeasurement α) : IndexedSubMeasurement Unit Unit :=
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
      outcomeOperator := fun _ => formalProduct base.totalOperator weight
      totalOperator := formalProduct base.totalOperator weight }

/-- One recurrence-step right-hand family from the proof of `lem:from-H-to-G`. -/
def fromHToGRecurrenceRightFamily (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params) (k ℓ : ℕ) :
    IndexedSubMeasurement Unit Unit :=
  fun _ =>
    let base := bernoulliTailFromFamily params family k ()
    let weight := suffixBernoulliWeightOperator params family k ℓ (emptyGHatType k)
    { name := s!"fromHToG.right({params.m},{params.q},{params.d},{k},{ℓ})"
      outcomeOperator := fun _ => formalProduct base.totalOperator weight
      totalOperator := formalProduct base.totalOperator weight }

/-- The final completeness lower bound used in the pasting statements. -/
noncomputable def ldPastingCompletenessLowerBound (params : Parameters)
    (kappa nu : Error) (k : ℕ) : Error :=
  1 - kappa * (1 + 1 / (100 * (params.m : Error))) - nu -
    Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))

/-- Displayed error term for `lem:commutativity-switcheroo`. -/
noncomputable def commutativitySwitcherooError
    (zeta omega chi : Error) : Error :=
  6 * Real.rpow zeta (1 / (2 : Error)) +
    6 * Real.rpow omega (1 / (2 : Error)) +
    4 * Real.rpow chi (1 / (2 : Error))

/-- Displayed error term for `cor:commuting-with-G-complete`. -/
noncomputable def commutingWithGCompleteError (params : Parameters)
    (gamma zeta : Error) : Error :=
  36 * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Displayed error term for `cor:commuting-with-G-incomplete`. -/
noncomputable def commutingWithGIncompleteError (params : Parameters)
    (gamma zeta : Error) : Error :=
  commutingWithGCompleteError params gamma zeta

/-- Displayed self-consistency error for `\widehat G`. -/
def gHatSelfConsistencyError (zeta : Error) : Error :=
  2 * zeta

/-- Displayed commutation error for `\widehat G`. -/
noncomputable def gHatCommutationError (params : Parameters)
    (gamma zeta : Error) : Error :=
  138 * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Displayed error term for commuting past `k` completed slices. -/
noncomputable def commuteGHalfSandwichError (params : Parameters)
    (gamma zeta : Error) (k : ℕ) : Error :=
  426 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Displayed error term for `lem:ld-sandwich-line-one-point`. -/
noncomputable def ldSandwichLineOnePointError (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) : Error :=
  43 * (k : Error) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- Displayed error term for `lem:h-b-consistency`. -/
noncomputable def hBConsistencyError (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) : Error :=
  44 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- Displayed error term for `lem:over-all-outcomes`. -/
noncomputable def overAllOutcomesError (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) : Error :=
  46 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- Displayed error term for `lem:from-H-to-G`. -/
noncomputable def fromHToGError (params : Parameters)
    (gamma zeta : Error) (k : ℕ) : Error :=
  46 * (k : Error) * (params.m : Error) *
    (Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- The per-step recurrence loss from the proof of `lem:from-H-to-G`. -/
noncomputable def fromHToGRecurrenceError (params : Parameters)
    (gamma zeta : Error) (k : ℕ) : Error :=
  2 * Real.rpow (2 * zeta) (1 / (2 : Error)) +
    2 * Real.rpow (commuteGHalfSandwichError params gamma zeta k) (1 / (2 : Error))

/-- Output package for `thm:ld-pasting`. -/
structure LdPastingConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (H : Measurement (Polynomial params.next))
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  constructedMeasurement :
    H = constructedPastedMeasurement params family k
  pointConsistency :
    ConsistentWithPolynomialEvaluation params.next strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      H.toSubMeasurement
      (Section6MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta)

/-- Output package for `lem:ld-pasting-sub-measurement`. -/
structure LdPastingSubMeasurementConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (H : SubMeasurement (Polynomial params.next))
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  constructedSubMeasurement :
    H = constructedPastedSubMeasurement params family k
  pointConsistency :
    ConsistentWithPolynomialEvaluation params.next strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      H
      (Section6MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta)
  completeness :
    CompletenessAtLeast strategy.state H
      (ldPastingCompletenessLowerBound params kappa
        (Section6MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta) k)

/-- Output package for `lem:g-complete-self-consistency`. -/
structure GCompleteSelfConsistencyStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params) (zeta : Error) : Prop where
  completePartSelfConsistency :
    StateDependentDistanceRel ψ
      (uniformDistribution (SliceQuestion params))
      (completePartLeftFamily params family)
      (completePartRightFamily params family)
      zeta

/-- Output package for `cor:g-bot-self-consistency`. -/
structure GBotSelfConsistencyStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params) (zeta : Error) : Prop where
  completePartWitness :
    GCompleteSelfConsistencyStatement params ψ family zeta
  incompletePartSelfConsistency :
    StateDependentDistanceRel ψ
      (uniformDistribution (SliceQuestion params))
      (incompletePartLeftFamily params family)
      (incompletePartRightFamily params family)
      zeta

/-- Output package for `lem:commutativity-switcheroo`. -/
structure CommutativitySwitcherooStatement {Outcome : Type _} (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome)
    (zeta omega chi : Error) : Prop where
  aggregateCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (switcherooAggregateLeft params family M)
      (switcherooAggregateRight params family M)
      (commutativitySwitcherooError zeta omega chi)

/-- Output package for `cor:commuting-with-G-complete`. -/
structure CommutingWithGCompleteStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) : Prop where
  pointWithCompletePartCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (completePartPointProductLeft params family)
      (completePartPointProductRight params family)
      (commutingWithGCompleteError params gamma zeta)
  completePartCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (completePartTotalProductLeft params family)
      (completePartTotalProductRight params family)
      (commutingWithGCompleteError params gamma zeta)

/-- Output package for `cor:commuting-with-G-incomplete`. -/
structure CommutingWithGIncompleteStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) : Prop where
  completePartWitness :
    CommutingWithGCompleteStatement params ψ family gamma zeta
  pointWithIncompletePartCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartPointProductLeft params family)
      (incompletePartPointProductRight params family)
      (commutingWithGIncompleteError params gamma zeta)
  incompletePartCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartTotalProductLeft params family)
      (incompletePartTotalProductRight params family)
      (commutingWithGIncompleteError params gamma zeta)

/-- Output package for `cor:G-hat-facts`. -/
structure GHatFactsStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) : Prop where
  completePartSelfConsistencyWitness :
    GCompleteSelfConsistencyStatement params ψ family zeta
  incompletePartSelfConsistencyWitness :
    GBotSelfConsistencyStatement params ψ family zeta
  completePartCommutationWitness :
    CommutingWithGCompleteStatement params ψ family gamma zeta
  incompletePartCommutationWitness :
    CommutingWithGIncompleteStatement params ψ family gamma zeta
  completedSelfConsistency :
    StateDependentDistanceRel ψ
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)
  completedCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)

/-- Output package for `lem:commute-g-half-sandwich`. -/
structure CommuteGHalfSandwichStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) (k : ℕ) : Prop where
  repeatedCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft params family k)
      (gHatHalfSandwichRight params family k)
      (commuteGHalfSandwichError params gamma zeta k)

/-- Output package for `lem:ld-sandwich-line-one-point`. -/
structure LdSandwichLineOnePointStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (eps delta gamma zeta : Error)
    (k i : ℕ) : Prop where
  linePointComparison :
    ConsistencyRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k)

/-- Output package for `lem:h-b-consistency`. -/
structure HBConsistencyStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  lineConsistency :
    ConsistencyRel strategy.state
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params (constructedPastedSubMeasurement params family k))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k)

/-- Output package for `lem:over-all-outcomes`. -/
structure OverAllOutcomesStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  totalOutcomeExpansion :
    StateDependentDistanceRel strategy.state (uniformDistribution Unit)
      (constructedPastedMeasurementTotal params family k)
      (allOutcomesExpansionFamily params strategy family k)
      (overAllOutcomesError params eps delta gamma zeta k)

/-- Output package for `lem:from-H-to-G`. -/
structure FromHToGStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) (k : ℕ) : Prop where
  recurrenceStep :
    ∀ ℓ : ℕ, ℓ < k →
      StateDependentDistanceRel strategy.state (uniformDistribution Unit)
        (fromHToGRecurrenceLeftFamily params strategy family k ℓ)
        (fromHToGRecurrenceRightFamily params strategy family k ℓ)
        (fromHToGRecurrenceError params gamma zeta k)
  bernoulliPolynomialRewrite :
    StateDependentDistanceRel strategy.state (uniformDistribution Unit)
      (allOutcomesExpansionFamily params strategy family k)
      (bernoulliTailFromFamily params family k)
      (fromHToGError params gamma zeta k)

/-- Output package for `lem:chernoff-bernoulli-matrix`. -/
structure ChernoffBernoulliMatrixStatement
    (ψ : QuantumState)
    (theta : Error) (k d : ℕ) (X : Operator) (kappa : Error) : Prop where
  matrixTailBound :
    CompletenessAtLeast ψ (bernoulliTailSubMeasurement k d X)
      (1 - kappa / (1 - theta) - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2))

/-- Output package for `cor:ld-pasting-N-completeness`. -/
structure LdPastingNCompletenessStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (kappa nu : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  completenessBound :
    CompletenessAtLeast strategy.state
      (constructedPastedSubMeasurement params family k)
      (ldPastingCompletenessLowerBound params kappa nu k)

/-- `thm:ld-pasting`. -/
theorem ldPasting
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next),
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  sorry

/-- `lem:ld-pasting-sub-measurement`. -/
lemma ldPastingSubMeasurement
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeasurement (Polynomial params.next),
      LdPastingSubMeasurementConclusion params strategy family H eps delta gamma kappa zeta k := by
  sorry

/-- `prop:ld-dnoteq`. -/
theorem ldDnoteq
    (params : Parameters) (k : ℕ) :
    totalVariationDistance (uniformDistribution (PointTuple params k))
        (distinctTupleDistribution params k)
      ≤ ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  sorry

/-- `lem:looks-easy-but-took-me-a-while`. -/
lemma looksEasyButTookMeAWhile
    (lambda : Error) (d : ℕ)
    (h0 : 0 ≤ lambda) (h1 : lambda ≤ 1) :
    lambda * (1 - lambda ^ d)
      ≤ 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) (1 / ((d + 1 : ℕ) : Error)) := by
  sorry

/-- `lem:g-complete-self-consistency`. -/
lemma gCompleteSelfConsistency
    (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (zeta : Error)
    (hself : family.StronglySelfConsistent ψ zeta) :
    GCompleteSelfConsistencyStatement params ψ family zeta := by
  sorry

/-- `cor:g-bot-self-consistency`. -/
theorem gBotSelfConsistency
    (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (zeta : Error)
    (hcomplete : GCompleteSelfConsistencyStatement params ψ family zeta) :
    GBotSelfConsistencyStatement params ψ family zeta := by
  sorry

/-- `lem:commutativity-switcheroo`. -/
lemma commutativitySwitcheroo {Outcome : Type _}
    (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome)
    (zeta omega chi : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψ family zeta)
    (hselfM : StateDependentDistanceRel ψ
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega)
    (hcomm : StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    CommutativitySwitcherooStatement params ψ family M zeta omega chi := by
  sorry

/-- `cor:commuting-with-G-complete`. -/
theorem commutingWithGComplete
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error)
    (hcom : Section11Commutativity.ComMainConclusion params strategy family gamma zeta)
    (hself : GCompleteSelfConsistencyStatement params strategy.state family zeta) :
    CommutingWithGCompleteStatement params strategy.state family gamma zeta := by
  sorry

/-- `cor:commuting-with-G-incomplete`. -/
theorem commutingWithGIncomplete
    (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error)
    (hcomm : CommutingWithGCompleteStatement params ψ family gamma zeta) :
    CommutingWithGIncompleteStatement params ψ family gamma zeta := by
  sorry

/-- `cor:G-hat-facts`. -/
theorem gHatFacts
    (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error)
    (hselfComplete : GCompleteSelfConsistencyStatement params ψ family zeta)
    (hselfIncomplete : GBotSelfConsistencyStatement params ψ family zeta)
    (hcommComplete : CommutingWithGCompleteStatement params ψ family gamma zeta)
    (hcommIncomplete : CommutingWithGIncompleteStatement params ψ family gamma zeta) :
    GHatFactsStatement params ψ family gamma zeta := by
  sorry

/-- `lem:commute-g-half-sandwich`. -/
lemma commuteGHalfSandwich
    (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hfacts : GHatFactsStatement params ψ family gamma zeta) :
    CommuteGHalfSandwichStatement params ψ family gamma zeta k := by
  sorry

/-- `lem:ld-sandwich-line-one-point`. -/
lemma ldSandwichLineOnePoint
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i := by
  sorry

/-- `lem:h-b-consistency`. -/
lemma hBConsistency
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i) :
    HBConsistencyStatement params strategy family eps delta gamma zeta k := by
  sorry

/-- `lem:over-all-outcomes`. -/
lemma overAllOutcomes
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma zeta : Error)
    (family : IndexedPolynomialFamily params)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  sorry

/-- `lem:from-H-to-G`. -/
lemma fromHToG
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (gamma zeta : Error)
    (family : IndexedPolynomialFamily params)
    (k : ℕ)
    (hhalf : CommuteGHalfSandwichStatement params strategy.state family gamma zeta k) :
    FromHToGStatement params strategy family gamma zeta k := by
  sorry

/-- `lem:chernoff-bernoulli-matrix`. -/
lemma chernoffBernoulliMatrix
    (ψ : QuantumState)
    (theta : Error) (k d : ℕ) (X : Operator) (kappa : Error)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (d : Error)) / theta ≤ (k : Error))
    (hXpsd : PositiveSemidefinite X)
    (hXleOne : PositiveSemidefinite (operatorComplement X))
    (hcomplete : CompletenessAtLeast ψ (operatorAsSubMeasurement X) (1 - kappa)) :
    ChernoffBernoulliMatrixStatement ψ theta k d X kappa := by
  sorry

/-- `cor:ld-pasting-N-completeness`. -/
theorem ldPastingNCompleteness
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (kappa nu : Error)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa nu k := by
  sorry

end MIPStarRE.Paper2009LDT.Section12Pasting
