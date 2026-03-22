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
abbrev SandwichedLineQuestion (params : Parameters) (k : ℕ) := Point params × PointTuple params k
abbrev VerticalLineQuestion (params : Parameters) := Point params

/-- Placeholder matrix-valued Bernoulli tail operator from `lem:chernoff-bernoulli-matrix`. -/
def bernoulliTailOperator (_k _d : ℕ) (_X : Operator) : Operator :=
  { name := "BernoulliTail" }

/-- Add a descriptive tag to a paper-local submeasurement placeholder. -/
def tagSubMeasurement {α : Type _} (tag : String) (A : SubMeasurement α) : SubMeasurement α where
  name := s!"{A.name}.{tag}"

/-- Placeholder complement operator `I - X`. -/
def operatorComplement (X : Operator) : Operator :=
  { name := s!"I - {X.name}" }

/-- Regard an operator expression as a `Unit`-valued submeasurement placeholder. -/
def operatorAsSubMeasurement (X : Operator) : SubMeasurement Unit :=
  { name := s!"operator({X.name})" }

/-- Regard the Bernoulli tail operator as a `Unit`-valued submeasurement placeholder. -/
def bernoulliTailSubMeasurement (k d : ℕ) (X : Operator) : SubMeasurement Unit :=
  { name := s!"{(bernoulliTailOperator k d X).name}.sub" }

/-- Aggregate the polynomial outcomes of `G^x` into its complete part `G^x`. -/
def completePartSubMeasurement (params : Parameters)
    (family : IndexedPolynomialFamily params) (x : Fq params) : SubMeasurement Unit :=
  tagSubMeasurement "complete"
    (postprocess ((family.meas x).toSubMeasurement) (fun _ => ()))

/-- Placeholder for the incomplete part `G^x_⊥ = I - G^x`. -/
def incompletePartSubMeasurement (params : Parameters)
    (family : IndexedPolynomialFamily params) (x : Fq params) : SubMeasurement Unit :=
  { name := s!"{(family.meas x).toSubMeasurement.name}.incomplete" }

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

/-- Left tensor-placement placeholder for the complete part `G^x`. -/
def completePartLeftFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) Unit :=
  fun x => tagSubMeasurement "left" (completePartSubMeasurement params family x)

/-- Right tensor-placement placeholder for the complete part `G^x`. -/
def completePartRightFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) Unit :=
  fun x => tagSubMeasurement "right" (completePartSubMeasurement params family x)

/-- Left tensor-placement placeholder for the incomplete part `G^x_⊥`. -/
def incompletePartLeftFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) Unit :=
  fun x => tagSubMeasurement "left" (incompletePartSubMeasurement params family x)

/-- Right tensor-placement placeholder for the incomplete part `G^x_⊥`. -/
def incompletePartRightFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) Unit :=
  fun x => tagSubMeasurement "right" (incompletePartSubMeasurement params family x)

/-- Left tensor-placement placeholder for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyLeft {Outcome : Type _} (params : Parameters)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SliceQuestion params) Outcome :=
  fun x => tagSubMeasurement "left" ((M x).toSubMeasurement)

/-- Right tensor-placement placeholder for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyRight {Outcome : Type _} (params : Parameters)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SliceQuestion params) Outcome :=
  fun x => tagSubMeasurement "right" ((M x).toSubMeasurement)

/-- Placeholder family for the hypothesis `G^x_g M^y_o`. -/
def switcherooPointProductLeft {Outcome : Type _} (params : Parameters)
    (_family : IndexedPolynomialFamily params)
    (_M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params × Outcome) :=
  fun _ => { name := s!"switcheroo.point.left({params.m},{params.q},{params.d})" }

/-- Placeholder family for the hypothesis `M^y_o G^x_g`. -/
def switcherooPointProductRight {Outcome : Type _} (params : Parameters)
    (_family : IndexedPolynomialFamily params)
    (_M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params × Outcome) :=
  fun _ => { name := s!"switcheroo.point.right({params.m},{params.q},{params.d})" }

/-- Placeholder family for the conclusion `G^x M^y_o`. -/
def switcherooAggregateLeft {Outcome : Type _} (params : Parameters)
    (_family : IndexedPolynomialFamily params)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SlicePairQuestion params) Outcome :=
  fun ⟨x, y⟩ => tagSubMeasurement s!"withComplete({x.1})" ((M y).toSubMeasurement)

/-- Placeholder family for the conclusion `M^y_o G^x`. -/
def switcherooAggregateRight {Outcome : Type _} (params : Parameters)
    (_family : IndexedPolynomialFamily params)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome) :
    IndexedSubMeasurement (SlicePairQuestion params) Outcome :=
  fun ⟨x, y⟩ => tagSubMeasurement s!"completeOnRight({x.1})" ((M y).toSubMeasurement)

/-- Placeholder family for the relation `G^x_g G^y`. -/
def completePartPointProductLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params) :=
  fun ⟨x, y⟩ =>
    tagSubMeasurement s!"timesComplete({y.1})" ((family.meas x).toSubMeasurement)

/-- Placeholder family for the relation `G^y G^x_g`. -/
def completePartPointProductRight (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params) :=
  fun ⟨x, _⟩ =>
    tagSubMeasurement s!"completeTimes({x.1})" ((family.meas x).toSubMeasurement)

/-- Placeholder family for the relation `G^x G^y`. -/
def completePartTotalProductLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) Unit :=
  fun ⟨x, y⟩ =>
    tagSubMeasurement s!"timesComplete({y.1})" (completePartSubMeasurement params family x)

/-- Placeholder family for the relation `G^y G^x`. -/
def completePartTotalProductRight (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) Unit :=
  fun ⟨x, y⟩ =>
    tagSubMeasurement s!"completeTimes({x.1})" (completePartSubMeasurement params family y)

/-- Placeholder family for the relation `G^x_g G^y_⊥`. -/
def incompletePartPointProductLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params) :=
  fun ⟨x, y⟩ =>
    tagSubMeasurement s!"timesIncomplete({y.1})" ((family.meas x).toSubMeasurement)

/-- Placeholder family for the relation `G^y_⊥ G^x_g`. -/
def incompletePartPointProductRight (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (Polynomial params) :=
  fun ⟨x, _⟩ =>
    tagSubMeasurement s!"incompleteTimes({x.1})" ((family.meas x).toSubMeasurement)

/-- Placeholder family for the relation `G^x_⊥ G^y_⊥`. -/
def incompletePartTotalProductLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) Unit :=
  fun ⟨x, y⟩ =>
    tagSubMeasurement s!"timesIncomplete({y.1})" (incompletePartSubMeasurement params family x)

/-- Placeholder family for the relation `G^y_⊥ G^x_⊥`. -/
def incompletePartTotalProductRight (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) Unit :=
  fun ⟨x, y⟩ =>
    tagSubMeasurement s!"incompleteTimes({x.1})" (incompletePartSubMeasurement params family y)

/-- Left tensor-placement placeholder for `\widehat G^x_g`. -/
def gHatSelfConsistencyLeftFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) (GHatOutcome params) :=
  fun x => tagSubMeasurement "left" ((gHatIndexedMeasurement params family x).toSubMeasurement)

/-- Right tensor-placement placeholder for `\widehat G^x_g`. -/
def gHatSelfConsistencyRightFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SliceQuestion params) (GHatOutcome params) :=
  fun x => tagSubMeasurement "right" ((gHatIndexedMeasurement params family x).toSubMeasurement)

/-- Placeholder family for the pairwise product `\widehat G^x_g \widehat G^y_h`. -/
def gHatPairProductLeft (params : Parameters)
    (_family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) :=
  fun _ => { name := s!"ghat.pair.left({params.m},{params.q},{params.d})" }

/-- Placeholder family for the reversed pairwise product `\widehat G^y_h \widehat G^x_g`. -/
def gHatPairProductRight (params : Parameters)
    (_family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) :=
  fun _ => { name := s!"ghat.pair.right({params.m},{params.q},{params.d})" }

/-- Placeholder family for the half-sandwich product of `k` completed slices. -/
def gHatHalfSandwichLeft (params : Parameters)
    (_family : IndexedPolynomialFamily params) (k : ℕ) :
    IndexedSubMeasurement (PointTuple params k) (GHatTupleOutcome params k) :=
  fun _ => { name := s!"ghat.half.left({params.m},{params.q},{params.d},{k})" }

/-- Placeholder family for the cyclically permuted half-sandwich product. -/
def gHatHalfSandwichRight (params : Parameters)
    (_family : IndexedPolynomialFamily params) (k : ℕ) :
    IndexedSubMeasurement (PointTuple params k) (GHatTupleOutcome params k) :=
  fun _ => { name := s!"ghat.half.right({params.m},{params.q},{params.d},{k})" }

/-- Placeholder family for the predicted value of the `i`-th sandwiched slice. -/
def ldSandwichLineOnePointLeftFamily (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (_family : IndexedPolynomialFamily params)
    (k i : ℕ) : IndexedSubMeasurement (SandwichedLineQuestion params k) (Fq params) :=
  fun _ => { name := s!"ldSandwich.left({params.m},{params.q},{params.d},{k},{i})" }

/-- Placeholder family for the corresponding line-value measurement from `B^u`. -/
def ldSandwichLineOnePointRightFamily (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (_family : IndexedPolynomialFamily params)
    (k i : ℕ) : IndexedSubMeasurement (SandwichedLineQuestion params k) (Fq params) :=
  fun _ => { name := s!"ldSandwich.right({params.m},{params.q},{params.d},{k},{i})" }

/-- Placeholder family for the restriction `H_[h|_u = f]`. -/
def hRestrictionToVerticalLine (params : Parameters)
    (H : SubMeasurement (Polynomial params.next)) :
    IndexedSubMeasurement (VerticalLineQuestion params) (AxisLinePolynomial params.next) :=
  fun _ => { name := s!"{H.name}.verticalRestriction" }

/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
def verticalLineMeasurementFamily (params : Parameters)
    (_strategy : SymmetricStrategy params.next) :
    IndexedSubMeasurement (VerticalLineQuestion params) (AxisLinePolynomial params.next) :=
  fun _ => { name := s!"verticalLine.B({params.m},{params.q},{params.d})" }

/-- Collapse a submeasurement to its `Unit`-valued total operator. -/
def pastedMeasurementTotal {α : Type _} (H : SubMeasurement α) : IndexedSubMeasurement Unit Unit :=
  constantSubMeasurementFamily (postprocess H (fun _ => ()))

/-- Placeholder family for the expansion over all outcome types `τ`. -/
def allOutcomesExpansionFamily (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (_family : IndexedPolynomialFamily params)
    (_H : SubMeasurement (Polynomial params.next)) (k : ℕ) :
    IndexedSubMeasurement Unit Unit :=
  fun _ => { name := s!"allOutcomes({params.m},{params.q},{params.d},{k})" }

/-- Placeholder family for the Bernoulli-tail polynomial in the complete part `G`. -/
def bernoulliTailFromFamily (params : Parameters)
    (_family : IndexedPolynomialFamily params) (k : ℕ) :
    IndexedSubMeasurement Unit Unit :=
  fun _ => { name := s!"familyBernoulliTail({params.m},{params.q},{params.d},{k})" }

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

/-- Output package for `thm:ld-pasting`. -/
structure LdPastingConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (H : Measurement (Polynomial params.next))
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
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
    (H : SubMeasurement (Polynomial params.next))
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  lineConsistency :
    ConsistencyRel strategy.state
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k)

/-- Output package for `lem:over-all-outcomes`. -/
structure OverAllOutcomesStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (H : SubMeasurement (Polynomial params.next))
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  totalOutcomeExpansion :
    StateDependentDistanceRel strategy.state (uniformDistribution Unit)
      (pastedMeasurementTotal H)
      (allOutcomesExpansionFamily params strategy family H k)
      (overAllOutcomesError params eps delta gamma zeta k)

/-- Output package for `lem:from-H-to-G`. -/
structure FromHToGStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (H : SubMeasurement (Polynomial params.next))
    (gamma zeta : Error) (k : ℕ) : Prop where
  bernoulliPolynomialRewrite :
    StateDependentDistanceRel strategy.state (uniformDistribution Unit)
      (allOutcomesExpansionFamily params strategy family H k)
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
    (H : SubMeasurement (Polynomial params.next))
    (kappa nu : Error) (k : ℕ) : Prop where
  completenessBound :
    CompletenessAtLeast strategy.state H
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
    (k : ℕ) :
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
    (k : ℕ) :
    ∃ H : SubMeasurement (Polynomial params.next),
      LdPastingSubMeasurementConclusion params strategy family H eps delta gamma kappa zeta k := by
  sorry

/-- `prop:ld-dnoteq`. -/
theorem ldDnoteq
    (params : Parameters) (k : ℕ) :
    totalVariationDistance (uniformDistribution (PointTuple params k))
        (distinctTupleDistribution params k)
      ≤ ((k : Error) ^ (2 : ℕ)) / ((params.q : Error) + 1) := by
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
    (H : SubMeasurement (Polynomial params.next))
    (k : ℕ) :
    HBConsistencyStatement params strategy family H eps delta gamma zeta k := by
  sorry

/-- `lem:over-all-outcomes`. -/
lemma overAllOutcomes
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma zeta : Error)
    (family : IndexedPolynomialFamily params)
    (H : SubMeasurement (Polynomial params.next))
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family H eps delta gamma zeta k := by
  sorry

/-- `lem:from-H-to-G`. -/
lemma fromHToG
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (gamma zeta : Error)
    (family : IndexedPolynomialFamily params)
    (H : SubMeasurement (Polynomial params.next))
    (k : ℕ) :
    FromHToGStatement params strategy family H gamma zeta k := by
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
    (H : SubMeasurement (Polynomial params.next))
    (kappa nu : Error)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family H kappa nu k := by
  sorry

end MIPStarRE.Paper2009LDT.Section12Pasting
