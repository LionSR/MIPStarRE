import MIPStarRE.Paper2009LDT.Section10CommutativityPoints

/-!
Matching scaffold for Section 11 of the low individual degree paper in
`references/ldt-paper/commutativity-G.tex`.
-/

namespace MIPStarRE.Paper2009LDT.Section11Commutativity

open MIPStarRE.Paper2009LDT
open MIPStarRE.Paper2009LDT.Section7ExpansionHypercubeGraph
open MIPStarRE.Paper2009LDT.Section10CommutativityPoints

abbrev EvaluatedSliceQuestion (params : Parameters) := Point params.next × Point params.next
abbrev EvaluatedSliceOutcome (params : Parameters) := Fq params × Fq params
abbrev FullSliceQuestion (params : Parameters) := Fq params × Fq params
abbrev FullSliceOutcome (params : Parameters) := Polynomial params × Polynomial params

/-- Ordered product placed on the left tensor factor. -/
def leftOrderedProductSubMeasurement {α β : Type _}
    (label : String) (A : SubMeasurement α) (B : SubMeasurement β) :
    SubMeasurement (α × β) :=
  leftPlacedSubMeasurement (orderedProductSubMeasurement label A B)

/-- Append a total operator on the right of every outcome operator. -/
def appendRightTotalSubMeasurement {α : Type _}
    (tag : String) (A : SubMeasurement α) (X : Operator) : SubMeasurement α where
  name := s!"{A.name}.{tag}"
  outcomeOperator := fun a => formalProduct (A.outcomeOperator a) X
  totalOperator := formalProduct A.totalOperator X

/-- Sandwiched product `A_a B_b A_a`. -/
def sandwichByOuterSubMeasurement {α β : Type _}
    (label : String) (A : SubMeasurement α) (B : SubMeasurement β) :
    SubMeasurement (α × β) where
  name := label
  outcomeOperator := fun ab =>
    match ab with
    | (a, b) =>
        formalProduct (A.outcomeOperator a)
          (formalProduct (B.outcomeOperator b) (A.outcomeOperator a))
  totalOperator := formalProduct A.totalOperator
    (formalProduct B.totalOperator A.totalOperator)

/-- The full-slice question underlying an evaluated-slice sample. -/
def fullSliceQuestionOfEvaluatedSlice (params : Parameters)
    (q : EvaluatedSliceQuestion params) : FullSliceQuestion params :=
  (pointHeight params q.1, pointHeight params q.2)

/-- The postprocessed family `((u,x) ↦ G^x_[g(u)=a])`. -/
def evaluatedPointFamily (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (Point params.next) (Fq params) :=
  IndexedPolynomialFamily.evaluatedAtNextPoint family

/-- Left tensor-placement for the evaluated family `G^x_[g(u)=a]`. -/
def evaluatedPointFamilyLeft (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (Point params.next) (Fq params) :=
  fun u => leftPlacedSubMeasurement (evaluatedPointFamily params family u)

/-- Right tensor-placement for the evaluated family `G^x_[g(u)=a]`. -/
def evaluatedPointFamilyRight (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (Point params.next) (Fq params) :=
  fun u => rightPlacedSubMeasurement (evaluatedPointFamily params family u)

/-- The first evaluated factor `G^x_[g(u)=a]`. -/
def evaluatedSliceFirstFactor (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (Fq params) :=
  fun q => evaluatedPointFamily params family q.1

/-- The second evaluated factor `G^y_[h(v)=b]`. -/
def evaluatedSliceSecondFactor (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (Fq params) :=
  fun q => evaluatedPointFamily params family q.2

/-- The ordered evaluated-slice product `(G^x_[g(u)=a] G^y_[h(v)=b]) ⊗ I`. -/
def evaluatedSliceProductLeft (params : Parameters)
    (_strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun q =>
    leftOrderedProductSubMeasurement
      s!"evalSlice.left({params.m},{params.q},{params.d})"
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)

/-- The reversed evaluated-slice product `(G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`. -/
def evaluatedSliceProductRight (params : Parameters)
    (_strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun q =>
    leftPlacedSubMeasurement <|
      reversedProductSubMeasurement
        s!"evalSlice.right({params.m},{params.q},{params.d})"
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)

/-- The sandwiched evaluated product `(G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`. -/
def evaluatedSliceSandwichFirstFactor (params : Parameters)
    (_strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun q =>
    leftPlacedSubMeasurement <|
      sandwichByOuterSubMeasurement
        s!"evalSlice.sandwich({params.m},{params.q},{params.d})"
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)

/-- The first full slice measurement `G^x`. -/
def fullSliceFirstFactor (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (FullSliceQuestion params) (Polynomial params) :=
  fun q => (family.meas q.1).toSubMeasurement

/-- The second full slice measurement `G^y`. -/
def fullSliceSecondFactor (params : Parameters)
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (FullSliceQuestion params) (Polynomial params) :=
  fun q => (family.meas q.2).toSubMeasurement

/-- The ordered full-slice product `(G^x_g G^y_h) ⊗ I`. -/
def fullSliceProductLeft (params : Parameters)
    (_strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (FullSliceQuestion params) (FullSliceOutcome params) :=
  fun q =>
    leftOrderedProductSubMeasurement
      s!"fullSlice.left({params.m},{params.q},{params.d})"
      (fullSliceFirstFactor params family q)
      (fullSliceSecondFactor params family q)

/-- The reversed full-slice product `(G^y_h G^x_g) ⊗ I`. -/
def fullSliceProductRight (params : Parameters)
    (_strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (FullSliceQuestion params) (FullSliceOutcome params) :=
  fun q =>
    leftPlacedSubMeasurement <|
      reversedProductSubMeasurement
        s!"fullSlice.right({params.m},{params.q},{params.d})"
        (fullSliceFirstFactor params family q)
        (fullSliceSecondFactor params family q)

/-- Evaluate a pair of full-slice outcomes at the sampled points `((u,x),(v,y))`. -/
def evaluateFullSliceOutcomeAtQuestion (params : Parameters)
    (q : EvaluatedSliceQuestion params) :
    FullSliceOutcome params → EvaluatedSliceOutcome params :=
  fun gh =>
    (gh.1 (truncatePoint params q.1), gh.2 (truncatePoint params q.2))

/-- Postprocess the full-slice ordered product at sampled points. -/
def evaluatedFromFullSliceProductLeft (params : Parameters)
    (strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    postprocess (fullSliceProductLeft params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Postprocess the full-slice reversed product at sampled points. -/
def evaluatedFromFullSliceProductRight (params : Parameters)
    (strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    postprocess (fullSliceProductRight params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Internal stability family from the `G^y` insertion/removal step. -/
def commDataProcessedGStabilityOneLeft (params : Parameters)
    (strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    appendRightTotalSubMeasurement "timesGy"
      (evaluatedSliceSandwichFirstFactor params strategy family q)
      (leftTensor ((fullSliceSecondFactor params family xy).totalOperator))

/-- Internal stability family after removing the trailing `G^y`. -/
def commDataProcessedGStabilityOneRight (params : Parameters)
    (strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun q => evaluatedSliceSandwichFirstFactor params strategy family q

/-- Internal stability family from the `G^x` insertion/removal step. -/
def commDataProcessedGStabilityTwoLeft (params : Parameters)
    (strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    appendRightTotalSubMeasurement "timesGx"
      (evaluatedSliceProductLeft params strategy family q)
      (leftTensor ((fullSliceFirstFactor params family xy).totalOperator))

/-- Internal stability family after removing the trailing `G^x`. -/
def commDataProcessedGStabilityTwoRight (params : Parameters)
    (strategy : SymmetricStrategy params.next) (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun q => evaluatedSliceProductLeft params strategy family q

/-- The operator `C_{a,b} = Q_b P_a Q_b` from `lem:normalization-condition`. -/
def normalizationConditionSandwichedOperator {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB)
    (a : OutcomeA) (b : OutcomeB) : Operator :=
  formalProduct (Q.outcomeOperator b)
    (formalProduct (P.outcomeOperator a) (Q.outcomeOperator b))

/-- The sandwiched family `b ↦ Q_b P_a Q_b`. -/
def normalizationConditionSandwichedFamily {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) :
    IndexedSubMeasurement OutcomeA OutcomeB :=
  fun a =>
    { name := s!"sandwich({P.name},{Q.toSubMeasurement.name})"
      outcomeOperator := fun b => normalizationConditionSandwichedOperator P Q a b
      totalOperator := { name := s!"sandwichTotal({P.name},{Q.toSubMeasurement.name})" } }

/-- The total family `a ↦ ∑_b C_{a,b}` from `lem:normalization-condition`. -/
def normalizationConditionSandwichedTotalFamily {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) :
    IndexedSubMeasurement OutcomeA Unit :=
  fun a => postprocess (normalizationConditionSandwichedFamily P Q a) (fun _ => ())

/-- The formal operator `∑_b C_{a,b}` from `lem:normalization-condition`. -/
def normalizationConditionSandwichedTotalOperator {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB)
    (a : OutcomeA) : Operator :=
  (normalizationConditionSandwichedTotalFamily P Q a).totalOperator

/-- The family `a ↦ (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
def normalizationConditionSquareFamily {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) :
    SubMeasurement OutcomeA where
  name := s!"normSquareFamily({P.name},{Q.toSubMeasurement.name})"
  outcomeOperator := fun a =>
    formalProduct
      (normalizationConditionSandwichedTotalOperator P Q a)
      (formalAdjoint (normalizationConditionSandwichedTotalOperator P Q a))
  totalOperator := { name := s!"normSquare({P.name},{Q.toSubMeasurement.name})" }

/-- The family `a ↦ (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
def normalizationConditionAdjointSquareFamily {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) :
    SubMeasurement OutcomeA where
  name := s!"normAdjointSquareFamily({P.name},{Q.toSubMeasurement.name})"
  outcomeOperator := fun a =>
    formalProduct
      (formalAdjoint (normalizationConditionSandwichedTotalOperator P Q a))
      (normalizationConditionSandwichedTotalOperator P Q a)
  totalOperator := { name := s!"normAdjointSquare({P.name},{Q.toSubMeasurement.name})" }

/-- The operator `∑_a (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
def normalizationConditionSquareOperator {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) : Operator :=
  (normalizationConditionSquareFamily P Q).totalOperator

/-- The operator `∑_a (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
def normalizationConditionAdjointSquareOperator {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) : Operator :=
  (normalizationConditionAdjointSquareFamily P Q).totalOperator

/-- The identity bound appearing in `lem:normalization-condition`. -/
def normalizationConditionIdentityBound {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) : Operator :=
  Section7ExpansionHypercubeGraph.identityOperator s!"normalization({P.name},{Q.toSubMeasurement.name})"

/-- Operator domination, written in source order as `X ≤ Y`. -/
abbrev OperatorDominatedBy (X Y : Operator) : Prop :=
  DominatesOperator Y X

/-- Displayed error term for `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGError (params : Parameters) (gamma zeta : Error) : Error :=
  48 * (params.m : Error) *
    (Real.rpow gamma (1 / (2 : Error)) + Real.rpow zeta (1 / (2 : Error)))

/-- The first internal stability error from `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGStabilityOneError (zeta : Error) : Error :=
  Real.rpow zeta (1 / (2 : Error))

/-- The second internal stability error from `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGStabilityTwoError
    (params : Parameters) (gamma zeta : Error) : Error :=
  Real.rpow zeta (1 / (2 : Error)) +
    6 * Real.rpow (gamma * (((params.m + 1 : ℕ) : Error))) (1 / (2 : Error))

/-- Displayed error term for `thm:com-main`. -/
noncomputable def comMainError (params : Parameters) (gamma zeta : Error) : Error :=
  30 * (params.m : Error) *
    (Real.rpow gamma (1 / (4 : Error)) +
      Real.rpow zeta (1 / (4 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)))

/-- Output package for `lem:comm-data-processed-g`. -/
structure CommDataProcessedGConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) : Prop where
  postprocessedPointConsistency :
    ConsistencyRel strategy.state
      (uniformDistribution (Point params.next))
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta
  postprocessedSelfConsistency :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta
  stabilityOne :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family)
      (commDataProcessedGStabilityOneRight params strategy family)
      (commDataProcessedGStabilityOneError zeta)
  stabilityTwo :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family)
      (commDataProcessedGStabilityTwoRight params strategy family)
      (commDataProcessedGStabilityTwoError params gamma zeta)
  evaluatedSliceCommutation :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)

/-- Output package for `thm:com-main`. -/
structure ComMainConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) : Prop where
  evaluatedCommutation :
    CommDataProcessedGConclusion params strategy family gamma zeta
  evaluationSpecialization :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft params strategy family)
      (evaluatedFromFullSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)
  fullSliceCommutation :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (FullSliceQuestion params))
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)

/-- Output package for `lem:normalization-condition`. -/
structure NormalizationConditionStatement {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA)
    (Q : ProjectiveSubMeasurement OutcomeB) : Prop where
  sandwichedHermitianSquare :
    normalizationConditionAdjointSquareOperator P Q =
      normalizationConditionSquareOperator P Q
  sandwichedBoundedByIdentity :
    OperatorDominatedBy
      (normalizationConditionSquareOperator P Q)
      (normalizationConditionIdentityBound P Q)

/-- `lem:comm-data-processed-g`. -/
lemma commDataProcessedG
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta) :
    CommDataProcessedGConclusion params strategy family gamma zeta := by
  sorry

/-- `thm:com-main`. -/
theorem comMain
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta) :
    ComMainConclusion params strategy family gamma zeta := by
  sorry

/-- `lem:normalization-condition`. -/
lemma normalizationCondition {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA)
    (Q : ProjectiveSubMeasurement OutcomeB) :
    NormalizationConditionStatement P Q := by
  sorry

end MIPStarRE.Paper2009LDT.Section11Commutativity
