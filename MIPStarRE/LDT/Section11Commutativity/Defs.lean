import MIPStarRE.LDT.Section10CommutativityPoints

/-!
Definitions and operator constructions for Section 11 commutativity.
-/

namespace MIPStarRE.LDT.Section11Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.Section7ExpansionHypercubeGraph
open MIPStarRE.LDT.Section10CommutativityPoints

noncomputable section

abbrev EvaluatedSliceQuestion (params : Parameters) := Point params.next × Point params.next
abbrev EvaluatedSliceOutcome (params : Parameters) := Fq params × Fq params
abbrev FullSliceQuestion (params : Parameters) := Fq params × Fq params
abbrev FullSliceOutcome (params : Parameters) := Polynomial params × Polynomial params

/-- Ordered product placed on the left tensor factor. -/
def leftOrderedProductSubMeasurement {α β : Type*}
    (label : String) (A : SubMeasurement α) (B : SubMeasurement β) :
    SubMeasurement (α × β) :=
  leftPlacedSubMeasurement (orderedProductSubMeasurement label A B)

/-- Append a total operator on the right of every outcome operator. -/
def appendRightTotalSubMeasurement {α : Type*}
    (tag : String) (A : SubMeasurement α) (X : Operator) : SubMeasurement α where
  name := s!"{A.name}.{tag}"
  outcomeOperator := fun a => operatorMul (A.outcomeOperator a) X
  totalOperator := operatorMul A.totalOperator X

/-- Sandwiched product `A_a B_b A_a`.

Its total operator should be the sum-of-sandwiches
`∑_a A_a (∑_b B_b) A_a` whenever `α` is finitely enumerable. -/
noncomputable def sandwichByOuterSubMeasurement {α β : Type*}
    (label : String) (A : SubMeasurement α) (B : SubMeasurement β) :
    SubMeasurement (α × β) where
  name := label
  outcomeOperator := fun ab =>
    match ab with
    | (a, b) =>
        operatorMul (A.outcomeOperator a)
          (operatorMul (B.outcomeOperator b) (A.outcomeOperator a))
  totalOperator := by
    classical
    if h : Nonempty (Fintype α) then
      letI : Fintype α := Classical.choice h
      exact sumOperatorList A.totalOperator
        (Finset.univ.toList.map fun a =>
          operatorMul (A.outcomeOperator a)
            (operatorMul B.totalOperator (A.outcomeOperator a)))
    else
      exact
        { name := s!"TODO(sumSandwiches:{label})"
          dim := A.totalOperator.dim
          matrix := A.totalOperator.matrix }

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

/-- The operator `C_{a,b} = Q_b P_a Q_b` from `lem:normalization-condition`.

We propagate explicit `dim` and `matrix` from the input operators so that
`operatorAdd`/`sumOperatorList` (which require matching dimensions) can
accumulate the sum `∑_b C_{a,b}` correctly even when `dim ≠ 1`. -/
def normalizationConditionSandwichedOperator {OutcomeA OutcomeB : Type*}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB)
    (a : OutcomeA) (b : OutcomeB) : Operator :=
  let pa := P.outcomeOperator a
  let qb := Q.outcomeOperator b
  if h : qb.dim = pa.dim then
    { name := s!"({qb.name})*({pa.name})*({qb.name})"
      dim := pa.dim
      matrix := (castOp h qb.matrix) * pa.matrix * (castOp h qb.matrix) }
  else
    -- TODO: dim-mismatch fallback is placeholder
    { name := s!"({qb.name})*({pa.name})*({qb.name})"
      dim := pa.dim }

/-- The sandwiched family `b ↦ Q_b P_a Q_b`. -/
noncomputable def normalizationConditionSandwichedFamily {OutcomeA OutcomeB : Type*}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) :
    IndexedSubMeasurement OutcomeA OutcomeB :=
  fun a =>
    { name := s!"sandwich({P.name},{Q.toSubMeasurement.name})"
      outcomeOperator := fun b => normalizationConditionSandwichedOperator P Q a b
      totalOperator := by
        classical
        if h : Nonempty (Fintype OutcomeB) then
          letI : Fintype OutcomeB := Classical.choice h
          exact sumOperatorList Q.totalOperator
            (Finset.univ.toList.map
              (fun b => normalizationConditionSandwichedOperator P Q a b))
        else
          exact Q.totalOperator }

/-- The total family `a ↦ ∑_b C_{a,b}` from `lem:normalization-condition`. -/
def normalizationConditionSandwichedTotalFamily {OutcomeA OutcomeB : Type*}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) :
    IndexedSubMeasurement OutcomeA Unit :=
  fun a => postprocess (normalizationConditionSandwichedFamily P Q a) (fun _ => ())

/-- The formal operator `∑_b C_{a,b}` from `lem:normalization-condition`. -/
def normalizationConditionSandwichedTotalOperator {OutcomeA OutcomeB : Type*}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB)
    (a : OutcomeA) : Operator :=
  (normalizationConditionSandwichedTotalFamily P Q a).totalOperator

/-- The family `a ↦ (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
def normalizationConditionSquareFamily {OutcomeA OutcomeB : Type*}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) :
    SubMeasurement OutcomeA where
  name := s!"normSquareFamily({P.name},{Q.toSubMeasurement.name})"
  outcomeOperator := fun a =>
    operatorMul
      (normalizationConditionSandwichedTotalOperator P Q a)
      (operatorAdjoint (normalizationConditionSandwichedTotalOperator P Q a))
  totalOperator := by
    classical
    if h : Nonempty (Fintype OutcomeA) then
      letI : Fintype OutcomeA := Classical.choice h
      exact sumOperatorList P.totalOperator
        (Finset.univ.toList.map (fun a =>
          operatorMul
            (normalizationConditionSandwichedTotalOperator P Q a)
            (operatorAdjoint (normalizationConditionSandwichedTotalOperator P Q a))))
    else
      exact { name := s!"normSquare({P.name},{Q.toSubMeasurement.name})"
              dim := P.totalOperator.dim }

/-- The family `a ↦ (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
def normalizationConditionAdjointSquareFamily {OutcomeA OutcomeB : Type*}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) :
    SubMeasurement OutcomeA where
  name := s!"normAdjointSquareFamily({P.name},{Q.toSubMeasurement.name})"
  outcomeOperator := fun a =>
    operatorMul
      (operatorAdjoint (normalizationConditionSandwichedTotalOperator P Q a))
      (normalizationConditionSandwichedTotalOperator P Q a)
  totalOperator := by
    classical
    if h : Nonempty (Fintype OutcomeA) then
      letI : Fintype OutcomeA := Classical.choice h
      exact sumOperatorList P.totalOperator
        (Finset.univ.toList.map (fun a =>
          operatorMul
            (operatorAdjoint (normalizationConditionSandwichedTotalOperator P Q a))
            (normalizationConditionSandwichedTotalOperator P Q a)))
    else
      exact { name := s!"normAdjointSquare({P.name},{Q.toSubMeasurement.name})"
              dim := P.totalOperator.dim }

/-- The operator `∑_a (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
def normalizationConditionSquareOperator {OutcomeA OutcomeB : Type*}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) : Operator :=
  (normalizationConditionSquareFamily P Q).totalOperator

/-- The operator `∑_a (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
def normalizationConditionAdjointSquareOperator {OutcomeA OutcomeB : Type*}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) : Operator :=
  (normalizationConditionAdjointSquareFamily P Q).totalOperator

/-- The identity bound appearing in `lem:normalization-condition`. -/
def normalizationConditionIdentityBound {OutcomeA OutcomeB : Type*}
    (P : SubMeasurement OutcomeA) (Q : ProjectiveSubMeasurement OutcomeB) : Operator :=
  -- TODO: identityOperator dim should match normalizationConditionSquareOperator
  identityOperator s!"normalization({P.name},{Q.toSubMeasurement.name})"

end

end MIPStarRE.LDT.Section11Commutativity
