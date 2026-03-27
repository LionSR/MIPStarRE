import MIPStarRE.LDT.CommutativityPoints.Theorem

/-!
Definitions and operator constructions for Section 11 commutativity.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints

noncomputable section

abbrev EvaluatedSliceQuestion (params : Parameters) := Point params.next × Point params.next
abbrev EvaluatedSliceOutcome (params : Parameters) := Fq params × Fq params
abbrev FullSliceQuestion (params : Parameters) := Fq params × Fq params
abbrev FullSliceOutcome (params : Parameters) := Polynomial params × Polynomial params

/-- Ordered product placed on the left tensor factor. -/
def leftOrderedProductSubMeas {α β : Type*}
    (label : String) (A : SubMeas α d) (B : SubMeas β d) :
    SubMeas (α × β) d :=
  leftPlacedSubMeas (orderedProductSubMeas label A B)

/-- Append a total operator on the right of every outcome operator. -/
def appendRightTotalSubMeas {α : Type*}
    (tag : String) (A : SubMeas α d) (X : Operator d) : SubMeas α d where
  name := s!"{A.name}.{tag}"
  outcome := fun a => opMul (A.outcome a) X
  total := opMul A.total X

/-- Sandwiched product `A_a B_b A_a`.

Its total operator should be the sum-of-sandwiches
`∑_a A_a (∑_b B_b) A_a` whenever `α` is finitely enumerable. -/
noncomputable def sandwichByOuterSubMeas {α β : Type*}
    (label : String) (A : SubMeas α d) (B : SubMeas β d) :
    SubMeas (α × β) d where
  name := label
  outcome := fun ab =>
    match ab with
    | (a, b) =>
        opMul (A.outcome a)
          (opMul (B.outcome b) (A.outcome a))
  total := by
    classical
    if h : Nonempty (Fintype α) then
      letI : Fintype α := Classical.choice h
      exact sumOpList
        (Finset.univ.toList.map fun a =>
          opMul (A.outcome a)
            (opMul B.total (A.outcome a)))
    else
      exact
        { name := s!"TODO(sumSandwiches:{label})"
          matrix := A.total.matrix }

/-- The full-slice question underlying an evaluated-slice sample. -/
def fullSliceQuestionOfEvaluatedSlice (params : Parameters)
    (q : EvaluatedSliceQuestion params) : FullSliceQuestion params :=
  (pointHeight params q.1, pointHeight params q.2)

/-- The postprocessed family `((u,x) ↦ G^x_[g(u)=a])`. -/
def evaluatedPointFamily (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (Point params.next) (Fq params) d :=
  IdxPolyFamily.evaluatedAtNextPoint family

/-- Left tensor-placement for the evaluated family `G^x_[g(u)=a]`. -/
def evaluatedPointFamilyLeft (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (Point params.next) (Fq params) d :=
  fun u => leftPlacedSubMeas (evaluatedPointFamily params family u)

/-- Right tensor-placement for the evaluated family `G^x_[g(u)=a]`. -/
def evaluatedPointFamilyRight (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (Point params.next) (Fq params) d :=
  fun u => rightPlacedSubMeas (evaluatedPointFamily params family u)

/-- The first evaluated factor `G^x_[g(u)=a]`. -/
def evaluatedSliceFirstFactor (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) d :=
  fun q => evaluatedPointFamily params family q.1

/-- The second evaluated factor `G^y_[h(v)=b]`. -/
def evaluatedSliceSecondFactor (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) d :=
  fun q => evaluatedPointFamily params family q.2

/-- The ordered evaluated-slice product `(G^x_[g(u)=a] G^y_[h(v)=b]) ⊗ I`. -/
def evaluatedSliceProductLeft (params : Parameters)
    (_strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) d :=
  fun q =>
    leftOrderedProductSubMeas
      s!"evalSlice.left({params.m},{params.q},{params.d})"
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)

/-- The reversed evaluated-slice product `(G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`. -/
def evaluatedSliceProductRight (params : Parameters)
    (_strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) d :=
  fun q =>
    leftPlacedSubMeas <|
      reversedProductSubMeas
        s!"evalSlice.right({params.m},{params.q},{params.d})"
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)

/-- The sandwiched evaluated product `(G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`. -/
def evaluatedSliceSandwichFirstFactor (params : Parameters)
    (_strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) d :=
  fun q =>
    leftPlacedSubMeas <|
      sandwichByOuterSubMeas
        s!"evalSlice.sandwich({params.m},{params.q},{params.d})"
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)

/-- The first full slice measurement `G^x`. -/
def fullSliceFirstFactor (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (FullSliceQuestion params) (Polynomial params) d :=
  fun q => (family.meas q.1).toSubMeas

/-- The second full slice measurement `G^y`. -/
def fullSliceSecondFactor (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (FullSliceQuestion params) (Polynomial params) d :=
  fun q => (family.meas q.2).toSubMeas

/-- The ordered full-slice product `(G^x_g G^y_h) ⊗ I`. -/
def fullSliceProductLeft (params : Parameters)
    (_strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (FullSliceQuestion params) (FullSliceOutcome params) d :=
  fun q =>
    leftOrderedProductSubMeas
      s!"fullSlice.left({params.m},{params.q},{params.d})"
      (fullSliceFirstFactor params family q)
      (fullSliceSecondFactor params family q)

/-- The reversed full-slice product `(G^y_h G^x_g) ⊗ I`. -/
def fullSliceProductRight (params : Parameters)
    (_strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (FullSliceQuestion params) (FullSliceOutcome params) d :=
  fun q =>
    leftPlacedSubMeas <|
      reversedProductSubMeas
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
    (strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) d :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    postprocess (fullSliceProductLeft params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Postprocess the full-slice reversed product at sampled points. -/
def evaluatedFromFullSliceProductRight (params : Parameters)
    (strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) d :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    postprocess (fullSliceProductRight params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Internal stability family from the `G^y` insertion/removal step. -/
def commDataProcessedGStabilityOneLeft (params : Parameters)
    (strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) d :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    appendRightTotalSubMeas "timesGy"
      (evaluatedSliceSandwichFirstFactor params strategy family q)
      (leftTensor ((fullSliceSecondFactor params family xy).total))

/-- Internal stability family after removing the trailing `G^y`. -/
def commDataProcessedGStabilityOneRight (params : Parameters)
    (strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) d :=
  fun q => evaluatedSliceSandwichFirstFactor params strategy family q

/-- Internal stability family from the `G^x` insertion/removal step. -/
def commDataProcessedGStabilityTwoLeft (params : Parameters)
    (strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) d :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    appendRightTotalSubMeas "timesGx"
      (evaluatedSliceProductLeft params strategy family q)
      (leftTensor ((fullSliceFirstFactor params family xy).total))

/-- Internal stability family after removing the trailing `G^x`. -/
def commDataProcessedGStabilityTwoRight (params : Parameters)
    (strategy : SymStrat params.next d) (family : IdxPolyFamily params d) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) d :=
  fun q => evaluatedSliceProductLeft params strategy family q

/-- The operator `C_{a,b} = Q_b P_a Q_b` from `lem:normalization-condition`.

We propagate explicit `dim` and `matrix` from the input operators so that
`opAdd`/`sumOpList` (which require matching dimensions) can
accumulate the sum `∑_b C_{a,b}` correctly even when `dim ≠ 1`. -/
def normalizationConditionSandwichedOperator {OutcomeA OutcomeB : Type*} {d : ℕ}
    (P : SubMeas OutcomeA d) (Q : ProjSubMeas OutcomeB d)
    (a : OutcomeA) (b : OutcomeB) : Operator d :=
  let pa := P.outcome a
  let qb := Q.outcome b
  { name := s!"({qb.name})*({pa.name})*({qb.name})"
    matrix := qb.matrix * pa.matrix * qb.matrix }

/-- The sandwiched family `b ↦ Q_b P_a Q_b`. -/
noncomputable def normalizationConditionSandwichedFamily {OutcomeA OutcomeB : Type*}
    (P : SubMeas OutcomeA d) (Q : ProjSubMeas OutcomeB d) :
    IdxSubMeas OutcomeA OutcomeB d :=
  fun a =>
    { name := s!"sandwich({P.name},{Q.toSubMeas.name})"
      outcome := fun b => normalizationConditionSandwichedOperator P Q a b
      total := by
        classical
        if h : Nonempty (Fintype OutcomeB) then
          letI : Fintype OutcomeB := Classical.choice h
          exact sumOpList
            (Finset.univ.toList.map
              (fun b => normalizationConditionSandwichedOperator P Q a b))
        else
          exact Q.total }

/-- The total family `a ↦ ∑_b C_{a,b}` from `lem:normalization-condition`. -/
def normalizationConditionSandwichedTotalFamily {OutcomeA OutcomeB : Type*}
    (P : SubMeas OutcomeA d) (Q : ProjSubMeas OutcomeB d) :
    IdxSubMeas OutcomeA Unit d :=
  fun a => postprocess (normalizationConditionSandwichedFamily P Q a) (fun _ => ())

/-- The formal operator `∑_b C_{a,b}` from `lem:normalization-condition`. -/
def normalizationConditionSandwichedTotalOperator {OutcomeA OutcomeB : Type*}
    (P : SubMeas OutcomeA d) (Q : ProjSubMeas OutcomeB d)
    (a : OutcomeA) : Operator d :=
  (normalizationConditionSandwichedTotalFamily P Q a).total

/-- The family `a ↦ (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
def normalizationConditionSquareFamily {OutcomeA OutcomeB : Type*}
    (P : SubMeas OutcomeA d) (Q : ProjSubMeas OutcomeB d) :
    SubMeas OutcomeA d where
  name := s!"normSquareFamily({P.name},{Q.toSubMeas.name})"
  outcome := fun a =>
    opMul
      (normalizationConditionSandwichedTotalOperator P Q a)
      (opAdj (normalizationConditionSandwichedTotalOperator P Q a))
  total := by
    classical
    if h : Nonempty (Fintype OutcomeA) then
      letI : Fintype OutcomeA := Classical.choice h
      exact sumOpList
        (Finset.univ.toList.map (fun a =>
          opMul
            (normalizationConditionSandwichedTotalOperator P Q a)
            (opAdj (normalizationConditionSandwichedTotalOperator P Q a))))
    else
      exact { name := s!"normSquare({P.name},{Q.toSubMeas.name})" }

/-- The family `a ↦ (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
def normalizationConditionAdjointSquareFamily {OutcomeA OutcomeB : Type*}
    (P : SubMeas OutcomeA d) (Q : ProjSubMeas OutcomeB d) :
    SubMeas OutcomeA d where
  name := s!"normAdjointSquareFamily({P.name},{Q.toSubMeas.name})"
  outcome := fun a =>
    opMul
      (opAdj (normalizationConditionSandwichedTotalOperator P Q a))
      (normalizationConditionSandwichedTotalOperator P Q a)
  total := by
    classical
    if h : Nonempty (Fintype OutcomeA) then
      letI : Fintype OutcomeA := Classical.choice h
      exact sumOpList
        (Finset.univ.toList.map (fun a =>
          opMul
            (opAdj (normalizationConditionSandwichedTotalOperator P Q a))
            (normalizationConditionSandwichedTotalOperator P Q a)))
    else
      exact { name := s!"normAdjointSquare({P.name},{Q.toSubMeas.name})" }

/-- The operator `∑_a (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
def normalizationConditionSquareOperator {OutcomeA OutcomeB : Type*}
    (P : SubMeas OutcomeA d) (Q : ProjSubMeas OutcomeB d) : Operator d :=
  (normalizationConditionSquareFamily P Q).total

/-- The operator `∑_a (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
def normalizationConditionAdjointSquareOperator {OutcomeA OutcomeB : Type*}
    (P : SubMeas OutcomeA d) (Q : ProjSubMeas OutcomeB d) : Operator d :=
  (normalizationConditionAdjointSquareFamily P Q).total

/-- The identity bound appearing in `lem:normalization-condition`. -/
def normalizationConditionIdentityBound {OutcomeA OutcomeB : Type*}
    (P : SubMeas OutcomeA d) (Q : ProjSubMeas OutcomeB d) : Operator d :=
  -- TODO: idOp dim should match normalizationConditionSquareOperator
  idOp s!"normalization({P.name},{Q.toSubMeas.name})"

end

end MIPStarRE.LDT.Commutativity
