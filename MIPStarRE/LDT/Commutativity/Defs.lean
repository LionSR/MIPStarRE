import MIPStarRE.LDT.CommutativityPoints.Theorem

/-!
Definitions and operator constructions for Section 11 commutativity.

In the bipartite model, functions that use `leftPlacedSubMeas` /
`rightPlacedSubMeas` produce `SubMeas` at the bipartite dimension `d * d`,
while functions that stay on a single register produce `SubMeas` at `d`.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev EvaluatedSliceQuestion (params : Parameters) := Point params.next × Point params.next
abbrev EvaluatedSliceOutcome (params : Parameters) := Fq params × Fq params
abbrev FullSliceQuestion (params : Parameters) := Fq params × Fq params
abbrev FullSliceOutcome (params : Parameters) := Polynomial params × Polynomial params

/-- Ordered product placed on the left tensor factor of the bipartite space `ι × ι`. -/
noncomputable def leftOrderedProductSubMeas {α β : Type*}
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) (ι × ι) :=
  leftPlacedSubMeas (ιB := ι) (orderedProductSubMeas A B)

/-- Append a total operator on the right of every outcome operator. -/
noncomputable def appendRightTotalSubMeas {α : Type*} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : SubMeas α κ) (X : MIPStarRE.Quantum.Op κ) : SubMeas α κ where
  outcome := fun a => A.outcome a * X
  total := A.total * X

/-- Sandwiched product `A_a B_b A_a`.

Its total operator should be the sum-of-sandwiches
`∑_a A_a (∑_b B_b) A_a` whenever `α` is finitely enumerable. -/
noncomputable def sandwichByOuterSubMeas {α β : Type*} [Fintype α]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) ι where
  outcome := fun ab =>
    match ab with
    | (a, b) =>
        A.outcome a * B.outcome b * A.outcome a
  total :=
    ∑ a : α, A.outcome a * B.total * A.outcome a

/-- The full-slice question underlying an evaluated-slice sample. -/
def fullSliceQuestionOfEvaluatedSlice (params : Parameters)
    (q : EvaluatedSliceQuestion params) : FullSliceQuestion params :=
  (pointHeight params q.1, pointHeight params q.2)

/-- The postprocessed family `((u,x) ↦ G^x_[g(u)=a])`. -/
noncomputable def evaluatedPointFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  IdxPolyFamily.evaluatedAtNextPoint family

/-- Left tensor-placement for the evaluated family `G^x_[g(u)=a]`
on the bipartite space `d * d`. -/
noncomputable def evaluatedPointFamilyLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
  fun u => leftPlacedSubMeas (ιB := ι) (evaluatedPointFamily params family u)

/-- Right tensor-placement for the evaluated family `G^x_[g(u)=a]`
on the bipartite space `d * d`. -/
noncomputable def evaluatedPointFamilyRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
  fun u => rightPlacedSubMeas (ιA := ι) (evaluatedPointFamily params family u)

/-- The first evaluated factor `G^x_[g(u)=a]`. -/
noncomputable def evaluatedSliceFirstFactor (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q => evaluatedPointFamily params family q.1

/-- The second evaluated factor `G^y_[h(v)=b]`. -/
noncomputable def evaluatedSliceSecondFactor (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q => evaluatedPointFamily params family q.2

/-- The ordered evaluated-slice product `(G^x_[g(u)=a] G^y_[h(v)=b]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceProductLeft (params : Parameters)
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    leftOrderedProductSubMeas
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)

/-- The reversed evaluated-slice product `(G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceProductRight (params : Parameters)
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      reversedProductSubMeas
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)

/-- The sandwiched evaluated product `(G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceSandwichFirstFactor (params : Parameters)
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      sandwichByOuterSubMeas
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)

/-- The first full slice measurement `G^x`. -/
def fullSliceFirstFactor (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => (family.meas q.1).toSubMeas

/-- The second full slice measurement `G^y`. -/
def fullSliceSecondFactor (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => (family.meas q.2).toSubMeas

/-- The ordered full-slice product `(G^x_g G^y_h) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def fullSliceProductLeft (params : Parameters)
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (FullSliceOutcome params) (ι × ι) :=
  fun q =>
    leftOrderedProductSubMeas
      (fullSliceFirstFactor params family q)
      (fullSliceSecondFactor params family q)

/-- The reversed full-slice product `(G^y_h G^x_g) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def fullSliceProductRight (params : Parameters)
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (FullSliceOutcome params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      reversedProductSubMeas
        (fullSliceFirstFactor params family q)
        (fullSliceSecondFactor params family q)

/-- Evaluate a pair of full-slice outcomes at the sampled points `((u,x),(v,y))`. -/
def evaluateFullSliceOutcomeAtQuestion (params : Parameters)
    (q : EvaluatedSliceQuestion params) :
    FullSliceOutcome params → EvaluatedSliceOutcome params :=
  fun gh =>
    (gh.1 (truncatePoint params q.1), gh.2 (truncatePoint params q.2))

/-- Postprocess the full-slice ordered product at sampled points.
On the bipartite space `d * d`. -/
noncomputable def evaluatedFromFullSliceProductLeft (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    postprocess (fullSliceProductLeft params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Postprocess the full-slice reversed product at sampled points.
On the bipartite space `d * d`. -/
noncomputable def evaluatedFromFullSliceProductRight (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    postprocess (fullSliceProductRight params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Internal stability family from the `G^y` insertion/removal step.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityOneLeft (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    appendRightTotalSubMeas
      (evaluatedSliceSandwichFirstFactor params strategy family q)
      (leftTensor (ι₂ := ι) ((fullSliceSecondFactor params family xy).total))

/-- Internal stability family after removing the trailing `G^y`.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityOneRight (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q => evaluatedSliceSandwichFirstFactor params strategy family q

/-- Internal stability family from the `G^x` insertion/removal step.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityTwoLeft (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    appendRightTotalSubMeas
      (evaluatedSliceProductLeft params strategy family q)
      (leftTensor (ι₂ := ι) ((fullSliceFirstFactor params family xy).total))

/-- Internal stability family after removing the trailing `G^x`.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityTwoRight (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q => evaluatedSliceProductLeft params strategy family q

/-- The operator `C_{a,b} = Q_b P_a Q_b` from `lem:normalization-condition`.

We propagate explicit `matrix` from the input operators so that
the sum `∑_b C_{a,b}` accumulates correctly. -/
noncomputable def normalizationConditionSandwichedOperator {OutcomeA OutcomeB : Type*}
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    (a : OutcomeA) (b : OutcomeB) : MIPStarRE.Quantum.Op ι :=
  Q.outcome b * P.outcome a * Q.outcome b

/-- The sandwiched family `b ↦ Q_b P_a Q_b`. -/
noncomputable def normalizationConditionSandwichedFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    IdxSubMeas OutcomeA OutcomeB ι :=
  fun a =>
    { outcome := fun b => normalizationConditionSandwichedOperator P Q a b
      total :=
        ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b }

/-- The total family `a ↦ ∑_b C_{a,b}` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedTotalFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    IdxSubMeas OutcomeA Unit ι :=
  fun a => postprocess (normalizationConditionSandwichedFamily P Q a) (fun _ => ())

/-- The formal operator `∑_b C_{a,b}` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedTotalOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    (a : OutcomeA) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionSandwichedTotalFamily P Q a).total

/-- The family `a ↦ (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
noncomputable def normalizationConditionSquareFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    SubMeas OutcomeA ι where
  outcome := fun a =>
    normalizationConditionSandwichedTotalOperator P Q a *
      (normalizationConditionSandwichedTotalOperator P Q a)ᴴ
  total :=
    ∑ a : OutcomeA,
      normalizationConditionSandwichedTotalOperator P Q a *
        (normalizationConditionSandwichedTotalOperator P Q a)ᴴ

/-- The family `a ↦ (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
noncomputable def normalizationConditionAdjointSquareFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    SubMeas OutcomeA ι where
  outcome := fun a =>
    (normalizationConditionSandwichedTotalOperator P Q a)ᴴ *
      normalizationConditionSandwichedTotalOperator P Q a
  total :=
    ∑ a : OutcomeA,
      (normalizationConditionSandwichedTotalOperator P Q a)ᴴ *
        normalizationConditionSandwichedTotalOperator P Q a

/-- The operator `∑_a (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
noncomputable def normalizationConditionSquareOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionSquareFamily P Q).total

/-- The operator `∑_a (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
noncomputable def normalizationConditionAdjointSquareOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionAdjointSquareFamily P Q).total

/-- The identity bound appearing in `lem:normalization-condition`. -/
def normalizationConditionIdentityBound {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (_P : SubMeas OutcomeA ι) (_Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  1

end MIPStarRE.LDT.Commutativity
