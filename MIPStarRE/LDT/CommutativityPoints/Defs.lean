import MIPStarRE.LDT.SelfImprovement.Theorems

/-!
Matching scaffold for Section 10 of the low individual degree paper in
`references/ldt-paper/commutativity-points.tex`.
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev PointPairOutcome (params : Parameters) := Fq params × Fq params
abbrev PointDiagonalLineQuestion (params : Parameters) := DiagonalLine params × Fq params
abbrev PointPairDiagonalLineQuestion (params : Parameters) :=
  DiagonalLine params × (Fq params × Fq params)

-- leftPlacedSubMeas / rightPlacedSubMeas are defined in Basic/SubMeasurement.lean

/-- Ordered product of two paper-local submeasurements on the same tensor factor. -/
noncomputable def orderedProductSubMeas {α β : Type*}
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) ι where
  outcome := fun | (a, b) => A.outcome a * B.outcome b
  total := A.total * B.total

/-- Reversed product of two paper-local submeasurements on the same tensor factor. -/
noncomputable def reversedProductSubMeas {α β : Type*}
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) ι where
  outcome := fun | (a, b) => B.outcome b * A.outcome a
  total := B.total * A.total

/-- Tensor-product bridge `A_a ⊗ B_b` on the bipartite space `ι × ι`. -/
noncomputable def tensorProductSubMeas {α β : Type*}
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) (ι × ι) where
  outcome := fun ab =>
    match ab with
    | (a, b) =>
        leftTensor (ι₂ := ι) (A.outcome a) *
          rightTensor (ι₁ := ι) (B.outcome b)
  total := leftTensor (ι₂ := ι) A.total *
             rightTensor (ι₁ := ι) B.total

/-- Recover the sampled point from a diagonal-line/parameter sample. -/
def sampledPointFromDiagonalQuestion (params : Parameters)
    (q : PointDiagonalLineQuestion params) : Point params :=
  q.1.pointAt q.2

/-- Recover the two sampled points from a shared diagonal-line sample. -/
def sampledPointPairFromSharedDiagonalQuestion (params : Parameters)
    (q : PointPairDiagonalLineQuestion params) : PointPairQuestion params :=
  (q.1.pointAt q.2.1, q.1.pointAt q.2.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I` on the bipartite space `d * d`. -/
noncomputable def pointMeasurementProductLeft (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    leftPlacedSubMeas (ιB := ι) <|
      orderedProductSubMeas Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I` on the bipartite space `ι × ι`. -/
noncomputable def pointMeasurementProductRight (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    leftPlacedSubMeas (ιB := ι) <|
      reversedProductSubMeas Au Av

/-- Distribution obtained by sampling a diagonal line together with a parameter on that line. -/
def pointWithDiagonalLineDistribution (params : Parameters) :
    Distribution (PointDiagonalLineQuestion params) where

/-- Distribution obtained by sampling a diagonal line together with two parameters on it. -/
def pointPairSharedDiagonalLineDistribution (params : Parameters) :
    Distribution (PointPairDiagonalLineQuestion params) where

/-- The point measurement, reindexed by a sampled diagonal line and a parameter on it. -/
def sampledPointMeasurement (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas

/-- Evaluate the diagonal-line measurement at the sampled parameter. -/
noncomputable def sampledDiagonalLineEvaluation (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLine (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    pointMeasurementProductLeft params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The reversed point product `(A^v_b A^u_a) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLineReversed (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    pointMeasurementProductRight params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The mixed bridge `A^u_a ⊗ L^ℓ_[f(v)=b]` on the bipartite space `d * d`. -/
noncomputable def pointDiagonalLineMixedProductLeft (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Au := (strategy.pointMeasurement (ℓ.pointAt tu)).toSubMeas
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    tensorProductSubMeas Au Lv

/-- The bridge `I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])` on the bipartite space `d * d`. -/
noncomputable def diagonalLineProductOrdered (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    rightPlacedSubMeas (ιA := ι) <|
      orderedProductSubMeas Lu Lv

/-- The swapped bridge `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b])` on the bipartite space `ι × ι`. -/
noncomputable def diagonalLineProductReversed (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    rightPlacedSubMeas (ιA := ι) <|
      reversedProductSubMeas Lu Lv

/-- The mixed bridge `A^v_b ⊗ L^ℓ_[f(u)=a]` on the bipartite space `ι × ι`. -/
noncomputable def pointDiagonalLineMixedProductRight (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Av := (strategy.pointMeasurement (ℓ.pointAt tv)).toSubMeas
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    tensorProductSubMeas Av Lu

/-- The intermediate consistency loss coming from the `m`-restricted diagonal-lines test. -/
def restrictedDiagonalLinesConsistencyError (params : Parameters) (gamma : Error) : Error :=
  gamma * (params.m : Error)

/-- The approximation loss obtained from `prop:simeq-to-approx`. -/
def pointDiagonalLineApproxError (params : Parameters) (gamma : Error) : Error :=
  2 * restrictedDiagonalLinesConsistencyError params gamma

/-- The displayed commutativity error from `thm:commutativity-points`. -/
def commutativityPointsError (params : Parameters) (gamma : Error) : Error :=
  32 * gamma * (params.m : Error)

end MIPStarRE.LDT.CommutativityPoints
