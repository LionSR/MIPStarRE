import MIPStarRE.LDT.Section9SelfImprovement

/-!
Matching scaffold for Section 10 of the low individual degree paper in
`references/ldt-paper/commutativity-points.tex`.
-/

namespace MIPStarRE.LDT.Section10CommutativityPoints

open MIPStarRE.LDT
open MIPStarRE.LDT.Section7ExpansionHypercubeGraph
open MIPStarRE.LDT.Section8GlobalVariance (PointPairQuestion)

abbrev PointPairOutcome (params : Parameters) := Fq params × Fq params
abbrev PointDiagonalLineQuestion (params : Parameters) := DiagonalLine params × Fq params
abbrev PointPairDiagonalLineQuestion (params : Parameters) :=
  DiagonalLine params × (Fq params × Fq params)

/-- Place a submeasurement on the left tensor factor. -/
def leftPlacedSubMeasurement {α : Type*} (A : SubMeasurement α) : SubMeasurement α where
  name := s!"{A.name}.left"
  outcomeOperator := fun a => leftTensor (A.outcomeOperator a)
  totalOperator := leftTensor A.totalOperator

/-- Place a submeasurement on the right tensor factor. -/
def rightPlacedSubMeasurement {α : Type*} (A : SubMeasurement α) : SubMeasurement α where
  name := s!"{A.name}.right"
  outcomeOperator := fun a => rightTensor (A.outcomeOperator a)
  totalOperator := rightTensor A.totalOperator

/-- Ordered product of two paper-local submeasurements on the same tensor factor. -/
noncomputable def orderedProductSubMeasurement {α β : Type*}
    (label : String) (A : SubMeasurement α) (B : SubMeasurement β) :
    SubMeasurement (α × β) where
  name := label
  outcomeOperator := fun | (a, b) => operatorMul (A.outcomeOperator a) (B.outcomeOperator b)
  totalOperator := operatorMul A.totalOperator B.totalOperator

/-- Reversed product of two paper-local submeasurements on the same tensor factor. -/
noncomputable def reversedProductSubMeasurement {α β : Type*}
    (label : String) (A : SubMeasurement α) (B : SubMeasurement β) :
    SubMeasurement (α × β) where
  name := label
  outcomeOperator := fun | (a, b) => operatorMul (B.outcomeOperator b) (A.outcomeOperator a)
  totalOperator := operatorMul B.totalOperator A.totalOperator

/-- Tensor-product bridge `A_a ⊗ B_b`. -/
noncomputable def tensorProductSubMeasurement {α β : Type*}
    (label : String) (A : SubMeasurement α) (B : SubMeasurement β) :
    SubMeasurement (α × β) where
  name := label
  outcomeOperator := fun ab =>
    match ab with
    | (a, b) =>
        operatorMul (leftTensor (A.outcomeOperator a)) (rightTensor (B.outcomeOperator b))
  totalOperator := operatorMul (leftTensor A.totalOperator) (rightTensor B.totalOperator)

/-- Recover the sampled point from a diagonal-line/parameter sample. -/
def sampledPointFromDiagonalQuestion (params : Parameters)
    (q : PointDiagonalLineQuestion params) : Point params :=
  q.1.pointAt q.2

/-- Recover the two sampled points from a shared diagonal-line sample. -/
def sampledPointPairFromSharedDiagonalQuestion (params : Parameters)
    (q : PointPairDiagonalLineQuestion params) : PointPairQuestion params :=
  (q.1.pointAt q.2.1, q.1.pointAt q.2.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I`. -/
noncomputable def pointMeasurementProductLeft (params : Parameters)
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointPairQuestion params) (PointPairOutcome params) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeasurement
    let Av := (strategy.pointMeasurement uv.2).toSubMeasurement
    leftPlacedSubMeasurement <|
      orderedProductSubMeasurement
        s!"pointComm.left({Au.name},{Av.name})" Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I`. -/
noncomputable def pointMeasurementProductRight (params : Parameters)
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointPairQuestion params) (PointPairOutcome params) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeasurement
    let Av := (strategy.pointMeasurement uv.2).toSubMeasurement
    leftPlacedSubMeasurement <|
      reversedProductSubMeasurement
        s!"pointComm.right({Au.name},{Av.name})" Au Av

/-- Distribution obtained by sampling a diagonal line together with a parameter on that line. -/
def pointWithDiagonalLineDistribution (params : Parameters) :
    Distribution (PointDiagonalLineQuestion params) where
  name := s!"pointWithDiagonalLine({params.m},{params.q})"

/-- Distribution obtained by sampling a diagonal line together with two parameters on it. -/
def pointPairSharedDiagonalLineDistribution (params : Parameters) :
    Distribution (PointPairDiagonalLineQuestion params) where
  name := s!"pointPairSharedDiagonalLine({params.m},{params.q})"

/-- The point measurement, reindexed by a sampled diagonal line and a parameter on it. -/
def sampledPointMeasurement (params : Parameters)
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointDiagonalLineQuestion params) (Fq params) :=
  fun q =>
    (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeasurement

/-- Evaluate the diagonal-line measurement at the sampled parameter. -/
noncomputable def sampledDiagonalLineEvaluation (params : Parameters)
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointDiagonalLineQuestion params) (Fq params) :=
  fun q =>
    postprocess ((strategy.diagonalMeasurement q.1).toSubMeasurement) (fun f => f q.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLine (params : Parameters)
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointPairDiagonalLineQuestion params) (PointPairOutcome params) :=
  fun q =>
    pointMeasurementProductLeft params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The reversed point product `(A^v_b A^u_a) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLineReversed (params : Parameters)
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointPairDiagonalLineQuestion params) (PointPairOutcome params) :=
  fun q =>
    pointMeasurementProductRight params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The mixed bridge `A^u_a ⊗ L^ℓ_[f(v)=b]`. -/
noncomputable def pointDiagonalLineMixedProductLeft (params : Parameters)
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointPairDiagonalLineQuestion params) (PointPairOutcome params) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Au := (strategy.pointMeasurement (ℓ.pointAt tu)).toSubMeasurement
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    tensorProductSubMeasurement
      s!"pointComm.mixedLeft({Au.name},{Lv.name})" Au Lv

/-- The bridge `I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])`. -/
noncomputable def diagonalLineProductOrdered (params : Parameters)
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointPairDiagonalLineQuestion params) (PointPairOutcome params) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    rightPlacedSubMeasurement <|
      orderedProductSubMeasurement
        s!"pointComm.lineOrdered({Lu.name},{Lv.name})" Lu Lv

/-- The swapped bridge `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b])`. -/
noncomputable def diagonalLineProductReversed (params : Parameters)
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointPairDiagonalLineQuestion params) (PointPairOutcome params) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    -- BUG: this is identical to diagonalLineProductOrdered, needs fix (see PR #46 review)
    rightPlacedSubMeasurement <|
      orderedProductSubMeasurement
        s!"pointComm.lineReversed({Lu.name},{Lv.name})" Lu Lv

/-- The mixed bridge `A^v_b ⊗ L^ℓ_[f(u)=a]`. -/
noncomputable def pointDiagonalLineMixedProductRight (params : Parameters)
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointPairDiagonalLineQuestion params) (PointPairOutcome params) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Av := (strategy.pointMeasurement (ℓ.pointAt tv)).toSubMeasurement
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    { name := s!"pointComm.mixedRight({Av.name},{Lu.name})"
      outcomeOperator := fun ab =>
        operatorMul (leftTensor (Av.outcomeOperator ab.2))
          (rightTensor (Lu.outcomeOperator ab.1))
      totalOperator :=
        operatorMul (leftTensor Av.totalOperator)
          (rightTensor Lu.totalOperator) }

/-- The intermediate consistency loss coming from the `m`-restricted diagonal-lines test. -/
def restrictedDiagonalLinesConsistencyError (params : Parameters) (gamma : Error) : Error :=
  gamma * (params.m : Error)

/-- The approximation loss obtained from `prop:simeq-to-approx`. -/
def pointDiagonalLineApproxError (params : Parameters) (gamma : Error) : Error :=
  2 * restrictedDiagonalLinesConsistencyError params gamma

/-- The displayed commutativity error from `thm:commutativity-points`. -/
def commutativityPointsError (params : Parameters) (gamma : Error) : Error :=
  32 * gamma * (params.m : Error)

end MIPStarRE.LDT.Section10CommutativityPoints
