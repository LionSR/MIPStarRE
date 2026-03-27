import MIPStarRE.LDT.SelfImprovement.Theorems

/-!
Matching scaffold for Section 10 of the low individual degree paper in
`references/ldt-paper/commutativity-points.tex`.
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

abbrev PointPairOutcome (params : Parameters) := Fq params × Fq params
abbrev PointDiagonalLineQuestion (params : Parameters) := DiagonalLine params × Fq params
abbrev PointPairDiagonalLineQuestion (params : Parameters) :=
  DiagonalLine params × (Fq params × Fq params)

/-- Place a submeasurement on the left tensor factor of `dA * dB`. -/
def leftPlacedSubMeas {α : Type*} {dA dB : ℕ} (A : SubMeas α dA) :
    SubMeas α (dA * dB) where
  name := s!"{A.name}.left"
  outcome := fun a => leftTensor (d₂ := dB) (A.outcome a)
  total := leftTensor (d₂ := dB) A.total

/-- Place a submeasurement on the right tensor factor of `dA * dB`. -/
def rightPlacedSubMeas {α : Type*} {dA dB : ℕ} (A : SubMeas α dB) :
    SubMeas α (dA * dB) where
  name := s!"{A.name}.right"
  outcome := fun a => rightTensor (d₁ := dA) (A.outcome a)
  total := rightTensor (d₁ := dA) A.total

/-- Ordered product of two paper-local submeasurements on the same tensor factor. -/
noncomputable def orderedProductSubMeas {α β : Type*}
    (label : String) (A : SubMeas α d) (B : SubMeas β d) :
    SubMeas (α × β) d where
  name := label
  outcome := fun | (a, b) => opMul (A.outcome a) (B.outcome b)
  total := opMul A.total B.total

/-- Reversed product of two paper-local submeasurements on the same tensor factor. -/
noncomputable def reversedProductSubMeas {α β : Type*}
    (label : String) (A : SubMeas α d) (B : SubMeas β d) :
    SubMeas (α × β) d where
  name := label
  outcome := fun | (a, b) => opMul (B.outcome b) (A.outcome a)
  total := opMul B.total A.total

/-- Tensor-product bridge `A_a ⊗ B_b` on the bipartite space `d * d`. -/
noncomputable def tensorProductSubMeas {α β : Type*} {d : ℕ}
    (label : String) (A : SubMeas α d) (B : SubMeas β d) :
    SubMeas (α × β) (d * d) where
  name := label
  outcome := fun ab =>
    match ab with
    | (a, b) =>
        opMul (leftTensor (d₂ := d) (A.outcome a))
              (rightTensor (d₁ := d) (B.outcome b))
  total := opMul (leftTensor (d₂ := d) A.total)
                 (rightTensor (d₁ := d) B.total)

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
    (strategy : SymStrat params d) :
    IdxSubMeas (PointPairQuestion params) (PointPairOutcome params) (d * d) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    leftPlacedSubMeas (dB := d) <|
      orderedProductSubMeas
        s!"pointComm.left({Au.name},{Av.name})" Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I` on the bipartite space `d * d`. -/
noncomputable def pointMeasurementProductRight (params : Parameters)
    (strategy : SymStrat params d) :
    IdxSubMeas (PointPairQuestion params) (PointPairOutcome params) (d * d) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    leftPlacedSubMeas (dB := d) <|
      reversedProductSubMeas
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
    (strategy : SymStrat params d) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) d :=
  fun q =>
    (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas

/-- Evaluate the diagonal-line measurement at the sampled parameter. -/
noncomputable def sampledDiagonalLineEvaluation (params : Parameters)
    (strategy : SymStrat params d) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) d :=
  fun q =>
    postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLine (params : Parameters)
    (strategy : SymStrat params d) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (d * d) :=
  fun q =>
    pointMeasurementProductLeft params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The reversed point product `(A^v_b A^u_a) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLineReversed (params : Parameters)
    (strategy : SymStrat params d) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (d * d) :=
  fun q =>
    pointMeasurementProductRight params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The mixed bridge `A^u_a ⊗ L^ℓ_[f(v)=b]` on the bipartite space `d * d`. -/
noncomputable def pointDiagonalLineMixedProductLeft (params : Parameters)
    (strategy : SymStrat params d) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (d * d) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Au := (strategy.pointMeasurement (ℓ.pointAt tu)).toSubMeas
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    tensorProductSubMeas
      s!"pointComm.mixedLeft({Au.name},{Lv.name})" Au Lv

/-- The bridge `I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])` on the bipartite space `d * d`. -/
noncomputable def diagonalLineProductOrdered (params : Parameters)
    (strategy : SymStrat params d) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (d * d) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    rightPlacedSubMeas (dA := d) <|
      orderedProductSubMeas
        s!"pointComm.lineOrdered({Lu.name},{Lv.name})" Lu Lv

/-- The swapped bridge `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b])` on the bipartite space `d * d`. -/
noncomputable def diagonalLineProductReversed (params : Parameters)
    (strategy : SymStrat params d) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (d * d) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    -- BUG: this is identical to diagonalLineProductOrdered, needs fix (see PR #46 review)
    rightPlacedSubMeas (dA := d) <|
      orderedProductSubMeas
        s!"pointComm.lineReversed({Lu.name},{Lv.name})" Lu Lv

/-- The mixed bridge `A^v_b ⊗ L^ℓ_[f(u)=a]` on the bipartite space `d * d`. -/
noncomputable def pointDiagonalLineMixedProductRight (params : Parameters)
    (strategy : SymStrat params d) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (d * d) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Av := (strategy.pointMeasurement (ℓ.pointAt tv)).toSubMeas
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    { name := s!"pointComm.mixedRight({Av.name},{Lu.name})"
      outcome := fun ab =>
        opMul (leftTensor (d₂ := d) (Av.outcome ab.2))
          (rightTensor (d₁ := d) (Lu.outcome ab.1))
      total :=
        opMul (leftTensor (d₂ := d) Av.total)
          (rightTensor (d₁ := d) Lu.total) }

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
