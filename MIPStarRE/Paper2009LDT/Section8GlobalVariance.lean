import MIPStarRE.Paper2009LDT.Section7ExpansionHypercubeGraph

/-!
Matching scaffold for Section 8 of the low individual degree paper in
`references/ldt-paper/expansion.tex`.

This file records the named lemmas controlling the global variance of the points
measurements. The declarations now expose the operator families and variance
quantities that the paper bounds, while still leaving proofs to a later pass.
-/

namespace MIPStarRE.Paper2009LDT.Section8GlobalVariance

open MIPStarRE.Paper2009LDT
open MIPStarRE.Paper2009LDT.Section7ExpansionHypercubeGraph

abbrev AxisParallelLineQuestion (params : Parameters) := AxisParallelLine params × Point params
abbrev PointPairQuestion (params : Parameters) := Point params × Point params

/-- The distribution of an axis-parallel line together with a point queried on it. -/
def axisParallelLineQuestionDistribution (params : Parameters) :
    Distribution (AxisParallelLineQuestion params) :=
  { name := s!"axisLinePoint({params.m},{params.q},{params.d})" }

/--
The operator family `u ↦ A^u_{g(u)}` appearing in the local/global variance
bounds for the points measurement against a polynomial submeasurement `G`.
-/
def pointConditionedOperator (params : Parameters)
    (strategy : SymmetricStrategy params) (G : SubMeasurement (Polynomial params))
    (u : Point params) : Operator :=
  { name := s!"{(strategy.pointMeasurement u).toSubMeasurement.name}[g(u)|{G.name}]" }

/-- The full conditioned operator family `u ↦ A^u_{g(u)}`. -/
def pointConditionedOperatorFamily (params : Parameters)
    (strategy : SymmetricStrategy params) (G : SubMeasurement (Polynomial params)) :
    Point params → Operator :=
  fun u => pointConditionedOperator params strategy G u

/-- The local variance of the conditioned points family. -/
noncomputable def pointConditionedLocalVariance (params : Parameters)
    (strategy : SymmetricStrategy params) (G : SubMeasurement (Polynomial params)) : Error :=
  localVariance params (pointConditionedOperatorFamily params strategy G) strategy.state

/-- The global variance of the conditioned points family. -/
noncomputable def pointConditionedGlobalVariance (params : Parameters)
    (strategy : SymmetricStrategy params) (G : SubMeasurement (Polynomial params)) : Error :=
  globalVariance params (pointConditionedOperatorFamily params strategy G) strategy.state

/--
The left-hand family in `lem:generalize-b`, representing the event
`B^ℓ_[f(u)=g(u)]` against the polynomial submeasurement `G`.
-/
def generalizeBLeftFamily (params : Parameters)
    (strategy : SymmetricStrategy params) (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (AxisParallelLineQuestion params) Unit :=
  fun qu =>
    let ℓ := qu.1
    let u := qu.2
    let lineName := (strategy.axisParallelMeasurement ℓ).toSubMeasurement.name
    let pointName := (strategy.pointMeasurement u).toSubMeasurement.name
    { name := s!"{lineName}.agreeAt[{pointName}|{G.name}]" }

/--
The right-hand family in `lem:generalize-b`, representing the event
`B^ℓ_[f = g|_ℓ]` against the polynomial submeasurement `G`.
-/
def generalizeBRightFamily (params : Parameters)
    (strategy : SymmetricStrategy params) (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (AxisParallelLineQuestion params) Unit :=
  fun qu =>
    let ℓ := qu.1
    let u := qu.2
    let lineName := (strategy.axisParallelMeasurement ℓ).toSubMeasurement.name
    let pointName := (strategy.pointMeasurement u).toSubMeasurement.name
    { name := s!"{G.name}.lineRestriction[{lineName}|{pointName}]" }

/--
The left-hand family in the local-variance comparison, representing
`A^u_[g(u)] ⊗ (G_g)^{1/2}` on a hypercube edge `(u,v)`.
-/
def localVarianceLeftFamily (params : Parameters)
    (strategy : SymmetricStrategy params) (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun uv =>
    { name := s!"{(strategy.pointMeasurement uv.1).toSubMeasurement.name}.polyEval[{G.name}]" }

/--
The right-hand family in the local-variance comparison, representing
`A^v_[g(v)] ⊗ (G_g)^{1/2}` on the same edge `(u,v)`.
-/
def localVarianceRightFamily (params : Parameters)
    (strategy : SymmetricStrategy params) (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun uv =>
    { name := s!"{(strategy.pointMeasurement uv.2).toSubMeasurement.name}.polyEval[{G.name}]" }

/--
The left-hand family in the global-variance comparison on two independent points.
-/
def globalVarianceLeftFamily (params : Parameters)
    (strategy : SymmetricStrategy params) (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun uv =>
    let pointName := (strategy.pointMeasurement uv.1).toSubMeasurement.name
    { name := s!"{pointName}.globalPolyEval[{G.name}]" }

/--
The right-hand family in the global-variance comparison on two independent points.
-/
def globalVarianceRightFamily (params : Parameters)
    (strategy : SymmetricStrategy params) (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun uv =>
    let pointName := (strategy.pointMeasurement uv.2).toSubMeasurement.name
    { name := s!"{pointName}.globalPolyEval[{G.name}]" }

/-- The displayed error term in `lem:generalize-b`. -/
noncomputable def generalizeBError (params : Parameters) : Error :=
  ((params.m : Error) * (params.d : Error)) / (params.q : Error)

/-- The displayed error term in `lem:local-variance-of-points`. -/
noncomputable def localVarianceOfPointsError (params : Parameters) (eps delta : Error) : Error :=
  24 * (eps + delta + generalizeBError params)

/-- The displayed error term in `lem:global-variance-of-points`. -/
noncomputable def globalVarianceOfPointsError (params : Parameters) (eps delta : Error) : Error :=
  24 * (params.m : Error) * (eps + delta + generalizeBError params)

/-- Output package for `lem:generalize-b`. -/
structure GeneralizeBStatement (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) : Prop where
  lineRestrictionComparison :
    StateDependentDistanceRel strategy.state
      (axisParallelLineQuestionDistribution params)
      (generalizeBLeftFamily params strategy G)
      (generalizeBRightFamily params strategy G)
      (generalizeBError params)

/-- Output package for `lem:local-variance-of-points`. -/
structure LocalVarianceOfPointsStatement (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) (eps delta : Error) : Prop where
  edgewiseVarianceBound :
    StateDependentDistanceRel strategy.state
      (rerandomizeCoord params)
      (localVarianceLeftFamily params strategy G)
      (localVarianceRightFamily params strategy G)
      (localVarianceOfPointsError params eps delta)
  localVarianceBound :
    pointConditionedLocalVariance params strategy G ≤
      localVarianceOfPointsError params eps delta

/-- Output package for `lem:global-variance-of-points`. -/
structure GlobalVarianceOfPointsStatement (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) (eps delta : Error) : Prop where
  globalVarianceDistance :
    StateDependentDistanceRel strategy.state
      (independentPointPair params)
      (globalVarianceLeftFamily params strategy G)
      (globalVarianceRightFamily params strategy G)
      (globalVarianceOfPointsError params eps delta)
  expansionTransfer :
    pointConditionedGlobalVariance params strategy G ≤
      (params.m : Error) * pointConditionedLocalVariance params strategy G
  globalVarianceBound :
    pointConditionedGlobalVariance params strategy G ≤
      globalVarianceOfPointsError params eps delta

/-- `lem:generalize-b`. -/
lemma generalizeB
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params)) :
    GeneralizeBStatement params strategy G := by
  sorry

/-- `lem:local-variance-of-points`. -/
lemma localVarianceOfPoints
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params)) :
    LocalVarianceOfPointsStatement params strategy G eps delta := by
  sorry

/-- `lem:global-variance-of-points`. -/
lemma globalVarianceOfPoints
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params)) :
    GlobalVarianceOfPointsStatement params strategy G eps delta := by
  sorry

end MIPStarRE.Paper2009LDT.Section8GlobalVariance
