import MIPStarRE.Paper2009LDT.Section7ExpansionHypercubeGraph

/-!
Matching scaffold for Section 8 of the low individual degree paper in
`references/ldt-paper/expansion.tex`.

This file records the named lemmas controlling the global variance of the points
measurements. Their statements are intentionally lightweight placeholders for the
matching pass.
-/

namespace MIPStarRE.Paper2009LDT.Section8GlobalVariance

open MIPStarRE.Paper2009LDT

abbrev AxisParallelLineQuestion (params : Parameters) := AxisParallelLine params × Point params
abbrev PointPairQuestion (params : Parameters) := Point params × Point params

/-- Placeholder family for the two line-answer evaluations in `lem:generalize-b`. -/
def generalizeBLeftFamily (params : Parameters)
    (_strategy : SymmetricStrategy params) (_G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (AxisParallelLineQuestion params) Unit :=
  fun _ => { name := s!"generalizeB.left({params.m},{params.q},{params.d})" }

/-- Placeholder family for the restricted polynomial answer in `lem:generalize-b`. -/
def generalizeBRightFamily (params : Parameters)
    (_strategy : SymmetricStrategy params) (_G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (AxisParallelLineQuestion params) Unit :=
  fun _ => { name := s!"generalizeB.right({params.m},{params.q},{params.d})" }

/-- Placeholder family for the local-variance comparison along one hypercube edge. -/
def localVarianceLeftFamily (params : Parameters)
    (_strategy : SymmetricStrategy params) (_G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun _ => { name := s!"localVariance.left({params.m},{params.q},{params.d})" }

/-- Placeholder family for the opposite endpoint in the local-variance comparison. -/
def localVarianceRightFamily (params : Parameters)
    (_strategy : SymmetricStrategy params) (_G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun _ => { name := s!"localVariance.right({params.m},{params.q},{params.d})" }

/-- Placeholder family for the global-variance comparison on two independent points. -/
def globalVarianceLeftFamily (params : Parameters)
    (_strategy : SymmetricStrategy params) (_G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun _ => { name := s!"globalVariance.left({params.m},{params.q},{params.d})" }

/-- Placeholder family for the reversed global-variance comparison. -/
def globalVarianceRightFamily (params : Parameters)
    (_strategy : SymmetricStrategy params) (_G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun _ => { name := s!"globalVariance.right({params.m},{params.q},{params.d})" }

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
      (uniformDistribution (AxisParallelLineQuestion params))
      (generalizeBLeftFamily params strategy G)
      (generalizeBRightFamily params strategy G)
      (generalizeBError params)

/-- Output package for `lem:local-variance-of-points`. -/
structure LocalVarianceOfPointsStatement (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) (eps delta : Error) : Prop where
  edgewiseVarianceBound :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (localVarianceLeftFamily params strategy G)
      (localVarianceRightFamily params strategy G)
      (localVarianceOfPointsError params eps delta)

/-- Output package for `lem:global-variance-of-points`. -/
structure GlobalVarianceOfPointsStatement (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) (eps delta : Error) : Prop where
  globalVarianceBound :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (globalVarianceLeftFamily params strategy G)
      (globalVarianceRightFamily params strategy G)
      (globalVarianceOfPointsError params eps delta)

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
