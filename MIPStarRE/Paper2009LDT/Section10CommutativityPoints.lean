import MIPStarRE.Paper2009LDT.Section9SelfImprovement

/-!
Matching scaffold for Section 10 of the low individual degree paper in
`references/ldt-paper/commutativity-points.tex`.
-/

namespace MIPStarRE.Paper2009LDT.Section10CommutativityPoints

open MIPStarRE.Paper2009LDT

abbrev PointPairQuestion (params : Parameters) := Point params × Point params
abbrev PointPairOutcome (params : Parameters) := Fq params × Fq params

/-- Placeholder family encoding the ordered product `A_a^u A_b^v`. -/
def pointMeasurementProductLeft (params : Parameters)
    (_strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointPairQuestion params) (PointPairOutcome params) :=
  fun _ => { name := s!"pointComm.left({params.m},{params.q},{params.d})" }

/-- Placeholder family encoding the reversed product `A_b^v A_a^u`. -/
def pointMeasurementProductRight (params : Parameters)
    (_strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (PointPairQuestion params) (PointPairOutcome params) :=
  fun _ => { name := s!"pointComm.right({params.m},{params.q},{params.d})" }

/-- The displayed commutativity error from `thm:commutativity-points`. -/
def commutativityPointsError (params : Parameters) (gamma : Error) : Error :=
  32 * gamma * (params.m : Error)

/-- Output package for `thm:commutativity-points`. -/
structure CommutativityPointsStatement (params : Parameters)
    (strategy : SymmetricStrategy params)
    (_eps _delta gamma : Error) : Prop where
  pointwiseCommutation :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (pointMeasurementProductLeft params strategy)
      (pointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma)

/-- `thm:commutativity-points`. -/
theorem commutativityPoints
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    CommutativityPointsStatement params strategy eps delta gamma := by
  sorry

end MIPStarRE.Paper2009LDT.Section10CommutativityPoints
