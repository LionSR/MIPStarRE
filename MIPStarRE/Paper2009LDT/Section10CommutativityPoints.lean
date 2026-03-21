import MIPStarRE.Paper2009LDT.Section9SelfImprovement

/-!
Matching scaffold for Section 10 of the low individual degree paper in
`references/ldt-paper/commutativity-points.tex`.
-/

namespace MIPStarRE.Paper2009LDT.Section10CommutativityPoints

open MIPStarRE.Paper2009LDT

/-- Output package for `thm:commutativity-points`. -/
structure CommutativityPointsStatement (params : Parameters)
    (_strategy : SymmetricStrategy params)
    (_eps _delta _gamma : Error) : Prop where
  pointwiseCommutation : True

/-- `thm:commutativity-points`. -/
theorem commutativityPoints
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    CommutativityPointsStatement params strategy eps delta gamma := by
  sorry

end MIPStarRE.Paper2009LDT.Section10CommutativityPoints
