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

/-- Output package for `lem:generalize-b`. -/
structure GeneralizeBStatement (params : Parameters)
    (_strategy : SymmetricStrategy params)
    (_G : SubMeasurement (Polynomial params)) : Prop where
  lineRestrictionComparison : True

/-- Output package for `lem:local-variance-of-points`. -/
structure LocalVarianceOfPointsStatement (params : Parameters)
    (_strategy : SymmetricStrategy params)
    (_G : SubMeasurement (Polynomial params)) : Prop where
  edgewiseVarianceBound : True

/-- Output package for `lem:global-variance-of-points`. -/
structure GlobalVarianceOfPointsStatement (params : Parameters)
    (_strategy : SymmetricStrategy params)
    (_G : SubMeasurement (Polynomial params)) : Prop where
  globalVarianceBound : True

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
    LocalVarianceOfPointsStatement params strategy G := by
  sorry

/-- `lem:global-variance-of-points`. -/
lemma globalVarianceOfPoints
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params)) :
    GlobalVarianceOfPointsStatement params strategy G := by
  sorry

end MIPStarRE.Paper2009LDT.Section8GlobalVariance
