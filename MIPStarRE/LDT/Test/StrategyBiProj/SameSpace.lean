import MIPStarRE.LDT.Test.StrategyBiProj.Measurements

/-!
# Two-Space Projective Strategies: Same-Space Projection Lemmas

This module contains the same-space-to-two-space projection lemmas.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace SameSpaceProjStrat

/-! Projection lemmas keep the same-space-to-two-space embedding transparent.
They are deliberately definitional: `SameSpaceProjStrat` extends the general
paper-faithful `ProjStrat`, so Lean's generated `toProjStrat` parent accessor is
the canonical forgetful map. -/

/-- Source-level alias for Lean's generated `toProjStrat` parent accessor.

The actual parent projection comes from the `extends ProjStrat params ι ι` clause
on `SameSpaceProjStrat`; this alias gives blueprint/checkdecl tooling a named
source declaration for the same forgetful map. -/
def toGeneralProjStrat {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) : ProjStrat params ι ι :=
  strategy.toProjStrat

end SameSpaceProjStrat


end MIPStarRE.LDT
