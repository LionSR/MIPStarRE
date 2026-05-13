import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.FinalFields

/-!
# Residual-domination proof-gap boundary

This compatibility module no longer exports top-level conditional
self-improvement theorems whose hypotheses package the remaining Section 9
work.  The useful local material for the monotone total comparison remains in
`SelfImprovementTop.FinalFields`.  The paper-facing theorem
`selfImprovement` is the place where the missing Section 9 derivation is now
recorded as an explicit `sorry`.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end MIPStarRE.LDT.SelfImprovement
