import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.Core
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.ApproxDelta

/-!
# Preliminary comparison theorems: switch-sandwich preparation

Barrel module re-exporting the concrete switch-sandwich preparation submodules.

## Paper alignment

All definitions in this layer use the bipartite tensor formulation
(`leftTensor` / `rightTensor`) matching the paper's `prop:switch-sandwich`
and `prop:cons-sub-meas`:

* `diagonalSandwichFamily A B` = `A_a ⊗ B_a` (paper's middle term for `cons-sub-meas`)
* `totalSandwichFamily A B` = `A_total ⊗ B_a` (paper's right term)
* Cauchy–Schwarz lemmas `leftTensor_opBounded01`, `opBounded01_hermitian`, etc.
  provide the operator-domain infrastructure for the switch-sandwich gap bounds.

See `Preliminaries/Defs.lean` for the full definition layer.
-/
