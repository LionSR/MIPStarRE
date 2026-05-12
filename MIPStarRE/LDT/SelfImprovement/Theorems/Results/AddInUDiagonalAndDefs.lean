import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.Selection
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.Residual
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.ScalarChain

/-!
# Diagonal add-in-u specialization and CS chain definitions

Compatibility module for the diagonal add-in-`u` selection, off-diagonal residual
estimates, and scalar-chain endpoint identities used in the self-improvement
helper strong-self-consistency argument.

The implementation is split into:

- `Selection` for the diagonal selection and point-sandwich endpoint identities;
- `Residual` for the off-diagonal residual quantities and estimates;
- `ScalarChain` for the selected and diagonal Q₀--Q₄ scalar chains.

## References

- `references/ldt-paper/self_improvement.tex` lines 247--252, 455--468
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/
