import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.Core
import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.BadLine
import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.BadMass
import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.Averaging
import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.HBError
import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.Final

/-!
# Section 12 pasting: line interpolation bridge helpers

Compatibility module re-exporting the line-interpolation leaves:
`Core`, `BadLine`, `BadMass`, `Averaging`, `HBError`, and `Final`.

Interpolation-support, bad-line, bad-mass, and distribution-comparison helpers used by the line-
consistency chain.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/
