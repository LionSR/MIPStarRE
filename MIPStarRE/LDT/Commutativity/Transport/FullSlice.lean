import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Averages
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.ZeroBounds
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Bridges

/-!
# Section 11 commutativity: full-slice transport

Barrel module re-exporting the full-slice transport sub-modules:

- `Averages`: zero-family definition, scalar/tensor averages, data indices
- `ZeroBounds`: zero-family SDDOpRel bounds
- `Machinery`: sandwich-tensor expansion, collision residuals,
  marginalization, normalization conditions, self-consistency
- `Bridges`: scalar-to-tensor closenessOfIP bridges, main result

Architecture: The public API is scalar (e.g. `fullSliceABAAvg`,
`evaluatedSliceABABAvg`).  Internal tensor-form intermediates (e.g.
`fullSliceBABAtensorAvg`) carry the operator-level Schwartz–Zippel and
`closenessOfIP` arguments.  The scalar↔tensor bridge chain lives in
`Main/Auxiliary.lean`.  See `docs/decisions/713-scalar-tensor-decision.md`
for the Option 3 (hybrid) decision record.

## References

- arXiv:2009.12982, Section 11.
-/
