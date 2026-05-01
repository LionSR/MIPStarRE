import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Averages
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.ZeroBounds
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Bridges

/-!
# Section 11 commutativity: full-slice transport

Barrel module re-exporting the full-slice transport sub-modules:

- `Averages`: zero-family definition, scalar/tensor averages, data indices
- `ZeroBounds`: zero-family SDDOpRel bounds
- `Machinery.Marginalization`: sandwich-tensor expansion, collision residuals,
  and marginalization bounds
- `Machinery.Normalization`: normalization conditions and self-consistency bounds
- `Bridges.QSDD`: `qSDDOp` averaging assembly and scalar commutation identity
- `Bridges.Closeness`: scalar-to-tensor `closenessOfIP` bridges

Architecture: The public API is scalar (e.g. `fullSliceABAAvg`,
`evaluatedSliceABABAvg`).  Internal tensor-form intermediates (e.g.
`fullSliceBABAtensorAvg`) carry the operator-level Schwartz–Zippel and
`closenessOfIP` arguments.  The scalar↔tensor bridge chain lives in
`Main/Auxiliary.lean`.  See `docs/decisions/713-scalar-tensor-decision.md`
for the Option 3 (hybrid) decision record.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API.

## References

- arXiv:2009.12982, Section 11.
-/
