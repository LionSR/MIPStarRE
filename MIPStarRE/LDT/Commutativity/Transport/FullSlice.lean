import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Averages
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Bridges
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.ZeroBounds

/-!
# Section 11 commutativity: full-slice transport

Compatibility module re-exporting the full-slice transport sub-modules:

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

Import direction: `Averages` is the shared base leaf for FullSlice-specific
Fubini, symmetry, and data-reindexing helpers.  `ZeroBounds`, `Machinery.*`,
and `Bridges.QSDD` depend on that base.  `Bridges.Closeness` depends on
`Averages` plus the two machinery leaves.  FullSlice leaves should not import
these compatibility modules.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API.

## References

- arXiv:2009.12982, Section 11.
-/
