import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Bridges.Closeness
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Bridges.ClosenessXEval
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Bridges.QSDD

/-!
# Full-slice bridges and main result

Compatibility barrel re-exporting the full-slice bridge leaves:

- `Bridges.QSDD`: `qSDDOp` expansion and
  `fullSliceCommutation_qSDDOp_avg_eq`.
- `Bridges.Closeness`: scalar↔tensor `closenessOfIP` bridges and assembled
  `ABAB` transport bounds.
- `Bridges.ClosenessXEval`: x-evaluated/full-y `closenessOfIP` bridge
  (extracted per #1127).

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

## References

- arXiv:2009.12982, Section 11.
-/
