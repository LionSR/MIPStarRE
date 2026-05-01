import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Bridges.QSDD
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Bridges.Closeness

/-!
# Full-slice bridges and main result

Compatibility barrel re-exporting the full-slice bridge leaves:

- `Bridges.QSDD`: `qSDDOp` expansion, averaging symmetry, and
  `fullSliceCommutation_qSDDOp_avg_eq`.
- `Bridges.Closeness`: scalar↔tensor `closenessOfIP` bridges and assembled
  `ABAB` transport bounds.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

## References

- arXiv:2009.12982, Section 11.
-/
