import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Marginalization
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Normalization

/-!
# Full-slice machinery

Compatibility barrel re-exporting the full-slice machinery leaves:

- `Machinery.Marginalization`: collision residuals, postprocessing expansions,
  and tensor marginalization bounds.
- `Machinery.Normalization`: normalization-condition and self-consistency bounds.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

## References

- arXiv:2009.12982, Section 11.
-/
