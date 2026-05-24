import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.Witness
import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.Saturated
import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.StrongDuality

/-!
# Section 9 — Matrix realization

Compatibility module for the concrete finite-dimensional matrix realization of
the self-improvement SDP data.  The base SDP data, canonical block SDP layer,
canonical optimal-witness packages, and saturated zero-slack canonical interface
are re-exported from the corresponding `MatrixRealization` submodules; this
file keeps the matrix add-in-u transfer interface at the original import path.

## References

- `references/ldt-paper/self_improvement.tex`
-/
