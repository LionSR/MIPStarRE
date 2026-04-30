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

## References

- arXiv:2009.12982, Section 11.
-/
