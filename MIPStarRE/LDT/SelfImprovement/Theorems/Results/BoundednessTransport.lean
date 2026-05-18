import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport.Decomposition
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport.PointConsistency
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport.PointConsistencyLiteral
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport.BoundednessGap
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport.Agreement

/-!
# Final-fields projective-residual boundedness transport

This file re-exports the boundedness-transport submodules.  The original
monolithic file was split for issue #1647.

## Submodules

- `BoundednessTransport.Decomposition` contains the helper-agreement and
  off-diagonal decomposition identities.
- `BoundednessTransport.PointConsistency` contains the natural point-consistency
  transports.
- `BoundednessTransport.PointConsistencyLiteral` contains the corresponding
  literal-threshold transports.
- `BoundednessTransport.BoundednessGap` contains the helper boundedness-gap,
  data-processing transport, and final boundedness constructors.
- `BoundednessTransport.Agreement` preserves the old helper-agreement import
  path.

## References

- `references/ldt-paper/self_improvement.tex` lines 435, 612--613, 742--755
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/
