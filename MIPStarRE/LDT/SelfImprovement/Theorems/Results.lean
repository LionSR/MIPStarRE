import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SdpMatrixBridge
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUPointConsistency
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep12
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperSSC
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop

/-!
# Section 9 — Self-improvement theorem wrappers

Reduced theorem wrappers for the self-improvement pipeline.

This module is a compatibility module re-exporting the split leaf modules.
All original declarations remain available under the same namespace.

## Leaf modules

- `CommonHelpers` — shared internal helpers (formerly private)
- `SdpMatrixBridge` — comparison between the matrix-level slackness interface
  and the abstract SDP statement with slackness
- `HelperCompleteness` — input-consistency lower bounds, SDP bridge, `sdp`, `addInU`
- `AddInUDiagonalAndDefs` — diagonal add-in-u specialization, Q₀–Q₄ CS chain defs
- `AddInUPointConsistency` — off-diagonal add-in-u selection infrastructure for
  helper `A`-consistency
- `AddInUStep12` — algebraic alignment and raw CS Step 1/2 bounds
- `AddInUStep34AndTransfer` — variance conversions, factored CS, assembly, transfer
- `HelperSSC` — final helper strong self-consistency obligation construction
- `BoundednessTransport` — off-diagonal decomposition, boundedness gap transport,
  projective-residual estimates
  (`projective_boundedness_gap_le_helper_boundedness_gap`,
  `final_fields_projective_residual_bound_natural`,
  `final_fields_projective_residual_bound`, `final_fields_bounded`)
- `SelfImprovementTop` — `selfImprovement` wrappers and final-fields obligations

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end MIPStarRE.LDT.SelfImprovement
