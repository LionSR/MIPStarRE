import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUPointConsistency
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep12
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop

/-!
# Section 9 — Self-improvement theorem wrappers

Reduced theorem wrappers for the self-improvement pipeline.

This module is a compatibility barrel re-exporting the split leaf modules.
All original declarations remain available under the same namespace.

## Leaf modules

- `CommonHelpers` — shared internal helpers (formerly private)
- `HelperCompleteness` — input-consistency lower bounds, SDP bridge, `sdp`, `addInU`
- `AddInUDiagonalAndDefs` — diagonal add-in-u specialization, Q₀–Q₄ CS chain defs
- `AddInUPointConsistency` — off-diagonal add-in-u selection infrastructure for
  helper `A`-consistency
- `AddInUStep12` — algebraic alignment and raw CS Step 1/2 bounds
- `AddInUStep34AndTransfer` — variance conversions, factored CS, assembly, transfer
- `BoundednessTransport` — off-diagonal decomposition, boundedness gap transport,
  projective-residual producers
  (`projective_boundedness_gap_le_helper_boundedness_gap`,
  `final_fields_projective_residual_bound_natural`,
  `final_fields_projective_residual_bound`, `final_fields_bounded`)
- `SelfImprovementTop` — `selfImprovement` wrappers, completeness/self-closeness producers

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
