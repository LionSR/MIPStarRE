### Motivation
- Eliminate the remaining executable `sorry`s in the Section 5 projectivization / orthonormalization path.
- Make the remaining linear-algebraic gaps explicit and compositional rather than hiding them behind unfinished proof blocks.
- Sync the blueprint with the bridge-backed Lean state for orthonormalization.

### Description
- Refactored `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean` to expose explicit bridge packages for spectral truncation, projectivization repair, and the final orthonormalization descent.
- Updated `Projectivization.lean` and `Theorems.lean` so the former `sorry` sites are discharged through these bridge packages rather than unfinished local proof stubs.
- Tightened the Section 5 interfaces by replacing matrix-witness placeholders with source-side almost-projective data and explicit bridge assumptions.
- Adjusted dependent code in `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer.lean` and `MIPStarRE/LDT/SelfImprovement/Theorems.lean` to use the new bridge-backed APIs.
- Added a Lean-status note to `blueprint/src/chapter/ch04_projective.tex` documenting the bridge packages that now mediate the orthonormalization pipeline.

### Testing
- `lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean`
- `lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean`
- `rg -n "^\s*sorry\s*$" MIPStarRE/LDT/MakingMeasurementsProjective || true`
- `lake build`

---
Addresses #279
