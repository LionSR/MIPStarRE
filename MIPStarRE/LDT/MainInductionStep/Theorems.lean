import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementBridge
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds
import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities
import MIPStarRE.LDT.MainInductionStep.Theorems.PackageConstructors
import MIPStarRE.LDT.MainInductionStep.Theorems.AvgSliceErrors
import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly
import MIPStarRE.LDT.MainInductionStep.Theorems.MainTheorems

/-!
# Section 6 — Theorem imports

Compatibility module re-exporting all induction-step theorem leaf modules:

- `SelfImprovementBridge`: ordinary and answer-valued self-improvement bridge API,
  with the Section 6 pasting theorem
- `InductionParameterBounds`: parameter-bound helpers for `mainInductionError < 1`
- `RestrictedProbabilities`: restricted failure probability bookkeeping
- `PackageConstructors`: constructors for the structured induction data and
  skeletal assembly
- `AvgSliceErrors`: averaged slice-error bounds
- `PastingAssembly`: pasting assembly and `assembleAveragedPastingInput`
- `MainTheorems`: top-level induction theorems

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/
