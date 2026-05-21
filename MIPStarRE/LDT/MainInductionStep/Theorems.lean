import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementAssembly
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds
import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities
import MIPStarRE.LDT.MainInductionStep.Theorems.StageDataConstructors
import MIPStarRE.LDT.MainInductionStep.Theorems.AvgSliceErrors
import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly
import MIPStarRE.LDT.MainInductionStep.Theorems.MainTheorems
import MIPStarRE.LDT.MainInductionStep.Theorems.SmallErrorRecordStatement
import MIPStarRE.LDT.MainInductionStep.Theorems.SourceTheorems

/-!
# Section 6 — Theorem imports

Compatibility module re-exporting all induction-step theorem leaf modules:

- `SelfImprovementAssembly`: ordinary and answer-valued self-improvement assembly,
  including the Section 6 pasting theorem
- `InductionParameterBounds`: parameter-bound helpers for `mainInductionError < 1`
- `RestrictedProbabilities`: restricted failure probability bookkeeping
- `StageDataConstructors`: constructors for the structured induction data and
  skeletal assembly
- `AvgSliceErrors`: averaged slice-error bounds
- `PastingAssembly`: pasting assembly and `assembleAveragedPastingData`
- `MainTheorems`: corrected large-`k` top-level induction theorems
- `SmallErrorRecordStatement`: record-valued successor construction frontier
- `SourceTheorems`: printed source-range theorems and public restriction data

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/
