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
- `MainTheorems.Base` and `MainTheorems.Successor`: corrected large-`k`
  top-level induction theorems
- `SourceTheorems`: corrected source-boundary theorem and public restriction data

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/
