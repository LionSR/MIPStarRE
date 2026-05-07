import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Averaging
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.MainError
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.SelfImprovement

/-!
# Section 6 — Induction Parameter Bounds

Compatibility barrel for the scalar parameter bounds used in the proof of the
main induction step.  The estimates follow the notation of
`references/ldt-paper/inductive_step.tex`, in particular the error terms
`mainInductionError`, `mainInductionNu`, and `selfImprovementInInductionError`.

The leaf modules are:

- `Preliminaries`: elementary point-line and real-variable estimates;
- `Averaging`: Jensen and slice-conditioning estimates for uniform averages;
- `MainError`: consequences of `mainInductionError < 1`;
- `SelfImprovement`: consequences of `selfImprovementInInductionError ≤ 1`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/
