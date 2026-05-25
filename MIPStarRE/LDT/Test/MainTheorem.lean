import MIPStarRE.LDT.Test.MainTheorem.AnswerValuedRestriction
import MIPStarRE.LDT.Test.MainTheorem.MainFormal

/-!
# Section 3 — Main theorem

Compatibility module that imports the split modules under
`MIPStarRE.LDT.Test.MainTheorem` and presents them as a single import target.
The assembly proves the source theorem labelled `thm:main-formal`, the main
theorem of Section 3, following the proof given in
`references/ldt-paper/inductive_step.tex`.  The argument symmetrizes a
non-symmetric strategy with a role register, applies the main induction
(`thm:main-induction`), unsymmetrizes the resulting measurement, makes it
projective via orthonormalization (`lem:orthonormalization-main-lemma`) and
completion (`prop:completing-to-measurement`), and collects the three final
consistency bounds recorded in the blueprint as
`eq:final-left-point-consistency`, `eq:final-right-point-consistency`, and
`eq:completed-polynomial-consistency`.

The imported modules carry the split proof assembly:
* `ClassicalAndBase` — classical soundness and the base case `m = 1`
* `AnswerValuedRestriction` — answer-valued `x`-restricted successor route
* `ErrorScalars` — the Section 3 error cascade `σ, ζ₁, …, ζ₄`
* `RoleRegister.Core` — role-register measurement and branch witness
* `UnsymmetrizedTargets` — factor-two unsymmetrization and projective assembly
* `ProjectiveConsistency` — projective-consistency transport through lines 154–172
* `CompletionTransport` — post-role completion transport witnesses
* `OrthonormalizationData` — orthonormalization and completion data
* `DiagonalCompletion` — diagonal consistency inputs for completing each side
* `NativeTargets` — the final `ζ₄` native consistency targets
* `MainFormal` — base, successor, and final branch assembly for `thm:main-formal`
* `SourceRoleRegister.Final` — two-space source-boundary role-register handoff

## References

* Paper: `references/ldt-paper/inductive_step.tex`, proof of
  `thm:main-formal` (lines 26–236).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `\label{thm:main-formal}`; and
  `blueprint/src/chapter/ch10_induction.tex`,
  `\label{rem:main-formal-lean-witness-records}`.
-/
