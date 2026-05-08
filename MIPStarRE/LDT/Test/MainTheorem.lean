import MIPStarRE.LDT.Test.MainTheorem.ClassicalAndBase
import MIPStarRE.LDT.Test.MainTheorem.OrdinaryRestriction
import MIPStarRE.LDT.Test.MainTheorem.AnswerValuedRestriction
import MIPStarRE.LDT.Test.MainTheorem.ErrorScalars
import MIPStarRE.LDT.Test.MainTheorem.RoleRegister
import MIPStarRE.LDT.Test.MainTheorem.UnsymmetrizedTargets
import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency
import MIPStarRE.LDT.Test.MainTheorem.CompletionTransport
import MIPStarRE.LDT.Test.MainTheorem.OrthonormalizationData
import MIPStarRE.LDT.Test.MainTheorem.DiagonalCompletion
import MIPStarRE.LDT.Test.MainTheorem.NativeTargets
import MIPStarRE.LDT.Test.MainTheorem.MainFormal

/-!
# Section 3 — Main theorem

Compatibility barrel that imports the twelve split modules under
`MIPStarRE.LDT.Test.MainTheorem` and presents them as a single import target.
The assembly proves `thm:main-formal` (`\Cref{thm:main-formal}`), the main
theorem of Section 3, following the proof given in
`references/ldt-paper/inductive_step.tex`.  The argument symmetrizes a
non-symmetric strategy with a role register, applies the main induction
(`thm:main-induction`), unsymmetrizes the resulting measurement, makes it
projective via orthonormalization (`lem:orthonormalization-main-lemma`) and
completion (`prop:completing-to-measurement`), and collects the three final
consistency bounds (`eq:one-goal`, `eq:another-goal`, `eq:third-goal`).

The imported modules carry the split proof assembly:
* `ClassicalAndBase` — classical soundness and the base case `m = 1`
* `OrdinaryRestriction` — ordinary `x`-restricted successor route
* `AnswerValuedRestriction` — answer-valued `x`-restricted successor route
* `ErrorScalars` — the Section 3 error cascade `σ, ζ₁, …, ζ₄`
* `RoleRegister` — role-register measurement and branch residual
* `UnsymmetrizedTargets` — factor-two unsymmetrization and projective assembly
* `ProjectiveConsistency` — projective-consistency transport through lines 154–172
* `CompletionTransport` — post-role completion transport residuals
* `OrthonormalizationData` — orthonormalization and completion hypotheses
* `DiagonalCompletion` — diagonal consistency inputs for completing each side
* `NativeTargets` — the final `ζ₄` native consistency targets
* `MainFormal` — base, successor, and final branch assembly for `thm:main-formal`

## References

* Paper: `references/ldt-paper/inductive_step.tex`, proof of
  `\Cref{thm:main-formal}` (lines 27–239).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `\label{thm:main-formal}`; and
  `blueprint/src/chapter/ch10_induction.tex`,
  `\label{rem:main-formal-lean-residual-packages}`.
-/
