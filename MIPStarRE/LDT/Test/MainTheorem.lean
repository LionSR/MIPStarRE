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
import MIPStarRE.LDT.Test.MainTheorem.MainFormal

/-!
# Section 3 — Main theorem

Compatibility barrel re-exporting the eleven leaves of the split `mainFormal`
assembly.  The leaves split the Section 3 chain by mathematical layer rather
than by paper line number; importing this file is equivalent to importing every
leaf below.

## Main definitions

The public surface of the assembly is unchanged from the pre-split file.  The
top-level result is `MIPStarRE.LDT.Test.mainFormal`
(`MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`), formalising
`thm:main-formal` of `references/ldt-paper/test_definition.tex`.  The supporting
layers are exposed through

* `MainFormalCascadeScalars` and the `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄` cascade
  (`ErrorScalars.lean`);
* the role-register packages `MainFormalRoleMeasurementPackage`,
  `MainFormalRolePackageResidual`, `MainFormalRolePackageBranchResidual`
  (`RoleRegister.lean`);
* the unsymmetrized cascade targets `MainFormalCascadeTargets`,
  `MainFormalCascadeTransportTargets`,
  `MainFormalCascadePreProjectiveSelfConsistency`
  (`UnsymmetrizedTargets.lean`);
* the projective-consistency residuals
  `MainFormalCascadeProjectiveHandoffResidual`,
  `MainFormalCascadeProjectiveEvaluationHandoffResidual`,
  `MainFormalCascadeProjectiveCompletionTransportResidual`
  (`ProjectiveConsistency.lean`);
* the post-role completion transport family
  `MainFormalPostRolePackageCompletionTransportResidual` and its variants
  (`CompletionTransport.lean`);
* the orthonormalization witness data
  `MainFormalPostRolePackageProjectiveCompletionResidual` and the
  diagonal-orthonormalization input/residual pair
  (`OrthonormalizationData.lean`);
* the diagonal-consistency and `ConsRel` completion inputs
  `MainFormalPostRolePackageDiagonalConsistencyInput`,
  `MainFormalPostRolePackageDiagonalSSCInput`,
  `MainFormalPostRolePackageDiagonalCompletionInput`
  (`DiagonalCompletion.lean`);
* the two successor-route families (ordinary in `OrdinaryRestriction.lean`,
  answer-valued in `AnswerValuedRestriction.lean`); and
* the classical wrappers and the base-case bridge in `ClassicalAndBase.lean`.

## References

* `references/ldt-paper/test_definition.tex`, `thm:main-formal` and the
  Section 3 statement of the main theorem.
* `references/ldt-paper/inductive_step.tex`, lines 68–169 — Step 1
  symmetrization, the `mainInductionStep` call, and the full role-register /
  unsymmetrization / projective-completion chain.
* `blueprint/src/chapter/ch10_induction.tex` — blueprint cross-references for
  every public declaration above.
-/
