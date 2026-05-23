import MIPStarRE.LDT.Test.MainTheorem.RoleRegister.Core

/-!
# Role-register witnesses

Compatibility module for the role-register witnesses used by the `mainFormal`
assembly.

Earlier versions of this module exported branch records for ordinary
and answer-valued successor cases.  Those records allowed the final theorem
assembly to be supplied with recursive slice witnesses and self-improvement
inputs that are not hypotheses of `thm:main-formal`.  They have been removed.
The paper-theorem route now obtains the role-register witness from
`MainInductionStep.mainInduction` through
`MainFormalRoleInductionWitness.ofMainInduction`.  The corrected Section 6
successor theorem is now proved, so this module no longer records a final-theorem
successor hypothesis.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  symmetrization with role register and factor-two block estimates
  (lines 97--108).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{rem:main-formal-lean-witness-records}`.
-/
