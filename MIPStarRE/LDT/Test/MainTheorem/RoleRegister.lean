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
`MainFormalRoleInductionWitness.ofMainInduction`; any remaining successor
work is therefore an explicit `sorry` in the Section 6 theorem rather than an
extra hypothesis on the Section 3 theorem.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  symmetrization with role register and factor-two block estimates
  (lines 97--108).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{rem:main-formal-lean-witness-records}`.
-/
