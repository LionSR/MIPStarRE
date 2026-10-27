-- Generated from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Mathlib

namespace LIDT

/-!
# Error cascade — envelope and root bounding machinery

Internal helper lemmas for the error-cascade bookkeeping of Step 8.
These provide the step-envelope interpolation (`stepEnvelope`),
monotonicity under denominator enlargement, square-root scaling, and
explicit numeric bounds on various `rpow` and `sqrt` expressions.
All lemmas are technical and should not be part of downstream API.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

/-- A paper-local envelope with exponent `1/n` and decay scale `N`. -/
noncomputable def stepEnvelope (params : Parameters) (k : ℕ) (eps : Error)
    (n N : Error) : Error :=
  Real.rpow eps (1 / n) +
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / n) +
    Real.exp (-((k : Error) / (N * ((params.m : Error) ^ (2 : ℕ)))))





































































end Test

end MIPStarRE.LDT

end

end LIDT
