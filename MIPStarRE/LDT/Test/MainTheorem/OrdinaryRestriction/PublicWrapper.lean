import MIPStarRE.LDT.Test.MainTheorem.OrdinaryRestriction.SliceData

/-!
# Ordinary restricted-slice recursion

This compatibility module used to export a conditional successor wrapper for
the Section 3 proof.  That wrapper assumed a boundary record containing
recursive slice witnesses and a self-improvement input that are not hypotheses
of `thm:main-formal`.  The conditional transition has been removed; the remaining
ordinary successor route exports only the restricted-probability and
recursive-slice targets from the imported modules, while the missing successor
argument is the explicit proof obligation in the Section 6 theorem
theorem.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

end MIPStarRE.LDT
