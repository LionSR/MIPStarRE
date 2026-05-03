import MIPStarRE.LDT.Basic.ParametersBase

/-!
# Square-root bounds for error estimates

Small reusable inequalities for square roots of nonnegative error terms.
-/

namespace MIPStarRE.LDT

/-- Subadditivity of the square root on nonnegative error terms. -/
theorem sqrt_add_le_add_sqrt {x y : Error} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  refine Real.sqrt_le_iff.mpr ?_
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- Three-term subadditivity of the square root on nonnegative error terms. -/
theorem sqrt_add3_le_add3_sqrt {x y z : Error}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x + y + z) ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
  calc
    Real.sqrt (x + y + z) = Real.sqrt ((x + y) + z) := by ring_nf
    _ ≤ Real.sqrt (x + y) + Real.sqrt z := sqrt_add_le_add_sqrt (add_nonneg hx hy) hz
    _ ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
      nlinarith [sqrt_add_le_add_sqrt hx hy, Real.sqrt_nonneg z]

end MIPStarRE.LDT
