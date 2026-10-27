-- Generated from MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian

namespace LIDT

namespace MIPStarRE.LDT.Pasting
end MIPStarRE.LDT.Pasting

/-!
# Scalar Bernoulli polynomial helpers for pasting

Purely scalar inequalities used by the matrix Chernoff comparison.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Scalar Bernoulli tail polynomial
`F(p) = ∑_{r=degree+1}^k C(k,r) p^r (1-p)^{k-r}` from
`lem:chernoff-bernoulli-matrix`. -/
noncomputable def scalarBernoulliTail (k degree : ℕ) (p : Error) : Error :=
  ∑ r ∈ Finset.Icc (degree + 1) k,
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))

/-- The complementary lower-tail sum `∑_{r=0}^d C(k,r) p^r (1-p)^(k-r)`. -/
 noncomputable def scalarBernoulliLowerTail (k degree : ℕ) (p : Error) : Error :=
  ∑ r ∈ Finset.range (degree + 1),
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))

/-- The affine lower envelope used in the matrix Chernoff reduction. -/
noncomputable def bernoulliTailLowerAffine (theta c : Error) (p : Error) : Error :=
  (1 - c) - ((1 / (1 - theta)) * (1 - p))



















end MIPStarRE.LDT.Pasting

end

end LIDT
