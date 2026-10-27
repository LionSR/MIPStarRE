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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

open LIDT
/-!
# Scalar Bernoulli polynomial helpers for pasting

Purely scalar inequalities used by the matrix Chernoff comparison.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine_le_scalarBernoulliTail
    (theta : _root_.LIDT.MIPStarRE.LDT.Error) (k degree : ℕ)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : _root_.LIDT.MIPStarRE.LDT.Error)) / theta ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error))
    {p : _root_.LIDT.MIPStarRE.LDT.Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta
      (Real.exp (-((theta ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error)) / 2)) p ≤
        _root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail k degree p := by sorry
