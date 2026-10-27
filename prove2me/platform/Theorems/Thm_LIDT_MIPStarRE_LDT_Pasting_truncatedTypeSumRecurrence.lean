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

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

open LIDT
/-!
# Section 12 pasting: Bernoulli truncated sums

Truncated type sums and their one-step recurrence.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Bernoulli recurrence weights -/

theorem LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSumRecurrence
    (G : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hGpsd : 0 ≤ G)
    (hGleOne : G ≤ 1)
    (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType tailLen) :
    (_root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail)ᴴ = _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail ∧
      0 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail ∧
      _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail ≤ 1 ∧
      _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d (prefixLen + 1) τtail =
        _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit true τtail) * G +
          _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit false τtail) * (1 - G) := by sorry
