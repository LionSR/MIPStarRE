import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

open LIDT
/-!
# Quantum states and tensor placement for the low individual degree test

Core quantum-state definitions together with tensor-placement operators.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT













open LIDT.MIPStarRE.LDT.PureState

theorem LIDT.MIPStarRE.LDT.PureState.toQuantumState_isNormalized {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : _root_.LIDT.MIPStarRE.LDT.PureState ι) :
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι).IsNormalized := by sorry
