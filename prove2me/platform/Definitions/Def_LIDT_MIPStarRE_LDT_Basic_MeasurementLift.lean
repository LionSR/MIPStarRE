-- Generated from MIPStarRE/LDT/Basic/MeasurementLift.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/-!
# Measurement lift infrastructure for the low individual degree test

Measurement-level tensor-factor lifts built from the submeasurement placement API.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- Lift a measurement to the left tensor factor of `ιA × ιB`. -/
def leftLiftedMeasurement {α : Type*}
    {ιA ιB : Type*} [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α ιA) :
    Measurement α (ιA × ιB) :=
  { toSubMeas := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
    total_eq_one :=
      Eq.trans rfl <|
        Eq.trans (congrArg (leftTensor (ι₂ := ιB)) A.total_eq_one)
          (leftTensor_one (ι₁ := ιA) (ι₂ := ιB)) }

/-- Lift a measurement to the right tensor factor of `ιA × ιB`. -/
def rightLiftedMeasurement {α : Type*}
    {ιA ιB : Type*} [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α ιB) :
    Measurement α (ιA × ιB) :=
  { toSubMeas := rightPlacedSubMeas (ιA := ιA) A.toSubMeas
    total_eq_one :=
      Eq.trans rfl <|
        Eq.trans (congrArg (rightTensor (ι₁ := ιA)) A.total_eq_one)
          (rightTensor_one (ι₁ := ιA) (ι₂ := ιB)) }

end MIPStarRE.LDT

end

end LIDT
