import MIPStarRE.LDT.Basic.SubMeasurementFamilies

/-!
# Measurement lift infrastructure for the low individual degree test

Measurement-level tensor-factor lifts built from the submeasurement placement API.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- Lift a measurement to the left tensor factor of `ιA × ιB`. -/
def leftLiftedMeasurement {α : Type*}
    {ιA ιB : Type*} [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α ιA) :
    Measurement α (ιA × ιB) :=
  { toSubMeas := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
    total_eq_one := by
      calc
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).total
            = leftTensor (ι₂ := ιB) A.total := by
              rfl
        _ = leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA) := by
              rw [A.total_eq_one]
        _ = 1 := by
              exact leftTensor_one (ι₁ := ιA) (ι₂ := ιB) }

/-- Lift a measurement to the right tensor factor of `ιA × ιB`. -/
def rightLiftedMeasurement {α : Type*}
    {ιA ιB : Type*} [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α ιB) :
    Measurement α (ιA × ιB) :=
  { toSubMeas := rightPlacedSubMeas (ιA := ιA) A.toSubMeas
    total_eq_one := by
      calc
        (rightPlacedSubMeas (ιA := ιA) A.toSubMeas).total
            = rightTensor (ι₁ := ιA) A.total := by
              rfl
        _ = rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB) := by
              rw [A.total_eq_one]
        _ = 1 := by
              exact rightTensor_one (ι₁ := ιA) (ι₂ := ιB) }

end MIPStarRE.LDT
