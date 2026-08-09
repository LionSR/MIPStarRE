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
