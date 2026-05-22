import MIPStarRE.LDT.Test.StrategyBiProj.Measurements

/-!
# Two-Space Projective Strategies: Same-Space Projection Lemmas

This module contains the same-space-to-two-space projection lemmas.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace SameSpaceProjStrat

/-! Projection lemmas keep the same-space-to-two-space embedding transparent.
They are deliberately definitional: `SameSpaceProjStrat` extends the general
paper-faithful `ProjStrat`, so Lean's generated `toProjStrat` parent accessor is
the canonical forgetful map. -/

/-- Source-level alias for Lean's generated `toProjStrat` parent accessor.

The actual parent projection comes from the `extends ProjStrat params ι ι` clause
on `SameSpaceProjStrat`; this alias gives blueprint/checkdecl tooling a named
source declaration for the same forgetful map. -/
def toGeneralProjStrat {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) : ProjStrat params ι ι :=
  strategy.toProjStrat

@[simp] theorem toGeneralProjStrat_eq_toProjStrat {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toGeneralProjStrat = strategy.toProjStrat :=
  rfl

@[simp] theorem toProjStrat_state {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.state = strategy.state :=
  rfl

@[simp] theorem toProjStrat_isNormalized {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.isNormalized = strategy.isNormalized :=
  rfl

@[simp] theorem toProjStrat_pointMeasurementA {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.pointMeasurementA = strategy.pointMeasurementA :=
  rfl

@[simp] theorem toProjStrat_axisParallelMeasurementA {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.axisParallelMeasurementA = strategy.axisParallelMeasurementA :=
  rfl

@[simp] theorem toProjStrat_diagonalMeasurementA {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.diagonalMeasurementA = strategy.diagonalMeasurementA :=
  rfl

@[simp] theorem toProjStrat_pointMeasurementB {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.pointMeasurementB = strategy.pointMeasurementB :=
  rfl

@[simp] theorem toProjStrat_axisParallelMeasurementB {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.axisParallelMeasurementB = strategy.axisParallelMeasurementB :=
  rfl

@[simp] theorem toProjStrat_diagonalMeasurementB {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.diagonalMeasurementB = strategy.diagonalMeasurementB :=
  rfl

end SameSpaceProjStrat


end MIPStarRE.LDT
