-- Generated from MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/Witness.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 9 — Canonical matrix SDP witnesses

This module contains the optimal-witness structures extracted from the canonical
matrix SDP.  The preceding canonical module proves the block-diagonal algebra,
including the dual slack identities and saturation of the slack block.  This
file records the paper-form optimal pair and the measurement witnesses used by
the self-improvement comparison.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix

/-- Paper origin: `references/ldt-paper/self_improvement.tex:82-88`
(`\label{lem:sdp}`, `\label{eq:slater}`);
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex` (SDP gap).

Matrix-level witness for an optimal SDP pair. -/
structure MatrixSdpOptimalWitness (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  primalTotalEqOne :
    ∑ g : Polynomial params, T.effect g = 1
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g
  strongDuality :
    matrixSdpPrimalObjective params model T = matrixSdpDualObjective model Z
  complementarySlackness :
    ∀ g : Polynomial params,
      T.effect g * Z = T.effect g * matrixAveragedPointOperator params model g

/-- Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`), with complementary slackness from
`eq:complementary-slackness` at line 179; matrix realization of
`SdpStatementWithSlackness`.

Matrix-level statement of the strong-duality output for the SDP.

This is the concrete matrix analogue of `SdpStatementWithSlackness`: it does
not assert that the explicit strict feasible witnesses are optimal.  Instead it
records the kind of optimal witness obtained from the paper's
Slater/strong-duality argument.  The feasible primal variables in the canonical
SDP remain submeasurements; this statement stores the selected saturated
optimal witness as a complete matrix measurement.

Grounded by: #1230. -/
structure MatrixSdpStatementWithSlackness (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) : Prop where
  witness :
    ∃ T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∃ Z : MatrixOperator model.space,
        MatrixSdpOptimalWitness params model T.toSubmeasurement Z

/-- The concrete complementary-slackness equation `T_g Z = T_g A_g`. -/
def matrixSdpComplementarySlacknessEquation (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : Prop :=
  T.effect g * Z = T.effect g * matrixAveragedPointOperator params model g

namespace MatrixSdpOptimalWitness



/-- An optimal matrix SDP witness whose primal total is the identity determines
a complete matrix measurement. -/
noncomputable def primalMeasurement {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) :
    MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne T.effect T.pos h.primalTotalEqOne

@[simp] theorem primalMeasurement_effect {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) (g : Polynomial params) :
    h.primalMeasurement.effect g = T.effect g :=
  rfl

/-- The stored complementary-slackness equation, expressed through the named
matrix-level predicate. -/
theorem complementarySlacknessEquation {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) (g : Polynomial params) :
    matrixSdpComplementarySlacknessEquation params model T Z g := by
  exact h.complementarySlackness g

end MatrixSdpOptimalWitness

namespace MatrixSdpStatementWithSlackness



end MatrixSdpStatementWithSlackness

end MIPStarRE.LDT.SelfImprovement

end

end LIDT
