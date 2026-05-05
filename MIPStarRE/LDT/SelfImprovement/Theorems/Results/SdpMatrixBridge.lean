import MIPStarRE.LDT.SelfImprovement.MatrixRealization
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements

/-!
# Matrix SDP bridge

This file compares the concrete matrix-level SDP slackness interface with the
abstract self-improvement SDP statement interface.

The bridge is intentionally conditional: the matrix optimal witness supplies
dual feasibility and complementary slackness, while the reduced abstract
interface used by the current helper proof also asks for the additional bound
`I ≤ Z`.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- View a matrix submeasurement as the paper-local `SubMeas` structure. -/
noncomputable def matrixSubmeasurementToSubMeas {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixSubmeasurement Outcome H) : SubMeas Outcome H.carrier where
  outcome := M.effect
  total := MIPStarRE.Quantum.Submeasurement.total M
  outcome_pos := M.pos
  sum_eq_total := rfl
  total_le_one := by
    simpa [MIPStarRE.Quantum.Submeasurement.total] using M.sum_le_one

/-- The matrix SDP realization canonically associated to a strategy. -/
noncomputable def matrixSdpRealizationOfStrategy (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) : MatrixSdpRealization params where
  space := {
    carrier := ι
    instFintype := inferInstance
    instDecidableEq := inferInstance
    instNonempty := by
      rcases strategy.isNormalized.nonempty with ⟨x⟩
      exact ⟨x.1⟩
  }
  state := {
    matrix := 0
    positive := by simp
  }
  pointMeasurement := fun u => {
    effect := fun a => (strategy.pointMeasurement u).toSubMeas.outcome a
    pos := fun a => (strategy.pointMeasurement u).toSubMeas.outcome_pos a
    sum_le_one := by
      rw [(strategy.pointMeasurement u).toSubMeas.sum_eq_total]
      exact le_of_eq (strategy.pointMeasurement u).total_eq_one
  }

/-- The matrix averaged point operator for the canonical strategy realization
is the abstract averaged point operator. -/
theorem matrixAveragedPointOperator_ofStrategy (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) (g : Polynomial params) :
    matrixAveragedPointOperator params
        (matrixSdpRealizationOfStrategy params strategy) g =
      averagedPointOperator params strategy g := by
  unfold matrixAveragedPointOperator averagedPointOperator
  refine averageOperatorOverDistribution_congr _ _ _ ?_
  intro u
  simp [matrixAveragedPointOperatorContribution,
    pointConditionedOutcomeOperatorAtPolynomial, matrixSdpRealizationOfStrategy]

/-- The matrix dual slack operator for the canonical strategy realization is
the abstract dual slack operator. -/
theorem matrixSdpDualSlackOperator_ofStrategy (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) :
    matrixSdpDualSlackOperator params
        (matrixSdpRealizationOfStrategy params strategy) Z g =
      sdpDualSlackOperator params strategy Z g := by
  rw [matrixSdpDualSlackOperator, sdpDualSlackOperator,
    matrixAveragedPointOperator_ofStrategy]

namespace MatrixSdpOptimalWitness

/-- A matrix optimal witness gives an abstract SDP optimal pair with slackness,
provided the additional reduced-interface bound `I ≤ Z` is supplied.

The extra hypothesis is not part of `MatrixSdpOptimalWitness`; this theorem
therefore isolates the precise additional fact needed to pass from the
matrix-level strong-duality output to the current abstract helper interface. -/
theorem toSdpOptimalPairWithSlackness_of_dualDominatesIdentity
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params)
      (matrixSdpRealizationOfStrategy params strategy).space}
    {Z : MIPStarRE.Quantum.Op ι}
    (h : MatrixSdpOptimalWitness params
      (matrixSdpRealizationOfStrategy params strategy) T Z)
    (hdom : (1 : MIPStarRE.Quantum.Op ι) ≤ Z) :
    SdpOptimalPairWithSlackness params strategy (matrixSubmeasurementToSubMeas T) Z where
  toSdpOptimalPair := {
    primalTotalOperator := by
      simpa [matrixSubmeasurementToSubMeas, MIPStarRE.Quantum.Submeasurement.total] using
        h.primalTotalEqOne
    dualPositive := h.dualPositive
    dualDominatesIdentity := hdom
    dualFeasible := by
      intro g
      simpa [matrixSdpDualSlackOperator_ofStrategy] using h.dualFeasible g
  }
  complementarySlackness := by
    intro g
    simpa [matrixSubmeasurementToSubMeas, sdpComplementarySlacknessEquation,
      matrixSdpComplementarySlacknessEquation, matrixAveragedPointOperator_ofStrategy] using
        h.complementarySlacknessEquation g

end MatrixSdpOptimalWitness

namespace MatrixSdpStatementWithSlackness

/-- A matrix strong-duality statement for the canonical strategy realization
implies the abstract slackness statement, assuming the chosen matrix optimal
dual witness also dominates the identity.

The dominance hypothesis records the remaining mismatch between the matrix SDP
output and the reduced abstract interface used by the helper proof.  It is
asked only for the concrete witness supplied by `h.witness`, not for all
possible matrix optimal witnesses. -/
theorem toSdpStatementWithSlackness_of_dualDominatesIdentity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (h : MatrixSdpStatementWithSlackness params
      (matrixSdpRealizationOfStrategy params strategy))
    (hdom :
      let hTZ := Classical.choose_spec h.witness
      let Z := Classical.choose hTZ
      (1 : MIPStarRE.Quantum.Op ι) ≤ Z) :
    SdpStatementWithSlackness params strategy := by
  let T := Classical.choose h.witness
  let hTZ := Classical.choose_spec h.witness
  let Z := Classical.choose hTZ
  have hopt :
      MatrixSdpOptimalWitness params
        (matrixSdpRealizationOfStrategy params strategy) T Z :=
    Classical.choose_spec hTZ
  exact ⟨matrixSubmeasurementToSubMeas T, Z,
    hopt.toSdpOptimalPairWithSlackness_of_dualDominatesIdentity hdom⟩

end MatrixSdpStatementWithSlackness

end MIPStarRE.LDT.SelfImprovement
