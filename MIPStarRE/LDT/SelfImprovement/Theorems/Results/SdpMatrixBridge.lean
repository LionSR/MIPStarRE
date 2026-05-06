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

Mathlib 4.28.0 provides the underlying finite-dimensional matrix order and
convex-cone infrastructure used throughout this project, but it does not yet
provide a ready-made finite-dimensional semidefinite-programming strong-duality
theorem with complementary slackness in the shape needed here.  Consequently
this file does not reprove SDP duality.  It only transports the project-local
matrix witness `MatrixSdpStatementWithSlackness` to the abstract Section 9
interface.  If a Mathlib SDP theorem is later available, its output should
replace the project-local witness while the bridge below should remain the
comparison with the self-improvement notation.

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

/-- The point-measurement part of the matrix SDP realization associated to a strategy.

The present bridge only uses the point-measurement fields of
`MatrixSdpRealization`, through `matrixAveragedPointOperator` and
`matrixSdpDualSlackOperator`.  The state field is therefore filled by the zero
positive operator.  This construction should not be used for state-dependent
matrix expressions such as `matrixExpectation`; such expressions would compute
with the zero operator rather than with `strategy.state`. -/
noncomputable def matrixSdpPointRealizationOfStrategy (params : Parameters)
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

/-- The averaged point operator for the point-measurement matrix realization is
the abstract averaged point operator. -/
theorem matrixAveragedPointOperator_ofPointRealization (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) (g : Polynomial params) :
    matrixAveragedPointOperator params
        (matrixSdpPointRealizationOfStrategy params strategy) g =
      averagedPointOperator params strategy g := by
  unfold matrixAveragedPointOperator averagedPointOperator
  refine averageOperatorOverDistribution_congr _ _ _ ?_
  intro u
  simp [matrixAveragedPointOperatorContribution,
    pointConditionedOutcomeOperatorAtPolynomial, matrixSdpPointRealizationOfStrategy]

/-- The matrix dual slack operator for the point-measurement matrix realization
is the abstract dual slack operator. -/
theorem matrixSdpDualSlackOperator_ofPointRealization (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) :
    matrixSdpDualSlackOperator params
        (matrixSdpPointRealizationOfStrategy params strategy) Z g =
      sdpDualSlackOperator params strategy Z g := by
  rw [matrixSdpDualSlackOperator, sdpDualSlackOperator,
    matrixAveragedPointOperator_ofPointRealization]

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
      (matrixSdpPointRealizationOfStrategy params strategy).space}
    {Z : MIPStarRE.Quantum.Op ι}
    (h : MatrixSdpOptimalWitness params
      (matrixSdpPointRealizationOfStrategy params strategy) T Z)
    (hdom : (1 : MIPStarRE.Quantum.Op ι) ≤ Z) :
    SdpOptimalPairWithSlackness params strategy (matrixSubmeasurementToSubMeas T) Z where
  toSdpOptimalPair := {
    primalTotalOperator := by
      simpa [matrixSubmeasurementToSubMeas, MIPStarRE.Quantum.Submeasurement.total] using
        h.primalTotalEqOne
    dualDominatesIdentity := hdom
    dualFeasible := by
      intro g
      simpa [matrixSdpDualSlackOperator_ofPointRealization] using h.dualFeasible g
  }
  complementarySlackness := by
    intro g
    simpa [matrixSubmeasurementToSubMeas, sdpComplementarySlacknessEquation,
      matrixSdpComplementarySlacknessEquation,
      matrixAveragedPointOperator_ofPointRealization] using
        h.complementarySlacknessEquation g

end MatrixSdpOptimalWitness

namespace MatrixSdpStatementWithSlackness

/-- A matrix strong-duality statement for the point-measurement realization of
a strategy implies the abstract slackness statement, assuming the chosen matrix
optimal dual witness also dominates the identity.

The dominance hypothesis records the remaining mismatch between the matrix SDP
output and the reduced abstract interface used by the helper proof.  It is
asked only for the concrete witness supplied by `h.witness`, not for all
possible matrix optimal witnesses. -/
theorem toSdpStatementWithSlackness_of_dualDominatesIdentity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (h : MatrixSdpStatementWithSlackness params
      (matrixSdpPointRealizationOfStrategy params strategy))
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
        (matrixSdpPointRealizationOfStrategy params strategy) T Z :=
    Classical.choose_spec hTZ
  exact ⟨matrixSubmeasurementToSubMeas T, Z,
    hopt.toSdpOptimalPairWithSlackness_of_dualDominatesIdentity hdom⟩

end MatrixSdpStatementWithSlackness

namespace MatrixSdpStatementWithSlacknessAndDominance

/-- A matrix strong-duality statement with a dominance-carrying optimal dual
witness gives the abstract SDP statement with complementary slackness. -/
theorem toSdpStatementWithSlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (h : MatrixSdpStatementWithSlacknessAndDominance params
      (matrixSdpPointRealizationOfStrategy params strategy)) :
    SdpStatementWithSlackness params strategy := by
  obtain ⟨T, Z, hopt⟩ := h.witness
  exact ⟨matrixSubmeasurementToSubMeas T, Z,
    hopt.toMatrixSdpOptimalWitness.toSdpOptimalPairWithSlackness_of_dualDominatesIdentity
      hopt.dualDominatesIdentity⟩

end MatrixSdpStatementWithSlacknessAndDominance

/-- Canonical block-SDP feasibility, objective equality, complementary
slackness, and dual dominance give the abstract Section 9 SDP statement.

This is the canonical-block version of
`MatrixSdpStatementWithSlacknessAndDominance.toSdpStatementWithSlackness`,
specialized to the point-measurement matrix realization of a strategy.  It
uses the block-diagonal extraction theorem from `MatrixRealization.lean` to
replace a feasible canonical primal matrix by the associated paper
submeasurement, and then transports the resulting matrix witness to the
abstract `SdpStatementWithSlackness` interface. -/
theorem sdpStatementWithSlackness_of_canonicalFeasibleComplementarySlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (hX : MatrixSdpCanonicalPrimalFeasible params
      (matrixSdpPointRealizationOfStrategy params strategy) X)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params
            (matrixSdpPointRealizationOfStrategy params strategy) * X)) =
        matrixSdpDualObjective
          (matrixSdpPointRealizationOfStrategy params strategy) Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z -
            matrixSdpCanonicalObjectiveOperator params
              (matrixSdpPointRealizationOfStrategy params strategy)) =
        0)
    (hOneLe : (1 : MIPStarRE.Quantum.Op ι) ≤ Z) :
    SdpStatementWithSlackness params strategy :=
  MatrixSdpStatementWithSlacknessAndDominance.toSdpStatementWithSlackness
    params strategy
    (matrixSdpStatementWithSlacknessAndDominance_of_canonicalFeasibleComplementarySlackness
      params (matrixSdpPointRealizationOfStrategy params strategy) X hX Z
      hdual hstrong hcanonical hOneLe)

/-- Canonical block-SDP feasibility, objective equality, complementary
slackness, and dual dominance give the displayed abstract SDP measurement
witness.

This theorem is the direct paper-form extraction from canonical block data at
the point-measurement realization of a strategy.  It first transports the
canonical data to `SdpStatementWithSlackness`, then reads the complete
measurement and dual inequalities from the abstract slackness statement. -/
theorem sdpMeasurementWitness_of_canonicalFeasibleComplementarySlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (hX : MatrixSdpCanonicalPrimalFeasible params
      (matrixSdpPointRealizationOfStrategy params strategy) X)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params
            (matrixSdpPointRealizationOfStrategy params strategy) * X)) =
        matrixSdpDualObjective
          (matrixSdpPointRealizationOfStrategy params strategy) Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z -
            matrixSdpCanonicalObjectiveOperator params
              (matrixSdpPointRealizationOfStrategy params strategy)) =
        0)
    (hOneLe : (1 : MIPStarRE.Quantum.Op ι) ≤ Z) :
    ∃ T : Measurement (Polynomial params) ι,
      0 ≤ Z ∧
      (1 : MIPStarRE.Quantum.Op ι) ≤ Z ∧
      (∀ g : Polynomial params, 0 ≤ sdpDualSlackOperator params strategy Z g) ∧
      ∀ g : Polynomial params,
        sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g := by
  let model := matrixSdpPointRealizationOfStrategy params strategy
  let Tsub := matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX
  let hopt :
      MatrixSdpOptimalWitnessWithDominance params model Tsub Z :=
    matrixSdpOptimalWitnessWithDominance_of_canonicalFeasibleComplementarySlackness
      params model X hX Z hdual hstrong hcanonical hOneLe
  let hpair :
      SdpOptimalPairWithSlackness params strategy (matrixSubmeasurementToSubMeas Tsub) Z :=
    hopt.toMatrixSdpOptimalWitness.toSdpOptimalPairWithSlackness_of_dualDominatesIdentity
      hopt.dualDominatesIdentity
  exact ⟨hpair.primalMeasurement, hpair.toSdpOptimalPair.dualPositive,
    hpair.toSdpOptimalPair.dualDominatesIdentity, hpair.toSdpOptimalPair.dualFeasible,
    hpair.complementarySlackness⟩

end MIPStarRE.LDT.SelfImprovement
