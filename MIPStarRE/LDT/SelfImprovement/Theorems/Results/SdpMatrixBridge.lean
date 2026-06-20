import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.Saturated
import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.StrongDuality.Separation
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements

/-!
# Matrix SDP comparison

This file compares the concrete matrix-level SDP slackness interface with the
abstract self-improvement SDP statement interface.

The comparison is intentionally split into two interfaces.  The source-shaped
matrix optimal witness supplies dual feasibility, complementary slackness, and
the saturated canonical slack block needed for the abstract Section 9 statement.
No auxiliary dominance bound `I ≤ Z` is part of this comparison theorem.

Mathlib provides the underlying finite-dimensional matrix order and convex-cone
infrastructure used throughout this project, but it does not yet provide a
ready-made finite-dimensional semidefinite-programming strong-duality theorem
with complementary slackness in the shape needed here.  Consequently this file
does not reprove SDP duality.  It only transports the project-local matrix
witness `MatrixSdpStatementWithSlackness` to the abstract Section 9 interface.
If a Mathlib SDP theorem is later available, its output should replace the
project-local witness while the comparison theorem below should remain the
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

@[simp] theorem matrixSubmeasurementToSubMeas_outcome {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixSubmeasurement Outcome H) (a : Outcome) :
    (matrixSubmeasurementToSubMeas M).outcome a = M.effect a :=
  rfl

@[simp] theorem matrixSubmeasurementToSubMeas_total {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixSubmeasurement Outcome H) :
    (matrixSubmeasurementToSubMeas M).total =
      MIPStarRE.Quantum.Submeasurement.total M :=
  rfl

/-- View a matrix measurement as the paper-local `Measurement` structure. -/
noncomputable def matrixMeasurementToMeasurement {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixMeasurement Outcome H) : Measurement Outcome H.carrier where
  toSubMeas := matrixSubmeasurementToSubMeas M.toSubmeasurement
  total_eq_one := by
    simpa [matrixSubmeasurementToSubMeas, MIPStarRE.Quantum.Submeasurement.total] using
      M.sum_eq_one

@[simp] theorem matrixMeasurementToMeasurement_toSubMeas {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixMeasurement Outcome H) :
    (matrixMeasurementToMeasurement M).toSubMeas =
      matrixSubmeasurementToSubMeas M.toSubmeasurement :=
  rfl

@[simp] theorem matrixMeasurementToMeasurement_outcome {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixMeasurement Outcome H) (a : Outcome) :
    (matrixMeasurementToMeasurement M).outcome a = M.effect a :=
  rfl

/-- The point-measurement part of the matrix SDP realization associated to a strategy.

The present comparison only uses the point-measurement fields of
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
  rfl

/-- Canonical primal-dual data with complementary slackness and zero slack
block.

This is the paper-faithful canonical output still required from the
strong-duality argument in `lem:sdp`: a feasible canonical primal matrix, a
dual-feasible operator with the same objective value, canonical complementary
slackness, and vanishing of the extra slack block \(X_{\mathrm{none},\mathrm{none}}\).
The dominance condition \(I \le Z\) is not part of this structure. -/
structure MatrixSdpCanonicalOptimalPair
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (Z : MatrixOperator model.space) : Prop where
  feasible : MatrixSdpCanonicalPrimalFeasible params model X
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g
  strongDuality :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) =
      matrixSdpDualObjective model Z
  complementarySlackness :
    X * (matrixSdpCanonicalDualOperator params model Z -
          matrixSdpCanonicalObjectiveOperator params model) =
      0
  slackBlock_eq_zero :
    matrixSdpCanonicalDiagonalBlock params model X none = 0

namespace MatrixSdpCanonicalOptimalPair

/-- Build a saturated canonical optimal pair by completing the primal slack
block at `sdpDistinguishedPolynomial params`.

Paper origin: `references/ldt-paper/self_improvement.tex:177-190`.  This is the
source-faithful strong-duality slice: from a feasible canonical primal matrix,
dual feasibility, and primal-dual objective equality, first move the `none`
slack block into the distinguished polynomial block.  The saturated matrix is
still feasible, has zero `none` block, and keeps objective equality by objective
monotonicity plus canonical weak duality.  No auxiliary dominance hypothesis
`I ≤ Z` is used. -/
theorem ofFeasibleStrongDualitySaturateSlackBlock
    {params : Parameters}
    [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    {Z : MatrixOperator model.space}
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) =
        matrixSdpDualObjective model Z) :
    MatrixSdpCanonicalOptimalPair params model
      (matrixSdpCanonicalSaturateSlackBlockMatrix params model X) Z := by
  let Xsat := matrixSdpCanonicalSaturateSlackBlockMatrix params model X
  have hXsat : MatrixSdpCanonicalPrimalFeasible params model Xsat :=
    matrixSdpCanonicalSaturateSlackBlockMatrix_feasible params model X hX
  have hstrongSat :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * Xsat)) =
        matrixSdpDualObjective model Z :=
    matrixSdpCanonicalSaturateSlackBlockMatrix_strongDuality
      params model X hX Z hdual hstrong
  exact {
    feasible := hXsat
    dualFeasible := hdual
    strongDuality := hstrongSat
    complementarySlackness :=
      matrixSdpCanonicalComplementarySlackness_of_strongDuality
        params model Xsat hXsat Z hdual hstrongSat
    slackBlock_eq_zero := by
      simp }

/-- A saturated canonical optimal pair gives the matrix-level slackness
statement without adding the auxiliary dominance condition. -/
theorem toMatrixSdpStatementWithSlackness
    {params : Parameters}
    [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpCanonicalOptimalPair params model X Z) :
    MatrixSdpStatementWithSlackness params model :=
  matrixSdpStatementWithSlackness_of_canonicalFeasibleSaturatedComplementarySlackness
    params model X h.feasible Z h.dualFeasible h.strongDuality
    h.complementarySlackness h.slackBlock_eq_zero

end MatrixSdpCanonicalOptimalPair

namespace MatrixSdpOptimalWitness

/-- A matrix optimal witness gives the abstract slackness-carrying SDP pair. -/
theorem toSdpOptimalPairWithSlackness
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params)
      (matrixSdpPointRealizationOfStrategy params strategy).space}
    {Z : MIPStarRE.Quantum.Op ι}
    (h : MatrixSdpOptimalWitness params
      (matrixSdpPointRealizationOfStrategy params strategy) T Z) :
    SdpOptimalPairWithSlackness params strategy (matrixSubmeasurementToSubMeas T) Z where
  toSdpOptimalPair := {
    primalTotalOperator := by
      change (∑ g : Polynomial params, T.effect g) = (1 : MIPStarRE.Quantum.Op ι)
      exact h.primalTotalEqOne
    dualFeasible := by
      intro g
      rw [← matrixSdpDualSlackOperator_ofPointRealization params strategy Z g]
      exact h.dualFeasible g
  }
  complementarySlackness := by
    intro g
    dsimp [matrixSubmeasurementToSubMeas, sdpComplementarySlacknessEquation,
      sdpDualSlackOperator, matrixSdpPointRealizationOfStrategy]
    rw [← matrixAveragedPointOperator_ofPointRealization params strategy g]
    exact h.complementarySlacknessEquation g

end MatrixSdpOptimalWitness

namespace MatrixSdpStatementWithSlackness

/-- A matrix strong-duality statement for the point-measurement realization of
a strategy implies the abstract slackness statement. -/
theorem toSdpStatementWithSlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (h : MatrixSdpStatementWithSlackness params
      (matrixSdpPointRealizationOfStrategy params strategy)) :
    SdpStatementWithSlackness params strategy := by
  let T := Classical.choose h.witness
  let hTZ := Classical.choose_spec h.witness
  let Z := Classical.choose hTZ
  have hopt :
      MatrixSdpOptimalWitness params
        (matrixSdpPointRealizationOfStrategy params strategy) T Z :=
    Classical.choose_spec hTZ
  exact ⟨matrixSubmeasurementToSubMeas T, Z,
    hopt.toSdpOptimalPairWithSlackness⟩

end MatrixSdpStatementWithSlackness

/-- A saturated canonical optimal pair gives the abstract Section 9 SDP
statement with complementary slackness. -/
theorem sdpStatementWithSlackness_of_canonicalOptimalPair
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (h : MatrixSdpCanonicalOptimalPair params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z) :
    SdpStatementWithSlackness params strategy :=
  MatrixSdpStatementWithSlackness.toSdpStatementWithSlackness
    params strategy h.toMatrixSdpStatementWithSlackness

/-- An existential canonical optimal pair gives the abstract Section 9 SDP
statement with complementary slackness.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 82--190
(`\label{lem:sdp}`), documented by
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

**Source-faithful transport:** This declaration assumes exactly the canonical
optimal-pair output used in the proof of `lem:sdp` and translates it without
strengthening the paper hypotheses.

This is the native transport from the canonical block-SDP output appearing in
the proof of `lem:sdp` to the abstract self-improvement statement.  The
existential hypothesis is precisely the strong-duality and complementary-slackness
output: it supplies a feasible canonical primal matrix, a dual-feasible operator
with equal objective value, canonical complementary slackness, and a vanishing
slack block. -/
theorem sdpStatementWithSlackness_of_exists_canonicalOptimalPair
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (h :
      ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
          (matrixSdpPointRealizationOfStrategy params strategy)),
        ∃ Z : MIPStarRE.Quantum.Op ι,
          MatrixSdpCanonicalOptimalPair params
            (matrixSdpPointRealizationOfStrategy params strategy) X Z) :
    SdpStatementWithSlackness params strategy := by
  rcases h with ⟨X, Z, hpair⟩
  exact sdpStatementWithSlackness_of_canonicalOptimalPair
    params strategy X Z hpair

/-- A saturated canonical optimal pair gives the displayed abstract SDP
measurement witness, without asserting the auxiliary dominance condition
`I ≤ Z`.

This is the direct translation of the paper's saturated strong-duality output
at the point-measurement realization of a strategy.  It avoids the
dominance-carrying matrix interfaces and records only the measurement, dual
feasibility, and complementary-slackness data. -/
theorem sdpMeasurementWitness_of_canonicalOptimalPair
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (h : MatrixSdpCanonicalOptimalPair params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z) :
    ∃ T : Measurement (Polynomial params) ι,
      0 ≤ Z ∧
      (∀ g : Polynomial params, 0 ≤ sdpDualSlackOperator params strategy Z g) ∧
      ∀ g : Polynomial params,
        sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g := by
  let model := matrixSdpPointRealizationOfStrategy params strategy
  let Tsub := matrixSdpCanonicalExtractedPrimalSubmeasurement params model X h.feasible
  let hopt : MatrixSdpOptimalWitness params model Tsub Z :=
    matrixSdpOptimalWitness_of_canonicalFeasibleSaturatedComplementarySlackness
      params model X h.feasible Z h.dualFeasible h.strongDuality
      h.complementarySlackness h.slackBlock_eq_zero
  let T : Measurement (Polynomial params) ι :=
    matrixMeasurementToMeasurement hopt.primalMeasurement
  refine ⟨T, hopt.dualPositive, ?_, ?_⟩
  · intro g
    rw [← matrixSdpDualSlackOperator_ofPointRealization params strategy Z g]
    exact hopt.dualFeasible g
  · intro g
    dsimp [T, matrixMeasurementToMeasurement, matrixSubmeasurementToSubMeas,
      MatrixSdpOptimalWitness.primalMeasurement, sdpComplementarySlacknessEquation,
      sdpDualSlackOperator, matrixSdpPointRealizationOfStrategy, model]
    rw [← matrixAveragedPointOperator_ofPointRealization params strategy g]
    exact hopt.complementarySlacknessEquation g

/-- An existential saturated canonical optimal pair gives the displayed
abstract SDP measurement witness.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 82--190
(`\label{lem:sdp}`), documented by
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

**Source-faithful transport:** This declaration assumes exactly the canonical
optimal-pair output used in the proof of `lem:sdp` and translates it without
strengthening the paper hypotheses.

This is the measurement-level counterpart of
`sdpStatementWithSlackness_of_exists_canonicalOptimalPair`.  It avoids the
dominance-carrying hypotheses and uses only the saturated canonical output
asserted by the paper's strong-duality and complementary-slackness argument. -/
theorem sdpMeasurementWitness_of_exists_canonicalOptimalPair
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (h :
      ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
          (matrixSdpPointRealizationOfStrategy params strategy)),
        ∃ Z : MIPStarRE.Quantum.Op ι,
          MatrixSdpCanonicalOptimalPair params
            (matrixSdpPointRealizationOfStrategy params strategy) X Z) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ Z : MIPStarRE.Quantum.Op ι,
        0 ≤ Z ∧
        (∀ g : Polynomial params, 0 ≤ sdpDualSlackOperator params strategy Z g) ∧
        ∀ g : Polynomial params,
          sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g := by
  rcases h with ⟨X, Z, hpair⟩
  obtain ⟨T, hZpos, hdual, hslack⟩ :=
    sdpMeasurementWitness_of_canonicalOptimalPair params strategy X Z hpair
  exact ⟨T, Z, hZpos, hdual, hslack⟩

/-- Canonical strong-duality and complementary-slackness construction for the
point-measurement realization of the Section 9 SDP.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 82--190
(`\label{lem:sdp}` and the proof using Slater's condition).  The paper first
rewrites the primal and dual SDPs in canonical block form, invokes strong
duality, and then applies complementary slackness to obtain a saturated
canonical optimal pair.

This is the source-faithful construction for the formalized SDP route.  Its
conclusion is the native canonical block-SDP output: a feasible canonical primal
matrix, a dual-feasible operator with equal objective value, canonical
complementary slackness, and a vanishing slack block.  It does not
assume the auxiliary dominance condition `I ≤ Z`; the saturated slack block is
part of the expected strong-duality output.  The matrix statement
`matrixSdpPointRealization_statementWithSlackness` follows by extracting the
diagonal polynomial blocks.

Tracked by issue #1230 and documented in
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`. -/
theorem matrixSdpPointRealization_canonicalOptimalPair
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
        (matrixSdpPointRealizationOfStrategy params strategy)),
      ∃ Z : MIPStarRE.Quantum.Op ι,
        MatrixSdpCanonicalOptimalPair params
          (matrixSdpPointRealizationOfStrategy params strategy) X Z := by
  let model := matrixSdpPointRealizationOfStrategy params strategy
  obtain ⟨X, Z, hX, hdual, hstrong⟩ := matrixSdpCanonicalStrongDuality params model
  refine ⟨matrixSdpCanonicalSaturateSlackBlockMatrix params model X, Z, ?_⟩
  exact MatrixSdpCanonicalOptimalPair.ofFeasibleStrongDualitySaturateSlackBlock
    (params := params) (model := model) (X := X) (Z := Z) hX hdual hstrong

/-- Matrix-level strong-duality and complementary-slackness statement for the
point-measurement realization of the Section 9 SDP.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 82--190
(`\label{lem:sdp}`), documented by
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

**Source-faithful transport:** This declaration is a proved extraction from the
canonical optimal-pair construction for `lem:sdp`; it is not a conditional
replacement for the SDP strong-duality theorem.

This theorem is a proved transport from the native canonical optimal-pair
construction `matrixSdpPointRealization_canonicalOptimalPair`.  It contains no
additional dominance, bridge, residual, or package hypothesis. -/
theorem matrixSdpPointRealization_statementWithSlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    MatrixSdpStatementWithSlackness params
      (matrixSdpPointRealizationOfStrategy params strategy) := by
  rcases matrixSdpPointRealization_canonicalOptimalPair params strategy with
    ⟨X, Z, hpair⟩
  exact hpair.toMatrixSdpStatementWithSlackness

end MIPStarRE.LDT.SelfImprovement
