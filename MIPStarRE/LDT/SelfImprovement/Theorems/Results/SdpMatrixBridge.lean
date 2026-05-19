import MIPStarRE.LDT.SelfImprovement.MatrixRealization
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements

/-!
# Matrix SDP comparison

This file compares the concrete matrix-level SDP slackness interface with the
abstract self-improvement SDP statement interface.

The comparison is intentionally split into two interfaces.  The source-shaped
matrix optimal witness supplies dual feasibility and complementary slackness.
Some internal routes also retain the auxiliary dominance bound `I ≤ Z`, because
that bound can be used to prove saturation of the extra canonical slack block.
The dominance-carrying interfaces are Lean-only technical routes; they are not
additional hypotheses in the paper SDP statement.

Mathlib 4.28.0 provides the underlying finite-dimensional matrix order and
convex-cone infrastructure used throughout this project, but it does not yet
provide a ready-made finite-dimensional semidefinite-programming strong-duality
theorem with complementary slackness in the shape needed here.  Consequently
this file does not reprove SDP duality.  It only transports the project-local
matrix witness `MatrixSdpStatementWithSlackness` to the abstract Section 9
interface.  If a Mathlib SDP theorem is later available, its output should
replace the project-local witness while the comparison theorem below should remain the
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

/-- Build a saturated canonical optimal pair from feasible primal-dual data,
zero duality gap, and an explicitly vanishing slack block.

The product complementary-slackness equation is derived from zero duality gap by
`matrixSdpCanonicalComplementarySlackness_of_strongDuality`.  Thus the only
remaining Watrous/Slater producer obligations are existence of feasible witnesses
with equal objective values and a saturated slack block. -/
theorem ofFeasibleStrongDualitySlackBlock
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
        matrixSdpDualObjective model Z)
    (hSlack : matrixSdpCanonicalDiagonalBlock params model X none = 0) :
    MatrixSdpCanonicalOptimalPair params model X Z where
  feasible := hX
  dualFeasible := hdual
  strongDuality := hstrong
  complementarySlackness :=
    matrixSdpCanonicalComplementarySlackness_of_strongDuality
      params model X hX Z hdual hstrong
  slackBlock_eq_zero := hSlack

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

/-- Canonical primal-dual data with complementary slackness and auxiliary dual
dominance.

Paper-gap note: `docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

This Lean-only strengthened structure records a feasible canonical primal matrix,
a dual-feasible operator with the same objective value, canonical complementary
slackness, and \(I \le Z\).  The extra dominance field is useful for proving
the saturation condition required by `MatrixSdpCanonicalOptimalPair`; it is not
part of the source SDP assertion. -/
structure MatrixSdpCanonicalOptimalPairWithDominance
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
  dualDominatesIdentity : (1 : MatrixOperator model.space) ≤ Z

namespace MatrixSdpCanonicalOptimalPairWithDominance

/-- A canonical optimal pair with dominance gives the Lean-only
matrix-level slackness statement with dominance. -/
theorem toMatrixSdpStatementWithSlacknessAndDominance
    {params : Parameters}
    [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpCanonicalOptimalPairWithDominance params model X Z) :
    MatrixSdpStatementWithSlacknessAndDominance params model :=
  matrixSdpStatementWithSlacknessAndDominance_of_canonicalFeasibleComplementarySlackness
    params model X h.feasible Z h.dualFeasible h.strongDuality
    h.complementarySlackness h.dualDominatesIdentity

/-- A canonical optimal pair with dominance is saturated.

The paper obtains the vanishing of the extra canonical slack block from
complementary slackness on the `none` block.  In the dominance-carrying
interface this same conclusion follows from the block equation
`X(D(Z)-C)=0` and the lower bound \(I \le Z\). -/
theorem toCanonicalOptimalPair
    {params : Parameters}
    [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpCanonicalOptimalPairWithDominance params model X Z) :
    MatrixSdpCanonicalOptimalPair params model X Z where
  feasible := h.feasible
  dualFeasible := h.dualFeasible
  strongDuality := h.strongDuality
  complementarySlackness := h.complementarySlackness
  slackBlock_eq_zero := by
    let T := matrixSdpCanonicalExtractedPrimalSubmeasurement params model X h.feasible
    have hcanonical_T :
        matrixSdpCanonicalPrimalBlockMatrix params model T *
            (matrixSdpCanonicalDualOperator params model Z -
              matrixSdpCanonicalObjectiveOperator params model) =
          0 :=
      matrixSdpCanonicalPrimalBlockMatrix_extracted_mul_dualSlack_of_canonical
        params model X h.feasible Z h.complementarySlackness
    have hSlackDual : matrixSdpCanonicalSlackOperator params model T * Z = 0 :=
      matrixSdpCanonicalSlack_mul_dual_of_complementarySlackness
        params model T Z hcanonical_T
    have hSlack : matrixSdpCanonicalSlackOperator params model T = 0 :=
      matrixSdpCanonicalSlackOperator_eq_zero_of_mul_dual_eq_zero_of_one_le
        params model T Z hSlackDual h.dualDominatesIdentity
    simpa [T] using
      (matrixSdpCanonicalSlackOperator_extractedPrimalSubmeasurement
        params model X h.feasible).symm.trans hSlack

/-- A canonical optimal pair with dominance also gives the dominance-free
matrix slackness statement after saturating the extra canonical block. -/
theorem toMatrixSdpStatementWithSlackness
    {params : Parameters}
    [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpCanonicalOptimalPairWithDominance params model X Z) :
    MatrixSdpStatementWithSlackness params model :=
  h.toCanonicalOptimalPair.toMatrixSdpStatementWithSlackness

end MatrixSdpCanonicalOptimalPairWithDominance

namespace MatrixSdpCanonicalOptimalPair

/-- Add the auxiliary dominance condition to a saturated canonical optimal
pair.

The saturated structure records the paper-facing strong-duality output: the
primal slack block vanishes, but no condition `I ≤ Z` is imposed on the chosen
dual witness.  This constructor keeps that distinction explicit while allowing
callers that have separately proved `I ≤ Z` to reuse the existing
dominance-carrying interface. -/
theorem withDominance
    {params : Parameters}
    [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpCanonicalOptimalPair params model X Z)
    (hOneLe : (1 : MatrixOperator model.space) ≤ Z) :
    MatrixSdpCanonicalOptimalPairWithDominance params model X Z where
  feasible := h.feasible
  dualFeasible := h.dualFeasible
  strongDuality := h.strongDuality
  complementarySlackness := h.complementarySlackness
  dualDominatesIdentity := hOneLe

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
      simpa [matrixSubmeasurementToSubMeas, MIPStarRE.Quantum.Submeasurement.total] using
        h.primalTotalEqOne
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

/-- A saturated matrix SDP statement for the point realization of a strategy gives
the paper-form abstract SDP measurement witness.

This translation deliberately avoids the auxiliary dominance condition `I ≤ Z`:
it records only the saturated primal measurement, positivity and feasibility of
the dual operator, and the complementary-slackness equations. -/
theorem toSdpMeasurementWitness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (h : MatrixSdpStatementWithSlackness params
      (matrixSdpPointRealizationOfStrategy params strategy)) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ Z : MIPStarRE.Quantum.Op ι,
        0 ≤ Z ∧
        (∀ g : Polynomial params, 0 ≤ sdpDualSlackOperator params strategy Z g) ∧
        ∀ g : Polynomial params,
          sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g := by
  obtain ⟨Tsub, Z, hopt⟩ := h.witness
  have htotal : (matrixSubmeasurementToSubMeas Tsub).total = 1 := by
    simpa [matrixSubmeasurementToSubMeas, MIPStarRE.Quantum.Submeasurement.total] using
      hopt.primalTotalEqOne
  let T : Measurement (Polynomial params) ι :=
    (matrixSubmeasurementToSubMeas Tsub).toMeasurement htotal
  refine ⟨T, Z, hopt.dualPositive, ?_, ?_⟩
  · intro g
    simpa [matrixSdpDualSlackOperator_ofPointRealization] using hopt.dualFeasible g
  · intro g
    simpa [T, matrixSubmeasurementToSubMeas, sdpComplementarySlacknessEquation,
      matrixSdpComplementarySlacknessEquation,
      matrixAveragedPointOperator_ofPointRealization] using
        hopt.complementarySlacknessEquation g

end MatrixSdpStatementWithSlackness

namespace MatrixSdpStatementWithSlacknessAndDominance

/-- A dominance-carrying matrix strong-duality statement forgets its auxiliary
dominance field and gives the abstract SDP statement with complementary
slackness. -/
theorem toSdpStatementWithSlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (h : MatrixSdpStatementWithSlacknessAndDominance params
      (matrixSdpPointRealizationOfStrategy params strategy)) :
    SdpStatementWithSlackness params strategy := by
  obtain ⟨T, Z, hopt⟩ := h.witness
  exact ⟨matrixSubmeasurementToSubMeas T, Z,
    hopt.toMatrixSdpOptimalWitness.toSdpOptimalPairWithSlackness⟩

end MatrixSdpStatementWithSlacknessAndDominance

/-- Canonical block-SDP feasibility, objective equality, complementary
slackness, and auxiliary dual dominance give the abstract Section 9 SDP
statement.

This is the dominance-carrying canonical-block version of
`MatrixSdpStatementWithSlacknessAndDominance.toSdpStatementWithSlackness`,
specialized to the point-measurement matrix realization of a strategy.  It
uses the block-diagonal extraction theorem from `MatrixRealization.lean` to
replace a feasible canonical primal matrix by the associated paper
submeasurement, and then transports the resulting matrix witness to the
abstract `SdpStatementWithSlackness` interface after forgetting dominance. -/
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

/-- A canonical optimal pair with dominance gives the abstract Section 9 SDP
statement with complementary slackness. -/
theorem sdpStatementWithSlackness_of_canonicalOptimalPairWithDominance
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (h : MatrixSdpCanonicalOptimalPairWithDominance params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z) :
    SdpStatementWithSlackness params strategy :=
  MatrixSdpStatementWithSlacknessAndDominance.toSdpStatementWithSlackness
    params strategy h.toMatrixSdpStatementWithSlacknessAndDominance

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

/-- A saturated canonical optimal pair, together with a separately proved
dominance bound `I ≤ Z`, gives the abstract Section 9 SDP statement with
complementary slackness.

This is the comparison theorem from the paper-faithful saturated structure
`MatrixSdpCanonicalOptimalPair` to the dominance-carrying route.  The abstract
target remains `SdpStatementWithSlackness`; the extra input is used only to
enter the strengthened matrix-side interface. -/
theorem sdpStatementWithSlackness_of_canonicalOptimalPair_of_dualDominatesIdentity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (h : MatrixSdpCanonicalOptimalPair params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z)
    (hOneLe : (1 : MIPStarRE.Quantum.Op ι) ≤ Z) :
    SdpStatementWithSlackness params strategy :=
  sdpStatementWithSlackness_of_canonicalOptimalPairWithDominance
    params strategy X Z (h.withDominance hOneLe)

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
  have htotal : (matrixSubmeasurementToSubMeas Tsub).total = 1 := by
    simpa [matrixSubmeasurementToSubMeas, MIPStarRE.Quantum.Submeasurement.total] using
      hopt.primalTotalEqOne
  let T : Measurement (Polynomial params) ι :=
    (matrixSubmeasurementToSubMeas Tsub).toMeasurement htotal
  refine ⟨T, hopt.dualPositive, ?_, ?_⟩
  · intro g
    simpa [matrixSdpDualSlackOperator_ofPointRealization] using hopt.dualFeasible g
  · intro g
    simpa [T, matrixSubmeasurementToSubMeas, sdpComplementarySlacknessEquation,
      matrixSdpComplementarySlacknessEquation,
      matrixAveragedPointOperator_ofPointRealization] using
        hopt.complementarySlacknessEquation g

/-- Canonical block-SDP feasibility, objective equality, complementary
slackness, and dual dominance give the displayed abstract SDP measurement
witness.

This theorem is the dominance-carrying extraction from canonical block data at
the point-measurement realization of a strategy.  It records the additional
bound \(I \le Z\) explicitly in the conclusion; the dominance-free paper-form
measurement witness is `sdpMeasurementWitness_of_canonicalOptimalPair`. -/
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
    hopt.toMatrixSdpOptimalWitness.toSdpOptimalPairWithSlackness
  exact ⟨hpair.primalMeasurement, hpair.toSdpOptimalPair.dualPositive,
    hOneLe, hpair.toSdpOptimalPair.dualFeasible, hpair.complementarySlackness⟩

/-- A canonical optimal pair with dominance gives the displayed abstract SDP
measurement witness. -/
theorem sdpMeasurementWitness_of_canonicalOptimalPairWithDominance
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (h : MatrixSdpCanonicalOptimalPairWithDominance params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z) :
    ∃ T : Measurement (Polynomial params) ι,
      0 ≤ Z ∧
      (1 : MIPStarRE.Quantum.Op ι) ≤ Z ∧
      (∀ g : Polynomial params, 0 ≤ sdpDualSlackOperator params strategy Z g) ∧
      ∀ g : Polynomial params,
        sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g :=
  sdpMeasurementWitness_of_canonicalFeasibleComplementarySlackness
    params strategy X h.feasible Z h.dualFeasible h.strongDuality
    h.complementarySlackness h.dualDominatesIdentity

/-- A saturated canonical optimal pair, together with a separately proved
dominance bound `I ≤ Z`, gives the displayed abstract SDP measurement
witness. -/
theorem sdpMeasurementWitness_of_canonicalOptimalPair_of_dualDominatesIdentity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (h : MatrixSdpCanonicalOptimalPair params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z)
    (hOneLe : (1 : MIPStarRE.Quantum.Op ι) ≤ Z) :
    ∃ T : Measurement (Polynomial params) ι,
      0 ≤ Z ∧
      (1 : MIPStarRE.Quantum.Op ι) ≤ Z ∧
      (∀ g : Polynomial params, 0 ≤ sdpDualSlackOperator params strategy Z g) ∧
      ∀ g : Polynomial params,
        sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g :=
  sdpMeasurementWitness_of_canonicalOptimalPairWithDominance
    params strategy X Z (h.withDominance hOneLe)

end MIPStarRE.LDT.SelfImprovement
