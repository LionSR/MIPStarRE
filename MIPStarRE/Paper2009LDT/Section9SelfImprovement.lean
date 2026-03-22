import MIPStarRE.Paper2009LDT.Section8GlobalVariance

/-!
Matching scaffold for Section 9 of the low individual degree paper in
`references/ldt-paper/self_improvement.tex`.

This file now exposes the paper's SDP witnesses, the `add-in-u` transfer
identity, and the non-projective/projective self-improvement outputs through
explicit named constructions and error terms.
-/

namespace MIPStarRE.Paper2009LDT.Section9SelfImprovement

open MIPStarRE.Paper2009LDT
open MIPStarRE.Paper2009LDT.Section7ExpansionHypercubeGraph
open MIPStarRE.Paper2009LDT.Section8GlobalVariance
open MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective

/-- The averaged point operator `A_g = E_u A^u_{g(u)}`. -/
def averagedPointOperator (params : Parameters)
    (_strategy : SymmetricStrategy params) (_g : Polynomial params) : Operator :=
  { name := s!"Aavg({params.m},{params.q},{params.d})" }

/-- The pointwise sandwiched submeasurement `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`. -/
def sandwichedPolynomialSubMeasurementAt (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) (u : Point params) :
    SubMeasurement (Polynomial params) :=
  { name :=
      s!"Hslice[{(strategy.pointMeasurement u).toSubMeasurement.name}|{T.toSubMeasurement.name}]" }

/-- The averaged sandwiched submeasurement `H_h = E_u H^u_h`. -/
def averagedSandwichedPolynomialSubMeasurement (params : Parameters)
    (_strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) : SubMeasurement (Polynomial params) :=
  { name := s!"Havg[{T.toSubMeasurement.name}]" }

/-- Evaluate a polynomial submeasurement at each point `u`. -/
def polynomialEvaluationFamily (params : Parameters)
    (H : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (Point params) (Fq params) :=
  fun u => evaluateAt params u H

/-- The formal primal objective operator of the self-improvement SDP. -/
def sdpPrimalObjectiveOperator (params : Parameters)
    (_strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) : Operator :=
  { name := s!"PrimalObj({T.toSubMeasurement.name},{params.m},{params.q},{params.d})" }

/-- The primal objective value `Σ_g Tr(T_g A_g)`. -/
def sdpPrimalObjective (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) : Error :=
  operatorTrace (sdpPrimalObjectiveOperator params strategy T)

/-- The dual objective value `Tr(Z)`. -/
def sdpDualObjective (Z : Operator) : Error :=
  operatorTrace Z

/-- The dual slack operator `Z - A_g`. -/
def sdpDualSlackOperator (params : Parameters)
    (strategy : SymmetricStrategy params)
    (Z : Operator) (g : Polynomial params) : Operator :=
  formalDifference Z (averagedPointOperator params strategy g)

/-- The complementary-slackness operator `T_g (Z - A_g)`. -/
def sdpComplementarySlacknessOperator (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) (Z : Operator)
    (g : Polynomial params) : Operator :=
  formalProduct
    { name := s!"{T.toSubMeasurement.name}[g]" }
    (sdpDualSlackOperator params strategy Z g)

/-- The operator measuring the helper-stage boundedness defect. -/
def helperBoundednessOperator (params : Parameters)
    (_strategy : SymmetricStrategy params)
    (H : SubMeasurement (Polynomial params)) (Z : Operator) : Operator :=
  formalDifference Z { name := s!"A-vs-{H.name}({params.m},{params.q},{params.d})" }

/-- The helper-stage boundedness defect. -/
def helperBoundednessGap (params : Parameters)
    (strategy : SymmetricStrategy params)
    (H : SubMeasurement (Polynomial params)) (Z : Operator) : Error :=
  operatorExpectation strategy.state (helperBoundednessOperator params strategy H Z)

/-- The projective-stage boundedness defect. -/
def projectiveBoundednessGap (params : Parameters)
    (strategy : SymmetricStrategy params)
    (H : ProjectiveSubMeasurement (Polynomial params)) (Z : Operator) : Error :=
  let defect :=
    formalDifference Z
      { name := s!"A-vs-{H.toSubMeasurement.name}({params.m},{params.q},{params.d})" }
  operatorExpectation strategy.state defect

/-- The variance error entering `lem:add-in-u`. -/
noncomputable def selfImprovementVarianceError (params : Parameters)
    (eps delta : Error) : Error :=
  globalVarianceOfPointsError params eps delta

/-- The error term in `lem:add-in-u`. -/
noncomputable def addInUError (params : Parameters)
    (eps delta : Error) : Error :=
  4 * Real.rpow (selfImprovementVarianceError params eps delta) (1 / (2 : Error))

/-- The quantitative error from `lem:self-improvement-helper`. -/
noncomputable def selfImprovementHelperError (params : Parameters)
    (eps delta : Error) : Error :=
  100 * (params.m : Error) *
    (Real.rpow eps (1 / (2 : Error)) +
      Real.rpow delta (1 / (2 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (2 : Error)))

/-- The orthogonalization error applied to the helper output. -/
noncomputable def selfImprovementOrthogonalizationError (params : Parameters)
    (eps delta : Error) : Error :=
  orthonormalizationError (selfImprovementHelperError params eps delta)

/-- The postprocessed error after projecting the helper output. -/
noncomputable def selfImprovementDataProcessingError (params : Parameters)
    (eps delta : Error) : Error :=
  8 * selfImprovementHelperError params eps delta +
    8 * Real.rpow (selfImprovementOrthogonalizationError params eps delta)
      (1 / (2 : Error))

/-- The quantitative error from `thm:self-improvement`. -/
noncomputable def selfImprovementError (params : Parameters)
    (eps delta : Error) : Error :=
  Section6MainInductionStep.selfImprovementInInductionError params eps delta 0

/-- An optimal primal/dual pair for the section's semidefinite program. -/
structure SdpOptimalPair (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) (Z : Operator) : Prop where
  dualPositive : PositiveSemidefinite Z
  dualFeasible :
    ∀ g : Polynomial params,
      PositiveSemidefinite (sdpDualSlackOperator params strategy Z g)
  strongDuality :
    sdpPrimalObjective params strategy T = sdpDualObjective Z
  complementarySlackness :
    ∀ g : Polynomial params,
      sdpComplementarySlacknessOperator params strategy T Z g = formalZeroOperator

/-- Output package for `lem:sdp`. -/
structure SdpStatement (params : Parameters)
    (strategy : SymmetricStrategy params) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params), ∃ Z : Operator,
      SdpOptimalPair params strategy T Z

/-- The family of outcome/polynomial selections used in `lem:add-in-u`. -/
abbrev AddInUSelection (params : Parameters) (Outcome : Type _) :=
  Point params → Set (Outcome × Polynomial params)

/-- The left-hand expectation in `lem:add-in-u`. -/
def addInULeftQuantity {Outcome : Type _} (params : Parameters)
    (strategy : SymmetricStrategy params)
    (_M : IndexedSubMeasurement (Point params) Outcome)
    (H : SubMeasurement (Polynomial params))
    (_S : AddInUSelection params Outcome) : Error :=
  operatorExpectation strategy.state
    { name := s!"AddInU.left({params.m},{params.q},{params.d},{H.name})" }

/-- The right-hand expectation in `lem:add-in-u`. -/
def addInURightQuantity {Outcome : Type _} (params : Parameters)
    (strategy : SymmetricStrategy params)
    (_M : IndexedSubMeasurement (Point params) Outcome)
    (T : Measurement (Polynomial params))
    (_S : AddInUSelection params Outcome) : Error :=
  operatorExpectation strategy.state
    { name := s!"AddInU.right({params.m},{params.q},{params.d},{T.toSubMeasurement.name})" }

/-- Output package for `lem:add-in-u`. -/
structure AddInUStatement {Outcome : Type _} (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params))
    (M : IndexedSubMeasurement (Point params) Outcome)
    (H : SubMeasurement (Polynomial params))
    (eps delta : Error) : Prop where
  averagedConstruction :
    H = averagedSandwichedPolynomialSubMeasurement params strategy T
  varianceBound :
    pointConditionedGlobalVariance params strategy T.toSubMeasurement ≤
      selfImprovementVarianceError params eps delta
  transfer :
    ∀ S : AddInUSelection params Outcome,
      |addInULeftQuantity params strategy M H S -
          addInURightQuantity params strategy M T S| ≤
        addInUError params eps delta

/-- Output package for `lem:self-improvement-helper`. -/
structure SelfImprovementHelperConclusion (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : Measurement (Polynomial params))
    (T : Measurement (Polynomial params))
    (H : SubMeasurement (Polynomial params))
    (Z : Operator) (eps delta gamma nu : Error) : Prop where
  sdpWitness : SdpOptimalPair params strategy T Z
  averagedConstruction :
    H = averagedSandwichedPolynomialSubMeasurement params strategy T
  addInUTransfer :
    ∀ {Outcome : Type _} (M : IndexedSubMeasurement (Point params) Outcome),
      AddInUStatement params strategy T M H eps delta
  completeness :
    CompletenessAtLeast strategy.state H
      ((1 - nu) - selfImprovementHelperError params eps delta)
  pointConsistency :
    ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      H
      (selfImprovementHelperError params eps delta)
  strongSelfConsistency :
    PolynomialMeasurementStronglySelfConsistent params strategy.state H
      (selfImprovementHelperError params eps delta)
  positiveSemidefiniteWitness :
    PositiveSemidefinite Z
  dualDominatesAveragedPoint :
    ∀ g : Polynomial params,
      PositiveSemidefinite (sdpDualSlackOperator params strategy Z g)
  boundednessResidual :
    helperBoundednessGap params strategy H Z ≤
      selfImprovementHelperError params eps delta
  bounded :
    BoundedByOperator strategy.state H Z
      (selfImprovementHelperError params eps delta)

/-- Output package for `thm:self-improvement`. -/
structure SelfImprovementConclusion (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : Measurement (Polynomial params))
    (H : ProjectiveSubMeasurement (Polynomial params))
    (Z : Operator) (eps delta gamma nu : Error) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params),
      ∃ Hhat : SubMeasurement (Polynomial params),
        SelfImprovementHelperConclusion params strategy G T Hhat Z eps delta gamma nu ∧
        StateDependentDistanceRel strategy.state (uniformDistribution Unit)
          (constantSubMeasurementFamily Hhat)
          (constantSubMeasurementFamily H.toSubMeasurement)
          (selfImprovementOrthogonalizationError params eps delta) ∧
        StateDependentDistanceRel strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Hhat)
          (polynomialEvaluationFamily params H.toSubMeasurement)
          (selfImprovementDataProcessingError params eps delta)
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeasurement
      ((1 - nu) - selfImprovementError params eps delta)
  pointConsistency :
    ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      H.toSubMeasurement
      (selfImprovementError params eps delta)
  selfCloseness :
    StateDependentDistanceRel strategy.state (uniformDistribution Unit)
      (constantSubMeasurementFamily H.toSubMeasurement)
      (constantSubMeasurementFamily H.toSubMeasurement)
      (selfImprovementError params eps delta)
  positiveSemidefiniteWitness :
    PositiveSemidefinite Z
  dualDominatesAveragedPoint :
    ∀ g : Polynomial params,
      PositiveSemidefinite (sdpDualSlackOperator params strategy Z g)
  boundednessResidual :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta
  bounded :
    BoundedByOperator strategy.state H.toSubMeasurement Z
      (selfImprovementError params eps delta)

/-- `lem:self-improvement-helper`. -/
lemma selfImprovementHelper
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params))
    (hcons : ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      G.toSubMeasurement nu) :
    ∃ T : Measurement (Polynomial params),
      ∃ H : SubMeasurement (Polynomial params), ∃ Z : Operator,
        SelfImprovementHelperConclusion params strategy G T H Z eps delta gamma nu := by
  sorry

/-- `lem:sdp`. -/
lemma sdp
    (params : Parameters)
    (strategy : SymmetricStrategy params) :
    SdpStatement params strategy := by
  sorry

/-- `lem:add-in-u`. -/
lemma addInU {Outcome : Type _}
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (Polynomial params))
    (M : IndexedSubMeasurement (Point params) Outcome)
    (H : SubMeasurement (Polynomial params)) :
    AddInUStatement params strategy T M H eps delta := by
  sorry

/-- `thm:self-improvement`. -/
def selfImprovement
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params))
    (hcons : ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      G.toSubMeasurement nu) :
    Σ' H : ProjectiveSubMeasurement (Polynomial params), Σ' Z : Operator,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  sorry

end MIPStarRE.Paper2009LDT.Section9SelfImprovement
