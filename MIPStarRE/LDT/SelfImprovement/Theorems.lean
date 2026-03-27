import MIPStarRE.LDT.SelfImprovement.MatrixRealization

/-!
# Section 9 — Theorems

Theorem stubs for the self-improvement argument.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- An optimal primal/dual pair for the section's semidefinite program. -/
structure SdpOptimalPair (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (T : Measurement (Polynomial params) d) (Z : Operator d) : Prop where
  primalTotalOperator :
    T.totalOperator = polynomialIdentityOperator params
  dualPositive : PositiveSemidefinite Z
  dualFeasible :
    ∀ g : Polynomial params,
      PositiveSemidefinite (sdpDualSlackOperator params strategy Z g)
  strongDuality :
    sdpPrimalObjective params strategy T = sdpDualObjective Z
  complementarySlackness :
    ∀ g : Polynomial params,
      sdpComplementarySlacknessEquation params strategy T Z g
  matrixWitness :
    ∃ model : MatrixSdpRealization params,
      ∃ Tm : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
        ∃ Zm : MatrixOperator model.space,
          MatrixSdpOptimalWitness params model Tm Zm

/-- Output package for `lem:sdp`. -/
structure SdpStatement (params : Parameters)
    (strategy : SymmetricStrategy params d) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params) d, ∃ Z : Operator d,
      SdpOptimalPair params strategy T Z

/-- The operator inside the left-hand side of `lem:add-in-u` at a fixed point `u`. -/
noncomputable def addInULeftOperatorAtPoint {Outcome : Type*}
    (params : Parameters)
    (_strategy : SymmetricStrategy params d)
    (M : IndexedSubMeasurement (Point params) Outcome d)
    (H : SubMeasurement (Polynomial params) d)
    (S : AddInUSelection params Outcome)
    (u : Point params) : Operator d :=
  match addInUSelectionChoice params S u with
  | some (o, h) =>
      operatorMul -- TODO(tensor): placeholder for formalTensor
        ((M u).outcomeOperator o) (H.outcomeOperator h)
  | none => formalZeroOperator

/-- The operator inside the right-hand side of `lem:add-in-u` at a fixed point `u`. -/
noncomputable def addInURightOperatorAtPoint {Outcome : Type*}
    (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (M : IndexedSubMeasurement (Point params) Outcome d)
    (T : Measurement (Polynomial params) d)
    (S : AddInUSelection params Outcome)
    (u : Point params) : Operator d :=
  match addInUSelectionChoice params S u with
  | some (o, h) =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
      operatorMul -- TODO(tensor): placeholder for formalTensor
        (operatorMul (operatorMul Au ((M u).outcomeOperator o)) Au)
        (T.outcomeOperator h)
  | none => formalZeroOperator

/-- The left-hand expectation in `lem:add-in-u`. -/
noncomputable def addInULeftQuantity {Outcome : Type*} (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (M : IndexedSubMeasurement (Point params) Outcome d)
    (H : SubMeasurement (Polynomial params) d)
    (S : AddInUSelection params Outcome) : Error :=
  averageOverDistribution (uniformDistribution (Point params))
    (fun u =>
      operatorExpectation strategy.state
        (addInULeftOperatorAtPoint params strategy M H S u))

/-- The right-hand expectation in `lem:add-in-u`. -/
noncomputable def addInURightQuantity {Outcome : Type*} (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (M : IndexedSubMeasurement (Point params) Outcome d)
    (T : Measurement (Polynomial params) d)
    (S : AddInUSelection params Outcome) : Error :=
  averageOverDistribution (uniformDistribution (Point params))
    (fun u =>
      operatorExpectation strategy.state
        (addInURightOperatorAtPoint params strategy M T S u))

/-- The pointwise matched operator `Σ_a A^u_a ⊗ H_[h(u)=a]`. -/
noncomputable def helperAgreementOperatorAtPoint (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (H : SubMeasurement (Polynomial params) d)
    (u : Point params) : Operator d :=
  averageOperatorOverDistribution (uniformDistribution (Fq params))
    (fun a =>
      operatorMul -- TODO(tensor): placeholder for formalTensor
        ((strategy.pointMeasurement u).toSubMeasurement.outcomeOperator a)
        ((evaluateAt params u H).outcomeOperator a))

/-- The average operator `E_u Σ_a A^u_a ⊗ H_[h(u)=a]`. -/
noncomputable def helperAgreementAverageOperator (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (H : SubMeasurement (Polynomial params) d) : Operator d :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (helperAgreementOperatorAtPoint params strategy H)

/-- The helper-stage upper operator `Z ⊗ I`. -/
noncomputable def helperUpperOperator (params : Parameters) (Z : Operator d) : Operator d :=
  operatorMul -- TODO(tensor): placeholder for formalTensor
        Z (polynomialIdentityOperator params)

/-- The operator measuring the helper-stage boundedness defect. -/
noncomputable def helperBoundednessOperator (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (H : SubMeasurement (Polynomial params) d) (Z : Operator d) : Operator d :=
  operatorDifference
    (helperUpperOperator params Z)
    (helperAgreementAverageOperator params strategy H)

/-- The helper-stage boundedness defect. -/
noncomputable def helperBoundednessGap (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (H : SubMeasurement (Polynomial params) d) (Z : Operator d) : Error :=
  operatorExpectation strategy.state
    (helperBoundednessOperator params strategy H Z)

/-- The projective-stage residual operator `Z ⊗ (I - H)`. -/
noncomputable def projectiveResidualOperator (params : Parameters)
    (H : ProjectiveSubMeasurement (Polynomial params) d)
    (Z : Operator d) : Operator d :=
  operatorMul -- TODO(tensor): placeholder for formalTensor
        Z
    (operatorDifference (polynomialIdentityOperator params) H.toSubMeasurement.totalOperator)

/-- The projective-stage boundedness defect. -/
noncomputable def projectiveBoundednessGap (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (H : ProjectiveSubMeasurement (Polynomial params) d) (Z : Operator d) : Error :=
  operatorExpectation strategy.state
    (projectiveResidualOperator params H Z)

/-- Output package for `lem:add-in-u`. -/
structure AddInUStatement {Outcome : Type*} (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (T : Measurement (Polynomial params) d)
    (M : IndexedSubMeasurement (Point params) Outcome d)
    (H : SubMeasurement (Polynomial params) d)
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
  matrixWitness :
    ∃ model : MatrixSdpRealization params,
      ∃ Mmat : MatrixIndexedPointOutcomeFamily params Outcome model.space,
        ∃ Hmat : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space,
          ∃ Tm : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
            MatrixAddInUTransferStatement params model Tm Mmat Hmat eps delta

/-- Output package for `lem:self-improvement-helper`. -/
structure SelfImprovementHelperConclusion (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (G : Measurement (Polynomial params) d)
    (T : Measurement (Polynomial params) d)
    (H : SubMeasurement (Polynomial params) d)
    (Z : Operator d) (eps delta gamma nu : Error) : Prop where
  sdpWitness : SdpOptimalPair params strategy T Z
  averagedConstruction :
    H = averagedSandwichedPolynomialSubMeasurement params strategy T
  addInUTransfer :
    ∀ {Outcome : Type*} (M : IndexedSubMeasurement (Point params) Outcome d),
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
  helperResidualBound :
    helperBoundednessGap params strategy H Z ≤
      selfImprovementHelperError params eps delta
  bounded :
    BoundedByOperator strategy.state H Z
      (selfImprovementHelperError params eps delta)

/-- Output package for `thm:self-improvement`. -/
structure SelfImprovementConclusion (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (G : Measurement (Polynomial params) d)
    (H : ProjectiveSubMeasurement (Polynomial params) d)
    (Z : Operator d) (eps delta gamma nu : Error) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params) d,
      ∃ Hhat : SubMeasurement (Polynomial params) d,
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
  projectiveResidualBound :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta
  bounded :
    BoundedByOperator strategy.state H.toSubMeasurement Z
      (selfImprovementError params eps delta)

/-- Output package for the explicit bridge from measurement to submeasurement input. -/
structure SelfImprovementSubMeasurementConclusion (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (G : SubMeasurement (Polynomial params) d)
    (H : ProjectiveSubMeasurement (Polynomial params) d)
    (Z : Operator d) (eps delta gamma nu : Error) : Prop where
  measurementBridge :
    ∃ Gmeas : Measurement (Polynomial params) d,
      Gmeas.toSubMeasurement = G ∧
      SelfImprovementConclusion params strategy Gmeas H Z eps delta gamma nu

/-- `lem:self-improvement-helper`. -/
lemma selfImprovementHelper
    (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) d)
    (hcons : ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      G.toSubMeasurement nu) :
    ∃ T : Measurement (Polynomial params) d,
      ∃ H : SubMeasurement (Polynomial params) d, ∃ Z : Operator d,
        SelfImprovementHelperConclusion params strategy G T H Z eps delta gamma nu := by
  sorry

/-- `lem:sdp`. -/
lemma sdp
    (params : Parameters)
    (strategy : SymmetricStrategy params d) :
    SdpStatement params strategy := by
  sorry

/-- `lem:add-in-u`. -/
lemma addInU {Outcome : Type*}
    (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (Polynomial params) d)
    (M : IndexedSubMeasurement (Point params) Outcome d)
    (H : SubMeasurement (Polynomial params) d) :
    AddInUStatement params strategy T M H eps delta := by
  sorry

/-- `thm:self-improvement`. -/
theorem selfImprovement
    (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) d)
    (hcons : ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      G.toSubMeasurement nu) :
    ∃ H : ProjectiveSubMeasurement (Polynomial params) d, ∃ Z : Operator d,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  sorry

/--
Bridge from the measurement-input version in `self_improvement.tex` to the
submeasurement-input version used in `inductive_step.tex`.
-/
theorem selfImprovementFromSubMeasurement
    (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params) d)
    (Gmeas : Measurement (Polynomial params) d)
    (hbridge : Gmeas.toSubMeasurement = G)
    (hcons : ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      G nu) :
    ∃ H : ProjectiveSubMeasurement (Polynomial params) d, ∃ Z : Operator d,
      SelfImprovementSubMeasurementConclusion params strategy G H Z
        eps delta gamma nu := by
  sorry

end MIPStarRE.LDT.SelfImprovement

