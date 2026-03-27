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
    (strategy : SymStrat params d)
    (T : Measurement (Polynomial params) d) (Z : Operator d) : Prop where
  primalTotalOperator :
    T.totalOperator = polynomialIdentityOperator params
  dualPositive : OpPSD Z
  dualFeasible :
    ∀ g : Polynomial params,
      OpPSD (sdpDualSlackOperator params strategy Z g)
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
    (strategy : SymStrat params d) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params) d, ∃ Z : Operator d,
      SdpOptimalPair params strategy T Z

/-- The operator inside the left-hand side of `lem:add-in-u` at a fixed point `u`. -/
noncomputable def addInULeftOperatorAtPoint {Outcome : Type*}
    (params : Parameters)
    (_strategy : SymStrat params d)
    (M : IdxSubMeas (Point params) Outcome d)
    (H : SubMeas (Polynomial params) d)
    (S : AddInUSelection params Outcome)
    (u : Point params) : Operator d :=
  match addInUSelectionChoice params S u with
  | some (o, h) =>
      opMul -- TODO(tensor): placeholder for formalTensor
        ((M u).outcomeOperator o) (H.outcomeOperator h)
  | none => formalZeroOperator

/-- The operator inside the right-hand side of `lem:add-in-u` at a fixed point `u`. -/
noncomputable def addInURightOperatorAtPoint {Outcome : Type*}
    (params : Parameters)
    (strategy : SymStrat params d)
    (M : IdxSubMeas (Point params) Outcome d)
    (T : Measurement (Polynomial params) d)
    (S : AddInUSelection params Outcome)
    (u : Point params) : Operator d :=
  match addInUSelectionChoice params S u with
  | some (o, h) =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
      opMul -- TODO(tensor): placeholder for formalTensor
        (opMul (opMul Au ((M u).outcomeOperator o)) Au)
        (T.outcomeOperator h)
  | none => formalZeroOperator

/-- The left-hand expectation in `lem:add-in-u`. -/
noncomputable def addInULeftQuantity {Outcome : Type*} (params : Parameters)
    (strategy : SymStrat params d)
    (M : IdxSubMeas (Point params) Outcome d)
    (H : SubMeas (Polynomial params) d)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params))
    (fun u =>
      operatorExpectation strategy.state
        (addInULeftOperatorAtPoint params strategy M H S u))

/-- The right-hand expectation in `lem:add-in-u`. -/
noncomputable def addInURightQuantity {Outcome : Type*} (params : Parameters)
    (strategy : SymStrat params d)
    (M : IdxSubMeas (Point params) Outcome d)
    (T : Measurement (Polynomial params) d)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params))
    (fun u =>
      operatorExpectation strategy.state
        (addInURightOperatorAtPoint params strategy M T S u))

/-- The pointwise matched operator `Σ_a A^u_a ⊗ H_[h(u)=a]`. -/
noncomputable def helperAgreementOperatorAtPoint (params : Parameters)
    (strategy : SymStrat params d)
    (H : SubMeas (Polynomial params) d)
    (u : Point params) : Operator d :=
  averageOperatorOverDistribution (uniformDistribution (Fq params))
    (fun a =>
      opMul -- TODO(tensor): placeholder for formalTensor
        ((strategy.pointMeasurement u).toSubMeas.outcomeOperator a)
        ((evaluateAt params u H).outcomeOperator a))

/-- The average operator `E_u Σ_a A^u_a ⊗ H_[h(u)=a]`. -/
noncomputable def helperAgreementAverageOperator (params : Parameters)
    (strategy : SymStrat params d)
    (H : SubMeas (Polynomial params) d) : Operator d :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (helperAgreementOperatorAtPoint params strategy H)

/-- The helper-stage upper operator `Z ⊗ I`. -/
noncomputable def helperUpperOperator (params : Parameters) (Z : Operator d) : Operator d :=
  opMul -- TODO(tensor): placeholder for formalTensor
        Z (polynomialIdentityOperator params)

/-- The operator measuring the helper-stage boundedness defect. -/
noncomputable def helperBoundednessOperator (params : Parameters)
    (strategy : SymStrat params d)
    (H : SubMeas (Polynomial params) d) (Z : Operator d) : Operator d :=
  opDiff
    (helperUpperOperator params Z)
    (helperAgreementAverageOperator params strategy H)

/-- The helper-stage boundedness defect. -/
noncomputable def helperBoundednessGap (params : Parameters)
    (strategy : SymStrat params d)
    (H : SubMeas (Polynomial params) d) (Z : Operator d) : Error :=
  operatorExpectation strategy.state
    (helperBoundednessOperator params strategy H Z)

/-- The projective-stage residual operator `Z ⊗ (I - H)`. -/
noncomputable def projectiveResidualOperator (params : Parameters)
    (H : ProjSubMeas (Polynomial params) d)
    (Z : Operator d) : Operator d :=
  opMul -- TODO(tensor): placeholder for formalTensor
        Z
    (opDiff (polynomialIdentityOperator params) H.toSubMeas.totalOperator)

/-- The projective-stage boundedness defect. -/
noncomputable def projectiveBoundednessGap (params : Parameters)
    (strategy : SymStrat params d)
    (H : ProjSubMeas (Polynomial params) d) (Z : Operator d) : Error :=
  operatorExpectation strategy.state
    (projectiveResidualOperator params H Z)

/-- Output package for `lem:add-in-u`. -/
structure AddInUStatement {Outcome : Type*} (params : Parameters)
    (strategy : SymStrat params d)
    (T : Measurement (Polynomial params) d)
    (M : IdxSubMeas (Point params) Outcome d)
    (H : SubMeas (Polynomial params) d)
    (eps delta : Error) : Prop where
  averagedConstruction :
    H = averagedSandwichedPolynomialSubMeas params strategy T
  varianceBound :
    pointConditionedGlobalVariance params strategy T.toSubMeas ≤
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
    (strategy : SymStrat params d)
    (G : Measurement (Polynomial params) d)
    (T : Measurement (Polynomial params) d)
    (H : SubMeas (Polynomial params) d)
    (Z : Operator d) (eps delta gamma nu : Error) : Prop where
  sdpWitness : SdpOptimalPair params strategy T Z
  averagedConstruction :
    H = averagedSandwichedPolynomialSubMeas params strategy T
  addInUTransfer :
    ∀ {Outcome : Type*} (M : IdxSubMeas (Point params) Outcome d),
      AddInUStatement params strategy T M H eps delta
  completeness :
    CompletenessAtLeast strategy.state H
      ((1 - nu) - selfImprovementHelperError params eps delta)
  pointConsistency :
    ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      H
      (selfImprovementHelperError params eps delta)
  strongSelfConsistency :
    PolyMeasSSC params strategy.state H
      (selfImprovementHelperError params eps delta)
  positiveSemidefiniteWitness :
    OpPSD Z
  dualDominatesAveragedPoint :
    ∀ g : Polynomial params,
      OpPSD (sdpDualSlackOperator params strategy Z g)
  helperResidualBound :
    helperBoundednessGap params strategy H Z ≤
      selfImprovementHelperError params eps delta
  bounded :
    BoundedByOperator strategy.state H Z
      (selfImprovementHelperError params eps delta)

/-- Output package for `thm:self-improvement`. -/
structure SelfImprovementConclusion (params : Parameters)
    (strategy : SymStrat params d)
    (G : Measurement (Polynomial params) d)
    (H : ProjSubMeas (Polynomial params) d)
    (Z : Operator d) (eps delta gamma nu : Error) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params) d,
      ∃ Hhat : SubMeas (Polynomial params) d,
        SelfImprovementHelperConclusion params strategy G T Hhat Z eps delta gamma nu ∧
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily Hhat)
          (constSubMeasFamily H.toSubMeas)
          (selfImprovementOrthogonalizationError params eps delta) ∧
        SDDRel strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Hhat)
          (polynomialEvaluationFamily params H.toSubMeas)
          (selfImprovementDataProcessingError params eps delta)
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeas
      ((1 - nu) - selfImprovementError params eps delta)
  pointConsistency :
    ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      H.toSubMeas
      (selfImprovementError params eps delta)
  selfCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily H.toSubMeas)
      (constSubMeasFamily H.toSubMeas)
      (selfImprovementError params eps delta)
  positiveSemidefiniteWitness :
    OpPSD Z
  dualDominatesAveragedPoint :
    ∀ g : Polynomial params,
      OpPSD (sdpDualSlackOperator params strategy Z g)
  projectiveResidualBound :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta
  bounded :
    BoundedByOperator strategy.state H.toSubMeas Z
      (selfImprovementError params eps delta)

/-- Output package for the explicit bridge from measurement to submeasurement input. -/
structure SelfImprovementSubMeasConclusion (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d)
    (H : ProjSubMeas (Polynomial params) d)
    (Z : Operator d) (eps delta gamma nu : Error) : Prop where
  measurementBridge :
    ∃ Gmeas : Measurement (Polynomial params) d,
      Gmeas.toSubMeas = G ∧
      SelfImprovementConclusion params strategy Gmeas H Z eps delta gamma nu

/-- `lem:self-improvement-helper`. -/
lemma selfImprovementHelper
    (params : Parameters)
    (strategy : SymStrat params d)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) d)
    (hcons : ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      G.toSubMeas nu) :
    ∃ T : Measurement (Polynomial params) d,
      ∃ H : SubMeas (Polynomial params) d, ∃ Z : Operator d,
        SelfImprovementHelperConclusion params strategy G T H Z eps delta gamma nu := by
  sorry

/-- `lem:sdp`. -/
lemma sdp
    (params : Parameters)
    (strategy : SymStrat params d) :
    SdpStatement params strategy := by
  sorry

/-- `lem:add-in-u`. -/
lemma addInU {Outcome : Type*}
    (params : Parameters)
    (strategy : SymStrat params d)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (Polynomial params) d)
    (M : IdxSubMeas (Point params) Outcome d)
    (H : SubMeas (Polynomial params) d) :
    AddInUStatement params strategy T M H eps delta := by
  sorry

/-- `thm:self-improvement`. -/
theorem selfImprovement
    (params : Parameters)
    (strategy : SymStrat params d)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) d)
    (hcons : ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      G.toSubMeas nu) :
    ∃ H : ProjSubMeas (Polynomial params) d, ∃ Z : Operator d,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  sorry

/--
Bridge from the measurement-input version in `self_improvement.tex` to the
submeasurement-input version used in `inductive_step.tex`.
-/
theorem selfImprovementFromSubMeas
    (params : Parameters)
    (strategy : SymStrat params d)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) d)
    (Gmeas : Measurement (Polynomial params) d)
    (hbridge : Gmeas.toSubMeas = G)
    (hcons : ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      G nu) :
    ∃ H : ProjSubMeas (Polynomial params) d, ∃ Z : Operator d,
      SelfImprovementSubMeasConclusion params strategy G H Z
        eps delta gamma nu := by
  sorry

end MIPStarRE.LDT.SelfImprovement

