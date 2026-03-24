import MIPStarRE.LDT.Section8GlobalVariance

/-!
Matching scaffold for Section 9 of the low individual degree paper in
`references/ldt-paper/self_improvement.tex`.

This file exposes the paper's SDP witnesses, the `add-in-u` transfer identity,
and the non-projective/projective self-improvement outputs through explicit named
constructions and error terms.
-/

namespace MIPStarRE.LDT.Section9SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.Section7ExpansionHypercubeGraph
open MIPStarRE.LDT.Section8GlobalVariance
open MIPStarRE.LDT.Section5MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- The identity operator on the polynomial register. -/
def polynomialIdentityOperator (params : Parameters) : Operator :=
  Section7ExpansionHypercubeGraph.identityOperator s!"poly({params.m},{params.q},{params.d})"

/-- The pointwise operator `A^u_{g(u)}` entering the SDP average `A_g`. -/
def averagedPointOperatorContribution (params : Parameters)
    (strategy : SymmetricStrategy params)
    (g : Polynomial params) (u : Point params) : Operator :=
  pointConditionedOutcomeOperatorAtPolynomial params strategy g u

/-- The averaged point operator `A_g = E_u A^u_{g(u)}`. -/
noncomputable def averagedPointOperator (params : Parameters)
    (strategy : SymmetricStrategy params) (g : Polynomial params) : Operator :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (averagedPointOperatorContribution params strategy g)

/-- The operator `T_g A_g` contributing to the primal SDP objective. -/
noncomputable def sdpPrimalContributionOperator (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params))
    (g : Polynomial params) : Operator :=
  operatorMul (T.outcomeOperator g) (averagedPointOperator params strategy g)

/-- The formal primal objective operator `Σ_g T_g A_g`. -/
noncomputable def sdpPrimalObjectiveOperator (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) : Operator :=
  averageOperatorOverDistribution (polynomialDistribution params)
    (sdpPrimalContributionOperator params strategy T)

/-- The primal objective value `Σ_g Tr(T_g A_g)`. -/
noncomputable def sdpPrimalObjective (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) : Error :=
  operatorTrace (sdpPrimalObjectiveOperator params strategy T)

/-- The dual objective value `Tr(Z)`. -/
noncomputable def sdpDualObjective (Z : Operator) : Error :=
  operatorTrace Z

/-- The dual slack operator `Z - A_g`. -/
noncomputable def sdpDualSlackOperator (params : Parameters)
    (strategy : SymmetricStrategy params)
    (Z : Operator) (g : Polynomial params) : Operator :=
  operatorDifference Z (averagedPointOperator params strategy g)

/-- The complementary-slackness equation `T_g Z = T_g A_g`. -/
def sdpComplementarySlacknessEquation (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params))
    (Z : Operator) (g : Polynomial params) : Prop :=
  operatorMul (T.outcomeOperator g) Z =
    operatorMul (T.outcomeOperator g) (averagedPointOperator params strategy g)

/-- The pointwise sandwiched operator `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def sandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params))
    (u : Point params) (h : Polynomial params) : Operator :=
  let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
  operatorMul (operatorMul Au (T.outcomeOperator h)) Au

/-- The pointwise sandwiched submeasurement `H^u = {H^u_h}`. -/
noncomputable def sandwichedPolynomialSubMeasurementAt (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) (u : Point params) :
    SubMeasurement (Polynomial params) :=
  { name :=
      s!"Hslice[{pointCode params u}|{(strategy.pointMeasurement u).toSubMeasurement.name}|{T.toSubMeasurement.name}]"
    outcomeOperator := sandwichedPolynomialOutcomeOperatorAt params strategy T u
    totalOperator :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (sandwichedPolynomialOutcomeOperatorAt params strategy T u) }

/-- The averaged sandwiched submeasurement `H_h = E_u H^u_h`. -/
noncomputable def averagedSandwichedPolynomialSubMeasurement (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) : SubMeasurement (Polynomial params) :=
  { name := s!"Havg[{T.toSubMeasurement.name}]"
    outcomeOperator := fun h =>
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
    totalOperator :=
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => (sandwichedPolynomialSubMeasurementAt params strategy T u).totalOperator) }

/-- Evaluate a polynomial submeasurement at each point `u`. -/
noncomputable abbrev polynomialEvaluationFamily (params : Parameters)
    (H : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (Point params) (Fq params) :=
  MIPStarRE.LDT.polynomialEvaluationFamily params H

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

/-- A concrete finite-dimensional matrix realization of the SDP data. -/
structure MatrixSdpRealization (params : Parameters) where
  space : FiniteHilbertSpace
  state : PositiveMatrixState space
  pointMeasurement : Point params → MatrixSubmeasurement (Fq params) space

/-- The concrete operator `A^u_{g(u)}` entering the SDP average. -/
def matrixAveragedPointOperatorContribution (params : Parameters)
    (model : MatrixSdpRealization params)
    (g : Polynomial params) (u : Point params) : MatrixOperator model.space :=
  (model.pointMeasurement u).effect (g u)

/-- The concrete averaged operator `A_g = E_u A^u_{g(u)}`. -/
noncomputable def matrixAveragedPointOperator (params : Parameters)
    (model : MatrixSdpRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  matrixAverageOperator (matrixAveragedPointOperatorContribution params model g)

/-- The concrete primal contribution `T_g A_g`. -/
noncomputable def matrixSdpPrimalContributionOperator (params : Parameters)
    (model : MatrixSdpRealization params)
    (T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  (T.effect g) * matrixAveragedPointOperator params model g

/-- The concrete primal objective `E_g Re τ(ρ T_g A_g)`. -/
noncomputable def matrixSdpPrimalObjective (params : Parameters)
    (model : MatrixSdpRealization params)
    (T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space) : Error :=
  averageOverDistribution (polynomialDistribution params) (fun g =>
    Complex.re (matrixExpectation model.state
      (matrixSdpPrimalContributionOperator params model T g)))

/-- The concrete dual objective `Re τ(Z)`. -/
noncomputable def matrixSdpDualObjective {params : Parameters}
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) : Error :=
  Complex.re (MIPStarRE.Quantum.normalizedTrace Z)

/-- The concrete dual slack operator `Z - A_g`. -/
noncomputable def matrixSdpDualSlackOperator (params : Parameters)
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  Z - matrixAveragedPointOperator params model g

/-- The concrete complementary-slackness defect `T_g (Z - A_g)`. -/
noncomputable def matrixSdpComplementarySlacknessDefect (params : Parameters)
    (model : MatrixSdpRealization params)
    (T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  (T.effect g) * matrixSdpDualSlackOperator params model Z g

/-- Matrix-level witness for an optimal SDP pair. -/
structure MatrixSdpOptimalWitness (params : Parameters)
    (model : MatrixSdpRealization params)
    (T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  dualPositive : 0 ≤ Z
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g
  strongDuality :
    matrixSdpPrimalObjective params model T = matrixSdpDualObjective model Z
  complementarySlackness :
    ∀ g : Polynomial params,
      matrixSdpComplementarySlacknessDefect params model T Z g = 0

/-- The family of outcome/polynomial selections used in `lem:add-in-u`. -/
abbrev AddInUSelection (params : Parameters) (Outcome : Type _) :=
  Point params → Set (Outcome × Polynomial params)

/-- Choose one representative pair from `S_u` when it is nonempty. -/
noncomputable def addInUSelectionChoice {Outcome : Type _}
    (params : Parameters)
    (S : AddInUSelection params Outcome)
    (u : Point params) : Option (Outcome × Polynomial params) := by
  classical
  by_cases h : (S u).Nonempty
  · exact some (Classical.choose h)
  · exact none

/-- A raw point-indexed matrix outcome family used in the matrix `add-in-u` transfer. -/
abbrev MatrixIndexedPointOutcomeFamily (params : Parameters)
    (Outcome : Type _) (H : FiniteHilbertSpace) :=
  Point params → Outcome → MatrixOperator H

/-- The concrete sandwiched operator `A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def matrixSandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    (model : MatrixSdpRealization params)
    (T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) (h : Polynomial params) : MatrixOperator model.space :=
  let Au := matrixAveragedPointOperatorContribution params model h u
  Au * (T.effect h) * Au

/-- The averaged concrete sandwiched operator `E_u A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def matrixAveragedSandwichedPolynomialOutcomeOperator (params : Parameters)
    (model : MatrixSdpRealization params)
    (T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (h : Polynomial params) : MatrixOperator model.space :=
  matrixAverageOperator (fun u : Point params =>
    matrixSandwichedPolynomialOutcomeOperatorAt params model T u h)

/-- The matrix left-hand operator in `add-in-u`. -/
noncomputable def matrixAddInULeftOperatorAtPoint {Outcome : Type _}
    (params : Parameters)
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MatrixOperator model.space :=
  match addInUSelectionChoice params S u with
  | some (o, h) => (M u o) * (H.effect h)
  | none => 0

/-- The matrix right-hand operator in `add-in-u`. -/
noncomputable def matrixAddInURightOperatorAtPoint {Outcome : Type _}
    (params : Parameters)
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MatrixOperator model.space :=
  match addInUSelectionChoice params S u with
  | some (o, h) =>
      let Au := matrixAveragedPointOperatorContribution params model h u
      Au * (M u o) * Au * (T.effect h)
  | none => 0

/-- The matrix left-hand expectation in `add-in-u`. -/
noncomputable def matrixAddInULeftQuantity {Outcome : Type _}
    (params : Parameters)
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome) : Error :=
  finiteAverage (fun u : Point params =>
    Complex.re (matrixExpectation model.state
      (matrixAddInULeftOperatorAtPoint params model M H S u)))

/-- The matrix right-hand expectation in `add-in-u`. -/
noncomputable def matrixAddInURightQuantity {Outcome : Type _}
    (params : Parameters)
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome) : Error :=
  finiteAverage (fun u : Point params =>
    Complex.re (matrixExpectation model.state
      (matrixAddInURightOperatorAtPoint params model M T S u)))

/-- The concrete evaluated polynomial family `H_[h(u)=a]`. -/
noncomputable def matrixPolynomialEvaluationOutcomeOperatorAtPoint (params : Parameters)
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) (a : Fq params) : MatrixOperator model.space :=
  let evalFamily :=
    MIPStarRE.Quantum.Submeasurement.postprocess (M := H) (fun h => h u)
  evalFamily.effect a

/-- The concrete matched operator `E_a A^u_a H_[h(u)=a]`. -/
noncomputable def matrixHelperAgreementOperatorAtPoint (params : Parameters)
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) : MatrixOperator model.space :=
  matrixAverageOperator (fun a : Fq params =>
    (model.pointMeasurement u).effect a *
      matrixPolynomialEvaluationOutcomeOperatorAtPoint params model H u a)

/-- The concrete averaged matched operator `E_u E_a A^u_a H_[h(u)=a]`. -/
noncomputable def matrixHelperAgreementAverageOperator (params : Parameters)
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) : MatrixOperator model.space :=
  matrixAverageOperator (fun u : Point params =>
    matrixHelperAgreementOperatorAtPoint params model H u)

/-- The concrete helper boundedness gap `Re τ(ρ (Z - E_u Σ_a A^u_a H_[h(u)=a]))`. -/
noncomputable def matrixHelperBoundednessGap (params : Parameters)
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Error :=
  Complex.re (matrixExpectation model.state
    (Z - matrixHelperAgreementAverageOperator params model H))

/-- The concrete projective residual gap `Re τ(ρ (Z (I - Σ_h H_h)))`. -/
noncomputable def matrixProjectiveResidualGap (params : Parameters)
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Error :=
  let total := MIPStarRE.Quantum.Submeasurement.total H
  Complex.re (matrixExpectation model.state (Z * (1 - total)))

/-- Matrix-level version of the `add-in-u` transfer inequality. -/
structure MatrixAddInUTransferStatement {Outcome : Type _}
    (params : Parameters)
    (model : MatrixSdpRealization params)
    (T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (eps delta : Error) : Prop where
  transfer :
    ∀ S : AddInUSelection params Outcome,
      |matrixAddInULeftQuantity params model M H S -
          matrixAddInURightQuantity params model M T S| ≤
        addInUError params eps delta

/-- An optimal primal/dual pair for the section's semidefinite program. -/
structure SdpOptimalPair (params : Parameters)
    (strategy : SymmetricStrategy params)
    (T : Measurement (Polynomial params)) (Z : Operator) : Prop where
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
    (strategy : SymmetricStrategy params) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params), ∃ Z : Operator,
      SdpOptimalPair params strategy T Z

/-- The operator inside the left-hand side of `lem:add-in-u` at a fixed point `u`. -/
noncomputable def addInULeftOperatorAtPoint {Outcome : Type _}
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (M : IndexedSubMeasurement (Point params) Outcome)
    (H : SubMeasurement (Polynomial params))
    (S : AddInUSelection params Outcome)
    (u : Point params) : Operator :=
  match addInUSelectionChoice params S u with
  | some (o, h) =>
      formalTensor ((M u).outcomeOperator o) (H.outcomeOperator h)
  | none => formalZeroOperator

/-- The operator inside the right-hand side of `lem:add-in-u` at a fixed point `u`. -/
noncomputable def addInURightOperatorAtPoint {Outcome : Type _}
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (M : IndexedSubMeasurement (Point params) Outcome)
    (T : Measurement (Polynomial params))
    (S : AddInUSelection params Outcome)
    (u : Point params) : Operator :=
  match addInUSelectionChoice params S u with
  | some (o, h) =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
      formalTensor
        (operatorMul (operatorMul Au ((M u).outcomeOperator o)) Au)
        (T.outcomeOperator h)
  | none => formalZeroOperator

/-- The left-hand expectation in `lem:add-in-u`. -/
noncomputable def addInULeftQuantity {Outcome : Type _} (params : Parameters)
    (strategy : SymmetricStrategy params)
    (M : IndexedSubMeasurement (Point params) Outcome)
    (H : SubMeasurement (Polynomial params))
    (S : AddInUSelection params Outcome) : Error :=
  averageOverDistribution (uniformDistribution (Point params))
    (fun u =>
      operatorExpectation strategy.state
        (addInULeftOperatorAtPoint params strategy M H S u))

/-- The right-hand expectation in `lem:add-in-u`. -/
noncomputable def addInURightQuantity {Outcome : Type _} (params : Parameters)
    (strategy : SymmetricStrategy params)
    (M : IndexedSubMeasurement (Point params) Outcome)
    (T : Measurement (Polynomial params))
    (S : AddInUSelection params Outcome) : Error :=
  averageOverDistribution (uniformDistribution (Point params))
    (fun u =>
      operatorExpectation strategy.state
        (addInURightOperatorAtPoint params strategy M T S u))

/-- The pointwise matched operator `Σ_a A^u_a ⊗ H_[h(u)=a]`. -/
noncomputable def helperAgreementOperatorAtPoint (params : Parameters)
    (strategy : SymmetricStrategy params)
    (H : SubMeasurement (Polynomial params))
    (u : Point params) : Operator :=
  averageOperatorOverDistribution (uniformDistribution (Fq params))
    (fun a =>
      formalTensor
        ((strategy.pointMeasurement u).toSubMeasurement.outcomeOperator a)
        ((evaluateAt params u H).outcomeOperator a))

/-- The average operator `E_u Σ_a A^u_a ⊗ H_[h(u)=a]`. -/
noncomputable def helperAgreementAverageOperator (params : Parameters)
    (strategy : SymmetricStrategy params)
    (H : SubMeasurement (Polynomial params)) : Operator :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (helperAgreementOperatorAtPoint params strategy H)

/-- The helper-stage upper operator `Z ⊗ I`. -/
def helperUpperOperator (params : Parameters) (Z : Operator) : Operator :=
  formalTensor Z (polynomialIdentityOperator params)

/-- The operator measuring the helper-stage boundedness defect. -/
noncomputable def helperBoundednessOperator (params : Parameters)
    (strategy : SymmetricStrategy params)
    (H : SubMeasurement (Polynomial params)) (Z : Operator) : Operator :=
  operatorDifference
    (helperUpperOperator params Z)
    (helperAgreementAverageOperator params strategy H)

/-- The helper-stage boundedness defect. -/
noncomputable def helperBoundednessGap (params : Parameters)
    (strategy : SymmetricStrategy params)
    (H : SubMeasurement (Polynomial params)) (Z : Operator) : Error :=
  operatorExpectation strategy.state
    (helperBoundednessOperator params strategy H Z)

/-- The projective-stage residual operator `Z ⊗ (I - H)`. -/
noncomputable def projectiveResidualOperator (params : Parameters)
    (H : ProjectiveSubMeasurement (Polynomial params))
    (Z : Operator) : Operator :=
  formalTensor Z
    (operatorDifference (polynomialIdentityOperator params) H.toSubMeasurement.totalOperator)

/-- The projective-stage boundedness defect. -/
noncomputable def projectiveBoundednessGap (params : Parameters)
    (strategy : SymmetricStrategy params)
    (H : ProjectiveSubMeasurement (Polynomial params)) (Z : Operator) : Error :=
  operatorExpectation strategy.state
    (projectiveResidualOperator params H Z)

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
  matrixWitness :
    ∃ model : MatrixSdpRealization params,
      ∃ Mmat : MatrixIndexedPointOutcomeFamily params Outcome model.space,
        ∃ Hmat : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space,
          ∃ Tm : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
            MatrixAddInUTransferStatement params model Tm Mmat Hmat eps delta

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
  helperResidualBound :
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
  projectiveResidualBound :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta
  bounded :
    BoundedByOperator strategy.state H.toSubMeasurement Z
      (selfImprovementError params eps delta)

/-- Output package for the explicit bridge from measurement to submeasurement input. -/
structure SelfImprovementSubMeasurementConclusion (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params))
    (H : ProjectiveSubMeasurement (Polynomial params))
    (Z : Operator) (eps delta gamma nu : Error) : Prop where
  measurementBridge :
    ∃ Gmeas : Measurement (Polynomial params),
      Gmeas.toSubMeasurement = G ∧
      SelfImprovementConclusion params strategy Gmeas H Z eps delta gamma nu

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
theorem selfImprovement
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params))
    (hcons : ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      G.toSubMeasurement nu) :
    ∃ H : ProjectiveSubMeasurement (Polynomial params), ∃ Z : Operator,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  sorry

/--
Bridge from the measurement-input version in `self_improvement.tex` to the
submeasurement-input version used in `inductive_step.tex`.
-/
theorem selfImprovementFromSubMeasurement
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params))
    (Gmeas : Measurement (Polynomial params))
    (hbridge : Gmeas.toSubMeasurement = G)
    (hcons : ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      G nu) :
    ∃ H : ProjectiveSubMeasurement (Polynomial params), ∃ Z : Operator,
      SelfImprovementSubMeasurementConclusion params strategy G H Z
        eps delta gamma nu := by
  sorry

end MIPStarRE.LDT.Section9SelfImprovement
