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
  identityOperator s!"poly({params.m},{params.q},{params.d})"

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

end MIPStarRE.LDT.Section9SelfImprovement
