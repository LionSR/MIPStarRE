import MIPStarRE.LDT.GlobalVariance.Theorems
set_option linter.style.longLine false

/-!
Matching scaffold for Section 9 of the low individual degree paper in
`references/ldt-paper/self_improvement.tex`.

This file exposes the paper's SDP witnesses, the `add-in-u` transfer identity,
and the non-projective/projective self-improvement outputs through explicit named
constructions and error terms.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- The identity operator on the polynomial register. -/
def polynomialIdentityOperator (params : Parameters) : Operator d :=
  idOp s!"poly({params.m},{params.q},{params.d})"

/-- The pointwise operator `A^u_{g(u)}` entering the SDP average `A_g`. -/
def averagedPointOperatorContribution (params : Parameters)
    (strategy : SymStrat params d)
    (g : Polynomial params) (u : Point params) : Operator d :=
  pointConditionedOutcomeOperatorAtPolynomial params strategy g u

/-- The averaged point operator `A_g = E_u A^u_{g(u)}`. -/
noncomputable def averagedPointOperator (params : Parameters)
    (strategy : SymStrat params d) (g : Polynomial params) : Operator d :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (averagedPointOperatorContribution params strategy g)

/-- The operator `T_g A_g` contributing to the primal SDP objective. -/
noncomputable def sdpPrimalContributionOperator (params : Parameters)
    (strategy : SymStrat params d)
    (T : Measurement (Polynomial params) d)
    (g : Polynomial params) : Operator d :=
  opMul (T.outcome g) (averagedPointOperator params strategy g)

/-- The formal primal objective operator `Σ_g T_g A_g`. -/
noncomputable def sdpPrimalObjectiveOperator (params : Parameters)
    (strategy : SymStrat params d)
    (T : Measurement (Polynomial params) d) : Operator d :=
  averageOperatorOverDistribution (polynomialDistribution params)
    (sdpPrimalContributionOperator params strategy T)

/-- The primal objective value `Σ_g Tr(T_g A_g)`. -/
noncomputable def sdpPrimalObjective (params : Parameters)
    (strategy : SymStrat params d)
    (T : Measurement (Polynomial params) d) : Error :=
  operatorTrace (sdpPrimalObjectiveOperator params strategy T)

/-- The dual objective value `Tr(Z)`. -/
noncomputable def sdpDualObjective (Z : Operator d) : Error :=
  operatorTrace Z

/-- The dual slack operator `Z - A_g`. -/
noncomputable def sdpDualSlackOperator (params : Parameters)
    (strategy : SymStrat params d)
    (Z : Operator d) (g : Polynomial params) : Operator d :=
  opDiff Z (averagedPointOperator params strategy g)

/-- The complementary-slackness equation `T_g Z = T_g A_g`. -/
def sdpComplementarySlacknessEquation (params : Parameters)
    (strategy : SymStrat params d)
    (T : Measurement (Polynomial params) d)
    (Z : Operator d) (g : Polynomial params) : Prop :=
  opMul (T.outcome g) Z =
    opMul (T.outcome g) (averagedPointOperator params strategy g)

/-- The pointwise sandwiched operator `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def sandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    (strategy : SymStrat params d)
    (T : Measurement (Polynomial params) d)
    (u : Point params) (h : Polynomial params) : Operator d :=
  let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
  opMul (opMul Au (T.outcome h)) Au

/-- The pointwise sandwiched submeasurement `H^u = {H^u_h}`. -/
noncomputable def sandwichedPolynomialSubMeasAt (params : Parameters)
    (strategy : SymStrat params d)
    (T : Measurement (Polynomial params) d) (u : Point params) :
    SubMeas (Polynomial params) d :=
  { name :=
      s!"Hslice[{pointCode params u}|{(strategy.pointMeasurement u).toSubMeas.name}|{T.toSubMeas.name}]"
    outcome := sandwichedPolynomialOutcomeOperatorAt params strategy T u
    total :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (sandwichedPolynomialOutcomeOperatorAt params strategy T u) }

/-- The averaged sandwiched submeasurement `H_h = E_u H^u_h`. -/
noncomputable def averagedSandwichedPolynomialSubMeas (params : Parameters)
    (strategy : SymStrat params d)
    (T : Measurement (Polynomial params) d) : SubMeas (Polynomial params) d :=
  { name := s!"Havg[{T.toSubMeas.name}]"
    outcome := fun h =>
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
    total :=
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => (sandwichedPolynomialSubMeasAt params strategy T u).total) }

/-- Evaluate a polynomial submeasurement at each point `u`. -/
noncomputable abbrev polynomialEvaluationFamily (params : Parameters)
    (H : SubMeas (Polynomial params) d) :
    IdxSubMeas (Point params) (Fq params) d :=
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
  MainInductionStep.selfImprovementInInductionError params eps delta 0

end MIPStarRE.LDT.SelfImprovement
