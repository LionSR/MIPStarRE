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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The averaged point operator `A_g = E_u A^u_{g(u)}`. -/
noncomputable def averagedPointOperator (params : Parameters)
    (strategy : SymStrat params ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g)

/-- The operator `T_g A_g` contributing to the primal SDP objective. -/
noncomputable def sdpPrimalContributionOperator (params : Parameters)
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  T.outcome g * averagedPointOperator params strategy g

/-- The formal primal objective operator `Σ_g T_g A_g`. -/
noncomputable def sdpPrimalObjectiveOperator (params : Parameters)
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (polynomialDistribution params)
    (sdpPrimalContributionOperator params strategy T)

/-- The primal objective value `Σ_g Tr(T_g A_g)`. -/
noncomputable def sdpPrimalObjective (params : Parameters)
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι) : Error :=
  Complex.re (MIPStarRE.Quantum.normalizedTrace (sdpPrimalObjectiveOperator params strategy T))

/-- The dual objective value `Tr(Z)`. -/
noncomputable def sdpDualObjective (Z : MIPStarRE.Quantum.Op ι) : Error :=
  Complex.re (MIPStarRE.Quantum.normalizedTrace Z)

/-- The dual slack operator `Z - A_g`. -/
noncomputable def sdpDualSlackOperator (params : Parameters)
    (strategy : SymStrat params ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  Z - averagedPointOperator params strategy g

/-- The complementary-slackness equation `T_g Z = T_g A_g`. -/
def sdpComplementarySlacknessEquation (params : Parameters)
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) : Prop :=
  T.outcome g * Z =
    T.outcome g * averagedPointOperator params strategy g

private theorem pointConditionedOutcomeOperatorAtPolynomial_hermitian
    (params : Parameters) (strategy : SymStrat params ι)
    (h : Polynomial params) (u : Point params) :
    (pointConditionedOutcomeOperatorAtPolynomial params strategy h u)ᴴ =
      pointConditionedOutcomeOperatorAtPolynomial params strategy h u := by
  simpa [pointConditionedOutcomeOperatorAtPolynomial] using
    ProjMeas.outcome_hermitian (strategy.pointMeasurement u) (h u)

private theorem projection_sandwich_le_of_le_one
    (P B : MIPStarRE.Quantum.Op ι)
    (hPherm : Pᴴ = P) (hPproj : P * P = P) (hBle : B ≤ 1) :
    P * B * P ≤ P := by
  have hsand :
      0 ≤ P * (1 - B) * P := by
    simpa [hPherm] using
      (Matrix.PosSemidef.mul_mul_conjTranspose_same
        (Matrix.nonneg_iff_posSemidef.mp (by simpa using hBle))
        P).nonneg
  change 0 ≤ P - P * B * P
  simpa [Matrix.mul_sub, Matrix.sub_mul, hPproj, mul_assoc] using hsand

/-- The pointwise sandwiched operator `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def sandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (u : Point params) (h : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
  Au * (T.outcome h) * Au

/-- The pointwise sandwiched submeasurement `H^u = {H^u_h}`. -/
noncomputable def sandwichedPolynomialSubMeasAt (params : Parameters)
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι) (u : Point params) :
    SubMeas (Polynomial params) ι :=
  { outcome := sandwichedPolynomialOutcomeOperatorAt params strategy T u
    total := ∑ h : Polynomial params,
      sandwichedPolynomialOutcomeOperatorAt params strategy T u h
    outcome_pos := by
      intro h
      simpa [sandwichedPolynomialOutcomeOperatorAt,
        pointConditionedOutcomeOperatorAtPolynomial_hermitian params strategy h u] using
        (Matrix.PosSemidef.mul_mul_conjTranspose_same
          (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h))
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h u)).nonneg
    sum_eq_total := by
      rfl
    total_le_one := by
      let Pu := strategy.pointMeasurement u
      let Tu : SubMeas (Fq params) ι :=
        postprocess T.toSubMeas (fun h : Polynomial params => h u)
      calc
        ∑ h : Polynomial params, sandwichedPolynomialOutcomeOperatorAt params strategy T u h
          = ∑ a : Fq params, Pu.outcome a * Tu.outcome a * Pu.outcome a := by
              calc
                ∑ h : Polynomial params, sandwichedPolynomialOutcomeOperatorAt params strategy T u h
                  = ∑ a : Fq params, ∑ h : Polynomial params with h u = a,
                      sandwichedPolynomialOutcomeOperatorAt params strategy T u h := by
                        symm
                        exact
                          Finset.sum_fiberwise Finset.univ
                            (fun h : Polynomial params => h u)
                            (sandwichedPolynomialOutcomeOperatorAt params strategy T u)
                _ = ∑ a : Fq params, Pu.outcome a * Tu.outcome a * Pu.outcome a := by
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      simp [Pu, Tu, sandwichedPolynomialOutcomeOperatorAt,
                        pointConditionedOutcomeOperatorAtPolynomial,
                        postprocess, Matrix.mul_sum, Matrix.sum_mul, mul_assoc]
        _ ≤ ∑ a : Fq params, Pu.outcome a := by
              refine Finset.sum_le_sum ?_
              intro a _
              exact projection_sandwich_le_of_le_one
                (Pu.outcome a)
                (Tu.outcome a)
                (ProjMeas.outcome_hermitian Pu a)
                (Pu.proj a)
                (SubMeas.outcome_le_one Tu a)
        _ = 1 := by
              simpa using Measurement.sum_eq Pu }

/-- The averaged sandwiched submeasurement `H_h = E_u H^u_h`. -/
noncomputable def averagedSandwichedPolynomialSubMeas (params : Parameters)
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι) : SubMeas (Polynomial params) ι :=
  { outcome := fun h =>
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
    total := ∑ h : Polynomial params,
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
    outcome_pos := by
      intro h
      simp [averageOperatorOverDistribution, uniformDistribution]
      apply Finset.sum_nonneg
      intro u hu
      exact smul_nonneg (by positivity)
        ((sandwichedPolynomialSubMeasAt params strategy T u).outcome_pos h)
    sum_eq_total := by
      rfl
    total_le_one := by
      calc
        ∑ h : Polynomial params,
            averageOperatorOverDistribution (uniformDistribution (Point params))
              (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
          = averageOperatorOverDistribution (uniformDistribution (Point params))
              (fun u => ∑ h : Polynomial params,
                sandwichedPolynomialOutcomeOperatorAt params strategy T u h) := by
                  calc
                    ∑ h : Polynomial params,
                        averageOperatorOverDistribution (uniformDistribution (Point params))
                          (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
                      = ∑ u ∈ (uniformDistribution (Point params)).support,
                          ∑ h : Polynomial params,
                            (uniformDistribution (Point params)).weight u •
                              sandwichedPolynomialOutcomeOperatorAt params strategy T u h := by
                                simp_rw [averageOperatorOverDistribution]
                                rw [Finset.sum_comm]
                    _ = averageOperatorOverDistribution (uniformDistribution (Point params))
                        (fun u => ∑ h : Polynomial params,
                          sandwichedPolynomialOutcomeOperatorAt params strategy T u h) := by
                            simp [averageOperatorOverDistribution, Finset.smul_sum]
        _ ≤ ∑ u : Point params,
            (1 / (Fintype.card (Point params) : Error)) • (1 : MIPStarRE.Quantum.Op ι) := by
              simp [averageOperatorOverDistribution, uniformDistribution]
              exact Finset.sum_le_sum fun u _ =>
                smul_le_smul_of_nonneg_left
                  ((sandwichedPolynomialSubMeasAt params strategy T u).total_le_one)
                  (by positivity)
        _ = 1 := by
              have hcard : (Fintype.card (Point params) : Error) ≠ 0 := by positivity
              ext i j
              by_cases hij : i = j
              · subst hij
                simp [Finset.sum_const, nsmul_eq_mul, hcard]
              · simp [Finset.sum_const, hij, hcard] }

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
