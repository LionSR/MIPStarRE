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
open MIPStarRE.Quantum
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
    (T : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  T.outcome g * averagedPointOperator params strategy g

/-- The formal primal objective operator `Σ_g T_g A_g`. -/
noncomputable def sdpPrimalObjectiveOperator (params : Parameters)
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : MIPStarRE.Quantum.Op ι :=
  ∑ g : Polynomial params, sdpPrimalContributionOperator params strategy T g

/-- The primal objective value `Σ_g Tr(T_g A_g)`. -/
noncomputable def sdpPrimalObjective (params : Parameters)
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  Complex.re (Matrix.trace (sdpPrimalObjectiveOperator params strategy T))

/-- The dual objective value `Tr(Z)`. -/
noncomputable def sdpDualObjective (Z : MIPStarRE.Quantum.Op ι) : Error :=
  Complex.re (Matrix.trace Z)

/-- The dual slack operator `Z - A_g`. -/
noncomputable def sdpDualSlackOperator (params : Parameters)
    (strategy : SymStrat params ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  Z - averagedPointOperator params strategy g

/-- The complementary-slackness equation `T_g Z = T_g A_g`. -/
def sdpComplementarySlacknessEquation (params : Parameters)
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) : Prop :=
  T.outcome g * Z =
    T.outcome g * averagedPointOperator params strategy g

/-- The pointwise sandwiched operator `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def sandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (h : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
  Au * (T.outcome h) * Au

/-- The pointwise sandwiched submeasurement `H^u = {H^u_h}`. -/
noncomputable def sandwichedPolynomialSubMeasAt (params : Parameters)
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (u : Point params) :
    SubMeas (Polynomial params) ι :=
  { outcome := sandwichedPolynomialOutcomeOperatorAt params strategy T u
    total := ∑ h : Polynomial params,
      sandwichedPolynomialOutcomeOperatorAt params strategy T u h
    outcome_pos := by
      intro h
      simp only [sandwichedPolynomialOutcomeOperatorAt, pointConditionedOutcomeOperatorAtPolynomial]
      exact sandwich_nonneg (T.outcome_pos h)
        (SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas (h u))
    sum_eq_total := by
      rfl
    total_le_one := by
      let Au := (strategy.pointMeasurement u)
      -- Regroup by evaluation value a = h(u)
      calc
        ∑ h : Polynomial params, sandwichedPolynomialOutcomeOperatorAt params strategy T u h
          = ∑ a : Fq params,
              ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                Au.toSubMeas.outcome a * T.outcome h * Au.toSubMeas.outcome a := by
              rw [show ∑ h : Polynomial params,
                    sandwichedPolynomialOutcomeOperatorAt params strategy T u h =
                  ∑ a : Fq params,
                    ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                      sandwichedPolynomialOutcomeOperatorAt params strategy T u h from by
                simpa using (Finset.sum_fiberwise Finset.univ
                  (fun h : Polynomial params => h u)
                  (sandwichedPolynomialOutcomeOperatorAt params strategy T u)).symm]
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro h hh
              simp only [sandwichedPolynomialOutcomeOperatorAt,
                pointConditionedOutcomeOperatorAtPolynomial]
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
              simp [Au, hh]
        _ = ∑ a : Fq params,
              Au.toSubMeas.outcome a *
                (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                  T.outcome h) *
                Au.toSubMeas.outcome a := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [← Matrix.sum_mul, ← Matrix.mul_sum]
        _ ≤ ∑ a : Fq params, Au.toSubMeas.outcome a := by
              refine Finset.sum_le_sum ?_
              intro a _
              -- The filtered sum is bounded by the total operator, hence by `1`.
              have hfilt_le_one : ∑ h ∈ Finset.univ.filter
                  (fun h : Polynomial params => h u = a), T.outcome h ≤ 1 := by
                calc ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                        T.outcome h
                    ≤ ∑ h : Polynomial params, T.outcome h :=
                      Finset.sum_le_sum_of_subset_of_nonneg
                        (Finset.filter_subset _ _) (fun h _ _ => T.outcome_pos h)
                  _ = T.total := T.sum_eq_total
                  _ ≤ 1 := T.total_le_one
              simpa [Au.proj a] using
                sandwich_mono
                  (M := Au.toSubMeas.outcome a)
                  (hMH := Au.outcome_hermitian a)
                  (hPQ := hfilt_le_one)
        _ = Au.toSubMeas.total := by
              rw [Au.toSubMeas.sum_eq_total]
        _ = 1 := by
              simpa using Au.total_eq_one }

/-- The averaged sandwiched submeasurement `H_h = E_u H^u_h`. -/
noncomputable def averagedSandwichedPolynomialSubMeas (params : Parameters)
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : SubMeas (Polynomial params) ι :=
  { outcome := fun h =>
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
    total := ∑ h : Polynomial params,
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
    outcome_pos := by
      intro h
      simp only [averageOperatorOverDistribution]
      apply Finset.sum_nonneg
      intro u _
      exact smul_nonneg
        ((uniformDistribution (Point params)).nonnegative u)
        ((sandwichedPolynomialSubMeasAt params strategy T u).outcome_pos h)
    sum_eq_total := by
      rfl
    total_le_one := by
      let 𝒟 := uniformDistribution (Point params)
      calc
        ∑ h : Polynomial params,
            averageOperatorOverDistribution 𝒟
              (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
          = ∑ u ∈ 𝒟.support, 𝒟.weight u •
              ∑ h : Polynomial params,
                sandwichedPolynomialOutcomeOperatorAt
                  params strategy T u h := by
                simp only [averageOperatorOverDistribution]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl ?_
                intro u _
                rw [← Finset.smul_sum]
        _ = ∑ u ∈ 𝒟.support, 𝒟.weight u •
              (sandwichedPolynomialSubMeasAt params strategy T u).total := by
                refine Finset.sum_congr rfl ?_
                intro u _
                simp [sandwichedPolynomialSubMeasAt]
        _ ≤ ∑ u ∈ 𝒟.support, 𝒟.weight u • (1 : MIPStarRE.Quantum.Op ι) := by
              exact Finset.sum_le_sum fun u _ =>
                smul_le_smul_of_nonneg_left
                  (sandwichedPolynomialSubMeasAt params strategy T u).total_le_one
                  (𝒟.nonnegative u)
        _ = (∑ u ∈ 𝒟.support, 𝒟.weight u) • (1 : MIPStarRE.Quantum.Op ι) := by
              rw [Finset.sum_smul]
        _ ≤ (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
              exact smul_le_smul_of_nonneg_right
                (uniformDistribution_weight_sum_le_one (Point params)) zero_le_one
        _ = 1 := by simp }

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
