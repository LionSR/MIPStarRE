import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerPositiveSuccessor
import MIPStarRE.LDT.MainInductionStep.Theorems.MainTheorems.Base

/-!
# Dimension-one base case for the simplified induction

The axis-parallel line measurement is the global polynomial measurement
when there is one coordinate. Its point-consistency error is exactly the
axis-parallel test failure, which fits the simplified positive-degree bound.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:441-454`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The one-dimensional answer-valued strategy has a polynomial
measurement with error at most its axis-parallel test failure. -/
theorem simplifiedAnswerDimensionOneAxisMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (hm1 : params.m = 1) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        strategy.axisParallelFailureProbability := by
  classical
  haveI hsub : Subsingleton (Fin params.m) := by
    rw [hm1]
    infer_instance
  let i0 : Fin params.m := ⟨0, by simp [hm1]⟩
  let eSample : AxisParallelTestSample params ≃ Point params :=
    { toFun := fun s => s.1
      invFun := fun u => (u, i0)
      left_inv := fun s => Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }
  let canonicalLine : AxisParallelLine params :=
    AxisParallelLine.throughPoint (params := params) zeroPoint i0
  let G : Measurement (Polynomial params) ι :=
    { toSubMeas :=
        postprocess ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
          (axisLinePolynomialToPolynomial params i0)
      total_eq_one := (strategy.axisParallelMeasurement canonicalLine).total_eq_one }
  have haxisRaw :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (AnswerSymStrat.axisParallelPointAnswerFamily strategy)
        (AnswerSymStrat.axisParallelLineAnswerFamily strategy)
        strategy.axisParallelFailureProbability := by
    exact ⟨le_rfl⟩
  have haxisPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (fun u =>
          postprocess
            ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
            (· zeroCoord))
        strategy.axisParallelFailureProbability := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (fun b => (strategy.pointMeasurement b).toSubMeas)
      (fun u =>
        postprocess
          ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
          (· zeroCoord))
      strategy.axisParallelFailureProbability
    simpa [AnswerSymStrat.axisParallelPointAnswerFamily,
      AnswerSymStrat.axisParallelLineAnswerFamily, axisParallelPointAnswerFamilyOf,
      axisParallelLineAnswerFamilyOf, eSample, i0] using
      ((Preliminaries.consRel_uniform_equiv
        (e := eSample)
        (ψ := strategy.state)
        (A := AnswerSymStrat.axisParallelPointAnswerFamily strategy)
        (B := AnswerSymStrat.axisParallelLineAnswerFamily strategy)
        (δ := strategy.axisParallelFailureProbability)).mp haxisRaw)
  have hfamily :
      (fun u =>
        postprocess
          ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
          (· zeroCoord)) =
        polynomialEvaluationFamily params G.toSubMeas := by
    funext u
    apply SubMeas.ext
    · intro a
      calc
        (postprocess
            ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
            (· zeroCoord)).outcome a
          = (postprocess
              ((strategy.axisParallelMeasurement
                (AxisParallelLine.rebaseAt
                  (AxisParallelLine.throughPoint (params := params) u i0)
                  (AxisParallelLine.sampleParameter (params := params) u i0))).toSubMeas)
              (· zeroCoord)).outcome a := by
                simp [AxisParallelLine.rebaseAt_throughPoint_sampleParameter]
        _ = (postprocess
              ((strategy.axisParallelMeasurement
                (AxisParallelLine.throughPoint (params := params) u i0)).toSubMeas)
              (fun f =>
                f (AxisParallelLine.sampleParameter (params := params) u i0))).outcome a := by
                exact
                  (AxisParallelCovariantMeasurement.reparamInvariant
                    strategy.axisParallelMeasurement) _ _ _
        _ = (postprocess
              ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
              (fun f => f (u i0))).outcome a := by
                have hthrough :
                    AxisParallelLine.throughPoint (params := params) u i0 = canonicalLine := by
                  simpa [canonicalLine] using
                    throughPoint_eq_zeroPoint_of_m_eq_one params hm1 u i0
                simp [hthrough, AxisParallelLine.sampleParameter]
        _ = (polynomialEvaluationFamily params G.toSubMeas u).outcome a := by
              simp [polynomialEvaluationFamily, evaluateAt, G,
                axisLinePolynomialToPolynomial_apply]
    · change
          (postprocess
              ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
              (· zeroCoord)).total =
            (postprocess ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
              (fun f => f (u i0))).total
      rw [show
          (postprocess
              ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
              (· zeroCoord)).total =
            (strategy.axisParallelMeasurement { base := u, direction := i0 }).total by rfl]
      rw [show
          (postprocess ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
              (fun f => f (u i0))).total =
            (strategy.axisParallelMeasurement canonicalLine).total by rfl]
      rw [(strategy.axisParallelMeasurement { base := u, direction := i0 }).total_eq_one,
        (strategy.axisParallelMeasurement canonicalLine).total_eq_one]
  have hconsG :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        strategy.axisParallelFailureProbability := by
    simpa [hfamily] using haxisPoint
  exact ⟨G, hconsG⟩

/-- Positive-degree dimension-one base case for the simplified
answer-valued induction. -/
theorem simplifiedAnswerPositiveDegreeBase
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hm1 : params.m = 1)
    (hd : 0 < params.d)
    (heps1 : eps ≤ 1) :
    SimplifiedAnswerInductionConclusion params strategy eps delta gamma := by
  obtain ⟨G, hG⟩ := simplifiedAnswerDimensionOneAxisMeasurement params strategy hm1
  have heps0 := answer_eps_nonneg_of_isGood params strategy hgood
  have hepsPower : eps ≤ Real.rpow eps (1 / (32 : Error)) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' heps0 heps1
      (by positivity : (0 : Error) ≤ 1 / 32)
      (by norm_num : (1 / (32 : Error)) ≤ 1)
  have hdelta0 := answer_delta_nonneg_of_isGood params strategy hgood
  have hgamma0 := answer_gamma_nonneg_of_isGood params strategy hgood
  have hratio0 : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  have hcoef : (1 : Error) ≤
      1000 * (params.d : Error) ^ (2 : ℕ) * (params.m : Error) ^ (4 : ℕ) := by
    have hd1 : (1 : Error) ≤ params.d := by exact_mod_cast hd
    simp [hm1]
    nlinarith [sq_nonneg ((params.d : Error) - 1)]
  have herror : eps ≤ simplifiedMainInductionError params eps delta gamma := by
    simp only [simplifiedMainInductionError, Nat.ne_of_gt hd, if_false,
      simplifiedPositiveDegreeError]
    have hsum : Real.rpow eps (1 / (32 : Error)) ≤
        Real.rpow eps (1 / (32 : Error)) +
          Real.rpow delta (1 / (32 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) +
          Real.rpow gamma (1 / (8 : Error)) := by
      have hδ := Real.rpow_nonneg hdelta0 (1 / (32 : Error))
      have hθ := Real.rpow_nonneg hratio0 (1 / (32 : Error))
      have hγ := Real.rpow_nonneg hgamma0 (1 / (8 : Error))
      change 0 ≤ Real.rpow delta (1 / (32 : Error)) at hδ
      change 0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
        (1 / (32 : Error)) at hθ
      change 0 ≤ Real.rpow gamma (1 / (8 : Error)) at hγ
      linarith
    let S := Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) +
      Real.rpow gamma (1 / (8 : Error))
    have hS0 : 0 ≤ S := by
      dsimp [S]
      positivity
    have hscale : S ≤
        (1000 * (params.d : Error) ^ (2 : ℕ) *
          (params.m : Error) ^ (4 : ℕ)) * S := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) hS0]
    exact (hepsPower.trans hsum).trans hscale
  exact ⟨G, ConsRel.mono (hgood.axisParallelTest.trans herror) hG⟩

end MIPStarRE.LDT.MainInductionStep
