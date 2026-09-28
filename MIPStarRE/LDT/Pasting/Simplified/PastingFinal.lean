import MIPStarRE.LDT.Pasting.Simplified.PastingCompletion
import MIPStarRE.LDT.Pasting.Simplified.SuccessProbabilityStability
import MIPStarRE.LDT.Pasting.GHatFacts

/-!
# Completed measurement from simplified pasting

The distinct-success interpolant is completed at a fixed polynomial.
Its point consistency follows from the positive-contraction line bound
and its first-moment completeness estimate.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:ld-pasting`.
- `references/ldt-paper/ld-pasting.tex`, `thm:ld-pasting`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit consistency error for the completed distinct-success pasted
measurement before the final coarse parameter absorption. -/
noncomputable def distinctSuccessPastingError
    (params : Parameters) (k : ℕ)
    (eps delta gamma kappa zeta : Error) : Error :=
  (2 * (k : Error) *
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
    2 * (k : Error) * ((k : Error) - 1) *
      (Real.sqrt (Commutativity.comMainError params gamma zeta) +
        4 * Real.sqrt zeta) +
    Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
  ((k : Error) / ((k - params.d : ℕ) : Error) * kappa +
    Real.sqrt (2 * zeta) * marginalRootBudget k /
      ((k - params.d : ℕ) : Error) +
    ((k : Error) ^ (2 : ℕ)) / (params.q : Error))

/-- The completed distinct-success pasted measurement has the explicit
positive-contraction consistency bound. -/
theorem distinctSuccessPastedMeasurement_pointConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le_one : zeta ≤ 1)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hcomplete : family.Complete strategy.state kappa)
    (hsc : SDDRel strategy.state (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta))
    (k : ℕ) (hdk : params.d < k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (distinctSuccessPastedMeasurement params family k).toSubMeas)
      (distinctSuccessPastingError params k eps delta gamma kappa zeta) := by
  let H := distinctSuccessPastedSubMeas params family k
  let ν := 2 * (k : Error) *
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
    2 * (k : Error) * ((k : Error) - 1) *
      (Real.sqrt (Commutativity.comMainError params gamma zeta) +
        4 * Real.sqrt zeta) +
    Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)
  let μ := (k : Error) / ((k - params.d : ℕ) : Error) * kappa +
    Real.sqrt (2 * zeta) * marginalRootBudget k /
      ((k - params.d : ℕ) : Error) +
    ((k : Error) ^ (2 : ℕ)) / (params.q : Error)
  have hpoint : ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H) ν :=
    distinctSuccessPasted_pointConsistency_coarse
      params strategy family eps delta gamma zeta haxis hself_good
      hcons hzeta_nonneg hzeta_le_one hcom hself hsc k
  have hmass : 1 - μ ≤
      ev strategy.state (leftTensor (ι₂ := ι) H.total) := by
    have h := distinctSuccessPastedMass_ge_rootBudget
      params strategy family k (Classical.arbitrary (Point params))
      strategy.state strategy.isNormalized hdk kappa zeta hcomplete hsc
    dsimp [H, μ]
    convert h using 1; ring
  have hcompleted := pointConsistency_completeAtOutcome
    params strategy H (fallbackInterpolatedPolynomial params) ν μ hpoint hmass
  simpa [distinctSuccessPastedMeasurement, H, distinctSuccessPastingError,
    ν, μ] using hcompleted

/-- Source-facing hypotheses for the explicit simplified pasting
construction. The commutativity and completed-slice estimates used by
the analytic proof are derived from the four slice-family conditions. -/
theorem distinctSuccessPastedMeasurement_pointConsistency_ofPaperHypotheses
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le_one : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le_one : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) (hdk : params.d < k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (distinctSuccessPastedMeasurement params family k).toSubMeas)
      (distinctSuccessPastingError params k eps delta gamma kappa zeta) := by
  have hcom := Commutativity.comMain params strategy eps delta gamma zeta
    strategy.isNormalized hgood family hcons hself hbound
  have hfacts := gHatFacts params strategy family eps delta gamma zeta
    hgamma_nonneg hgamma_le_one hzeta_nonneg hzeta_le_one hdq_le
    hgood hcons hself hbound
  have hsc : SDDRel strategy.state (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family) (2 * zeta) := by
    simpa [gHatSelfConsistencyError] using hfacts.completedSelfConsistency
  exact distinctSuccessPastedMeasurement_pointConsistency
    params strategy family eps delta gamma kappa zeta
    hgood.axisParallelTest hgood.selfConsistencyTest hcons
    hzeta_nonneg hzeta_le_one hcom hself hcomplete hsc k hdk

/-- The attempt count selected internally for the positive-degree
induction step. -/
def simplifiedInductionAttemptCount (params : Parameters) : ℕ :=
  (params.m + 1) * params.d

/-- The explicit exponential-free induction pasting error, with its
attempt count fixed by the source proof. -/
noncomputable def simplifiedInductionPastingError
    (params : Parameters) (eps delta gamma kappa zeta : Error) : Error :=
  distinctSuccessPastingError params (simplifiedInductionAttemptCount params)
    eps delta gamma kappa zeta

/-- Positive-degree pasting with the attempt count internal to the
construction. The numerical coarsening to the paper's `21` constant is
a separate scalar step. -/
theorem distinctSuccessPastedMeasurement_induction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le_one : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le_one : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (distinctSuccessPastedMeasurement params family
          (simplifiedInductionAttemptCount params)).toSubMeas)
      (simplifiedInductionPastingError params eps delta gamma kappa zeta) := by
  have hdk : params.d < simplifiedInductionAttemptCount params := by
    unfold simplifiedInductionAttemptCount
    have hm0 := params.hm
    have hm : 2 ≤ params.m + 1 := by omega
    have htwo : params.d < 2 * params.d := by omega
    exact htwo.trans_le (Nat.mul_le_mul_right params.d hm)
  exact distinctSuccessPastedMeasurement_pointConsistency_ofPaperHypotheses
    params strategy family eps delta gamma kappa zeta
    hgood hgamma_nonneg hgamma_le_one hzeta_nonneg hzeta_le_one
    hdq_le hcomplete hcons hself hbound
    (simplifiedInductionAttemptCount params) hdk

end MIPStarRE.LDT.Pasting
