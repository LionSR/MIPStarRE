import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.AnswerFields
import MIPStarRE.LDT.Pasting.Simplified.PastingScalarBounds

/-!
# Simplified pasting for answer-valued symmetric strategies

The answer-valued diagonal-line test supplies the commutativity conclusion
for the ordinary point-equivalent carrier. The explicit first-success
pasting construction then applies with the same exponential-free error
as for an ordinary symmetric strategy.

## References

- `blueprint/src/low_degree_simplified.tex`, `thm:ld-pasting`.
- `references/ldt-paper/inductive_step.tex:461-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.Pasting
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Positive-degree simplified pasting for an answer-valued ambient
strategy. The dummy diagonal measurement of the ordinary carrier is used
only to carry the state and point/axis measurements; commutativity is
proved from the genuine answer-valued diagonal-line test. -/
theorem answerLdPastingSimplified
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput
      (answerSelfImprovementCarrier params.next strategy) family zeta)
    (hd : 0 < params.d)
    (k : ℕ) (hdk : params.d < k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (simplifiedPastingPaperError params k eps delta gamma kappa zeta) := by
  classical
  let carrier := answerSelfImprovementCarrier params.next strategy
  have heps0 := answer_eps_nonneg_of_isGood params.next strategy hgood
  have hdelta0 := answer_delta_nonneg_of_isGood params.next strategy hgood
  have hgamma0 := answer_gamma_nonneg_of_isGood params.next strategy hgood
  have hconsCarrier : family.ConsistentWithPoints carrier zeta := by
    exact ⟨by simpa [carrier, answerSelfImprovementCarrier] using hcons⟩
  have hzeta0 := IdxPolyFamily.zeta_nonneg_of_consistentWithPoints
    carrier family hconsCarrier
  have hkappa0 := kappa_nonneg_of_complete params carrier family
    (by simpa [carrier, answerSelfImprovementCarrier] using hcomplete)
  by_cases hregime : eps ≤ 1 ∧ delta ≤ 1 ∧ gamma ≤ 1 ∧
      zeta ≤ 1 ∧ params.d ≤ params.q
  · rcases hregime with ⟨heps1, hdelta1, hgamma1, hzeta1, hdq⟩
    have hcom := answerComMainForCarrier_ofAnswerGood
      params strategy eps delta gamma zeta hgood hgamma0
      family hcons hself hbound
    have hfacts := gHatFacts_ofComMainAndSelfConsistency
      params carrier family gamma zeta
      hgamma0 hgamma1 hzeta0 hzeta1 hdq hcom hself
    have hsc : SDDRel carrier.state (uniformDistribution (Fq params))
        (gHatSelfConsistencyLeftFamily params family)
        (gHatSelfConsistencyRightFamily params family) (2 * zeta) := by
      simpa [gHatSelfConsistencyError] using hfacts.completedSelfConsistency
    have haxis : carrier.axisParallelFailureProbability ≤ eps := by
      simpa [carrier, answerSelfImprovementCarrier,
        SymStrat.axisParallelFailureProbability,
        AnswerSymStrat.axisParallelFailureProbability,
        axisParallelPointAnswerFamily, axisParallelLineAnswerFamily,
        AnswerSymStrat.axisParallelPointAnswerFamily,
        AnswerSymStrat.axisParallelLineAnswerFamily] using hgood.axisParallelTest
    have hselfGood : carrier.selfConsistencyFailureProbability ≤ delta := by
      simpa [carrier, answerSelfImprovementCarrier,
        SymStrat.selfConsistencyFailureProbability,
        AnswerSymStrat.selfConsistencyFailureProbability] using
        hgood.selfConsistencyTest
    have hraw := distinctSuccessPastedMeasurement_pointConsistency
      params carrier family eps delta gamma kappa zeta
      haxis hselfGood hconsCarrier hzeta0 hzeta1 hcom hself
      (by simpa [carrier, answerSelfImprovementCarrier] using hcomplete)
      hsc k hdk
    have hscalar := distinctSuccessPastingError_le_paperBound
      params k eps delta gamma kappa zeta
      hd hdk hdq heps0 heps1 hdelta0 hdelta1 hgamma0 hzeta0 hzeta1
    refine ⟨distinctSuccessPastedMeasurement params family k, ?_⟩
    exact ConsRel.mono
      (by simpa [simplifiedPastingPaperError] using hscalar)
      (by simpa [carrier, answerSelfImprovementCarrier] using hraw)
  · have hbad : 1 < eps ∨ 1 < delta ∨ 1 < gamma ∨
        1 < zeta ∨ params.q < params.d := by
      by_contra h
      push Not at h
      exact hregime ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    have hcomponent :
        1 ≤ Real.rpow eps (1 / (8 : Error)) ∨
        1 ≤ Real.rpow delta (1 / (8 : Error)) ∨
        1 ≤ Real.rpow gamma (1 / (8 : Error)) ∨
        1 ≤ Real.rpow zeta (1 / (8 : Error)) ∨
        1 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (8 : Error)) := by
      rcases hbad with h | h | h | h | h
      · exact Or.inl (le_of_lt (Real.one_lt_rpow h (by norm_num)))
      · exact Or.inr (Or.inl (le_of_lt (Real.one_lt_rpow h (by norm_num))))
      · exact Or.inr (Or.inr (Or.inl
          (le_of_lt (Real.one_lt_rpow h (by norm_num)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (le_of_lt (Real.one_lt_rpow h (by norm_num))))))
      · have hq : (0 : Error) < (params.q : Error) := by exact_mod_cast params.hq
        have hratio : (1 : Error) <
            (params.d : Error) / (params.q : Error) := by
          apply (lt_div_iff₀ hq).2
          have hcast : (params.q : Error) < (params.d : Error) := by
            exact_mod_cast h
          simpa using hcast
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (le_of_lt (Real.one_lt_rpow hratio (by norm_num))))))
    have hsum := one_le_pastingEighthSum_of_component
      params eps delta gamma zeta heps0 hdelta0 hgamma0 hzeta0 hcomponent
    have herror := one_le_simplifiedPastingPaperError_of_large_sum
      params k eps delta gamma kappa zeta hdk hkappa0 hsum
    let H : Measurement (Polynomial params.next) ι :=
      Measurement.trivialDistinguishedOutcome (fallbackInterpolatedPolynomial params)
    refine ⟨H, ?_⟩
    exact ⟨le_trans
      (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)) herror⟩

end MIPStarRE.LDT.MainInductionStep
