import MIPStarRE.LDT.Basic.LinePolynomialEmbedding
import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementBridge
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds
import MIPStarRE.LDT.MainInductionStep.Theorems.PackageConstructors
import MIPStarRE.LDT.MainInductionStep.Theorems.AvgSliceErrors
import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly

/-!
# Section 6 — Main Induction Theorems

The top-level induction theorems: `mainInductionBaseCase`,
`mainInductionByRecursionOnM`, `mainInductionPublicWrapper`, and their
answer-valued analogues.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Direct base case of `thm:main-induction` when `m = 1`.

The paper uses the unique axis-parallel line measurement as the global
polynomial measurement in this case. -/
theorem mainInductionBaseCase
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hm1 : params.m = 1)
    (hgood : strategy.IsGood eps delta gamma) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  classical
  haveI hsub : Subsingleton (Fin params.m) := by
    rw [hm1]
    infer_instance
  let i0 : Fin params.m := ⟨0, by simp [hm1]⟩
  let eSample : AxisParallelTestSample params ≃ Point params :=
    { toFun := fun s => s.1
      invFun := fun u => (u, i0)
      left_inv := by
        intro s
        rcases s with ⟨u, j⟩
        have hj : j = i0 := Subsingleton.elim _ _
        simp [hj, i0]
      right_inv := by
        intro u
        rfl }
  let canonicalLine : AxisParallelLine params :=
    AxisParallelLine.throughPoint (params := params) zeroPoint i0
  let G : Measurement (Polynomial params) ι :=
    { toSubMeas :=
        postprocess ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
          (axisLinePolynomialToPolynomial params i0)
      total_eq_one := (strategy.axisParallelMeasurement canonicalLine).total_eq_one }
  have haxisRaw :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
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
    simpa [IdxProjMeas.toIdxSubMeas, axisParallelPointAnswerFamily,
      axisParallelLineAnswerFamily, eSample, i0] using
      ((Preliminaries.consRel_uniform_equiv
        (e := eSample)
        (ψ := strategy.state)
        (A := axisParallelPointAnswerFamily strategy)
        (B := axisParallelLineAnswerFamily strategy)
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
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hgood.selfConsistencyTest
  have hdiag_nonneg : 0 ≤ strategy.diagonalFailureProbability :=
    diagonalFailureProbability_nonneg params strategy
  have hgamma_nonneg : 0 ≤ gamma := le_trans hdiag_nonneg hgood.diagonalLineTest
  have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
    simpa [SymStrat.axisParallelFailureProbability] using
      bipartiteConsError_uniform_le_one
        strategy.state strategy.isNormalized
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
  have herror_le :
      strategy.axisParallelFailureProbability ≤ mainInductionError params k eps delta gamma := by
    exact le_trans
      (le_min hgood.axisParallelTest haxis_le_one)
      (min_eps_one_le_mainInductionError_of_m_eq_one
        params k eps delta gamma hm1 heps_nonneg hdelta_nonneg hgamma_nonneg)
  exact
    mainInductionOfWitness params strategy eps delta gamma k
      ⟨strategy.axisParallelFailureProbability, G, hconsG, herror_le⟩

/-- `thm:main-induction`.

This is the source-facing statement from
`references/ldt-paper/inductive_step.tex`: a good symmetric strategy and an
integer `k ≥ m d` produce a polynomial measurement consistent with the point
measurement at error `mainInductionError`.

The checked successor-step assembly below currently uses the stronger auxiliary
side condition `400 * m * d ≤ k` and explicit proof-stage packages. Those are
internal proof obligations, not hypotheses of this theorem. -/
theorem mainInduction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  -- TODO(#1507): prove the paper theorem from `hgood` and `hk` by deriving
  -- the wrapper inputs internally, rather than assuming the successor-stage
  -- packages exposed by `mainInductionPublicWrapper`.
  sorry

/-- Successor-step recursion entry point for the main-induction conclusion.

Given the slice restriction package, a recursive producer for the slice-level
main-induction conclusions, and a producer for the corresponding slice-wise
self-improvement package, this theorem executes the remaining
`restrict → induct → self-improve → paste` assembly and returns the
higher-dimensional point-consistency conclusion.

Note: this is the internal assembly theorem. The public boundary wrapper is
`mainInductionPublicWrapper`. The restricted-probabilities boundary is already
exposed separately via `restrictedProbabilities`, and
`SelfImprovementPackage.ofSelfImprovementInInductionSection` packages the
slice-wise restricted-strategy self-improvement output once it is supplied. This
theorem therefore keeps `hselfProducer` as an explicit input; the remaining
producer/wiring work belongs to the final `mainFormal` integration tracked by
#931, #834, and #422. -/
theorem mainInductionByRecursionOnM
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (hrestrict : SliceRestrictionPackage params strategy eps delta gamma)
    (hrec :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x))
    (hselfProducer :
      ∀ hinduction :
        PerSliceInductionPackage params strategy eps delta gamma hrestrict k,
      SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  -- Split into the informative small-error regime and the trivial
  -- `mainInductionError ≥ 1` regime.
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · let hinduction :=
      PerSliceInductionPackage.ofRecursion params strategy eps delta gamma k
        hrestrict hrec
    let hself := hselfProducer hinduction
    have heps_le_one : eps ≤ 1 := by
      exact eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
    have hdelta_le_one : delta ≤ 1 := by
      exact delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
    have hgamma_le : gamma ≤ 1 := by
      exact gamma_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
    have hdq_le_q : params.d ≤ params.q := by
      exact dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall
    have hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1 := by
      have hnu_lt :=
        mainInductionNu_lt_one_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
      have hzeta_le_nu :=
        selfImprovementInInductionError_le_mainInductionNu params strategy eps delta gamma k
          hgood hsmall heps_le_one hdelta_le_one hdq_le_q
      linarith
    let hpaste :=
      assembleAveragedPastingInput params strategy eps delta gamma k
        hgood hsmall hgamma_le hzeta_le hdq_le_q hrestrict hinduction hself hk
    exact
      mainInductionFromPackages params strategy eps delta gamma k
        hgood hd hrestrict hinduction hself hpaste hk_pos hk
  · let G : Measurement (Polynomial params.next) ι :=
      trivialPolynomialMeasurement (ι := ι) params.next
    have hcons :
        ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
          1 := by
      exact ⟨bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)⟩
    exact
      mainInductionOfWitness params.next strategy eps delta gamma k
        ⟨1, G, hcons, le_of_not_gt hsmall⟩

/-- Restricted-probabilities package built from the explicit weighted bounds fed
into `mainInductionPublicWrapper`. -/
noncomputable def mainInductionPublicRestrictionPackage
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma) :
    SliceRestrictionPackage params strategy eps delta gamma :=
  SliceRestrictionPackage.ofRestrictedProbabilities params strategy eps delta gamma
    (RestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound)

/-- `rem:main-induction-successor-assembly`.

This conditional successor-step assembly combines the five explicit Section 6 inputs:
1. the weighted restricted-axis and restricted-diagonal bounds,
2. the resulting `mainInductionPublicRestrictionPackage`,
3. the slice-wise recursion witnesses used by `PerSliceInductionPackage.ofRecursion`,
4. the explicit `hselfProducer` boundary hypothesis supplying the outputs of
   `selfImprovementInInductionSection`, and
5. `mainInductionByRecursionOnM`.

The theorem deliberately keeps `hselfProducer` as an explicit conditional input:
the self-improvement outputs are assembled by
`SelfImprovementPackage.ofSelfImprovementInInductionSection` once they are
supplied, while producing those slice-wise outputs belongs to downstream
`mainFormal` integration. The conclusion exposes only the global measurement
witness needed downstream by `MIPStarRE.LDT.Test.MainTheorem`. -/
theorem mainInductionPublicWrapper
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma)
    (hrec :
      let hrestrict : SliceRestrictionPackage params strategy eps delta gamma :=
        mainInductionPublicRestrictionPackage params strategy eps delta gamma
          hgood haxisWeightedBound hdiagonalWeightedBound
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x))
    (hselfProducer :
      let hrestrict : SliceRestrictionPackage params strategy eps delta gamma :=
        mainInductionPublicRestrictionPackage params strategy eps delta gamma
          hgood haxisWeightedBound hdiagonalWeightedBound
      ∀ hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k,
        SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let hrestrict : SliceRestrictionPackage params strategy eps delta gamma :=
    mainInductionPublicRestrictionPackage params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound
  have hrec' :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x) := by
    intro x
    exact hrec x
  have hselfProducer' :
      ∀ hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k,
        SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction := by
    intro hinduction
    exact hselfProducer hinduction
  exact
    mainInductionByRecursionOnM params strategy eps delta gamma k hgood hd hrestrict hrec'
      hselfProducer' hk_pos hk

/-- Answer-valued successor-step recursion entry point.

This wrapper keeps the paper-facing restricted strategy interface
`xRestrictedAnswerSymStrat`, then explicitly forgets that extra diagonal answer
structure to reuse the checked legacy assembly. -/
theorem answerMainInductionByRecursionOnM
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (hrestrict : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (hrec :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x))
    (hselfProducer :
      ∀ hinduction :
        AnswerPerSliceInductionPackage params strategy eps delta gamma hrestrict k,
        AnswerSelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let legacyRestrict : SliceRestrictionPackage params strategy eps delta gamma :=
    SliceRestrictionPackage.ofAnswer params strategy eps delta gamma hrestrict
  have hrec' :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (legacyRestrict.profile.axisParallel x)
              (legacyRestrict.profile.selfConsistency x)
              (legacyRestrict.profile.diagonal x) := by
    intro x
    rcases hrec x with ⟨error, G, hcons, herror⟩
    refine ⟨error, G, ?_, ?_⟩
    · simpa using hcons
    · simpa [legacyRestrict, SliceRestrictionPackage.ofAnswer] using herror
  have hselfProducer' :
      ∀ hinduction : PerSliceInductionPackage params strategy eps delta gamma legacyRestrict k,
        SelfImprovementPackage params strategy eps delta gamma k legacyRestrict hinduction := by
    intro hinduction
    let answerInduction :
        AnswerPerSliceInductionPackage params strategy eps delta gamma hrestrict k :=
      AnswerPerSliceInductionPackage.ofLegacy params strategy eps delta gamma k hrestrict hinduction
    let answerSelf :
        AnswerSelfImprovementPackage params strategy eps delta gamma k hrestrict answerInduction :=
      hselfProducer answerInduction
    exact
      SelfImprovementPackage.ofAnswerForLegacy params strategy eps delta gamma k hrestrict
        hinduction answerSelf
  exact
    mainInductionByRecursionOnM params strategy eps delta gamma k hgood hd legacyRestrict hrec'
      hselfProducer' hk_pos hk

/-- Answer-valued restricted-probabilities package built from explicit weighted
answer-valued slice bounds. -/
noncomputable def answerMainInductionPublicRestrictionPackage
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma) :
    AnswerSliceRestrictionPackage params strategy eps delta gamma :=
  AnswerSliceRestrictionPackage.ofRestrictedProbabilities params strategy eps delta gamma
    (AnswerRestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound)

/-- Answer-valued public successor-step wrapper for `thm:main-induction`.

The external recursive and self-improvement inputs are stated against
`xRestrictedAnswerSymStrat`; internally, the verified legacy pasting assembly is
reused via explicit answer-to-legacy package bridges. -/
theorem answerMainInductionPublicWrapper
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma)
    (hrec :
      let hrestrict : AnswerSliceRestrictionPackage params strategy eps delta gamma :=
        answerMainInductionPublicRestrictionPackage params strategy eps delta gamma
          hgood haxisWeightedBound hdiagonalWeightedBound
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x))
    (hselfProducer :
      let hrestrict : AnswerSliceRestrictionPackage params strategy eps delta gamma :=
        answerMainInductionPublicRestrictionPackage params strategy eps delta gamma
          hgood haxisWeightedBound hdiagonalWeightedBound
      ∀ hinduction : AnswerPerSliceInductionPackage params strategy eps delta gamma hrestrict k,
        AnswerSelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let hrestrict : AnswerSliceRestrictionPackage params strategy eps delta gamma :=
    answerMainInductionPublicRestrictionPackage params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound
  have hrec' :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x) := by
    intro x
    exact hrec x
  have hselfProducer' :
      ∀ hinduction : AnswerPerSliceInductionPackage params strategy eps delta gamma hrestrict k,
        AnswerSelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction := by
    intro hinduction
    exact hselfProducer hinduction
  exact
    answerMainInductionByRecursionOnM params strategy eps delta gamma k hgood hd hrestrict hrec'
      hselfProducer' hk_pos hk

end MIPStarRE.LDT.MainInductionStep
