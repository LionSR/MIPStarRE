import MIPStarRE.LDT.Basic.LinePolynomialEmbedding
import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementAssembly.Core
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds
import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly

/-!
# Section 6 — Main Induction Theorems

The top-level induction theorem `mainInduction`, its proved base case
`mainInductionBaseCase`, and the public restricted-probability data record
constructors used by the Section 3 handoff.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

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

/-- Trivial branch of `thm:main-induction` when the target error is at least
`1`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the
successor proof reduces to the nontrivial small-error regime before invoking the
pasting argument.  In the complementary branch the normalized consistency defect
is bounded by `1`, so a distinguished trivial polynomial measurement suffices.
-/
theorem mainInductionOfOneLeError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (herror : 1 ≤ mainInductionError params k eps delta gamma) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  classical
  let G : Measurement (Polynomial params) ι :=
    Measurement.trivialDistinguishedOutcome
      (Classical.choice (inferInstance : Nonempty (Polynomial params)))
  refine ⟨G, ?_⟩
  exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas))
    herror⟩

/-- Positive-degree successor assembly from direct answer-valued slice
self-improvement outputs.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.  The paper
successor proof invokes the induction hypothesis on each answer-valued slice,
applies the induction-section self-improvement theorem to the resulting slice
measurements, and then pastes the averaged family.

This theorem is not a paper theorem.  It is the present formal proof frontier
for the answer-valued route: once the predecessor answer-valued induction
hypothesis and the slice-wise self-improvement conclusions have been obtained,
the remaining successor assembly is formal.  The slice-wise conclusions are
kept as direct outputs of the Section 9 theorem, rather than as an additional
source-level hypothesis on `thm:main-induction`. -/
theorem mainInductionSuccessorNext_ofAnswerSliceSelfImprovement
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hd : 0 < params.d)
    (hinduction : AnswerMainInductionHypothesis.{0, uι} params)
    (hsliceSelf :
      ∀ (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
        (inductionPkg :
          AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k),
        ∀ x,
          ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
            CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
              ((1 - inductionPkg.sliceError x) -
                answerSliceSelfImprovementError params restrictionPkg x) ∧
            ConsRel strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas
                (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
              (polynomialEvaluationFamily params H.toSubMeas)
              (answerSliceSelfImprovementError params restrictionPkg x) ∧
            BipartiteSSCRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily H.toSubMeas)
              (answerSliceSelfImprovementError params restrictionPkg x) ∧
            SDDRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
              (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
              (answerSliceSelfImprovementError params restrictionPkg x) ∧
            tensorFailureExpectation strategy.state Z H.toSubMeas ≤
              answerSliceSelfImprovementError params restrictionPkg x ∧
            (∀ h : Polynomial params,
              IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z)) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  have hk_pred : 400 * params.m * params.d ≤ k := by
    have hm_le_next : params.m ≤ params.next.m := by
      simp [Parameters.next]
    exact le_trans
      (Nat.mul_le_mul_right params.d (Nat.mul_le_mul_left 400 hm_le_next))
      (by simpa [Parameters.next, Nat.mul_assoc] using hk_next)
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · let answerRestrict : AnswerSliceRestrictionData params strategy eps delta gamma :=
      AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
        (answerRestrictedProbabilities params strategy eps delta gamma hgood)
    let answerInduction :
        AnswerPerSliceInductionData params strategy eps delta gamma answerRestrict k :=
      AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
        answerRestrict hinduction hd hk_pred
    let answerSelf :
        AnswerSelfImprovementData params strategy eps delta gamma k answerRestrict
          answerInduction :=
      AnswerSelfImprovementData.ofSelfImprovementInInductionSection
        params strategy eps delta gamma k answerRestrict answerInduction
        (hsliceSelf answerRestrict answerInduction)
    exact
      mainInductionFromAnswerStageDataOfSmallError params strategy eps delta gamma k
        hgood hsmall answerRestrict answerInduction answerSelf hk_pred
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Positive-degree successor assembly from the two remaining internal
obligations.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.  The paper
successor proof first invokes the induction hypothesis on each answer-valued
slice, then applies the induction-section self-improvement theorem to the slice
measurements, and finally pastes the averaged family.

This theorem proves the completed Lean assembly once those two genuine internal
obligations are supplied: the predecessor answer-valued induction hypothesis and
the slice-strategy transport needed to apply Section 9 to the answer-restricted
slices.  It is not a paper theorem and is not an extra hypothesis for
`thm:main-induction`; it records the precise remaining constructions needed to
discharge the source-facing successor branch. -/
theorem mainInductionSuccessorNext_ofAnswerSliceTransport
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hd : 0 < params.d)
    (hinduction : AnswerMainInductionHypothesis.{0, uι} params)
    (hsliceTransport :
      ∀ (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
        (inductionPkg :
          AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k),
        AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
          restrictionPkg inductionPkg) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionSuccessorNext_ofAnswerSliceSelfImprovement
      params strategy eps delta gamma k hgood hk_next hd hinduction
      (fun restrictionPkg inductionPkg =>
        AnswerSelfImprovementData.slice_outputs_ofSliceStrategyTransport
          params strategy eps delta gamma k restrictionPkg inductionPkg
          (hsliceTransport restrictionPkg inductionPkg))

/-- Small-error branch of the native successor step for `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the proof
passes from dimension `m` to dimension `m + 1` in the nontrivial regime where
the target error is below `1`.

This is an internal proof obligation, not a separate paper theorem.  The
additional hypothesis `hsmall` is the branch condition used by
`mainInductionSuccessorNext`; it is discharged there by a case distinction and
is not an additional assumption on the public induction theorem.  The statement
does not take any of the intermediate objects of the slice construction as
hypotheses; those objects must be obtained from the displayed hypotheses.

The declaration is temporary in the precise sense that, once the slice
restriction, recursive induction, self-improvement, and pasting constructions
are supplied, this branch should be proved from its displayed hypotheses and
remain only as the internal small-error case used by `mainInductionSuccessorNext`.

**Proof obligation:** Derive the restricted slice profiles, apply the recursive
main-induction hypothesis on each slice, run the induction-section
self-improvement theorem on the slice measurements, assemble the averaged
pasting input, and close the scalar side conditions, including the passage from
the `params.next` large-`k` hypothesis to the predecessor side conditions needed
inside the proof.  This is tracked by issue #1507 under the source-statement
boundary tracker #1458. -/
theorem mainInductionSuccessorNextOfSmallError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (_hgood : strategy.IsGood eps delta gamma)
    (_hk : 400 * params.next.m * params.next.d ≤ k)
    (_hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  sorry

/-- Native successor step for `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the proof
passes from dimension `m` to dimension `m + 1`.

This is the source-facing induction step in its native form: the ambient
strategy already lives in dimension `params.next`, so no predecessor
compatibility record is introduced.  In the large-error branch the normalized
consistency defect is bounded by `1`; in the small-error branch the remaining
source-faithful construction is isolated as
`mainInductionSuccessorNextOfSmallError`. -/
theorem mainInductionSuccessorNext
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.next.m * params.next.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · exact mainInductionSuccessorNextOfSmallError params strategy eps delta gamma k
      hgood hk hsmall
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Successor branch of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, the induction
step after the restricted-probability estimates and the slice-wise recursive
calls have been set up.

This theorem is the parameter-decomposition form used by `mainInduction`.
Its assumptions are the corrected large-`k` hypotheses for
`thm:main-induction`, together with the branch condition `params.m ≠ 1`; it
does not take the intermediate objects of the slice construction as hypotheses.
The proof decomposes the non-base parameter bundle as `pred.next` and then
invokes the native successor-step obligation `mainInductionSuccessorNext`. -/
theorem mainInductionSuccessor
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k)
    (hm1 : params.m ≠ 1) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  rcases Parameters.successorDecompositionOfNeOne params hm1 with ⟨pred, hnext⟩
  have hq : pred.q = params.q := by
    simpa [Parameters.next] using congrArg Parameters.q hnext
  letI : FieldModel pred.q := hq.symm ▸ (inferInstance : FieldModel params.q)
  cases hnext
  exact mainInductionSuccessorNext pred strategy eps delta gamma k hgood hk

/-- `thm:main-induction`.

This is the corrected large-`k` Lean statement corresponding to
`references/ldt-paper/inductive_step.tex`: a good symmetric strategy and an
integer `k ≥ 400 m d` produce a polynomial measurement consistent with the point
measurement at error `mainInductionError`.  The strengthening from the printed
`k ≥ m d` hypothesis is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.

**Proof gap:** the base case is proved by `mainInductionBaseCase`. The
successor case is isolated as the source-shaped theorem
`mainInductionSuccessor`, corresponding to
`references/ldt-paper/inductive_step.tex:441-551`.  This gap is tracked by
#1507 and #1458.  The proof should derive the restricted probability estimates,
recursive slice measurements, slice-wise self-improvement outputs, and pasting
side condition internally, rather than adding any of them to the theorem
statement. -/
theorem mainInduction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  by_cases hm1 : params.m = 1
  · exact mainInductionBaseCase params strategy eps delta gamma k hm1 hgood
  · exact mainInductionSuccessor params strategy eps delta gamma k hgood hk hm1

/-- Restricted-probabilities data built from the explicit weighted bounds in the
successor proof of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`), used in the proof of
`\label{thm:main-induction}` at
`references/ldt-paper/inductive_step.tex:441-454`. -/
noncomputable def mainInductionPublicRestrictionData
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
    SliceRestrictionData params strategy eps delta gamma :=
  SliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
    (RestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound)

/-- Answer-valued restricted-probabilities data record built from explicit weighted
answer-valued slice bounds.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`), used in the proof of
`\label{thm:main-induction}` at
`references/ldt-paper/inductive_step.tex:441-454`. -/
noncomputable def answerMainInductionPublicRestrictionData
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
    AnswerSliceRestrictionData params strategy eps delta gamma :=
  AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
    (AnswerRestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound)

end MIPStarRE.LDT.MainInductionStep
