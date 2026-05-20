import MIPStarRE.LDT.Basic.LinePolynomialEmbedding
import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementAssembly.Core
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds
import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly
import MIPStarRE.LDT.Pasting.Bernoulli.DegreeZero

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

/-- The successor large-`k` hypothesis implies the predecessor large-`k`
hypothesis used by the recursive slice calls.

This is a boundary arithmetic fact: the successor ambient dimension is
`params.m + 1`, while the recursive calls are made in dimension `params.m`. -/
theorem mainInductionSuccessorBound_pred
    (params : Parameters) {k : ℕ}
    (hk : 400 * params.next.m * params.next.d ≤ k) :
    400 * params.m * params.d ≤ k := by
  have hm_le : params.m ≤ params.next.m := by
    simp [Parameters.next]
  have hcoef : 400 * params.m ≤ 400 * params.next.m :=
    Nat.mul_le_mul_left 400 hm_le
  have hmul :
      400 * params.m * params.d ≤ 400 * params.next.m * params.next.d := by
    simpa [Parameters.next, Nat.mul_assoc] using
      Nat.mul_le_mul_right params.d hcoef
  exact le_trans hmul hk

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
  have hk_pred : 400 * params.m * params.d ≤ k :=
    mainInductionSuccessorBound_pred params hk_next
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

/-- Small-error successor construction from answer-valued slice transport.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.  The paper
successor proof first invokes the induction hypothesis on each answer-valued
slice, then applies the induction-section self-improvement theorem to the slice
measurements, and finally pastes the averaged family.

This theorem is not a paper theorem and is not marked as
`\label{thm:main-induction}`.  It records the checked part of the small-error
successor branch: once the predecessor answer-valued induction hypothesis and
the concrete slice-strategy transport are constructed inside the proof, the
remaining pasting construction follows from the existing Section 6 theorems. -/
theorem mainInductionSuccessorNextOfSmallError_ofAnswerSliceTransport
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
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
  have hk_pred : 400 * params.m * params.d ≤ k :=
    mainInductionSuccessorBound_pred params hk_next
  let answerRestrict : AnswerSliceRestrictionData params strategy eps delta gamma :=
    AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
      (answerRestrictedProbabilities params strategy eps delta gamma hgood)
  let answerInduction :
      AnswerPerSliceInductionData params strategy eps delta gamma answerRestrict k :=
    AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
      answerRestrict hinduction hd hk_pred
  let answerSelf :
      AnswerSelfImprovementData params strategy eps delta gamma k answerRestrict
        answerInduction :=
    AnswerSelfImprovementData.ofSliceStrategyTransport
      params strategy eps delta gamma k answerRestrict answerInduction
      (hsliceTransport answerRestrict answerInduction)
  exact
    mainInductionFromAnswerStageDataOfSmallError params strategy eps delta gamma k
      hgood hsmall answerRestrict answerInduction answerSelf hk_pred

/-- Positive-degree successor construction from the two remaining internal
obligations.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.  This is the
successor proof after its two genuine internal obligations have been supplied:
the predecessor answer-valued induction hypothesis and the slice-strategy
transport needed to apply Section 9 to the answer-restricted slices.

This theorem proves the full positive-degree conditional successor theorem by
combining the checked small-error branch with the trivial-measurement large-error
case.  It is not a paper theorem and is not an extra hypothesis for
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
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · exact
      mainInductionSuccessorNextOfSmallError_ofAnswerSliceTransport
        params strategy eps delta gamma k hgood hk_next hsmall hd hinduction hsliceTransport
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Internal degree-zero successor reduction through the completed degree-zero
pasting construction.

This theorem is not the degree-zero branch itself.  It records that, when
`params.d = 0`, the existing degree-zero pasting theorem supplies the desired
successor measurement once the successor proof has constructed a slice family
which is complete and point-consistent with sufficiently small parameters
`kappa` and `zeta`.  The final hypothesis is the scalar absorption from the
degree-zero pasting error into the main-induction error.

Thus the remaining degree-zero work is the construction of such a family and
the displayed scalar inequality, not an additional hypothesis on
`thm:main-induction`. -/
theorem mainInductionSuccessorNext_degreeZero_ofPastingFamily
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (kappa zeta : Error)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0)
    (herror :
      ldPastingInInductionError params k eps delta gamma kappa zeta ≤
        mainInductionError params.next k eps delta gamma) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  rcases Pasting.degreeZeroPastedPointConsistency params strategy eps delta gamma
      kappa zeta hgood family hcomplete hcons hd_zero k with
    ⟨H, _hH_eq, hH⟩
  exact ⟨H, ConsRel.mono herror hH⟩

/-- Construction target for the degree-zero branch of the successor step.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, in the
successor step of `\label{thm:main-induction}`.

When Lean's successor proof is split by whether the predecessor degree is zero,
this is the remaining datum needed in the degree-zero branch: a complete and
point-consistent degree-zero slice family together with the scalar comparison
which absorbs the pasting error into the next main-induction error.  The
conditional assembly theorems below use only the fields of this datum; this
definition is the named construction target that must eventually be proved from
the source hypotheses.

**Proof obligation:** This declaration is intentionally a `sorry`-bodied
construction target, tracked by issue #1507.  Planned discharge: construct the
degree-zero slice family from the hypotheses of
`mainInductionSuccessorNextOfSmallError` under `params.d = 0`, then prove the
displayed scalar inequality for the produced losses. -/
noncomputable def DegreeZeroPastingFamilyObligation.ofSmallError
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (_hgood : strategy.IsGood eps delta gamma)
    (_hk_next : 400 * params.next.m * params.next.d ≤ k)
    (_hsmall : mainInductionError params.next k eps delta gamma < 1)
    (_hd_zero : params.d = 0) :
    DegreeZeroPastingFamilyObligation params strategy eps delta gamma k := by
  classical
  sorry

/-- Internal small-error successor assembly from the two degree branches.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, restricted to
the nontrivial branch in which
`mainInductionError params.next k eps delta gamma < 1`.

This theorem is not a paper theorem.  It records that the small-error successor
branch follows once the proof has supplied its two branch constructions: in
degree zero, a complete and point-consistent slice family with scalar error
absorbed into the next main-induction error; in positive degree, the
answer-valued predecessor induction hypothesis and the slice-strategy transport
needed to run the induction-section self-improvement theorem.  The equivalent
named degree-zero construction target is
`DegreeZeroPastingFamilyObligation`.

No one of these objects is added as a hypothesis to `thm:main-induction`.  The
source-facing theorem `mainInductionSuccessorNextOfSmallError` must still
construct them from the displayed successor hypotheses.

**Internal proof obligation:** This conditional assembly theorem is tracked by
issue #1507.  Planned discharge: prove the degree-zero family construction and
the positive-degree answer-slice transport from the hypotheses of
`mainInductionSuccessorNextOfSmallError`, and then call this theorem. -/
theorem mainInductionSuccessorNextOfSmallError_ofDegreeSplitPastingObligations
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (degreeZeroPasting :
      params.d = 0 →
        ∃ family : IdxPolyFamily params ι, ∃ kappa zeta : Error,
          family.Complete strategy.state kappa ∧
            family.ConsistentWithPoints strategy zeta ∧
              ldPastingInInductionError params k eps delta gamma kappa zeta ≤
                mainInductionError params.next k eps delta gamma)
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
  by_cases hd : 0 < params.d
  · exact
      mainInductionSuccessorNextOfSmallError_ofAnswerSliceTransport
        params strategy eps delta gamma k hgood hk_next hsmall hd hinduction hsliceTransport
  · rcases degreeZeroPasting (Nat.eq_zero_of_not_pos hd) with
      ⟨family, kappa, zeta, hcomplete, hcons, herror⟩
    exact
      mainInductionSuccessorNext_degreeZero_ofPastingFamily
        params strategy eps delta gamma k hgood family kappa zeta
        hcomplete hcons (Nat.eq_zero_of_not_pos hd) herror

/-- Internal successor assembly after the large-error and degree splits.

This theorem is not the paper theorem and should not be linked as
`\label{thm:main-induction}`.  It records the proof obligations that remain
after the already checked large-error branch has been removed.  In the
small-error branch, there are two cases:

* if `0 < params.d`, the proof calls the answer-valued successor assembly from
  the predecessor answer-valued induction hypothesis and the concrete
  answer-valued slice transport;
* if `params.d = 0`, the proof calls the degree-zero pasting reduction from a
  constructed complete and point-consistent family.  This branch is now also
  named as `DegreeZeroPastingFamilyObligation` in the statement file.

Thus degree positivity is not being added to the public successor statement; it
is only the branch condition for one internal construction route.

**Proof obligation:** This is an internal conditional reduction for the
successor proof of `thm:main-induction`, tracked by issue #1507 and the
source-statement boundary tracker #1458.  Elimination: prove the degree-zero
family construction and the positive-degree answer-valued slice realization
from the source successor hypotheses. -/
theorem mainInductionSuccessorNext_ofDegreeSplitPastingObligations
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (degreeZeroPasting :
      ∀ _hsmall : mainInductionError params.next k eps delta gamma < 1,
        params.d = 0 →
          ∃ family : IdxPolyFamily params ι, ∃ kappa zeta : Error,
            family.Complete strategy.state kappa ∧
              family.ConsistentWithPoints strategy zeta ∧
                ldPastingInInductionError params k eps delta gamma kappa zeta ≤
                  mainInductionError params.next k eps delta gamma)
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
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · exact
      mainInductionSuccessorNextOfSmallError_ofDegreeSplitPastingObligations
        params strategy eps delta gamma k hgood hk_next hsmall
        (degreeZeroPasting hsmall) hinduction hsliceTransport
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

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
