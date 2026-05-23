import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Preliminaries.Defs
import MIPStarRE.LDT.Test.StrategyFailures
import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Pasting.Bernoulli.Final
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Core

/-!
# Section 6 — Ordinary Self-Improvement Data

Core public API for the ordinary self-improvement data: constructors for
`SelfImprovementData`, the induction-section theorem
`selfImprovementInInductionSection`, the monotone-witness cleanup
`mainInductionOfWitness`, and the source-facing pasting theorem
`ldPastingInInductionSection`.  The theorem
`ldPastingInInductionSectionNontrivial` is the restricted nontrivial-regime
form used as an auxiliary statement.

The answer-valued slice-transport constructors are separated into
`SelfImprovementAssembly.AnswerSlice`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Monotone postprocessing of an explicit witness for the main-induction conclusion.

This helper is the final `error ≤ mainInductionError` cleanup step only; the
actual Section 6 construction is carried by `mainInductionBaseCase`,
`mainInduction`, and the corrected source-facing theorem in
`SourceTheorems.lean`. -/
theorem mainInductionOfWitness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hwitness :
      ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas)
          error ∧
        error ≤ mainInductionError params k eps delta gamma) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  rcases hwitness with ⟨error, G, hG, herror⟩
  refine ⟨G, ?_⟩
  exact ⟨le_trans hG.offDiagonalBound herror⟩

/-- Convert the Section 9 self-improvement conclusion into the Section 6
induction-level self-improvement conclusion.

The Section 6 conclusion records the original input submeasurement only as a
parameter; its six mathematical fields concern the output projective
submeasurement and the dual witness.  This lemma isolates that transport, so
the induction-section self-improvement target is not confused with measurement-completion
bookkeeping. -/
theorem selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hfinal :
      SelfImprovement.SelfImprovementConclusion params strategy Gmeas H Z
        eps delta gamma nu) :
    SelfImprovementInInductionSectionConclusion params strategy G H Z
      eps delta gamma nu := by
  refine
    { completeness := by
        simpa [SelfImprovement.selfImprovementError, selfImprovementInInductionError] using
          hfinal.completeness
      pointConsistency := by
        simpa [SelfImprovement.selfImprovementError, selfImprovementInInductionError] using
          hfinal.pointConsistency
      strongSelfConsistency := by
        have hssc_eq :
            bipartiteSSCError strategy.state (uniformDistribution Unit)
                (constSubMeasFamily H.toSubMeas) =
              (1 / 2 : Error) *
                sddError strategy.state (uniformDistribution Unit)
                  (constSubMeasFamily H.toSubMeas.liftLeft)
                  (constSubMeasFamily H.toSubMeas.liftRight) := by
          simpa [bipartiteSSCError, sddError, avgOver, uniformDistribution, constSubMeasFamily]
            using
              Commutativity.qBipartiteSSCDefect_eq_half_qSDD_of_proj
                strategy.state strategy.permInvState H
        refine ⟨?_⟩
        rw [hssc_eq]
        have herr_nonneg : 0 ≤ SelfImprovement.selfImprovementError params eps delta := by
          exact le_trans
            (sddError_nonneg strategy.state (uniformDistribution Unit)
              (constSubMeasFamily H.toSubMeas.liftLeft)
              (constSubMeasFamily H.toSubMeas.liftRight))
            hfinal.selfCloseness.squaredDistanceBound
        calc
          (1 / 2 : Error) *
              sddError strategy.state (uniformDistribution Unit)
                (constSubMeasFamily H.toSubMeas.liftLeft)
                (constSubMeasFamily H.toSubMeas.liftRight)
            ≤ (1 / 2 : Error) * SelfImprovement.selfImprovementError params eps delta := by
                exact
                  mul_le_mul_of_nonneg_left
                    hfinal.selfCloseness.squaredDistanceBound (by norm_num)
          _ ≤ 1 * SelfImprovement.selfImprovementError params eps delta := by
                exact mul_le_mul_of_nonneg_right (by norm_num) herr_nonneg
          _ = selfImprovementInInductionError params eps delta gamma := by
                simp [SelfImprovement.selfImprovementError, selfImprovementInInductionError]
      selfCloseness := by
        simpa [SelfImprovement.selfImprovementError, selfImprovementInInductionError] using
          hfinal.selfCloseness
      bounded := by
        simpa [tensorFailureExpectation, SelfImprovement.projectiveBoundednessGap,
          SelfImprovement.projectiveResidualOperator, SelfImprovement.selfImprovementError,
          selfImprovementInInductionError] using hfinal.projectiveResidualBound
      dominatesAveragePointOperator := by
        intro h
        have hdom :=
          hfinal.dualDominatesAveragedPoint h
        have havg :
            IdxPolyFamily.averagedPointEvaluationOperator strategy h =
              ∑ x ∈ (uniformDistribution (Point params)).support,
                (uniformDistribution (Point params)).weight x •
                  (strategy.pointMeasurement x).outcome (h x) := by
          rfl
        rw [havg]
        have hdom' := hdom
        simp [SelfImprovement.sdpDualSlackOperator, SelfImprovement.averagedPointOperator,
          averageOperatorOverDistribution,
          GlobalVariance.pointConditionedOutcomeOperatorAtPolynomial] at hdom'
        simpa using hdom' }

/-- `thm:self-improvement-in-induction-section`.

Paper origin: `references/ldt-paper/self_improvement.tex:631-811`
(`\label{thm:self-improvement}`), used in the induction section at
`references/ldt-paper/inductive_step.tex:461-485`.  The labelled induction
statement at `references/ldt-paper/inductive_step.tex:249-286` states the input
as a submeasurement, while the proved form at
`references/ldt-paper/self_improvement.tex:635-671` uses a measurement.  This
Lean statement follows the proved measurement-valued form needed in the
induction proof.

The input \(G\) is a complete polynomial measurement, as in the paper's
restated self-improvement theorem.  The conclusion is phrased in the Section 6
record `SelfImprovementInInductionSectionConclusion`, whose fields are exactly
the projective output estimates used in the inductive step.  The proof applies
`SelfImprovement.selfImprovement` and transports the resulting fields into the
Section 6 record. -/
theorem selfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementInInductionSectionConclusion params strategy G.toSubMeas H Z
        eps delta gamma nu := by
  rcases SelfImprovement.selfImprovement params strategy eps delta gamma nu hgood G hcons with
    ⟨H, Z, hfinal⟩
  exact ⟨H, Z,
    selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion
      params strategy eps delta gamma nu G.toSubMeas G H Z hfinal⟩

/-- Induction-section self-improvement using only the two strategy bounds
consumed by Section 9.

Paper origin: `references/ldt-paper/self_improvement.tex:631-811`.

This is a formalization-only strengthening of
`selfImprovementInInductionSection`.  The paper states the theorem in the
standing context of an `(eps, delta, gamma)`-good strategy, but the displayed
self-improvement construction uses the axis-parallel and point
self-consistency bounds and its conclusion is independent of the diagonal-line
error parameter. -/
theorem selfImprovementInInductionSection_of_axisParallel_selfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (G : Measurement (Polynomial params) ι)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementInInductionSectionConclusion params strategy G.toSubMeas H Z
        eps delta gamma nu := by
  rcases SelfImprovement.selfImprovement_of_axisParallel_selfConsistency
      params strategy eps delta gamma nu haxis hself G hcons with
    ⟨H, Z, hfinal⟩
  exact ⟨H, Z,
    selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion
      params strategy eps delta gamma nu G.toSubMeas G H Z hfinal⟩

/-- Restricted nontrivial-regime Lean restatement of
`thm:ld-pasting-in-induction-section`.

This theorem calls `Pasting.ldPastingNontrivial`.  Its public assumptions therefore
include `gamma ≤ 1`, `zeta ≤ 1`, `params.d ≤ params.q`, `0 < params.d`, and
`1 ≤ k`, in addition to the hypotheses of the source theorem.  The paper
statement is `references/ldt-paper/ld-pasting.tex`, lines 12--50; lines 52--55
record these inequalities only as a proof reduction to the nontrivial regime.
The trivial complementary cases remain to be formalized before this declaration
can serve as the unrestricted induction-section pasting theorem. -/
-- NOTE: `FieldModel.{0}` is needed to match the universe at which
-- `Pasting.ldPastingNontrivial` was elaborated. See PR #288 discussion.
theorem ldPastingInInductionSectionNontrivial
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (_hgamma_le : gamma ≤ 1)
    (_hzeta_le : zeta ≤ 1)
    (_hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingInInductionSectionConclusion params strategy family H
        eps delta gamma kappa zeta k := by
  have hldPastingNontrivial :=
    Pasting.ldPastingNontrivial params strategy eps delta gamma kappa zeta
      hgood _hgamma_le _hzeta_le _hdq_le hd
      family hcomplete hcons hself hbound k hk_pos hk
  obtain ⟨H, _hHdef, hH⟩ := hldPastingNontrivial
  refine ⟨H, ?_⟩
  exact ⟨hH.pointConsistency⟩

/-- Source-facing Lean statement for `thm:ld-pasting-in-induction-section`.

Paper origin: `references/ldt-paper/inductive_step.tex:299-338`
(`\label{thm:ld-pasting-in-induction-section}`).  The statement is the
Chapter 6 restatement of `thm:ld-pasting`, with the error parameters named as
they are used in the main-induction proof.

**Source-faithful transport:** This theorem invokes the unrestricted formal
theorem `Pasting.ldPasting` and projects its point-consistency field into the
induction-section conclusion record.  It carries no additional assumption beyond
the already formalized pasting theorem. -/
theorem ldPastingInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingInInductionSectionConclusion params strategy family H
        eps delta gamma kappa zeta k := by
  obtain ⟨H, hH⟩ :=
    Pasting.ldPasting params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hself hbound k hk
  refine ⟨H, ?_⟩
  exact ⟨hH.pointConsistency⟩


end MIPStarRE.LDT.MainInductionStep
