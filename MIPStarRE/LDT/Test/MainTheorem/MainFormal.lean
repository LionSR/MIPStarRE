import MIPStarRE.LDT.Test.MainTheorem.NativeTargets
import MIPStarRE.LDT.Test.MainTheorem.SourceRoleRegister
import MIPStarRE.LDT.Test.StrategyBiProj

/-!
# Main-formal soundness theorem

Base handoff, final projective-completion transport, and the current same-space
formal interface toward `thm:main-formal` (`\Cref{thm:main-formal}`).  This
module contains:

* `mainFormalBaseRoleInductionWitness` — names the Section 6 role-register witness
  used by the base case `m = 1`.

* `mainFormal_ofProjectiveCompletionTransportWitness` — derives the three consistency
  conclusions of `thm:main-formal` from a constructed Section 6
  projective-completion witness.

* `mainFormal_sourceObligation` and `mainFormal_sourceStatement` — record the
  printed two-space source theorem, prove its saturated-error branch, and name
  the remaining small-error source-boundary obligation.

* `mainFormal_sourceConclusion_ofSameSpaceLargeK` — proves the source-shaped
  conclusion in the same-space corrected-range subcase by calling the current
  `mainFormal` interface.

* `mainFormal` — the current same-space formal interface toward the final
  theorem, taking a same-space projective strategy that passes the LID test with
  probability `≥ 1 − ε`, together with the explicit boundary conditions `0 < k`
  and `400md ≤ k`, and producing the three pointwise consistency targets at
  error bound `mainFormalError`.  The remaining same-space interface restriction
  is documented in
  `docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`; the
  large-`k` and `k > 0` scalar-cascade boundary is documented in
  `docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  Its proof follows the
  checked branch structure: the vacuous branch is closed by
  `mainFormal_trivial_witness`, the non-vacuous branch invokes the Section 6
  role-register witness, the post-role projective-completion construction
  target, and the final transport.  No bridge, residual, repair, or proof
  obligation package is assumed by `mainFormal`.

## References

* Paper: `references/ldt-paper/test_definition.tex`,
  `\Cref{thm:main-formal}` at line 180; its proof is in
  `references/ldt-paper/inductive_step.tex` (lines 26–236).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `\label{thm:main-formal-current-interface}`; and
  `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-step6-constructions}`,
  `\label{lem:main-formal-successor-handoff}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-! ### Base handoff and final projective-completion transport

The base branch of `mainFormal` needs a concrete Section 6 role witness and one
post-role projective-completion witness.  Earlier scaffolding expressed this
through separate bridge and obligation packages.  The current interface below
does not keep such packages as hypotheses: the source theorem remains separate in
the blueprint, and the missing source-boundary work is represented by named
obligations. -/

/--
Trivial saturated-error branch for the printed two-space theorem
`thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`; this is the
large-error branch separated by the source-boundary repair documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`.

**Source:** This is a source-faithful saturated-error branch: when the printed
target error is at least `1`, the consistency conclusion follows from the
normalization bound for bipartite consistency defects, without adding any
construction hypothesis to the source theorem.

Whenever `mainFormalError params k eps ≥ 1`, the three consistency conclusions
hold for arbitrary projective polynomial measurements, since each underlying
consistency defect is bounded by `1` for a normalized bipartite state and a
uniform question distribution.  This is the two-space analogue of
`mainFormal_trivial_witness`; it does not use the low individual degree test
hypothesis. -/
theorem mainFormal_source_trivial_witness
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (k : ℕ)
    (herr : 1 ≤ mainFormalError params k eps) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  classical
  haveI : Inhabited (Polynomial params) :=
    ⟨⟨0, by intro i; simp [MvPolynomial.degreeOf_zero]⟩⟩
  let trivialA : ProjMeas (Polynomial params) ιA := default
  let trivialB : ProjMeas (Polynomial params) ιB := default
  refine ⟨trivialA, trivialB, ?_, ?_, ?_⟩
  all_goals exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized _ _) herr⟩

private theorem projStrat_eps_nonneg_of_passes
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    {strategy : ProjStrat params ιA ιB}
    {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    0 ≤ eps := by
  have haxis : 0 ≤ strategy.axisParallelRoleAverage :=
    ProjStrat.axisParallelRoleAverage_nonneg strategy
  have hpoint : 0 ≤ strategy.pointAgreementFailureProbability :=
    ProjStrat.pointAgreementFailureProbability_nonneg strategy
  have hdiag : 0 ≤ strategy.diagonalRoleAverage :=
    ProjStrat.diagonalRoleAverage_nonneg strategy
  have hfail : 0 ≤ strategy.lowIndividualDegreeFailureProbability := by
    unfold ProjStrat.lowIndividualDegreeFailureProbability
    nlinarith
  exact hfail.trans hpass.soundnessHypothesis

/-- Source role-register conclusion after the scalar branch has supplied
`0 < k`.

This theorem is not an additional hypothesis of `thm:main-formal`; it isolates
the already checked two-space role-register construction from the remaining
source-range boundary.  The proof uses
`ProjStrat.sourceRoleRegisterFinalPointConsistency` and then weakens the three
explicit pre-absorption errors to `mainFormalError` by the existing Step 8
scalar cascade. -/
theorem mainFormal_sourceConclusion_ofRoleRegisterScalarBoundary
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k)
    (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  classical
  have hepsNN : 0 ≤ eps := projStrat_eps_nonneg_of_passes params hpass
  let scalars : MainFormalCascadeScalars params eps k :=
    MainFormalCascadeScalars.ofNontrivialMainFormal hepsNN hk0 hsmall
  let σsrc : Error :=
    2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
  let ζ₁src : Error :=
    σsrc + 2 * Real.sqrt (3 * eps + σsrc) + (params.m * params.d : Error) / params.q
  let ζ₂src : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁src
  let ηsrc : Error :=
    ζ₁src + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ₁src)
  let ζ₃src : Error := 6 * ζ₁src + 6 * ζ₂src
  have hσsrc : σsrc = 2 * scalars.sigma := by
    simp [σsrc, MainFormalCascadeScalars.sigma, mainFormalCascadeSigma_eq_mainInductionError]
  have hζ₁src : ζ₁src = scalars.zeta1 := by
    simp [ζ₁src, σsrc, MainFormalCascadeScalars.zeta1, cascadeZeta1,
      MainFormalCascadeScalars.sigma, mainFormalCascadeSigma_eq_mainInductionError]
  have hζ₂src : ζ₂src ≤ scalars.zeta2 := by
    change MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁src ≤ scalars.zeta2
    rw [hζ₁src]
    exact MainFormalCascadeScalars.orthonormalizeAndCompleteError_zeta1_le_zeta2
      scalars hsmall
  have hηsrc : ηsrc = scalars.line169Error := by
    have hζ0 : 0 ≤ scalars.zeta1 := MainFormalCascadeScalars.zeta1_nonneg scalars
    have hsqrt :
        Real.sqrt (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1) =
          10 * Real.rpow scalars.zeta1 (1 / (8 : Error)) :=
      MakingMeasurementsProjective.sqrt_orthonormalizationError_eq hζ0
    simp [ηsrc, hζ₁src, MainFormalCascadeScalars.line169Error,
      cascadeLine169RepairError, hsqrt]
  have hζ₃src : ζ₃src ≤ scalars.zeta3 := by
    have hζ₁le : ζ₁src ≤ scalars.zeta1 := le_of_eq hζ₁src
    have hcore : 6 * ζ₁src + 6 * ζ₂src ≤ 6 * scalars.zeta1 + 6 * scalars.zeta2 := by
      nlinarith
    simpa [ζ₃src, MainFormalCascadeScalars.zeta3, cascadeZeta3] using hcore
  have hsourcePoint :
      σsrc + 2 * Real.sqrt (ηsrc + ζ₃src / 2) ≤ mainFormalError params k eps := by
    have hrad :
        ηsrc + ζ₃src / 2 ≤ scalars.line169Error + scalars.zeta3 / 2 := by
      have hηle : ηsrc ≤ scalars.line169Error := le_of_eq hηsrc
      nlinarith
    have hsqrt :
        Real.sqrt (ηsrc + ζ₃src / 2) ≤
          Real.sqrt (scalars.line169Error + scalars.zeta3 / 2) :=
      Real.sqrt_le_sqrt hrad
    have hrepaired :
        σsrc + 2 * Real.sqrt (ηsrc + ζ₃src / 2) ≤ scalars.zeta4Repaired := by
      calc
        σsrc + 2 * Real.sqrt (ηsrc + ζ₃src / 2)
            = 2 * scalars.sigma + 2 * Real.sqrt (ηsrc + ζ₃src / 2) := by
              rw [hσsrc]
        _ ≤ 2 * scalars.sigma + 2 *
              Real.sqrt (scalars.line169Error + scalars.zeta3 / 2) := by
            nlinarith
        _ = scalars.zeta4Repaired := by
            rfl
    exact hrepaired.trans (MainFormalCascadeScalars.zeta4Repaired_le_mainFormalError scalars)
  have hsourceSelf :
      ζ₃src / 2 ≤ mainFormalError params k eps := by
    have htoCascade : ζ₃src / 2 ≤ scalars.zeta3 / 2 := by
      nlinarith
    exact htoCascade.trans (MainFormalCascadeScalars.zeta3_div_two_le_mainFormalError scalars)
  rcases ProjStrat.sourceRoleRegisterFinalPointConsistency
      params strategy eps hpass k hk with ⟨Q_A, Q_B, hA, hrest⟩
  rcases hrest with ⟨hB, hrest⟩
  rcases hrest with ⟨_hQQEval, hQQ⟩
  refine ⟨Q_A, Q_B, ?_, ?_, ?_⟩
  · exact ConsRel.mono (by
      simpa [σsrc, ζ₁src, ζ₂src, ηsrc, ζ₃src] using hsourcePoint) hA
  · exact ConsRel.mono (by
      simpa [σsrc, ζ₁src, ζ₂src, ηsrc, ζ₃src] using hsourcePoint) hB
  · exact ConsRel.mono (by
      simpa [σsrc, ζ₁src, ζ₂src, ηsrc, ζ₃src] using hsourceSelf) hQQ

/--
Degenerate zero-\(k\) source-boundary obligation for the printed two-space
theorem `thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This is not an additional hypothesis of the paper theorem.  It isolates the
only part of the final small-error branch not reached by the present nonzero
scalar-cascade route.  Since the parameter bundle allows `params.d = 0`, the
printed hypothesis `params.m * params.d ≤ k` does not imply `0 < k`; the corner
`k = 0` remains possible exactly when the degree bound is zero.  In this corner
`mainFormalError params k eps` is definitionally zero, so the saturated-error
branch and the Step 8 cascade do not apply automatically.

**Unfaithful:** This proof currently contains the tracked `sorry` for the
zero-sampling boundary of `references/ldt-paper/test_definition.tex:180-202`,
which is not derived from the printed hypotheses of `thm:main-formal`.
Documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue
#1458.  Elimination: prove the \(d=0,k=0\) source theorem directly, or record
a corrected source statement whose sampling parameter is required to be
nonzero. -/
theorem mainFormal_sourceZeroKBoundaryObligation
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (_hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (_hk : params.m * params.d ≤ k)
    (_hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (_hk_zero : k = 0) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  sorry

/--
Small-error internal proof obligation for the printed two-space theorem
`thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This theorem records the remaining non-vacuous source-boundary work needed to
derive the paper theorem from the present formal infrastructure.  It is not an
additional hypothesis of `thm:main-formal`; the source-boundary wrapper below
calls this obligation only after the saturated-error branch has been discharged
by `mainFormal_source_trivial_witness`.

**Proof gap:** The current checked route proves the separate same-space,
corrected large-`k` interface `mainFormal`.  To close this small-error
obligation one must derive the final conclusions for a general two-space
projective strategy with only the printed hypothesis `k ≥ m d` and
`mainFormalError params k eps < 1`.  The heterogeneous role-register
symmetrization, factor-two unsymmetrization, point-agreement branch,
heterogeneous triangle step, and Schwartz--Zippel Step 5 calculation are now
formalized through complete-measurement full-polynomial consistency in
`ProjStrat.sourceRoleRegisterCompletePolynomialSelfConsistency`, and the
two-sided projective-submeasurement construction is formalized in
`ProjStrat.sourceRoleRegisterTwoSidedProjectiveSubmeasurements`.  Completion to
projective measurements, line-169 transport, the final point-evaluation
triangle, and scalar absorption into `mainFormalError` are now checked in the
two-space route once the nonzero scalar-cascade boundary `0 < k` is supplied.
This wrapper now uses that theorem on the nonzero-\(k\) branch.  The remaining
direct proof hole in this file is the zero-sampling boundary
`mainFormal_sourceZeroKBoundaryObligation`; the nonzero branch still inherits
the source-range status of `MainInductionStep.mainInduction_sourceStatement`.
Both boundaries are recorded in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.

**Unfaithful:** This proof currently calls source-boundary declarations whose
proofs are not fully derived from the printed hypotheses: on the nonzero branch
it inherits `MainInductionStep.mainInduction_sourceStatement`, and on the
zero-sampling branch it calls `mainFormal_sourceZeroKBoundaryObligation`.
It therefore uses `sorryAx` transitively rather than deriving
`references/ldt-paper/test_definition.tex:180-202` from the paper hypotheses.
Documented in `docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`,
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`, and issue #1458.
Elimination: discharge the source `k ≥ m d` range boundary and the
zero-sampling final-theorem boundary. -/
theorem mainFormal_sourceSmallErrorObligation
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (_hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (_hk : params.m * params.d ≤ k)
    (_hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  by_cases hk0 : 0 < k
  · exact
      mainFormal_sourceConclusion_ofRoleRegisterScalarBoundary
        params strategy eps _hpass k _hk hk0 _hsmall
  · exact
      mainFormal_sourceZeroKBoundaryObligation
        params strategy eps _hpass k _hk _hsmall (Nat.eq_zero_of_not_pos hk0)

/--
Internal proof-obligation wrapper for the printed two-space theorem
`thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This theorem removes the saturated-error branch from the source-boundary
frontier.  If `mainFormalError params k eps ≥ 1`, the conclusion follows from
`mainFormal_source_trivial_witness`; otherwise the proof is exactly the named
small-error obligation `mainFormal_sourceSmallErrorObligation`.  The wrapper is
not an additional hypothesis of `thm:main-formal`.

**Unfaithful:** The small-error branch calls the tracked obligation
`mainFormal_sourceSmallErrorObligation`, whose proof is not yet derived from the
source theorem hypotheses.  Documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`,
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue #1458; the source
theorem is `references/ldt-paper/test_definition.tex:180-202`.
Elimination: discharge `mainFormal_sourceSmallErrorObligation` while preserving
the printed two-space statement and the paper bound `k ≥ m d`. -/
theorem mainFormal_sourceObligation
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  by_cases hlarge : 1 ≤ mainFormalError params k eps
  · exact mainFormal_source_trivial_witness params strategy eps k hlarge
  · exact mainFormal_sourceSmallErrorObligation params strategy eps hpass k hk hlarge

/--
Source statement of `thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This theorem records the printed paper theorem for a general two-space
projective strategy, with the paper's hypothesis `k ≥ m d` and the three final
consistency conclusions at the error `mainFormalError`.

**Proof gap:** The checked route below proves only the separate same-space,
corrected large-`k` interface `mainFormal`.  The same-space restriction is
documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`; the
large-`k` and scalar-cascade boundary is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  The source theorem is
therefore kept as a source-faithful statement and its proof is factored through
the named internal obligation `mainFormal_sourceObligation`, rather than being
replaced by a theorem with additional bridge, residual, repair, package,
producer, or generic hypothesis fields.

**Unfaithful:** The proof currently calls the tracked wrapper
`mainFormal_sourceObligation`; its saturated-error branch is proved, while its
small-error branch calls `mainFormal_sourceSmallErrorObligation`, whose proof is
not yet derived from the source theorem hypotheses.  Documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`,
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue #1458; the source
theorem is `references/ldt-paper/test_definition.tex:180-202`.
Elimination: discharge `mainFormal_sourceSmallErrorObligation` while preserving
the printed two-space statement and the paper bound `k ≥ m d`. -/
theorem mainFormal_sourceStatement
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  exact mainFormal_sourceObligation params strategy eps hpass k hk


/-- The role-register witness used by the `m = 1` branch of
`mainFormal`.

Supports the base case (`m = 1`) of the main formal theorem
`\label{thm:main-formal}` in `references/ldt-paper/inductive_step.tex`.
The base-case argument uses the witness produced by
`MainFormalRoleInductionWitness.ofBaseCase`; this definition names that choice. -/
noncomputable def mainFormalBaseRoleInductionWitness
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm1 : params.m = 1) :
    MainFormalRoleInductionWitness params strategy eps hpass k :=
  Classical.choice (MainFormalRoleInductionWitness.ofBaseCase params strategy eps k hpass hm1)

/-- Derives the three consistency conclusions of `thm:main-formal` from a
constructed Section 6 projective-completion witness.

The witness contains the role-register output and the post-role completion
data.  This theorem performs only the already-formalized final transport and
scalar absorption steps; it does not introduce additional auxiliary
hypotheses. -/
theorem mainFormal_ofProjectiveCompletionTransportWitness
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (projectiveCompletionWitness :
      MainFormalProjectiveCompletionTransportWitness params strategy eps k scalars) :
    ∃ G_A G_B : ProjMeas (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (polynomialEvaluationFamily params G_B.toSubMeas)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params G_A.toSubMeas)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily G_A.toSubMeas)
          (constSubMeasFamily G_B.toSubMeas)
          (mainFormalError params k eps) := by
  exact MainFormalProjectiveCompletionTransportWitness.toMainFormal
    projectiveCompletionWitness hpass

/--
`thm:main-formal`, current formal interface.

This is the same-space, corrected large-`k` Lean interface
toward the paper theorem.  The printed theorem in `test_definition.tex` starts
from a general two-space projective strategy and prints the weaker condition
`k ≥ m d`.  The same-space interface restriction is documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`; the
large-`k` and `k > 0` scalar-cascade boundary is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.

The statement does not assume repaired auxiliary data, role-register witness
data, or final projective-completion hypotheses. Those remain open steps to be
derived from the pass condition and the preceding sections.

The hypothesis `hk : 400 * params.m * params.d ≤ k`, together with `hk0`,
records the strengthened boundary from issue #906 and
`rem:main-formal-k-boundary`; the paper states the weaker condition `k ≥ md`.
The positivity of `k` is a scalar-cascade boundary: it supplies the `1 ≤ k`
field of `CascadeHypotheses` in the non-vacuous branch, rather than any
measurement-construction data.
The field model is presently fixed at universe level `0`, matching the current
Section 6 successor theorem rather than an additional mathematical restriction.

The current interface has no bridge, residual, repair, or obligation
hypotheses.  In the non-vacuous branch the proof constructs the scalar cascade
and role-register witness from the theorem hypotheses, then calls
`MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness` and the
already proved final transport.  The role-register witness is built from
`MainInductionStep.mainInduction` via `strategySymmetrization_mainInduction`;
the base case is discharged by `mainInductionBaseCase`.  The Step 6 base-case
transport uses the checked repaired line-169 estimate with its explicit
additional loss, so the exact match-mass branch no longer lies on the active
`mainFormal` path. -/
theorem mainFormal
    (params : Parameters) [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k) :
    ∃ G_A G_B : ProjMeas (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (polynomialEvaluationFamily params G_B.toSubMeas)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params G_A.toSubMeas)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily G_A.toSubMeas)
          (constSubMeasFamily G_B.toSubMeas)
          (mainFormalError params k eps) := by
  by_cases hlarge : 1 ≤ mainFormalError params k eps
  · exact mainFormal_trivial_witness params strategy eps k hlarge
  · have hepsNN : 0 ≤ eps := SameSpaceProjStrat.eps_nonneg_of_passes hpass
    let scalars : MainFormalCascadeScalars params eps k :=
      MainFormalCascadeScalars.ofNontrivialMainFormal hepsNN hk0 hlarge
    rcases MainFormalRoleInductionWitness.ofMainInduction
        params strategy eps k hpass hk with ⟨roleInductionWitness⟩
    rcases
        MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness
          (scalars := scalars) hlarge roleInductionWitness with
      ⟨projectiveCompletionWitness⟩
    exact mainFormal_ofProjectiveCompletionTransportWitness (hpass := hpass)
      projectiveCompletionWitness

/--
Same-space, corrected-range subcase of the source-shaped conclusion of
`thm:main-formal`.

This theorem records the portion of the printed two-space source theorem that is
already obtained from the current checked interface: after forgetting a
`SameSpaceProjStrat` to its underlying two-space `ProjStrat`, the three final
consistency conclusions follow under the corrected hypotheses
`400 * m * d ≤ k` and `0 < k`.

It is not a substitute for the source theorem.  The general two-space
symmetrization and the paper range `k ≥ m d` remain the separate source-boundary
work recorded in `mainFormal_sourceObligation`, whose saturated-error branch is
proved and whose remaining branch is `mainFormal_sourceSmallErrorObligation`.
This theorem is standard-axiom clean because it only calls the checked current
same-space interface; it is not a substitute for the printed two-space theorem. -/
theorem mainFormal_sourceConclusion_ofSameSpaceLargeK
    (params : Parameters)
    [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k) :
    ∃ G_A : ProjMeas (Polynomial params) ι,
      ∃ G_B : ProjMeas (Polynomial params) ι,
        ConsRel strategy.toProjStrat.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.toProjStrat.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.toProjStrat.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.toProjStrat.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.toProjStrat.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  simpa using
    mainFormal params strategy eps hpass k hk (hk0 := hk0)

end Test

end MIPStarRE.LDT
