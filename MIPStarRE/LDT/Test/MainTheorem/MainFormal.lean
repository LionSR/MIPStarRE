import MIPStarRE.LDT.Test.MainTheorem.NativeTargets

/-!
# Main-formal soundness theorem

Base case, successor branch, and conditional reductions for `thm:main-formal`
(`\Cref{thm:main-formal}`).  This module contains:

* `MainFormalBaseProjectiveCompletionObligations` — the still-unformalized
  analytic obligations needed for the base case `m = 1` (distinguished
  completion outcomes and match-mass preservation for the orthonormalized
  projective submeasurements).

* `MainFormalBaseCompletionObligations` — the remaining base-case analytic data,
  stated in the match-mass form used by the paper's line-130 completion route.

* `mainFormal_ofProjectiveCompletionResidual` — derives the three consistency
  conclusions of `thm:main-formal` from a constructed Section 6
  projective-completion residual.

* `mainFormal_ofInternalObligations` — the top-level theorem that keeps the
  paper-facing statement fixed while the remaining base and successor
  construction obligations are isolated as internal declarations.

* `mainFormal` — the paper theorem statement, taking a projective strategy that
  passes the LID test with probability `≥ 1 − ε`, together with the explicit
  boundary conditions `0 < d`, `0 < k`, and `400md ≤ k`, and producing the three
  pointwise consistency targets at error bound `mainFormalError`.

## References

* Paper: `references/ldt-paper/test_definition.tex`,
  `\Cref{thm:main-formal}` at line 180; its proof is in
  `references/ldt-paper/inductive_step.tex` (lines 26–236).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `\label{thm:main-formal}`; and
  `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-step6-obligations}`,
  `\label{lem:main-formal-successor-handoff}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-! ### Base (m = 1) Step 6 analytic obligations

The base case (`m = 1`) generation of the Step 6 witness residual still
requires the analytic completion content after orthonormalization: distinguished
completion outcomes and match-mass preservation for the orthonormalized
projective submeasurements.  The line-130 orthonormalization itself is now
derived from the checked role residual by the Section 5 repair construction.  When
these obligations are supplied, `baseProjectiveCompletionResidual` provides the
formal theorem that fills the base branch of `mainFormal`. -/

/-- Paper origin: `references/ldt-paper/test_definition.tex:180-202`
(`\label{thm:main-formal}`) and its proof in
`references/ldt-paper/inductive_step.tex:26-236`
(orthonormalization and completion cascade in Section 3);
blueprint `\label{def:main-formal-step6-obligations}`.

Analytic obligations that are still unformalized for the
base case (`m = 1`) Step 6 witness residual: distinguished
outcomes and match-mass preservation for the unsymmetrized POVMs.

Proving these obligations yields a complete `baseProjectiveCompletionResidual`
for the base branch of `mainFormal`; the remaining successor-case steps are
tracked separately. -/
structure MainFormalBaseProjectiveCompletionObligations
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
  (scalars : MainFormalCascadeScalars params eps k)
  (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k) where
  /-- Alice-side distinguished outcome for the completion step. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome for the completion step. -/
  a_B : Polynomial params
  /-- Alice-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_A` preserves match mass against
  Bob's unsymmetrized POVM. -/
  leftMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_A
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
  /-- Bob-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_B` preserves match mass against
  Alice's unsymmetrized POVM. -/
  rightMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_B
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)

/-- Assemble the Step 6 witness residual from the named analytic obligations.

This theorem takes an explicit `roleResidual` (obtainable from either
`MainFormalRolePackageResidual.ofBaseCase` or the successor-branch
handoff) and the `MainFormalBaseProjectiveCompletionObligations` record, then
assembles the Step 6 witness residual through
`MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
  .nonempty_ofRoleResidualAndMatchMassPreservation`.

Refs #1009, #422. -/
theorem baseProjectiveCompletionResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (obligations : MainFormalBaseProjectiveCompletionObligations params strategy eps k
      hpass scalars roleResidual) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      params strategy eps hpass k scalars) := by
  exact (open MainFormalCascadeRolePackageResidualProjectiveCompletionResidual in
    nonempty_ofRoleResidualAndMatchMassPreservation
      roleResidual obligations.a_A obligations.a_B
      obligations.leftMatchMassPreservation obligations.rightMatchMassPreservation)


/-- Paper origin: `references/ldt-paper/inductive_step.tex:26-236`
(proof of `\label{thm:main-formal}`, orthonormalization + completion cascade);
blueprint `\label{def:main-formal-step6-obligations}`.

Narrowed base-case completion obligations for Step 6 when `params.m = 1`.

Compared to `MainFormalBaseProjectiveCompletionObligations`, this structure
omits the two distinguished outcomes `a_A` and `a_B`, which the conversion below
fills with the explicit zero polynomial at `m = 1`.  The remaining fields are
the match-mass preservation obligations that must be proved by the base-case
branch argument.

A conversion theorem `baseProjectiveCompletionObligations_ofBaseCompletionObligations`
constructs the full `MainFormalBaseProjectiveCompletionObligations` from
`MainFormalBaseCompletionObligations` by providing the explicit zero polynomial
as the distinguished outcome on both sides.

Refs #1043, #1009, #422. -/
structure MainFormalBaseCompletionObligations
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
  (scalars : MainFormalCascadeScalars params eps k)
  (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k) where
  /-- Alice-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_A` preserves match mass against
  Bob's unsymmetrized POVM. -/
  leftMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_A
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
  /-- Bob-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_B` preserves match mass against
  Alice's unsymmetrized POVM. -/
  rightMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_B
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)

/-- Convert narrowed base completion obligations to the full
`MainFormalBaseProjectiveCompletionObligations` by providing the explicit zero
polynomial as the distinguished outcome on both sides.

Paper origin: the base case of `thm:main-induction` at
`references/ldt-paper/inductive_step.tex:418-427` and the final
orthonormalization/completion cascade at
`references/ldt-paper/inductive_step.tex:136-160`.

The distinguished outcomes `a_A` and `a_B` are chosen as the zero polynomial;
`completeAtOutcomeProj` works for any distinguished outcome, so this choice
is sound.  Arguments that need specific distinguished outcomes should use
`MainFormalBaseProjectiveCompletionObligations` directly.

Refs #1043. -/
noncomputable def baseProjectiveCompletionObligations_ofBaseCompletionObligations
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    {roleResidual : MainFormalRolePackageResidual params strategy eps hpass k}
    (obligations : MainFormalBaseCompletionObligations params strategy eps k hpass
      scalars roleResidual) :
    MainFormalBaseProjectiveCompletionObligations params strategy eps k hpass scalars
      roleResidual where
  a_A := { poly := 0, lowIndividualDegree := by intro i; simp [MvPolynomial.degreeOf_zero] }
  a_B := { poly := 0, lowIndividualDegree := by intro i; simp [MvPolynomial.degreeOf_zero] }
  leftMatchMassPreservation := obligations.leftMatchMassPreservation
  rightMatchMassPreservation := obligations.rightMatchMassPreservation

/-- Convenience theorem for `baseProjectiveCompletionResidual` using the narrowed
base completion obligations.

The narrowed `MainFormalBaseCompletionObligations` omits `a_A` and `a_B`, which
are filled with the explicit zero polynomial by
`baseProjectiveCompletionObligations_ofBaseCompletionObligations`. The
`params.m = 1` hypothesis is consumed upstream when constructing the base-case
role residual, so this theorem only performs the Step 6 completion conversion.

Refs #1043. -/
theorem baseProjectiveCompletionResidual_ofBaseCompletionObligations
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (obligations : MainFormalBaseCompletionObligations params strategy eps k hpass
      scalars roleResidual) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      params strategy eps hpass k scalars) := by
  exact baseProjectiveCompletionResidual roleResidual
    (baseProjectiveCompletionObligations_ofBaseCompletionObligations obligations)


/-- The checked role-register residual used by the `m = 1` branch of
`mainFormal`.

Supports the base case (`m = 1`) of the main formal theorem
`\label{thm:main-formal}` in `references/ldt-paper/inductive_step.tex`.
The base-case argument uses the residual produced by
`MainFormalRolePackageResidual.ofBaseCase`; this definition names that choice. -/
noncomputable def mainFormalBaseRoleResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm1 : params.m = 1) :
    MainFormalRolePackageResidual params strategy eps hpass k :=
  Classical.choice (MainFormalRolePackageResidual.ofBaseCase params strategy eps k hpass hm1)

/-- The remaining match-mass completion obligations for the base case of `mainFormal`.

Paper origin: `references/ldt-paper/inductive_step.tex:26-236`
(proof of `\label{thm:main-formal}`, base case of the
orthonormalization and completion argument); blueprint
`\label{def:main-formal-step6-obligations}`.

This type specializes `MainFormalBaseCompletionObligations` to the checked role
residual for the base case (`m = 1`).  Its fields are the line-130
match-mass preservation obligations, not diagonal self-consistency assumptions. -/
abbrev MainFormalBaseBranchCompletionObligations
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm1 : params.m = 1)
    (scalars : MainFormalCascadeScalars params eps k) :
    Prop :=
  MainFormalBaseCompletionObligations params strategy eps k hpass scalars
    (mainFormalBaseRoleResidual params strategy eps k hpass hm1)

/-- Derives the three consistency conclusions of `thm:main-formal` from a
constructed Section 6 projective-completion residual.

The residual contains the role-register output and the post-role completion
data.  This theorem performs only the already-formalized final transport and
scalar absorption steps; it does not introduce additional bridge hypotheses. -/
theorem mainFormal_ofProjectiveCompletionResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (projectiveCompletionResidual :
      MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
        params strategy eps hpass k scalars) :
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
  let rolePackage := projectiveCompletionResidual.roleResidual.rolePackage scalars
  have hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1 := by
    simpa [rolePackage] using
      projectiveCompletionResidual.roleResidual.diagonalConsistency scalars
  let rolePackageResidualLeftCompletionTransportResidual :
      MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual
        (params := params) (strategy := strategy) (eps := eps)
        (hpass := hpass) (k := k) (scalars := scalars) :=
    projectiveCompletionResidual.toLeftCompletionTransportResidual hsmall
  have hpreForResidual : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM
          (rolePackageResidualLeftCompletionTransportResidual.roleResidual.rolePackage
            scalars).roleMeasurement).toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM
          (rolePackageResidualLeftCompletionTransportResidual.roleResidual.rolePackage
            scalars).roleMeasurement).toSubMeas)
      scalars.zeta1 := by
    open MainFormalCascadeRolePackageResidualProjectiveCompletionResidual in
    simpa [rolePackage, rolePackageResidualLeftCompletionTransportResidual,
      toLeftCompletionTransportResidual] using hpre
  have rolePackageResidualCompletionTransportResidual :
      MainFormalCascadeRolePackageResidualCompletionTransportResidual
        (params := params) (strategy := strategy) (eps := eps)
        (hpass := hpass) (k := k) (scalars := scalars) :=
    rolePackageResidualLeftCompletionTransportResidual
      |>.toRolePackageResidualCompletionTransportResidual hpreForResidual
  have rolePackagedCompletionTransportResidual :
      MainFormalCascadeRolePackagedCompletionTransportResidual params strategy eps k scalars :=
    rolePackageResidualCompletionTransportResidual.toRolePackagedCompletionTransportResidual
  have completionTransportResidual :
      MainFormalCascadeProjectiveCompletionTransportResidual params strategy eps k scalars :=
    rolePackagedCompletionTransportResidual.toCompletionTransportResidual
  have projectiveTargets :
      MainFormalCascadeProjectiveStageTargets params strategy eps k scalars :=
    completionTransportResidual.toProjectiveStageTargets hpass
  exact MainFormalNativeTargets.toMainFormal
    (projectiveTargets.toTransportTargets.toCascadeTargets.toNativeTargets)

/-- Successor-case construction of the Section 6 projective-completion residual.

Paper origin: `references/ldt-paper/inductive_step.tex`, lines 352--386, where
the proof of `thm:main-induction` introduces the restricted strategies and their
failure probabilities, and lines 26--236, where the proof of `thm:main-formal`
transports the Section 6 witness through the final projectivization and
completion cascade.

This is not an additional hypothesis of the paper theorem `mainFormal`; it is an
open construction tracked separately.  The statement proves nonemptiness rather
than returning an arbitrary residual object, so the remaining gap is not hidden
as fabricated data.  The available structural constructors live in
`RoleRegister.lean` (`successorOfObligations` and the answer-valued variants);
the missing work is to produce the predecessor induction data and the per-slice
self-improvement inputs from the paper hypotheses, then assemble the resulting
role residual and completion residual.

Tracked by #1363, #422, and #1458. -/
theorem mainFormalSuccessorProjectiveCompletionObligation
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hd : 0 < params.d)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k)
    (hm_ne_one : params.m ≠ 1)
    (scalars : MainFormalCascadeScalars params eps k) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      (params := params) (strategy := strategy) (eps := eps)
      (hpass := hpass) (k := k) (scalars := scalars)) := by
  -- TODO(#1363, #422, #1458): produce the ordinary or answer-valued
  -- successor role residual and the post-role projective-completion residual
  -- from the predecessor induction package and the per-slice self-improvement
  -- proof obligations.  This should call the structural constructors in
  -- `RoleRegister.lean`, not add those inputs to `mainFormal`.
  sorry

/-- Base-case completion-input construction for `mainFormal`.

Paper origin: the orthonormalization and completion step in the proof of
`\label{thm:main-formal}`,
`references/ldt-paper/inductive_step.tex:136-160`; the `m = 1` selection
follows the base case of `\label{thm:main-induction}` at
`references/ldt-paper/inductive_step.tex:418-432`.  Blueprint:
`\label{def:main-formal-step6-obligations}`.

This theorem names the remaining base-case analytic obligation for
`mainFormal`.  It must construct match-mass preservation for the
orthonormalized projective submeasurements of the checked base-case role
residual.  The line-130 orthonormalization residual itself is derived from the
role residual by the Section 5 repair construction, not supplied as an extra
assumption.

This is the tracked proof obligation for the base branch. -/
theorem mainFormalBaseBranchCompletionObligations_ofBaseCase
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hm1 : params.m = 1)
    (scalars : MainFormalCascadeScalars params eps k) :
    MainFormalBaseBranchCompletionObligations params strategy eps k hpass hm1 scalars := by
  -- TODO(#1043): construct the base-case match-mass data from the
  -- paper's base-case orthonormalization and completion argument.  Do not
  -- replace this obligation by diagonal self-consistency assumptions.
  sorry

/--
Internal-obligation theorem for `thm:main-formal` from `test_definition.tex`.

This theorem has the same public hypotheses and conclusion as `mainFormal`.
Its proof body isolates the remaining construction work in internal obligation
declarations rather than adding obligations to the theorem statement.

The bipartite tensor placement follows the paper:
- **1a**: `A^A_u ⊗ I ≈_ν I ⊗ G^B_{[g(u)=a]}` — G_B on **right**
- **1b**: `I ⊗ A^B_u ≈_ν G^A_{[g(u)=a]} ⊗ I` — G_A on **left**, A^B on **right**
- **2**: `G^A_g ⊗ I ≈_ν I ⊗ G^B_g` — G_B on **right**

The `k`-bound boundary records the statement fix from issue #906: the paper's
successor proof applies the Section 6 / Pasting-side theorems, whose checked
side condition is `400 * params.m * params.d ≤ k`. The public theorem therefore
exposes this stronger hypothesis instead of trying to derive it from the paper's
printed `params.m * params.d ≤ k` assumption.

After first separating off the saturated-error branch, the checked role-register
infrastructure now exposes the base-case input construction, an ordinary
successor construction, and an answer-valued successor construction:

* the base handoff `strategySymmetrization_mainInductionBaseCase`, recorded as
  `MainFormalRolePackageBranchResidual.base`, and
* the predecessor/successor handoff
  `MainFormalRolePackageBranchResidual.successor`, which carries a structured
  `Parameters.SuccessorDecomposition`, transported passing strategy,
  `MainFormalSuccessorBoundary`, and
* the answer-valued predecessor/successor handoff
  `MainFormalRolePackageBranchResidual.answerSuccessor`, which carries the
  analogous `MainFormalSuccessorAnswerBoundary`.
The branch conversion receives the public current-dimension large-`k` hypothesis
and weakens it to the predecessor side condition `400 * pred.m * pred.d ≤ k`.

For arbitrary current parameters, the predecessor decomposition itself is
now formalized by `Parameters.successorDecompositionOfNeOne`.  The remaining
base-case match-mass obligation is isolated in
`mainFormalBaseBranchCompletionObligations_ofBaseCase`, while the successor branch still has its
own residual obligation.  No checked lemma here claims that the former
intermediate range `params.m * params.d ≤ k < 400 * params.m * params.d` is
vacuous.

Universe note: the formal statement uses `[FieldModel.{0} params.q]`, matching the
base-universe field-model assumption of the public Section 6 successor theorem.
This is a current formalization limitation, not a paper constraint; once the
Section 6 theorem is universe-polymorphic, this theorem should be generalized
as well.

**Unfaithful:** the public statement is source-shaped, but the proof still
depends on admitted obligation declarations:
`mainFormalBaseBranchCompletionObligations_ofBaseCase` for the base-case match-mass construction
and `mainFormalSuccessorProjectiveCompletionObligation` for the successor
projective-completion residual.  These are tracked proof obligations for
#1043, #1363, and #1458; see also
`docs/paper-gaps/issue-1099-sharper-local-fix.tex` for the local repair used in
the final completion transport.  They must be proved from the paper hypotheses,
not turned into hypotheses of `mainFormal`.  Elimination: prove the two named
obligation declarations from the hypotheses of `thm:main-formal`, then keep this
theorem as a checked internal assembly step.

Addresses #137, #239, #906, #1099, #1458.
-/
theorem mainFormal_ofInternalObligations
    (params : Parameters) [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (eps : Error)
    (hd : 0 < params.d)
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
  -- TODO(#422, #1458): The induction-side handoffs needed by
  -- `mainFormal_ofInternalObligations` are standalone formal theorems:
  -- * base branch: `strategySymmetrization_mainInductionBaseCase`,
  -- * weighted successor boundary fields:
  --   `mainFormalSuccessorAxisWeightedBound_ofPass` and
  --   `mainFormalSuccessorDiagonalWeightedBound_ofPass`,
  -- * successor Section 6 theorem call:
  --   `mainFormalSuccessorMainInductionPublicWrapper`, and
  -- * vacuous branch: `mainFormal_trivial_witness`.
  --
  -- The remaining paper-faithful target is now narrowed past the Step 5
  -- Schwartz--Zippel handoff, the line-116 triangle step, the duplicated
  -- pre-projective consistency field inside the projectivization handoff, the
  -- unused Section 6 consistency field inside the unsymmetrization package, the
  -- line-171--173 data-processing step for the `ζ₁` links, and the final `ζ₄`
  -- point-triangle argument leading to the paper-shaped Step 6 witness residual
  -- `MainFormalCascadeRolePackageResidualProjectiveCompletionResidual`.  The scalar
  -- cascade side conditions are discharged below: if `mainFormalError ≥ 1`, the
  -- theorem is vacuous; otherwise the pass condition gives `0 ≤ ε`, while
  -- `mainFormalError < 1` rules out `ε > 1` and `d > q`.
  --
  -- The remaining base and successor obligations are internal declarations,
  -- not additional hypotheses of the paper theorem.  The self-improvement
  -- assumptions are collected in `SelfImprovement.SelfImprovementObligations`.
  -- The remaining `mainFormal_ofInternalObligations` proof still needs:
  --
  -- 1. **Section 6 role residual** via base/successor branch:
  --    - `MainFormalRolePackageBranchResidual` constructed from either
  --      `base` (if `params.m = 1`), `successor`, or the answer-valued
  --      `answerSuccessor`,
  --    - ordinary or answer-valued recursive induction witnesses,
  --    - ordinary or answer-valued per-slice self-improvement obligations.
  --
  -- 2. **Completion input** for the two POVMs, derived through the paper's
  --    match-mass preservation route.  The base branch must produce the
  --    match-mass fields in `MainFormalBaseCompletionObligations`; it must not be
  --    closed by adding diagonal self-consistency assumptions.
  --
  -- 3. **Repaired line-169 transport**.  The paper's exact `ζ₁` replacement step
  --    is false as printed; the checked local repair compares with the
  --    orthonormalized submeasurement before completion and incurs the smaller
  --    loss `ζ₁ + 10 * ζ₁^(1/8)`, which is still absorbed by
  --    `mainFormalError`.
  --
  -- The full downstream cascade from the role-measurement record through the projective
  -- targets is already checked; once the residual above is supplied, the
  -- remaining proof is trivial.  Item 4 replaces the older generic `triangleSub`
  -- route whose loss was `ζ₁ + sqrt ζ₂` rather than the printed `ζ₁`.
  by_cases herr : 1 ≤ mainFormalError params k eps
  · exact mainFormal_trivial_witness params strategy eps k herr
  · have hepsNN : 0 ≤ eps := SameSpaceProjStrat.eps_nonneg_of_passes hpass
    let scalars : MainFormalCascadeScalars params eps k :=
      MainFormalCascadeScalars.ofNontrivialMainFormal hepsNN hk0 herr
    by_cases hm1 : params.m = 1
    · -- Base case (m = 1): use the checked base residual and the paper-shaped
      -- match-mass completion input.
      let roleResidual := mainFormalBaseRoleResidual params strategy eps k hpass hm1
      have hprojectiveCompletionResidual :
          Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
            (params := params) (strategy := strategy) (eps := eps)
            (hpass := hpass) (k := k) (scalars := scalars)) := by
        exact baseProjectiveCompletionResidual_ofBaseCompletionObligations roleResidual
          (mainFormalBaseBranchCompletionObligations_ofBaseCase
            params strategy eps hpass k hm1 scalars)
      rcases hprojectiveCompletionResidual with ⟨projectiveCompletionResidual⟩
      exact mainFormal_ofProjectiveCompletionResidual herr projectiveCompletionResidual
    · have hprojectiveCompletionResidual :
          Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
            (params := params) (strategy := strategy) (eps := eps)
            (hpass := hpass) (k := k) (scalars := scalars)) := by
        exact mainFormalSuccessorProjectiveCompletionObligation
          hpass hd hk hk0 hm1 scalars
      rcases hprojectiveCompletionResidual with ⟨projectiveCompletionResidual⟩
      exact mainFormal_ofProjectiveCompletionResidual herr projectiveCompletionResidual

/--
`thm:main-formal` from `test_definition.tex`.

This is the paper theorem statement. The statement includes the large-`k` and
positive-boundary conditions currently needed by the formalization, but it does
not assume the repaired bridge, role-register residual data, or final
projective-completion hypotheses. Those remain open steps to be derived from the
pass condition and the preceding sections.

The hypothesis `hk : 400 * params.m * params.d ≤ k`, together with `hk0`,
records the strengthened boundary from issue #906 and
`rem:main-formal-k-boundary`; the paper states the weaker condition `k ≥ md`.
The field model is presently fixed at universe level `0`, matching the current
Section 6 successor theorem rather than an additional mathematical restriction.

**Unfaithful:** this theorem delegates to `mainFormal_ofInternalObligations`,
whose proof uses the admitted obligation declarations
`mainFormalBaseBranchCompletionObligations_ofBaseCase` and
`mainFormalSuccessorProjectiveCompletionObligation`.  The remaining
obligations are tracked by #1043, #1363, and #1458 and must be discharged inside
the proof, rather than exposed as extra non-paper assumptions.  Elimination:
prove those two obligation declarations from the hypotheses of
`thm:main-formal`.
-/
theorem mainFormal
    (params : Parameters) [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (eps : Error)
    (hd : 0 < params.d)
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
  exact mainFormal_ofInternalObligations params strategy eps hd hpass k hk hk0

end Test

end MIPStarRE.LDT
