import MIPStarRE.LDT.Test.MainTheorem.NativeTargets

/-!
# Main-formal soundness theorem

Base handoff, final projective-completion transport, and the paper-facing proof
gap for `thm:main-formal` (`\Cref{thm:main-formal}`).  This module contains:

* `mainFormalBaseRoleResidual` — names the Section 6 role-register residual
  used by the base case `m = 1`.

* `mainFormal_ofProjectiveCompletionResidual` — derives the three consistency
  conclusions of `thm:main-formal` from a constructed Section 6
  projective-completion residual.

* `mainFormal` — the paper theorem statement, taking a projective strategy that
  passes the LID test with probability `≥ 1 − ε`, together with the explicit
  boundary conditions `0 < d`, `0 < k`, and `400md ≤ k`, and producing the three
  pointwise consistency targets at error bound `mainFormalError`.  Its proof is
  currently a direct proof gap rather than a theorem with extra bridge
  hypotheses.  The role-register Section 6 measurement itself is available from
  `MainFormalRolePackageResidual.ofMainInductionLargeK`; the successor part of
  that construction is the tracked `sorry` in the source theorem
  `MainInductionStep.mainInduction`, not an added hypothesis of `mainFormal`.

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

/-! ### Base handoff and final projective-completion transport

The base branch of `mainFormal` needs a concrete Section 6 role residual and one
post-role projective-completion residual.  Earlier scaffolding expressed this
through separate bridge and obligation packages.  The current public theorem below
does not keep such packages as hypotheses: the theorem remains paper-shaped, and
the missing construction is represented by a direct proof gap. -/


/-- The role-register residual used by the `m = 1` branch of
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

**Proof gap:** the paper-facing statement is restored without bridge, residual,
repair, or obligation hypotheses.  The Section 6 role-register residual is now
obtained by applying the source-facing theorem `MainInductionStep.mainInduction`
through `MainFormalRolePackageResidual.ofMainInductionLargeK`; its successor
case remains the tracked `sorry` in Section 6.  The remaining Section 3 work is
to construct the post-role projective-completion residual from the paper
hypotheses, then apply `mainFormal_ofProjectiveCompletionResidual` for the
already-proved final transport.  This is tracked by #1043, #1363, and #1458.
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
  -- TODO(#1043, #1363, #1458): construct the Section 6 role residual and the
  -- projective-completion residual from the paper hypotheses.  Once that
  -- residual is available, the proved final transport is
  -- `mainFormal_ofProjectiveCompletionResidual`.
  sorry

end Test

end MIPStarRE.LDT
