import MIPStarRE.LDT.Test.MainTheorem.DiagonalCompletion

/-!
# Main-formal final target assembly

Final target projection used by the `mainFormal` assembly.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

namespace MainFormalCascadeProjectiveCompletionTransportResidual

/-- Construct the final projective completion-transport residual from a concrete
role-register residual.

Paper origin: `references/ldt-paper/inductive_step.tex:130-173`.

This is the source-shaped internal construction target for the non-vacuous
branch of `mainFormal`.  It reconstructs the paper line-130 cross consistency
from the role residual and constructs the line-130 orthonormalization residual.
The remaining completion step is the explicit proof obligation in
`MainFormalPostRolePackageDiagonalCompletionResidual.nonempty_ofDiagonalConsistency`;
no match-mass or diagonal-consistency data is accepted as an extra input. -/
theorem nonempty_ofRoleResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k) :
    Nonempty (MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars) := by
  have hpre := roleResidual.diagonalConsistency scalars
  rcases MainFormalPostRolePackageDiagonalOrthonormalizationResidual.nonempty_ofDiagonalConsistency
      hpre with ⟨orthResidual⟩
  have hcompletion :
      Nonempty (MainFormalPostRolePackageDiagonalCompletionResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars)) :=
    MainFormalPostRolePackageDiagonalCompletionResidual.nonempty_ofDiagonalConsistency
      orthResidual hpre
  rcases hcompletion with ⟨completion⟩
  exact ⟨completion.toProjectiveCompletionTransportResidual hsmall hpre⟩

end MainFormalCascadeProjectiveCompletionTransportResidual

namespace MainFormalCascadeProjectiveCompletionTransportResidual

/-- Convert the reconstructed line-156 projective approximation into the native
`eq:third-goal` self-consistency estimate.

The only mathematical step performed here is the projective converse of
`prop:simeq-to-approx`: for projective measurements, an `≈_{ζ₃}` relation gives
`≃_{ζ₃/2}`, which is exactly paper `eq:third-goal`
(`references/ldt-paper/inductive_step.tex:159-162`). -/
theorem selfConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily residual.leftMeasurement.toSubMeas)
      (constSubMeasFamily residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2) := by
  let leftConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => residual.leftMeasurement
  let rightConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => residual.rightMeasurement
  let pre := residual.toPreProjectiveSelfConsistency hpass
  have hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1 := by
    simpa [
      pre,
      MainFormalCascadeProjectiveCompletionTransportResidual.toPreProjectiveSelfConsistency,
      MainFormalCascadeProjectiveCompletionTransportResidual.toUnsymmetrizedPOVMTargets
    ] using pre.fullSelfConsistency
  have happroxLine := residual.fullPolynomialConsistency hpre
  have happroxAtZeta :
      Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
        (IdxProjMeas.toIdxSubMeas leftConst)
        (IdxProjMeas.toIdxSubMeas rightConst)
        scalars.zeta3 := by
    change Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily residual.leftMeasurement.toSubMeas)
      (constSubMeasFamily residual.rightMeasurement.toSubMeas)
      scalars.zeta3
    exact happroxLine
  have happrox :
      Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
        (IdxProjMeas.toIdxSubMeas leftConst)
        (IdxProjMeas.toIdxSubMeas rightConst)
        (2 * (scalars.zeta3 / 2)) := by
    convert happroxAtZeta using 1
    ring
  have hcons :=
    Preliminaries.approxToSimeq strategy.state (uniformDistribution Unit)
      leftConst rightConst (scalars.zeta3 / 2) happrox
  simpa [leftConst, rightConst, constSubMeasFamily, IdxProjMeas.toIdxSubMeas] using hcons

/-- Final packaging step for `thm:main-formal` once the projective-completion
transport residual has been constructed.

* `eq:one-goal` (lines 175--181):
  $A^{\mathrm A,u}_a \otimes I \simeq_{\zeta_4}
    I \otimes Q^{\mathrm B}_{[g(u)=a]}$;
* `eq:another-goal` (lines 182--185):
  $I \otimes A^{\mathrm B,u}_a \simeq_{\zeta_4}
    Q^{\mathrm A}_{[g(u)=a]} \otimes I$;
* `eq:third-goal` (lines 160--162):
  $Q^{\mathrm A}_g \otimes I \simeq_{\zeta_3/2} I \otimes Q^{\mathrm B}_g$.

This theorem performs only the Step 8 weakening from the paper cascade errors
to `mainFormalError` using `ConsRel.mono`; the substantive construction is in
the projective-completion transport residual. -/
theorem toMainFormal {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
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
  refine ⟨residual.leftMeasurement, residual.rightMeasurement, ?_, ?_, ?_⟩
  · exact ConsRel.mono
      (MainFormalCascadeScalars.zeta4_le_mainFormalError scalars)
      (residual.pointAConsistency hpass)
  · exact ConsRel.mono
      (MainFormalCascadeScalars.zeta4_le_mainFormalError scalars)
      (residual.pointBConsistency hpass)
  · exact ConsRel.mono
      (MainFormalCascadeScalars.zeta3_div_two_le_mainFormalError scalars)
      (residual.selfConsistency hpass)

end MainFormalCascadeProjectiveCompletionTransportResidual

end Test

end MIPStarRE.LDT
