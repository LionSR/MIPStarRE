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

namespace MainFormalCascadeTransportTargets

/-- Final packaging step for `thm:main-formal` once the cascade transport
targets have been constructed.

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
the transport-target data. -/
theorem toMainFormal {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (targets : MainFormalCascadeTransportTargets params strategy eps k scalars) :
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
  refine ⟨targets.leftMeasurement, targets.rightMeasurement, ?_, ?_, ?_⟩
  · exact ConsRel.mono
      (MainFormalCascadeScalars.zeta4_le_mainFormalError scalars)
      targets.pointAConsistency
  · exact ConsRel.mono
      (MainFormalCascadeScalars.zeta4_le_mainFormalError scalars)
      targets.pointBConsistency
  · exact ConsRel.mono
      (MainFormalCascadeScalars.zeta3_div_two_le_mainFormalError scalars)
      targets.selfConsistency

end MainFormalCascadeTransportTargets

end Test

end MIPStarRE.LDT
