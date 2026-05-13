import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.MatchMass
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Output

/-!
# Completion transport residuals

Post-role completion transport residuals for the culminating step of the
`mainFormal` proof.  After the Section 6 role-register measurement is obtained
and the two unsymmetrization links are established, the remaining step is to
close the projective completion gap: the orthonormalize-and-complete procedure
(`lem:orthonormalization-main-lemma`, `prop:completing-to-measurement`)
produces projective measurements at distance `ζ₂` from the unsymmetrized ones.
This module records the post-role residual that asks only for the left-register
completion estimates and the match-mass monotonicity invariant needed to recover
the paper line-169 polynomial links.  It then converts directly to the projective
completion residual consumed by the culminating `mainFormal` step.

## References

* Paper: `references/ldt-paper/orthonormalization.tex`,
  `\Cref{lem:orthonormalization-main-lemma}` at line 282; and
  `references/ldt-paper/preliminaries.tex`,
  `\Cref{prop:completing-to-measurement}` at line 1101.
  These are applied in `references/ldt-paper/inductive_step.tex`
  (lines 135–143).
* Blueprint: `blueprint/src/chapter/ch04_projective.tex`,
  `\label{rem:lean-line169-projectivization-match-mass}`; and
  `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-step6-obligations}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Post-role residual whose Bob-side completion estimate is still in the
left-register form returned by the orthonormalize-and-complete chain.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`, with the
right-register transport formalized separately from the paper's line-147
completion estimate.

This is the paper Step 6 boundary just before applying the permutation-invariant
right-register transport from #869.  The Alice completion field already matches
`inductive_step.tex` line 146.  For Bob, the analytic completion theorem naturally
returns the left-lifted estimate for `G^B` and `Q^B`; the conversion below uses
`MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv` to recover
the line-147 right-register estimate.  The exact line-169 `ζ₁` links are not
stored directly here: this residual carries the construction-level match-mass
monotonicity invariant, and the outer conversion combines it with the
reconstructed pre-projective consistency proof to derive line 169. -/
structure MainFormalPostRolePackageLeftCompletionTransportResidual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- The completed projective measurement denoted $Q^{\mathrm A}$. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The completed projective measurement denoted $Q^{\mathrm B}$. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Left-register completion closeness, paper line 146 (`eq:G-with-Q-A`). -/
  leftCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily leftMeasurement.toSubMeas.liftLeft)
      scalars.zeta2
  /-- Bob-side completion closeness in the left-register form returned by the
  orthonormalize-and-complete chain, before #869 transports it to line 147. -/
  rightCompletionClosenessLeft :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily rightMeasurement.toSubMeas.liftLeft)
      scalars.zeta2
  /-- Construction-level invariant that yields the exact paper line-169 `ζ₁`
  transports once combined with the pre-projective `G^A/G^B` consistency proof. -/
  completionTransportMatchMassMonotonicity :
    MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity strategy.state
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      leftMeasurement rightMeasurement

namespace MainFormalPostRolePackageLeftCompletionTransportResidual

/-- Build the post-role residual from two orthonormalize-and-complete statements
whose completed measurements are the canonical completions of the produced
projective submeasurements.

The remaining non-analytic inputs are exactly the construction-level match-mass
monotonicity inequalities for the orthonormalized submeasurements; completion then
preserves those inequalities by positivity. -/
noncomputable def ofCompleteAtOutcomeStatements
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (P_A P_B : ProjSubMeas (Polynomial params) ι)
    (a_A a_B : Polynomial params)
    (leftStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
        P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1)
    (rightStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
        P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1)
    (hleftMass :
      qBipartiteMatchMass strategy.state P_A.toSubMeas
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
    (hrightMass :
      qBipartiteMatchMass strategy.state P_B.toSubMeas
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas) :
    MainFormalPostRolePackageLeftCompletionTransportResidual
      params strategy eps k scalars rolePackage where
  leftMeasurement := Preliminaries.completeAtOutcomeProj P_A a_A
  rightMeasurement := Preliminaries.completeAtOutcomeProj P_B a_B
  leftCompletionCloseness := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono strategy.state
      (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily (Preliminaries.completeAtOutcomeProj P_A a_A).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
      scalars.zeta2
      (MainFormalCascadeScalars.orthonormalizeAndCompleteError_zeta1_le_zeta2
        scalars hsmall)
      leftStmt.completedCloseness
  rightCompletionClosenessLeft := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono strategy.state
      (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily (Preliminaries.completeAtOutcomeProj P_B a_B).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
      scalars.zeta2
      (MainFormalCascadeScalars.orthonormalizeAndCompleteError_zeta1_le_zeta2
        scalars hsmall)
      rightStmt.completedCloseness
  completionTransportMatchMassMonotonicity :=
    MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity.of_completeAtOutcomeProj
      P_A P_B a_A a_B hleftMass hrightMass

/-- Transport the Bob-side completion estimate from the left-register form to the
right-register form and recover the projective completion residual consumed by
the culminating `mainFormal` step.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`; the transport
is a formalization-level register-placement step for the paper's line-147
estimate.

This is the local `mainFormal` consumer of the right-register completion helper
added in #869.  The factor-two unsymmetrization estimates are reconstructed from
the role measurement record by
`MainFormalRoleMeasurementPackage.toUnsymmetrizationBridge`, so no intermediate
record is needed here. -/
noncomputable def toCompletionTransportResidual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (residual : MainFormalPostRolePackageLeftCompletionTransportResidual
      params strategy eps k scalars rolePackage)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    MainFormalCascadeProjectiveCompletionTransportResidual params strategy eps k scalars :=
  let bridge := rolePackage.toUnsymmetrizationBridge
  { roleMeasurement := rolePackage.roleMeasurement
    pointARightPOVMConsistency := bridge.pointAConsistency
    leftPOVMPointBConsistency := bridge.pointBConsistency
    leftMeasurement := residual.leftMeasurement
    rightMeasurement := residual.rightMeasurement
    leftCompletionCloseness := residual.leftCompletionCloseness
    rightCompletionCloseness := by
      have hleft : SDDRel strategy.state (uniformDistribution Unit)
          (IdxSubMeas.liftLeft
            (constSubMeasFamily
              (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas))
          (IdxSubMeas.liftLeft
            (constSubMeasFamily residual.rightMeasurement.toSubMeas))
          scalars.zeta2 := by
        simpa [IdxSubMeas.liftLeft, constSubMeasFamily] using
          residual.rightCompletionClosenessLeft
      have hright :=
        MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv
          strategy.permInvState (uniformDistribution Unit)
          (constSubMeasFamily
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
          (constSubMeasFamily residual.rightMeasurement.toSubMeas)
          scalars.zeta2 hleft
      simpa [IdxSubMeas.liftRight, constSubMeasFamily] using hright
    leftProjectiveRightPOVMPolynomialConsistency :=
      MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity.leftConsistency
        residual.completionTransportMatchMassMonotonicity hpre
    rightProjectiveLeftPOVMPolynomialConsistency := by
      have hpre_symm : ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
          (constSubMeasFamily
            (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
          scalars.zeta1 :=
        consRel_symm_of_density_fixed strategy.state strategy.densityFixed
          (uniformDistribution Unit)
          (constSubMeasFamily
            (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
          (constSubMeasFamily
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
          scalars.zeta1 hpre
      exact
        MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity.rightConsistency
          residual.completionTransportMatchMassMonotonicity hpre_symm }

end MainFormalPostRolePackageLeftCompletionTransportResidual

end Test

end MIPStarRE.LDT
