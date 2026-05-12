import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.MatchMass
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Output

/-!
# Completion transport residuals

Post-role completion transport residuals for the `mainFormal` assembly.  After
the Section 6 role-register measurement is obtained and the two
unsymmetrization links are established, the remaining step is to close the
projective completion gap: the orthonormalize-and-complete procedure
(`lem:orthonormalization-main-lemma`, `prop:completing-to-measurement`)
produces projective measurements at distance `ζ₂` from the unsymmetrized ones.
This module records that post-role obligation as a series of nested residual
structures (`MainFormalCascadeRolePackagedCompletionTransportResidual`,
`MainFormalPostRolePackageCompletionTransportResidual`,
`MainFormalPostRolePackageLeftCompletionTransportResidual`, …), each asking
for progressively more specific inputs.  The farthest-reaching residual is
`MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual`, whose
first field is the concrete Section 6 role residual and whose post-role field
asks only for the left-register completion closeness and the match-mass
monotonicity invariant.

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

/-- Residual after consuming the checked role-register Section 6 record.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`, applying
`references/ldt-paper/orthonormalization.tex:282`
(`\label{lem:orthonormalization-main-lemma}`) and completion.

This residual record is narrower than
`MainFormalCascadeProjectiveCompletionTransportResidual`:
the role-register measurement and both factor-two unsymmetrization estimates are
no longer independent fields.  They are supplied by
`MainFormalRoleMeasurementPackage`, whose symmetrized consistency field feeds the
proved constructor `UnsymmetrizationBridgePackage.ofSymConsistency`.  The
remaining fields are therefore exactly the projectivization/completion data and
the two polynomial line-169 transport links. -/
structure MainFormalCascadeRolePackagedCompletionTransportResidual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The role-register Section 6 output at the cascade scalar `σ`. -/
  rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars
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
  /-- Right-register completion closeness, paper line 147. -/
  rightCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftRight)
      (constSubMeasFamily rightMeasurement.toSubMeas.liftRight)
      scalars.zeta2
  /-- Paper line 169, before the data-processing step at lines 171--173:
  $Q^{\mathrm A}_g\otimes I \simeq_{\zeta_1} I\otimes G^{\mathrm B}_g$. -/
  leftProjectiveRightPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Bob-role mirror of paper line 169, before point-evaluation data processing. -/
  rightProjectiveLeftPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1

namespace MainFormalCascadeRolePackagedCompletionTransportResidual

/-- Convert the residual carrying the role-measurement record to the previous
completion-transport shape.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`.

The only work is to expand `MainFormalRoleMeasurementPackage` into the
role-register measurement and the two Step 3 factor-two estimates using the
checked unsymmetrization constructor. -/
noncomputable def toCompletionTransportResidual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeRolePackagedCompletionTransportResidual
      params strategy eps k scalars) :
    MainFormalCascadeProjectiveCompletionTransportResidual params strategy eps k scalars :=
  let bridge := residual.rolePackage.toUnsymmetrizationBridge
  { roleMeasurement := residual.rolePackage.roleMeasurement
    pointARightPOVMConsistency := bridge.pointAConsistency
    leftPOVMPointBConsistency := bridge.pointBConsistency
    leftMeasurement := residual.leftMeasurement
    rightMeasurement := residual.rightMeasurement
    leftCompletionCloseness := residual.leftCompletionCloseness
    rightCompletionCloseness := residual.rightCompletionCloseness
    leftProjectiveRightPOVMPolynomialConsistency :=
      residual.leftProjectiveRightPOVMPolynomialConsistency
    rightProjectiveLeftPOVMPolynomialConsistency :=
      residual.rightProjectiveLeftPOVMPolynomialConsistency }

end MainFormalCascadeRolePackagedCompletionTransportResidual

/-- Projectivization/completion and line-169 residual after a concrete
role-measurement record has already been produced.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`, applying
`references/ldt-paper/orthonormalization.tex:282`
(`\label{lem:orthonormalization-main-lemma}`).

This is the post-role part of
`MainFormalCascadeRolePackagedCompletionTransportResidual`: the role-register
measurement is no longer a field, so the remaining data are exactly the two
completed projective measurements, their completion closeness to the
unsymmetrized POVMs, and the two polynomial line-169 transport estimates. -/
structure MainFormalPostRolePackageCompletionTransportResidual
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
  /-- Right-register completion closeness, paper line 147. -/
  rightCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftRight)
      (constSubMeasFamily rightMeasurement.toSubMeas.liftRight)
      scalars.zeta2
  /-- Paper line 169, before the data-processing step at lines 171--173. -/
  leftProjectiveRightPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Bob-role mirror of paper line 169, before point-evaluation data processing. -/
  rightProjectiveLeftPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1

namespace MainFormalPostRolePackageCompletionTransportResidual

/-- Reinsert the already-produced role-measurement record into the older
completion-transport residual carrying that record.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`. -/
noncomputable def toRolePackagedCompletionTransportResidual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (residual : MainFormalPostRolePackageCompletionTransportResidual
      params strategy eps k scalars rolePackage) :
    MainFormalCascadeRolePackagedCompletionTransportResidual params strategy eps k scalars where
  rolePackage := rolePackage
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  leftCompletionCloseness := residual.leftCompletionCloseness
  rightCompletionCloseness := residual.rightCompletionCloseness
  leftProjectiveRightPOVMPolynomialConsistency :=
    residual.leftProjectiveRightPOVMPolynomialConsistency
  rightProjectiveLeftPOVMPolynomialConsistency :=
    residual.rightProjectiveLeftPOVMPolynomialConsistency

end MainFormalPostRolePackageCompletionTransportResidual

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
right-register form and recover the previous post-role residual.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`; the transport
is a formalization-level register-placement step for the paper's line-147
estimate.

This is the local `mainFormal` consumer of the right-register completion helper
added in #869. -/
noncomputable def toPostRolePackageCompletionTransportResidual
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
    MainFormalPostRolePackageCompletionTransportResidual
      params strategy eps k scalars rolePackage where
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
        residual.completionTransportMatchMassMonotonicity hpre_symm

end MainFormalPostRolePackageLeftCompletionTransportResidual

/-- Combined live residual after isolating the concrete role-register output.

Paper origin: `references/ldt-paper/inductive_step.tex:68-173`, combining the
role-register Section 6 output, unsymmetrization, and projectivization/completion
steps of the `mainFormal` proof.

The first field is the actual Section 6 role residual: it carries the concrete
role-register measurement and its symmetrized consistency proof.  The second
field contains only the projectivization/completion and line-169 data for the
role-measurement record obtained from that concrete residual.  Thus the live
`mainFormal` hole no longer asks for an arbitrary
`MainFormalRoleMeasurementPackage`, an arbitrary Section 6 witness, or a branch
witness not tied to the concrete measurement. The branch-level base, ordinary
successor, and answer-valued
successor constructors remain available on `MainFormalRolePackageResidual` and
`MainFormalRolePackageBranchResidual` as the intended ways to supply this field;
their branch conversion consumes the public large-`k` hypothesis directly rather
than storing it as residual data. -/
structure MainFormalCascadeRolePackageResidualCompletionTransportResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The explicit isolated Section 6 residual.  Keeping this field concrete avoids
  hiding the role-register measurement behind `Classical.choice`. -/
  roleResidual : MainFormalRolePackageResidual params strategy eps hpass k
  /-- The remaining projectivization/completion and line-169 data after role production. -/
  postRoleResidual :
    MainFormalPostRolePackageCompletionTransportResidual params strategy eps k scalars
      (roleResidual.rolePackage scalars)

namespace MainFormalCascadeRolePackageResidualCompletionTransportResidual

/-- Convert the split role-residual/post-role record back to the
completion-transport residual carrying the role-measurement record.

Paper origin: `references/ldt-paper/inductive_step.tex:68-173`.

The conversion uses the explicit `roleResidual` field, so the role-register
measurement remains visible to the post-role residual. -/
noncomputable def toRolePackagedCompletionTransportResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeRolePackageResidualCompletionTransportResidual
      params strategy eps hpass k scalars) :
    MainFormalCascadeRolePackagedCompletionTransportResidual params strategy eps k scalars :=
  residual.postRoleResidual.toRolePackagedCompletionTransportResidual

end MainFormalCascadeRolePackageResidualCompletionTransportResidual

/-- Combined live residual after isolating the concrete role-register output
and the #869 Bob-side completion transport.

Paper origin: `references/ldt-paper/inductive_step.tex:68-173`, with Bob-side
completion transport recorded as a formalization-level register-placement step.

Compared with `MainFormalCascadeRolePackageResidualCompletionTransportResidual`,
this residual no longer asks the live hole to provide the right-register
completion closeness directly.  Instead the post-role field records the
left-register Bob-side completion estimate returned by the
orthonormalize-and-complete chain, and the conversion below transports it to the
right register using permutation invariance of the strategy state.  The concrete
role residual and the
construction-level match-mass invariant for the exact paper line-169 `ζ₁` links
remain explicit. -/
structure MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The explicit isolated Section 6 residual.  Keeping this field concrete avoids
  hiding the role-register measurement behind `Classical.choice`. -/
  roleResidual : MainFormalRolePackageResidual params strategy eps hpass k
  /-- The remaining projectivization/completion and line-169 data after role production,
  with Bob-side completion still left-lifted. -/
  postRoleResidual :
    MainFormalPostRolePackageLeftCompletionTransportResidual params strategy eps k scalars
      (roleResidual.rolePackage scalars)

namespace MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual

/-- Combine a concrete Section 6 role residual with the checked post-role
orthonormalize-and-complete constructor.

This is the direct constructor for the current live residual once role production,
completion statements, and the construction-level line-169 match-mass monotonicity
inputs are available. -/
noncomputable def ofRoleResidualAndCompleteAtOutcomeStatements
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (P_A P_B : ProjSubMeas (Polynomial params) ι)
    (a_A a_B : Polynomial params)
    (leftStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement)
        P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1)
    (rightStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement)
        P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1)
    (hleftMass :
      qBipartiteMatchMass strategy.state P_A.toSubMeas
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
    (hrightMass :
      qBipartiteMatchMass strategy.state P_B.toSubMeas
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas) :
    MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual
      params strategy eps hpass k scalars where
  roleResidual := roleResidual
  postRoleResidual :=
    MainFormalPostRolePackageLeftCompletionTransportResidual.ofCompleteAtOutcomeStatements
      hsmall P_A P_B a_A a_B leftStmt rightStmt hleftMass hrightMass

/-- Convert the left-completion residual to the previous role-residual completion
line-169 shape by applying the #869 right-register transport to the Bob-side
completion estimate, using the separately reconstructed paper line-130
`G^A/G^B` consistency proof.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`. -/
noncomputable def toRolePackageResidualCompletionTransportResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual
      params strategy eps hpass k scalars)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM
          (residual.roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM
          (residual.roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1) :
    MainFormalCascadeRolePackageResidualCompletionTransportResidual
      params strategy eps hpass k scalars where
  roleResidual := residual.roleResidual
  postRoleResidual := residual.postRoleResidual.toPostRolePackageCompletionTransportResidual hpre

end MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual

end Test

end MIPStarRE.LDT
