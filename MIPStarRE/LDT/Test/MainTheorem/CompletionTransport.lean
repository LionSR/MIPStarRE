import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency

/-!
# Completion transport residuals

Post-role completion-transport residuals used between the role-register output
and the projective-consistency layer.  The layered structures progressively
reduce the still-external Section 6 obligations: the role package is consumed
first, then the unsymmetrization and projectivization data, and finally the
left-completion transport links.

## Main definitions

* `MainFormalCascadeRolePackagedCompletionTransportResidual`,
  `toCompletionTransportResidual` — residual after consuming the checked
  role-register Section 6 package, with the
  `MainFormalRoleMeasurementPackage` carrying the symmetrized consistency.
* `MainFormalPostRolePackageCompletionTransportResidual`,
  `toRolePackagedCompletionTransportResidual` — post-role variant with the
  unsymmetrization bridge package carried explicitly.
* `MainFormalPostRolePackageLeftCompletionTransportResidual`,
  `ofCompleteAtOutcomeStatements`,
  `nonempty_ofOrthonormalizeAndCompleteInputs`,
  `toPostRolePackageCompletionTransportResidual` — left-side completion
  transport residual built from the orthonormalize-and-complete inputs.
* `MainFormalCascadeRolePackageResidualCompletionTransportResidual`,
  `toRolePackagedCompletionTransportResidual` — wrapper carrying the
  isolated `MainFormalRolePackageResidual` together with the completion
  transport data.
* `MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual`,
  `ofRoleResidualAndCompleteAtOutcomeStatements`,
  `nonempty_ofRoleResidualAndOrthonormalizeAndCompleteInputs`,
  `toRolePackageResidualCompletionTransportResidual` — same but starting
  from the role residual and the right-side complete-at-outcome statements.
* `MainFormalCascadeRolePackageResidualOrthonormalizeAndCompleteInputResidual`,
  `nonempty_leftCompletionTransportResidual` — residual using the unwrapped
  orthonormalize-and-complete inputs.

## References

* `references/ldt-paper/inductive_step.tex`, lines 130, 146 — the diagonal
  cross-relation and the completion-side measurements `Q^A`, `Q^B`.
* `references/ldt-paper/inductive_step.tex`, line 169 — the polynomial
  transport links between `(P^A, P^B)` and `(Q^A, Q^B)` consumed by the
  completion-transport residuals.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Residual after consuming the checked role-register Section 6 package.

This package is narrower than `MainFormalCascadeProjectiveCompletionTransportResidual`:
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

/-- Convert the role-packaged residual to the previous completion-transport shape.

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

/-- Projectivization/completion and polynomial projective-evaluation transport
residual (`references/ldt-paper/inductive_step.tex` line 169) after a concrete
role package has already been produced.

This is the post-role part of
`MainFormalCascadeRolePackagedCompletionTransportResidual`: the role-register
measurement is no longer a field, so the remaining data are exactly the two
completed projective measurements, their completion closeness to the
unsymmetrized POVMs, and the two polynomial projective-evaluation transport
estimates of `inductive_step.tex` line 169. -/
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

/-- Reinsert the already-produced role package into the older role-packaged
completion-transport residual. -/
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

/-- Produce the post-role residual by running the orthonormalize-and-complete chain
on the two unsymmetrized role-block POVMs.

This wrapper removes the need for callers to prepackage the two
`OrthonormalizeAndCompleteStatement`s.  The remaining analytic inputs are exactly
the strong self-consistency hypotheses and the explicit orthonormalization bridge
data required by `orthonormalizeAndComplete`.  The two match-mass hypotheses are
phrased over the produced projective submeasurements, so the exact line-169
`ζ₁` transport still remains construction-level data rather than a generic
`triangleSub` consequence.

The result is stated as `Nonempty`, rather than as a direct `def`, because
`orthonormalizeAndComplete` is an existential theorem in `Prop`; eliminating that
existential to construct a data-valued residual would require choice. -/
theorem nonempty_ofOrthonormalizeAndCompleteInputs
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (a_A a_B : Polynomial params)
    (leftSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1)
    (rightSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1)
    (leftBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas scalars.zeta1)
    (rightBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas scalars.zeta1)
    (hleftMass :
      ∀ P_A : ProjSubMeas (Polynomial params) ι,
        MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
          P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1 →
        qBipartiteMatchMass strategy.state P_A.toSubMeas
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas ≥
          qBipartiteMatchMass strategy.state
            (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
    (hrightMass :
      ∀ P_B : ProjSubMeas (Polynomial params) ι,
        MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
          P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1 →
        qBipartiteMatchMass strategy.state P_B.toSubMeas
            (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas ≥
          qBipartiteMatchMass strategy.state
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
            (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas) :
    Nonempty (MainFormalPostRolePackageLeftCompletionTransportResidual
      params strategy eps k scalars rolePackage) := by
  classical
  obtain ⟨P_A, Q_A, hQ_A, leftStmtRaw⟩ :=
    MakingMeasurementsProjective.orthonormalizeAndComplete
      (Outcome := Polynomial params) (ι := ι)
      strategy.state strategy.isNormalized strategy.permInvState
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement) a_A scalars.zeta1
      leftSelfConsistency leftBridge
  obtain ⟨P_B, Q_B, hQ_B, rightStmtRaw⟩ :=
    MakingMeasurementsProjective.orthonormalizeAndComplete
      (Outcome := Polynomial params) (ι := ι)
      strategy.state strategy.isNormalized strategy.permInvState
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement) a_B scalars.zeta1
      rightSelfConsistency rightBridge
  have hQ_A_canon : Q_A = Preliminaries.completeAtOutcomeProj P_A a_A := by
    have hQ_A_meas : Q_A.toMeasurement =
        (Preliminaries.completeAtOutcomeProj P_A a_A).toMeasurement := by
      simpa using hQ_A
    apply ProjMeas.ext
    intro g
    have h := congrArg
      (fun Q : Measurement (Polynomial params) ι => Q.outcome g) hQ_A_meas
    simpa using h
  have hQ_B_canon : Q_B = Preliminaries.completeAtOutcomeProj P_B a_B := by
    have hQ_B_meas : Q_B.toMeasurement =
        (Preliminaries.completeAtOutcomeProj P_B a_B).toMeasurement := by
      simpa using hQ_B
    apply ProjMeas.ext
    intro g
    have h := congrArg
      (fun Q : Measurement (Polynomial params) ι => Q.outcome g) hQ_B_meas
    simpa using h
  have leftStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
        P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1 := by
    simpa [hQ_A_canon] using leftStmtRaw
  have rightStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
        P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1 := by
    simpa [hQ_B_canon] using rightStmtRaw
  exact ⟨ofCompleteAtOutcomeStatements hsmall P_A P_B a_A a_B
    leftStmt rightStmt (hleftMass P_A leftStmt) (hrightMass P_B rightStmt)⟩

/-- Transport the Bob-side completion estimate from the left-register form to the
right-register form and recover the previous post-role residual.

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

/-- Combined live residual after isolating concrete role-package production.

The first field is the actual Section 6 role residual: it carries the concrete
role-register measurement and its symmetrized consistency proof.  The second
field contains only the projectivization/completion and line-169 data for the role
package obtained from that concrete residual.  Thus the live `mainFormal` hole no
longer asks for an arbitrary `MainFormalRoleMeasurementPackage`, an arbitrary raw
Section 6 witness, or a decorative branch witness not tied to the concrete
measurement. The branch-level base, ordinary successor, and answer-valued
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

/-- Convert the split role-residual/post-role package back to the role-packaged
completion-transport residual consumed by the existing downstream wrappers.

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

/-- Combined live residual after isolating concrete role-package production
and the #869 Bob-side completion transport.

Compared with `MainFormalCascadeRolePackageResidualCompletionTransportResidual`, this
package no longer asks the live hole to provide the right-register completion
closeness directly.  Instead the post-role field records the left-register
Bob-side completion estimate returned by the orthonormalize-and-complete chain,
and the conversion below transports it to the right register using permutation
invariance of the strategy state.  The concrete role residual and the
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

open MainFormalPostRolePackageLeftCompletionTransportResidual in
/-- Combine a concrete Section 6 role residual with orthonormalize-and-complete
inputs for the two unsymmetrized role blocks.

Like the post-role producer it calls, this is a `Nonempty` theorem rather than a
data-valued constructor: the two completed projective measurements are obtained
from the existential `orthonormalizeAndComplete` theorem without hiding that
choice behind a definition. -/
theorem nonempty_ofRoleResidualAndOrthonormalizeAndCompleteInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (a_A a_B : Polynomial params)
    (leftSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
        scalars.zeta1)
    (rightSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
        scalars.zeta1)
    (leftBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state
        (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
        scalars.zeta1)
    (rightBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state
        (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
        scalars.zeta1)
    (hleftMass :
      ∀ P_A : ProjSubMeas (Polynomial params) ι,
        MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement)
          P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1 →
        qBipartiteMatchMass strategy.state P_A.toSubMeas
            (unsymmetrizedRightPOVM
              (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
          qBipartiteMatchMass strategy.state
            (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
            (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
    (hrightMass :
      ∀ P_B : ProjSubMeas (Polynomial params) ι,
        MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement)
          P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1 →
        qBipartiteMatchMass strategy.state P_B.toSubMeas
            (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
          qBipartiteMatchMass strategy.state
            (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
            (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas) :
    Nonempty (MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual
      params strategy eps hpass k scalars) := by
  rcases
    nonempty_ofOrthonormalizeAndCompleteInputs
        (rolePackage := roleResidual.rolePackage scalars)
        hsmall a_A a_B leftSelfConsistency rightSelfConsistency leftBridge rightBridge
        hleftMass hrightMass with ⟨postRoleResidual⟩
  exact ⟨{ roleResidual := roleResidual, postRoleResidual := postRoleResidual }⟩

/-- Convert the left-completion residual to the previous role-residual completion
line-169 shape by applying the #869 right-register transport to the Bob-side
completion estimate, using the separately reconstructed paper line-130
`G^A/G^B` consistency proof. -/
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

/-- Live residual after role production and before eliminating the existential
outputs of the orthonormalize-and-complete theorem.

This is the paper Step 6 input boundary: a concrete Section 6 role residual, the
distinguished completion outcomes, strong self-consistency for the two
unsymmetrized POVMs, the explicit orthonormalization bridge data, and the
construction-level match-mass monotonicity facts for the projective
submeasurements produced by orthonormalization.  The completed projective
measurements themselves are intentionally not fields; they are obtained in the
conversion theorem below by eliminating the `orthonormalizeAndComplete`
existentials while the ambient goal is still a proposition. -/
structure MainFormalCascadeRolePackageResidualOrthonormalizeAndCompleteInputResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The explicit isolated Section 6 residual. -/
  roleResidual : MainFormalRolePackageResidual params strategy eps hpass k
  /-- Alice-side distinguished outcome that receives the completion residual. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome that receives the completion residual. -/
  a_B : Polynomial params
  /-- Strong self-consistency for the Alice-role unsymmetrized POVM. -/
  leftSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Strong self-consistency for the Bob-role unsymmetrized POVM. -/
  rightSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Alice-side orthonormalization bridge input. -/
  leftBridge :
    MakingMeasurementsProjective.OrthonormalizationInput strategy.state
      (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
      scalars.zeta1
  /-- Bob-side orthonormalization bridge input. -/
  rightBridge :
    MakingMeasurementsProjective.OrthonormalizationInput strategy.state
      (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
      scalars.zeta1
  /-- Alice-side construction-level match-mass monotonicity for the projective
  submeasurement produced by orthonormalization. -/
  leftMatchMass :
    ∀ P_A : ProjSubMeas (Polynomial params) ι,
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement)
        P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1 →
      qBipartiteMatchMass strategy.state P_A.toSubMeas
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
  /-- Bob-side construction-level match-mass monotonicity for the projective
  submeasurement produced by orthonormalization. -/
  rightMatchMass :
    ∀ P_B : ProjSubMeas (Polynomial params) ι,
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement)
        P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1 →
      qBipartiteMatchMass strategy.state P_B.toSubMeas
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas

namespace MainFormalCascadeRolePackageResidualOrthonormalizeAndCompleteInputResidual

open MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual in
/-- Run orthonormalize-and-complete on the two role-block POVMs and recover the
left-completion polynomial projective-evaluation transport residual
(`references/ldt-paper/inductive_step.tex` line 169). -/
theorem nonempty_leftCompletionTransportResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual :
      MainFormalCascadeRolePackageResidualOrthonormalizeAndCompleteInputResidual
        params strategy eps hpass k scalars)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    Nonempty (MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual
      params strategy eps hpass k scalars) :=
  nonempty_ofRoleResidualAndOrthonormalizeAndCompleteInputs
      hsmall residual.roleResidual residual.a_A residual.a_B
      residual.leftSelfConsistency residual.rightSelfConsistency
      residual.leftBridge residual.rightBridge residual.leftMatchMass residual.rightMatchMass

end MainFormalCascadeRolePackageResidualOrthonormalizeAndCompleteInputResidual

end Test

end MIPStarRE.LDT
