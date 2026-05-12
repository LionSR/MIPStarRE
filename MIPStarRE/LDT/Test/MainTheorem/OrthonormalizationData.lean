import MIPStarRE.LDT.Test.MainTheorem.CompletionTransport
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation
import MIPStarRE.LDT.SelfImprovement.Theorems.OrthonormalizationBridge

/-!
# Orthonormalization and completion data

Post-role projectivization and orthonormalization hypotheses for the
`mainFormal` assembly.  This module packages the data that the
orthonormalization lemma (`lem:orthonormalization-main-lemma`) and the
completion theorem (`prop:completing-to-measurement`) require beyond the
role-register measurement and the unsymmetrization links.  The central
structures are:

* `MainFormalPostRolePackageProjectiveCompletionResidual` — post-role Step 6
  witness data with concrete projectivization witnesses (spectral-truncation
  and locality-preserving repair).

* `MainFormalPostRolePackageDiagonalOrthonormalizationInput` — the diagonal
  self-consistency and match-mass inputs that feed orthonormalization.

* `MainFormalPostRolePackageDiagonalCompletionResidual` — the final residual
  that records both the diagonal orthonormalization input and the completion
  data, ready for consumption by the projective-consistency transport.

The module also proves tight `ζ₁` polynomial-consistency lemmas
(`leftPolynomialConsistency_with_orthonormalization_loss`,
`rightPolynomialConsistency_with_orthonormalization_loss`) that avoid
degradation of the final error exponent by using the match-mass monotonicity
invariant from `\label{rem:lean-line169-projectivization-match-mass}`.

## References

* Paper: `references/ldt-paper/orthonormalization.tex`,
  `\Cref{lem:orthonormalization-main-lemma}` at line 282.
  Applied in `references/ldt-paper/inductive_step.tex` (lines 135–143).
* Blueprint: `blueprint/src/chapter/ch04_projective.tex`,
  `\label{rem:lean-line169-projectivization-match-mass}`; and
  `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-step6-hypotheses}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT.MakingMeasurementsProjective

namespace MIPStarRE.LDT

namespace Test

/-- Post-role Step 6 witness data with the actual projectivization witnesses fixed.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`, using
`references/ldt-paper/orthonormalization.tex:282`
(`\label{lem:orthonormalization-main-lemma}`) and completion.

This package corresponds to `inductive_step.tex` lines 135--149 after the
role-register Section 6 output has already been produced and unsymmetrized.  It
stores the concrete projective submeasurements `P^A,P^B`, the distinguished
completion outcomes, and the two orthonormalize-and-complete statements giving
the completed measurements `Q^A,Q^B`.

The match-mass fields are the construction-level line-169 supplement: they are
tied to these chosen witnesses, rather than universally quantified over every
possible orthonormalize-and-complete output. -/
structure MainFormalPostRolePackageProjectiveCompletionResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- Alice-side projective submeasurement from paper line 138. -/
  P_A : ProjSubMeas (Polynomial params) ι
  /-- Bob-side projective submeasurement from paper line 138. -/
  P_B : ProjSubMeas (Polynomial params) ι
  /-- Alice-side distinguished outcome receiving the completion residual. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome receiving the completion residual. -/
  a_B : Polynomial params
  /-- Alice-side orthonormalize-and-complete statement, paper lines 140 and 146. -/
  leftStatement :
    MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1
  /-- Bob-side orthonormalize-and-complete statement, paper lines 141 and 147. -/
  rightStatement :
    MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1
  /-- Alice-side construction-level match-mass monotonicity for the chosen
  orthonormalization witness. -/
  leftMatchMass :
    qBipartiteMatchMass strategy.state P_A.toSubMeas
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas ≥
      qBipartiteMatchMass strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
  /-- Bob-side construction-level match-mass monotonicity for the chosen
  orthonormalization witness. -/
  rightMatchMass :
    qBipartiteMatchMass strategy.state P_B.toSubMeas
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas ≥
      qBipartiteMatchMass strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas

namespace MainFormalPostRolePackageProjectiveCompletionResidual

/-- Consume the post-role Step 6 witness residual and recover the checked
left-completion line-169 residual.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`. -/
noncomputable def toPostRolePackageLeftCompletionTransportResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (residual : MainFormalPostRolePackageProjectiveCompletionResidual
      params strategy eps k scalars rolePackage)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MainFormalPostRolePackageLeftCompletionTransportResidual
      params strategy eps k scalars rolePackage :=
  MainFormalPostRolePackageLeftCompletionTransportResidual.ofCompleteAtOutcomeStatements
    hsmall residual.P_A residual.P_B residual.a_A residual.a_B
    residual.leftStatement residual.rightStatement residual.leftMatchMass residual.rightMatchMass

end MainFormalPostRolePackageProjectiveCompletionResidual

/-- Paper origin: `references/ldt-paper/inductive_step.tex:130-142`
(`\label{eq:G-self-consistency}`) and
`references/ldt-paper/orthonormalization.tex:67-76`
(`\label{thm:orthonormalization}`).

Explicit bridge inputs for applying the paper's cross-consistency
orthonormalization lemma to the two unsymmetrized role measurements.

The fields expose the remaining spectral-truncation and locality-preserving
repair witnesses.  The constructor below consumes line 130's `ConsRel`
`G^A ⊗ I ≃ I ⊗ G^B` and applies it in the forward and symmetry-reversed
directions, instead of asking for independent `BipartiteSSCRel` inputs. -/
structure MainFormalPostRolePackageDiagonalOrthonormalizationInput
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- Spectral-truncation input for `G^A`. -/
  leftSpectral :
    MakingMeasurementsProjective.SpectralTruncationInput strategy.state
      (leftLiftedMeasurement (ιB := ι)
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement))
      (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)
  /-- Locality-preserving repair input for `G^A`. -/
  leftRepair :
    MakingMeasurementsProjective.LeftLiftedProjectivizationRepairInput strategy.state
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)
  /-- Spectral-truncation input for `G^B`. -/
  rightSpectral :
    MakingMeasurementsProjective.SpectralTruncationInput strategy.state
      (leftLiftedMeasurement (ιB := ι)
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement))
      (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)
  /-- Locality-preserving repair input for `G^B`. -/
  rightRepair :
    MakingMeasurementsProjective.LeftLiftedProjectivizationRepairInput strategy.state
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)

namespace MainFormalPostRolePackageDiagonalOrthonormalizationInput

/-- Build the line-130 orthonormalization input once the two locality-preserving
repair inputs are available.

This constructor supplies the spectral-truncation fields from the constructive
producer `spectralTruncationInput_of_sourceAlmostProjective`, applied to the two
unsymmetrized role measurements after left tensor placement.  Callers that use
this constructor therefore supply only the Alice- and Bob-side repair steps,
which preserve the local form of the repaired projective submeasurements.  The
existing bridge structures still accept a full orthonormalization input; routing
those bridges through this constructor is a separate assembly step. -/
noncomputable def ofRepairInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (leftRepair :
      MakingMeasurementsProjective.LeftLiftedProjectivizationRepairInput strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
        (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1))
    (rightRepair :
      MakingMeasurementsProjective.LeftLiftedProjectivizationRepairInput strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
        (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)) :
    MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars rolePackage where
  leftSpectral :=
    MakingMeasurementsProjective.spectralTruncationInput_of_sourceAlmostProjective
      strategy.state
      (leftLiftedMeasurement (ιB := ι)
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement))
      (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)
  leftRepair := leftRepair
  rightSpectral :=
    MakingMeasurementsProjective.spectralTruncationInput_of_sourceAlmostProjective
      strategy.state
      (leftLiftedMeasurement (ιB := ι)
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement))
      (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)
  rightRepair := rightRepair

/-- Build the line-130 orthonormalization input from QXP-layer repair witnesses.

The spectral-truncation fields are still supplied by
`spectralTruncationInput_of_sourceAlmostProjective`.  The two remaining repair
fields are obtained by choosing the canonical local projective submeasurement
attached to each QXP layer, so the repaired lifted family has the required form
`P_a ⊗ I`.  As for `ofRepairInputs`, this records a constructive producer for
the orthonormalization input; wiring the downstream main-theorem assembly to
this producer is a separate step. -/
noncomputable def ofQXPLayerRepairWitnesses
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (leftWitness :
      MakingMeasurementsProjective.SpectralTruncationStatement strategy.state
        (leftLiftedMeasurement (ιB := ι)
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement))
        (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1) →
      MIPStarRE.LDT.SelfImprovement.LeftLiftedQXPLayerRepairWitness strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
        (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1))
    (rightWitness :
      MakingMeasurementsProjective.SpectralTruncationStatement strategy.state
        (leftLiftedMeasurement (ιB := ι)
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement))
        (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1) →
      MIPStarRE.LDT.SelfImprovement.LeftLiftedQXPLayerRepairWitness strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
        (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)) :
    MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars rolePackage :=
  ofRepairInputs
    (MIPStarRE.LDT.SelfImprovement.leftLiftedProjectivizationRepairInput_of_qxpLayer
      leftWitness)
    (MIPStarRE.LDT.SelfImprovement.leftLiftedProjectivizationRepairInput_of_qxpLayer
      rightWitness)

/-- Build the line-130 orthonormalization input from lifted QXP approximations.

This is a more concrete form of `ofQXPLayerRepairWitnesses`: each side supplies
a QXP layer whose `q` family is the corresponding unsymmetrized POVM, together
with the lifted state-dependent approximation to the associated `P` family.
The constructor packages these approximations as locality-preserving repair
inputs for the Alice and Bob unsymmetrized measurements.  It supplies the same
line-130 input package as `ofRepairInputs`; the later bridge structures still
consume an already assembled orthonormalization input. -/
noncomputable def ofLiftedQXPApproximations
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (leftData :
      MakingMeasurementsProjective.QXPLayerData (Polynomial params) ι)
    (leftMatches :
      ∀ g : Polynomial params,
        leftData.qLayer.q.outcome g =
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).outcome g)
    (leftClose :
      SDDOpRel strategy.state (uniformDistribution Unit)
        (constOpFamily
          (OpFamily.leftPlacedOpFamily (ιB := ι) leftData.qLayer.q))
        (constOpFamily
          (OpFamily.leftPlacedOpFamily (ιB := ι)
            (MakingMeasurementsProjective.PFamily leftData)))
        (MakingMeasurementsProjective.roundingToProjectiveError
          (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)))
    (rightData :
      MakingMeasurementsProjective.QXPLayerData (Polynomial params) ι)
    (rightMatches :
      ∀ g : Polynomial params,
        rightData.qLayer.q.outcome g =
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).outcome g)
    (rightClose :
      SDDOpRel strategy.state (uniformDistribution Unit)
        (constOpFamily
          (OpFamily.leftPlacedOpFamily (ιB := ι) rightData.qLayer.q))
        (constOpFamily
          (OpFamily.leftPlacedOpFamily (ιB := ι)
            (MakingMeasurementsProjective.PFamily rightData)))
        (MakingMeasurementsProjective.roundingToProjectiveError
          (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1))) :
    MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars rolePackage :=
  ofRepairInputs
    (MIPStarRE.LDT.SelfImprovement.leftLiftedProjectivizationRepairInput_of_lifted_qxp_sddOpRel
      leftData leftMatches leftClose)
    (MIPStarRE.LDT.SelfImprovement.leftLiftedProjectivizationRepairInput_of_lifted_qxp_sddOpRel
      rightData rightMatches rightClose)

end MainFormalPostRolePackageDiagonalOrthonormalizationInput

/-- The pre-completion projective submeasurements obtained from line 130 by the
cross-consistency orthonormalization wrapper.

Paper origin: `references/ldt-paper/inductive_step.tex:130-149`, with
orthonormalization supplied by `references/ldt-paper/orthonormalization.tex:282`.

This stops before `completeAtOutcome`: the honest paper-shaped boundary records
only the part now derivable from the `G^A/G^B` `ConsRel`; completion closeness is
kept as a separate downstream obligation. -/
structure MainFormalPostRolePackageDiagonalOrthonormalizationResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- Alice-side projective submeasurement obtained from line-130 consistency. -/
  P_A : ProjSubMeas (Polynomial params) ι
  /-- Bob-side projective submeasurement obtained from line-130 consistency. -/
  P_B : ProjSubMeas (Polynomial params) ι
  /-- Alice-side line-138 orthonormalization closeness. -/
  leftCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily P_A.toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)
  /-- Bob-side line-138 orthonormalization closeness, before right-register transport. -/
  rightCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily P_B.toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)

namespace MainFormalPostRolePackageDiagonalOrthonormalizationResidual

/-- Apply the cross-consistency orthonormalization wrapper to the line-130
`G^A/G^B` consistency proof, producing the two pre-completion projective
submeasurements in the non-vacuous scalar regime. -/
theorem nonempty_ofDiagonalInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1)
    (input : MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars rolePackage) :
    Nonempty (MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage) := by
  have hζ0 : 0 ≤ scalars.zeta1 := MainFormalCascadeScalars.zeta1_nonneg scalars
  have hζ1 : scalars.zeta1 ≤ 1 :=
    MainFormalCascadeScalars.zeta1_le_one_of_not_mainFormalError_ge_one scalars hsmall
  obtain ⟨P_A, hP_A⟩ :=
    MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency
      (ψ := strategy.state) (hψ := strategy.isNormalized)
      (A := unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (B := unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      (ζ := scalars.zeta1) hζ0 hζ1 input.leftSpectral input.leftRepair hpre
  have hpre_symm : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1 :=
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1 hpre
  obtain ⟨P_B, hP_B⟩ :=
    MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency
      (ψ := strategy.state) (hψ := strategy.isNormalized)
      (A := unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      (B := unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (ζ := scalars.zeta1) hζ0 hζ1 input.rightSpectral input.rightRepair hpre_symm
  exact ⟨{
    P_A := P_A
    P_B := P_B
    leftCloseness := hP_A
    rightCloseness := hP_B }⟩

end MainFormalPostRolePackageDiagonalOrthonormalizationResidual

namespace MainFormalPostRolePackageDiagonalOrthonormalizationResidual

/-- Repaired Alice-side polynomial line-169 transport from the line-130
orthonormalization residual.

This uses the checked pre-completion replacement theorem from
`ProjectivizationLine169Repair`: the orthonormalized submeasurement is compared
to the source POVM before completion, so the additive loss is only
`10 * ζ₁^(1/8)`. -/
theorem leftPolynomialConsistency_with_orthonormalization_loss
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage)
    (a_A : Polynomial params)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (Preliminaries.completeAtOutcomeProj orthResidual.P_A a_A).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      (scalars.zeta1 + 10 * Real.rpow scalars.zeta1 (1 / (8 : Error))) := by
  have hraw :=
    ProjectivizationLine169Repair.leftConsistency_with_orthonormalization_loss
      strategy.state strategy.isNormalized orthResidual.P_A a_A hpre orthResidual.leftCloseness
  simpa using hraw

/-- Repaired Bob-side polynomial line-169 transport from the line-130
orthonormalization residual. -/
theorem rightPolynomialConsistency_with_orthonormalization_loss
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage)
    (a_B : Polynomial params)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (Preliminaries.completeAtOutcomeProj orthResidual.P_B a_B).toSubMeas)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (scalars.zeta1 + 10 * Real.rpow scalars.zeta1 (1 / (8 : Error))) := by
  have hraw :=
    ProjectivizationLine169Repair.rightConsistency_with_orthonormalization_loss
      strategy.state strategy.isNormalized orthResidual.P_B a_B hpre orthResidual.rightCloseness
  simpa using hraw

end MainFormalPostRolePackageDiagonalOrthonormalizationResidual

/-- Post-orthonormalization Step 6 residual that keeps the line-130 provenance
for `P^A,P^B` and exposes only the completion and match-mass obligations still
not produced by the cross-consistency wrapper.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`, with
completion supplied by `references/ldt-paper/preliminaries.tex:1095-1140`. -/
structure MainFormalPostRolePackageDiagonalCompletionResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- Projective submeasurements and line-138 closeness derived from line 130. -/
  orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
    params strategy eps k scalars rolePackage
  /-- Alice-side distinguished outcome receiving the completion residual. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome receiving the completion residual. -/
  a_B : Polynomial params
  /-- Alice-side completion closeness for the line-130 projective submeasurement. -/
  leftCompletedCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj orthResidual.P_A a_A).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
  /-- Bob-side completion closeness for the line-130 projective submeasurement. -/
  rightCompletedCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj orthResidual.P_B a_B).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
  /-- Alice-side construction-level match-mass monotonicity for the chosen line-130 witness. -/
  leftMatchMass :
    qBipartiteMatchMass strategy.state orthResidual.P_A.toSubMeas
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas ≥
      qBipartiteMatchMass strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
  /-- Bob-side construction-level match-mass monotonicity for the chosen line-130 witness. -/
  rightMatchMass :
    qBipartiteMatchMass strategy.state orthResidual.P_B.toSubMeas
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas ≥
      qBipartiteMatchMass strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas

namespace MainFormalPostRolePackageProjectiveCompletionResidual

/-- Build the fixed Step 6 witness package from a line-130 orthonormalization
residual plus the still-external completion estimates.

This constructor is the honest bridge from the new cross-consistency
orthonormalization wrapper to the existing orthonormalize-and-complete residual:
the projective submeasurements and their line-138 closeness now come from
`ConsRel G^A G^B ζ₁`; only the completion-to-measurement closeness and
match-mass monotonicity remain supplied separately. -/
noncomputable def ofDiagonalOrthonormalizationAndCompletion
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage)
    (a_A a_B : Polynomial params)
    (leftCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthResidual.P_A a_A).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1))
    (rightCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthResidual.P_B a_B).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1))
    (leftMatchMass :
      qBipartiteMatchMass strategy.state orthResidual.P_A.toSubMeas
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
    (rightMatchMass :
      qBipartiteMatchMass strategy.state orthResidual.P_B.toSubMeas
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas) :
    MainFormalPostRolePackageProjectiveCompletionResidual
      params strategy eps k scalars rolePackage where
  P_A := orthResidual.P_A
  P_B := orthResidual.P_B
  a_A := a_A
  a_B := a_B
  leftStatement :=
    { orthonormalizationCloseness := orthResidual.leftCloseness
      completedCloseness := leftCompletedCloseness }
  rightStatement :=
    { orthonormalizationCloseness := orthResidual.rightCloseness
      completedCloseness := rightCompletedCloseness }
  leftMatchMass := leftMatchMass
  rightMatchMass := rightMatchMass

end MainFormalPostRolePackageProjectiveCompletionResidual

end Test

end MIPStarRE.LDT
