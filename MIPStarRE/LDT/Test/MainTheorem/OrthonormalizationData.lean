import MIPStarRE.LDT.Test.MainTheorem.CompletionTransport
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Line169Repair
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Output
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation

/-!
# Orthonormalization and completion data

Post-role projectivization and orthonormalization hypotheses for the
`mainFormal` assembly.  This module records the data that the
orthonormalization lemma (`lem:orthonormalization-main-lemma`) and the
completion theorem (`prop:completing-to-measurement`) require beyond the
role-register measurement and the unsymmetrization links.

The central residual is `MainFormalPostRolePackageDiagonalCompletionResidual`.
It records the line-130 provenance of the projective submeasurements, the
completion estimates, and the construction-level match-mass obligations, and it
converts directly to the checked projective-consistency transport residual.

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
  `\label{def:main-formal-step6-obligations}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT.MakingMeasurementsProjective

namespace MIPStarRE.LDT

namespace Test

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

/-- Apply the source-faithful cross-consistency orthonormalization wrapper to
the line-130 `G^A/G^B` consistency proof, producing the two pre-completion
projective submeasurements in the non-vacuous scalar regime.

The proof uses the Section 5 locality-preserving repair construction directly, so
there is no additional orthonormalization-input hypothesis. -/
theorem nonempty_ofDiagonalConsistency
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    Nonempty (MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage) := by
  have hζ0 : 0 ≤ scalars.zeta1 := MainFormalCascadeScalars.zeta1_nonneg scalars
  obtain ⟨P_A, hP_A⟩ :=
    orthonormalizationMeasurement_of_consistency_from_projectivizationRepair
      (ψ := strategy.state) (hψ := strategy.isNormalized)
      (A := unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (B := unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      (ζ := scalars.zeta1) hζ0 hpre
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
    orthonormalizationMeasurement_of_consistency_from_projectivizationRepair
      (ψ := strategy.state) (hψ := strategy.isNormalized)
      (A := unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      (B := unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (ζ := scalars.zeta1) hζ0 hpre_symm
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

namespace MainFormalPostRolePackageDiagonalCompletionResidual

/-- Convert the line-130 diagonal completion residual directly to the checked
left-completion line-169 residual.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`.  The
orthonormalize-and-complete statements used by the transport theorem are formed
from the diagonal orthonormalization residual and the two completion estimates;
no separate projective-completion wrapper is introduced. -/
noncomputable def toPostRolePackageLeftCompletionTransportResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (residual : MainFormalPostRolePackageDiagonalCompletionResidual
      params strategy eps k scalars rolePackage)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MainFormalPostRolePackageLeftCompletionTransportResidual
      params strategy eps k scalars rolePackage :=
  MainFormalPostRolePackageLeftCompletionTransportResidual.ofCompleteAtOutcomeStatements
    hsmall residual.orthResidual.P_A residual.orthResidual.P_B residual.a_A residual.a_B
    { orthonormalizationCloseness := residual.orthResidual.leftCloseness
      completedCloseness := residual.leftCompletedCloseness }
    { orthonormalizationCloseness := residual.orthResidual.rightCloseness
      completedCloseness := residual.rightCompletedCloseness }
    residual.leftMatchMass residual.rightMatchMass

end MainFormalPostRolePackageDiagonalCompletionResidual

end Test

end MIPStarRE.LDT
