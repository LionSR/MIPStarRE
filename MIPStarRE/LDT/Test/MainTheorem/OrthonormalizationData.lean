import MIPStarRE.LDT.Test.MainTheorem.CompletionTransport
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Output
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation

/-!
# Orthonormalization and completion data

Post-role projectivization and orthonormalization witnesses for the
`mainFormal` assembly.  This module records the data that the
orthonormalization lemma (`lem:orthonormalization-main-lemma`) and the
completion theorem (`prop:completing-to-measurement`) require beyond the
role-register measurement and the unsymmetrization links.

The central construction witness is `MainFormalDiagonalCompletionWitness`.
It records the line-130 provenance of the projective submeasurements, the
completion estimates, and converts directly to the checked
projective-consistency transport witness.

The active route uses the checked local pre-completion repair from
`\label{rem:lean-line169-projectivization-match-mass}`.  The line-130
orthonormalization witness therefore stores only the pre-completion projective
submeasurements and line-138 closeness bounds; the repaired line-169 transport
with its explicit additional loss is introduced later in the completion
transport witness.

## References

* Paper: `references/ldt-paper/orthonormalization.tex`,
  `\Cref{lem:orthonormalization-main-lemma}` at line 282.
  Applied in `references/ldt-paper/inductive_step.tex` (lines 135–143).
* Blueprint: `blueprint/src/chapter/ch04_projective.tex`,
  `\label{rem:lean-line169-projectivization-match-mass}`; and
  `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-step6-constructions}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT.MakingMeasurementsProjective

namespace MIPStarRE.LDT

namespace Test

/-- The pre-completion projective submeasurements obtained from line 130 by
the cross-consistency orthonormalization construction.

Paper origin: `references/ldt-paper/inductive_step.tex:130-149`, with
orthonormalization supplied by `references/ldt-paper/orthonormalization.tex:282`.

This stops before `completeAtOutcome`: the honest paper-shaped boundary records
only the part now derivable from the `G^A/G^B` `ConsRel`; completion closeness is
handled by the downstream completion construction. -/
structure MainFormalDiagonalOrthonormalizationWitness
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (roleWitness : MainFormalRoleMeasurementWitness params strategy eps k scalars) where
  /-- Alice-side projective submeasurement obtained from line-130 consistency. -/
  P_A : ProjSubMeas (Polynomial params) ι
  /-- Bob-side projective submeasurement obtained from line-130 consistency. -/
  P_B : ProjSubMeas (Polynomial params) ι
  /-- Alice-side line-138 orthonormalization closeness. -/
  leftCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily P_A.toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)
  /-- Bob-side line-138 orthonormalization closeness, before right-register transport. -/
  rightCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily P_B.toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)

namespace MainFormalDiagonalOrthonormalizationWitness

/-- Apply the source-faithful cross-consistency orthonormalization construction to
the line-130 `G^A/G^B` consistency proof, producing the two pre-completion
projective submeasurements in the non-vacuous scalar regime.

The proof uses the Section 5 locality-preserving repair construction directly, so
there is no additional orthonormalization-input hypothesis.  The line-169
transport is handled later by the checked repaired route in
`ProjectivizationLine169Repair`, so this witness stores only the pre-completion
projective submeasurements and their line-138 closeness bounds. -/
theorem nonempty_ofDiagonalConsistency
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {roleWitness : MainFormalRoleMeasurementWitness params strategy eps k scalars}
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    Nonempty (MainFormalDiagonalOrthonormalizationWitness
      params strategy eps k scalars roleWitness) := by
  have hζ0 : 0 ≤ scalars.zeta1 := MainFormalCascadeScalars.zeta1_nonneg scalars
  obtain ⟨P_A, hP_A⟩ :=
    orthonormalizationMeasurement_of_consistency_from_projectivizationRepair
      (ψ := strategy.state) (hψ := strategy.isNormalized)
      (A := unsymmetrizedLeftPOVM roleWitness.roleMeasurement)
      (B := unsymmetrizedRightPOVM roleWitness.roleMeasurement)
      (ζ := scalars.zeta1) hζ0 hpre
  have hpre_symm : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
      scalars.zeta1 :=
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
      scalars.zeta1 hpre
  obtain ⟨P_B, hP_B⟩ :=
    orthonormalizationMeasurement_of_consistency_from_projectivizationRepair
      (ψ := strategy.state) (hψ := strategy.isNormalized)
      (A := unsymmetrizedRightPOVM roleWitness.roleMeasurement)
      (B := unsymmetrizedLeftPOVM roleWitness.roleMeasurement)
      (ζ := scalars.zeta1) hζ0 hpre_symm
  exact ⟨{
    P_A := P_A
    P_B := P_B
    leftCloseness := hP_A
    rightCloseness := hP_B }⟩

end MainFormalDiagonalOrthonormalizationWitness

/-- Post-orthonormalization Step 6 witness that keeps the line-130 provenance
for `P^A,P^B` and exposes only the completion estimates still needed after the
cross-consistency orthonormalization construction.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`, with
completion supplied by `references/ldt-paper/preliminaries.tex:1095-1140`. -/
structure MainFormalDiagonalCompletionWitness
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (roleWitness : MainFormalRoleMeasurementWitness params strategy eps k scalars) where
  /-- Projective submeasurements and line-138 closeness derived from line 130. -/
  orthWitness : MainFormalDiagonalOrthonormalizationWitness
    params strategy eps k scalars roleWitness
  /-- Alice-side distinguished outcome receiving the completion mass. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome receiving the completion mass. -/
  a_B : Polynomial params
  /-- Alice-side completion closeness for the line-130 projective submeasurement. -/
  leftCompletedCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj orthWitness.P_A a_A).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
  /-- Bob-side completion closeness for the line-130 projective submeasurement. -/
  rightCompletedCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj orthWitness.P_B a_B).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)

namespace MainFormalDiagonalCompletionWitness

/-- Convert the line-130 diagonal completion witness directly to the checked
projective completion-transport witness.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`.  The
orthonormalize-and-complete statements used by the transport theorem are formed
from the diagonal orthonormalization witness and the two completion estimates;
no additional projective-completion record is introduced. -/
noncomputable def toProjectiveCompletionTransportWitness
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {roleWitness : MainFormalRoleMeasurementWitness params strategy eps k scalars}
    (witness : MainFormalDiagonalCompletionWitness
      params strategy eps k scalars roleWitness)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    MainFormalProjectiveCompletionTransportWitness params strategy eps k scalars :=
  mainFormalProjectiveCompletionTransportWitnessOfCompleteAtOutcomeStatements
    hsmall hpre witness.orthWitness.P_A witness.orthWitness.P_B witness.a_A witness.a_B
    { orthonormalizationCloseness := witness.orthWitness.leftCloseness
      completedCloseness := witness.leftCompletedCloseness }
    { orthonormalizationCloseness := witness.orthWitness.rightCloseness
      completedCloseness := witness.rightCompletedCloseness }

end MainFormalDiagonalCompletionWitness

end Test

end MIPStarRE.LDT
