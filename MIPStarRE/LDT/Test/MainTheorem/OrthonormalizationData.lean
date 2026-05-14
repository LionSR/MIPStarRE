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
projective-consistency transport witness.  The exact line-169 match-mass proof
is retained one step earlier, together with the orthonormalization witness
whose QXP producer supplies it.

The active route uses the match-mass monotonicity invariant from
`\label{rem:lean-line169-projectivization-match-mass}` to obtain the exact
paper line-169 estimates, rather than a repaired line-169 helper with an
additional loss term.

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

/-- The pre-completion projective submeasurements obtained from line 130 by
the cross-consistency orthonormalization construction.

Paper origin: `references/ldt-paper/inductive_step.tex:130-149`, with
orthonormalization supplied by `references/ldt-paper/orthonormalization.tex:282`.

This stops before `completeAtOutcome`: the honest paper-shaped boundary records
only the part now derivable from the `G^A/G^B` `ConsRel`; completion closeness is
kept as a separate downstream obligation. -/
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
  /-- Alice-side line-169 match-mass preservation retained from the QXP repair producer. -/
  leftMatchMass :
    MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
      (unsymmetrizedLeftPOVM roleWitness.roleMeasurement) P_A
      (unsymmetrizedRightPOVM roleWitness.roleMeasurement)
  /-- Bob-side line-169 match-mass preservation retained from the role-reversed QXP producer. -/
  rightMatchMass :
    MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
      (unsymmetrizedRightPOVM roleWitness.roleMeasurement) P_B
      (unsymmetrizedLeftPOVM roleWitness.roleMeasurement)

namespace MainFormalDiagonalOrthonormalizationWitness

/-- Apply the source-faithful cross-consistency orthonormalization construction to
the line-130 `G^A/G^B` consistency proof, producing the two pre-completion
projective submeasurements in the non-vacuous scalar regime.

The proof uses the Section 5 locality-preserving repair construction directly, so
there is no additional orthonormalization-input hypothesis.

**Unfaithful:** This construction currently relies transitively on
`leftLiftedProjectivizationRepairWithMatchMass`, whose QXP
outcome-expectation preservation calculation is not yet derived from
`references/ldt-paper/orthonormalization.tex:862-1194` and
`references/ldt-paper/inductive_step.tex:135-169`.  Documented by issue #1610.
Elimination: prove `leftLiftedProjectivizationRepairWithMatchMass` and keep the
resulting match-mass evidence in this witness without adding any theorem-level
hypothesis. -/
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
  obtain ⟨P_A, hP_A, hMatch_A⟩ :=
    orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_with_matchMass
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
  obtain ⟨P_B, hP_B, hMatch_B⟩ :=
    orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_with_matchMass
      (ψ := strategy.state) (hψ := strategy.isNormalized)
      (A := unsymmetrizedRightPOVM roleWitness.roleMeasurement)
      (B := unsymmetrizedLeftPOVM roleWitness.roleMeasurement)
      (ζ := scalars.zeta1) hζ0 hpre_symm
  exact ⟨{
    P_A := P_A
    P_B := P_B
    leftCloseness := hP_A
    rightCloseness := hP_B
    leftMatchMass := hMatch_A
    rightMatchMass := hMatch_B }⟩

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
    witness.orthWitness.leftMatchMass.matchMassPreservation
    witness.orthWitness.rightMatchMass.matchMassPreservation

end MainFormalDiagonalCompletionWitness

end Test

end MIPStarRE.LDT
