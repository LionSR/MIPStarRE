import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Output
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Line169Repair

/-!
# Completion transport construction

Post-role completion transport for the culminating step of the `mainFormal`
proof.  After the Section 6 role-register measurement is obtained and the two
unsymmetrization links are established, the remaining step is to close the
projective completion gap: the orthonormalize-and-complete procedure
(`lem:orthonormalization-main-lemma`, `prop:completing-to-measurement`) produces
projective measurements at distance `ζ₂` from the unsymmetrized ones.  This
module records the direct construction that turns those completion estimates and
the checked repaired line-169 transport into the projective completion witness
consumed by the culminating `mainFormal` step.

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
  `\label{def:main-formal-step6-constructions}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

open MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationLine169Repair

/-- Construct the projective completion-transport witness from two
orthonormalize-and-complete statements whose completed measurements are the
canonical completions of the produced projective submeasurements.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`, with the
right-register transport formalized separately from the paper's line-147
completion estimate.

The Alice completion estimate already matches `inductive_step.tex` line 146. For
Bob, the analytic completion theorem naturally returns the left-lifted estimate
for `G^B` and `Q^B`; the proof below uses
`MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv` to recover
the line-147 right-register estimate.  The line-169 polynomial links are then
supplied by the checked local pre-completion repair from
`ProjectivizationLine169Repair`, introducing the explicit repaired loss
`ζ₁ + 10·ζ₁^(1/8)`. -/
noncomputable def mainFormalProjectiveCompletionTransportWitnessOfCompleteAtOutcomeStatements
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {roleWitness : MainFormalRoleMeasurementWitness params strategy eps k scalars}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
      scalars.zeta1)
    (P_A P_B : ProjSubMeas (Polynomial params) ι)
    (a_A a_B : Polynomial params)
    (leftStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedLeftPOVM roleWitness.roleMeasurement)
        P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1)
    (rightStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedRightPOVM roleWitness.roleMeasurement)
        P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1) :
    MainFormalProjectiveCompletionTransportWitness params strategy eps k scalars :=
  let leftMeasurement := Preliminaries.completeAtOutcomeProj P_A a_A
  let rightMeasurement := Preliminaries.completeAtOutcomeProj P_B a_B
  let consistency := roleWitness.toUnsymmetrizationConsistency
  { roleMeasurement := roleWitness.roleMeasurement
    pointARightPOVMConsistency := consistency.pointAConsistency
    leftPOVMPointBConsistency := consistency.pointBConsistency
    leftMeasurement := leftMeasurement
    rightMeasurement := rightMeasurement
    leftCompletionCloseness := by
      exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono strategy.state
        (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily leftMeasurement.toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
        scalars.zeta2
        (MainFormalCascadeScalars.orthonormalizeAndCompleteError_zeta1_le_zeta2
          scalars hsmall)
        leftStmt.completedCloseness
    rightCompletionCloseness := by
      have hrightLeft : SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily
            (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas.liftLeft)
          (constSubMeasFamily rightMeasurement.toSubMeas.liftLeft)
          scalars.zeta2 := by
        exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono strategy.state
          (uniformDistribution Unit)
          (constSubMeasFamily
            (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas.liftLeft)
          (constSubMeasFamily rightMeasurement.toSubMeas.liftLeft)
          (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
          scalars.zeta2
          (MainFormalCascadeScalars.orthonormalizeAndCompleteError_zeta1_le_zeta2
            scalars hsmall)
          rightStmt.completedCloseness
      have hleft : SDDRel strategy.state (uniformDistribution Unit)
          (IdxSubMeas.liftLeft
            (constSubMeasFamily
              (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas))
          (IdxSubMeas.liftLeft
            (constSubMeasFamily rightMeasurement.toSubMeas))
          scalars.zeta2 := by
        simpa [IdxSubMeas.liftLeft, constSubMeasFamily] using hrightLeft
      have hright :=
        MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv
          strategy.permInvState (uniformDistribution Unit)
          (constSubMeasFamily
            (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
          (constSubMeasFamily rightMeasurement.toSubMeas)
          scalars.zeta2 hleft
      simpa [IdxSubMeas.liftRight, constSubMeasFamily] using hright
    leftProjectiveRightPOVMPolynomialConsistency :=
      leftConsistency_with_orthonormalization_loss
        strategy.state strategy.isNormalized P_A a_A hpre
        leftStmt.orthonormalizationCloseness
    rightProjectiveLeftPOVMPolynomialConsistency := by
      have hpre_symm : ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily
            (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
          (constSubMeasFamily
            (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
          scalars.zeta1 :=
        consRel_symm_of_density_fixed strategy.state strategy.densityFixed
          (uniformDistribution Unit)
          (constSubMeasFamily
            (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
          (constSubMeasFamily
            (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
          scalars.zeta1 hpre
      exact
        rightConsistency_with_orthonormalization_loss
          strategy.state strategy.isNormalized P_B a_B hpre_symm
          rightStmt.orthonormalizationCloseness }

end Test

end MIPStarRE.LDT
