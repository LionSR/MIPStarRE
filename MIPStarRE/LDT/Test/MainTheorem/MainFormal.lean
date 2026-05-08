import MIPStarRE.LDT.Test.MainTheorem.NativeTargets

/-!
# Main-formal final assembly

Base case, successor branch, and final assembly for `thm:main-formal`
(`\Cref{thm:main-formal}`).  This module contains:

* `MainFormalBaseProjectiveCompletionHypotheses` — the still-unformalized
  analytic hypotheses needed for the base case `m = 1` (locality-preserving
  repair witnesses for orthonormalization, distinguished completion outcomes,
  and match-mass preservation for the orthonormalized projective
  submeasurements).

* `MainFormalBaseBridgeHypotheses` and
  `MainFormalBaseRepairedBridgeHypotheses` — intermediate residuals that
  carry these base-case hypotheses together with the role-register measurement.

* `mainFormal_ofRoleResidualAndRepairedBridge` — the main successor-branch
  assembly that combines a role-residual, the projective-consistency handoff
  data, and the orthonormalization/completion inputs into the three final
  consistency bounds `Gᴬ ≃ I ⊗ Gᴮ`, `Aᴬ ⊗ I ≃ I ⊗ Qᴮ`, `Qᴬ ⊗ I ≃ I ⊗ Aᴮ`.

* `mainFormal` — the top-level theorem, taking a projective strategy that
  passes the LID test with probability `≥ 1 − ε` and producing the three
  pointwise consistency targets at error bound `mainFormalError`.

## References

* Paper: `references/ldt-paper/test_definition.tex`,
  `\Cref{thm:main-formal}` at line 180; its proof is in
  `references/ldt-paper/inductive_step.tex` (lines 26–236).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `\label{thm:main-formal}`; and
  `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-step6-hypotheses}`,
  `\label{lem:main-formal-successor-handoff}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-! ### Base (m = 1) Step 6 analytic hypotheses

The base case (`m = 1`) generation of the Step 6 witness residual still
requires the same analytic content as the successor case: spectral
truncation and locality-preserving repair witnesses for the unsymmetrized
POVMs and match-mass preservation for the orthonormalized projective
submeasurements. These are proof obligations whose formalization
corresponds to unformalized content in Section 5 and Section 6 of the
paper; they are bundled as a single structure to give a single target
for the remaining work.  When these hypotheses are supplied,
`baseProjectiveCompletionResidual` provides the checked assembly theorem that
fills the base branch of `mainFormal`. -/

/-- Analytic hypotheses that are still unformalized for the
base case (`m = 1`) Step 6 witness residual: orthonormalization
inputs (spectral truncation and repair witnesses), distinguished
outcomes, and match-mass preservation for the unsymmetrized POVMs.

Supplying these hypotheses yields a complete `baseProjectiveCompletionResidual`
for the base branch of `mainFormal`; the remaining successor-case
proof obligations are tracked separately. -/
structure MainFormalBaseProjectiveCompletionHypotheses
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (scalars : MainFormalCascadeScalars params eps k)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k) where
  /-- Line-130 orthonormalization inputs: spectral-truncation and
  locality-preserving repair witnesses for both unsymmetrized POVMs. -/
  orthonormalizationInput :
    MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars)
  /-- Alice-side distinguished outcome for the completion step. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome for the completion step. -/
  a_B : Polynomial params
  /-- Alice-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_A` preserves match mass against
  Bob's unsymmetrized POVM. -/
  leftMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_A
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
  /-- Bob-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_B` preserves match mass against
  Alice's unsymmetrized POVM. -/
  rightMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_B
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)

/-- Assemble the Step 6 witness residual from the bundled analytic hypotheses.

This theorem takes an explicit `roleResidual` (obtainable from either
`MainFormalRolePackageResidual.ofBaseCase` or the successor-branch
handoff) and the `MainFormalBaseProjectiveCompletionHypotheses` bridge, then assembles the
Step 6 witness residual through
`MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
  .nonempty_ofRoleResidualAndDiagonalInputsAndMatchMassPreservation`.

Refs #1009, #422. -/
theorem baseProjectiveCompletionResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (bridge : MainFormalBaseProjectiveCompletionHypotheses params strategy eps k
      hpass scalars roleResidual) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      params strategy eps hpass k scalars) := by
  exact (open MainFormalCascadeRolePackageResidualProjectiveCompletionResidual in
    nonempty_ofRoleResidualAndDiagonalInputsAndMatchMassPreservation
      hsmall roleResidual bridge.orthonormalizationInput bridge.a_A bridge.a_B
      bridge.leftMatchMassPreservation bridge.rightMatchMassPreservation)


/-- Narrowed base-case bridge hypotheses for Step 6 when `params.m = 1`.

Compared to `MainFormalBaseProjectiveCompletionHypotheses`, this structure omits the two
distinguished outcomes `a_A` and `a_B`, which the conversion below fills with
the explicit zero polynomial at `m = 1`.  The remaining three fields
— orthonormalization inputs and match-mass preservation — are the genuinely
analytic obligations that must be supplied
by the caller.

A conversion theorem `baseProjectiveCompletionHypotheses_ofBaseBridge` constructs the full
`MainFormalBaseProjectiveCompletionHypotheses` from a `MainFormalBaseBridgeHypotheses` by
providing the explicit zero polynomial as the distinguished outcome on both sides.

Refs #1043, #1009, #422. -/
structure MainFormalBaseBridgeHypotheses
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (scalars : MainFormalCascadeScalars params eps k)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k) where
  /-- Line-130 orthonormalization inputs: spectral-truncation and
  locality-preserving repair witnesses for both unsymmetrized POVMs. -/
  orthonormalizationInput :
    MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars)
  /-- Alice-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_A` preserves match mass against
  Bob's unsymmetrized POVM. -/
  leftMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_A
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
  /-- Bob-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_B` preserves match mass against
  Alice's unsymmetrized POVM. -/
  rightMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_B
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)

/-- Convert narrowed base bridge hypotheses to the full
`MainFormalBaseProjectiveCompletionHypotheses` by providing the explicit zero polynomial as the
distinguished outcome on both sides.

The distinguished outcomes `a_A` and `a_B` are chosen as the zero polynomial;
`completeAtOutcomeProj` works for any distinguished outcome, so this choice
is sound.  Callers that need specific distinguished outcomes should use
`MainFormalBaseProjectiveCompletionHypotheses` directly.

Refs #1043. -/
noncomputable def baseProjectiveCompletionHypotheses_ofBaseBridge
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    {roleResidual : MainFormalRolePackageResidual params strategy eps hpass k}
    (bridge : MainFormalBaseBridgeHypotheses params strategy eps k hpass
      scalars roleResidual) :
    MainFormalBaseProjectiveCompletionHypotheses params strategy eps k hpass scalars
      roleResidual where
  orthonormalizationInput := bridge.orthonormalizationInput
  a_A := { poly := 0, lowIndividualDegree := by intro i; simp [MvPolynomial.degreeOf_zero] }
  a_B := { poly := 0, lowIndividualDegree := by intro i; simp [MvPolynomial.degreeOf_zero] }
  leftMatchMassPreservation := bridge.leftMatchMassPreservation
  rightMatchMassPreservation := bridge.rightMatchMassPreservation

/-- Convenience wrapper for `baseProjectiveCompletionResidual` using the narrowed
base bridge.

The narrowed `MainFormalBaseBridgeHypotheses` omits `a_A` and `a_B`, which
are filled with the explicit zero polynomial by
`baseProjectiveCompletionHypotheses_ofBaseBridge`. The `params.m = 1` hypothesis is consumed
upstream when constructing the base-case role residual, so this wrapper only
packages the Step~6 bridge conversion.

Refs #1043. -/
theorem baseProjectiveCompletionResidual_ofBaseBridge
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (bridge : MainFormalBaseBridgeHypotheses params strategy eps k hpass
      scalars roleResidual) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      params strategy eps hpass k scalars) := by
  exact baseProjectiveCompletionResidual hsmall roleResidual
    (baseProjectiveCompletionHypotheses_ofBaseBridge bridge)


/-- Narrowed repaired base-case bridge for Step 6 when `params.m = 1`.

This removes the exact line-169 match-mass preservation fields from the base
bridge.  The repaired pre-completion route needs only the line-130
orthonormalization inputs and an additional diagonal consistency input for the
completion theorem on the two unsymmetrized role-block POVMs.  This diagonal
input is not the paper's line-130 assertion itself; line 130 supplies the
cross relation between the two unsymmetrized roles. -/
structure MainFormalBaseRepairedBridgeHypotheses
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (scalars : MainFormalCascadeScalars params eps k)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k) where
  /-- Line-130 orthonormalization inputs: spectral-truncation and locality-preserving
  repair witnesses for both unsymmetrized POVMs. -/
  orthonormalizationInput :
    MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars)
  /-- Additional diagonal consistency for the two unsymmetrized role POVMs, used
  to invoke the completion theorem without the exact match-mass route. -/
  diagonalConsistency :
    MainFormalPostRolePackageDiagonalConsistencyInput
      params strategy eps k scalars (roleResidual.rolePackage scalars)

/-- Generic repaired Step-6 bridge over an already constructed role residual. -/
abbrev MainFormalRepairedBridgeHypotheses
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (scalars : MainFormalCascadeScalars params eps k)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k) :
    Type _ :=
  MainFormalBaseRepairedBridgeHypotheses params strategy eps k hpass scalars roleResidual

/-- Base-case assembly of `mainFormal` through the repaired line-169 route.

Starting from the checked base-role residual, this theorem runs the line-130
orthonormalization wrapper, completes the resulting projective submeasurements
using the diagonal consistency input, derives the repaired polynomial line-169
transport with loss `10 * ζ₁^(1/8)`, and then proves the final point and
self-consistency goals directly at `mainFormalError`. -/
theorem baseMainFormal_ofRepairedBaseBridge
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (bridge : MainFormalBaseRepairedBridgeHypotheses params strategy eps k hpass
      scalars roleResidual) :
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
  let rolePackage := roleResidual.rolePackage scalars
  let unsym := rolePackage.toUnsymmetrizationBridge
  have hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1 := by
    simpa [rolePackage] using roleResidual.diagonalConsistency scalars
  rcases MainFormalPostRolePackageDiagonalOrthonormalizationResidual.nonempty_ofDiagonalInputs
      hsmall hpre bridge.orthonormalizationInput with ⟨orthResidual⟩
  let a0 : Polynomial params :=
    { poly := 0
      lowIndividualDegree := by intro i; simp [MvPolynomial.degreeOf_zero] }
  let diagonalSSC : MainFormalPostRolePackageDiagonalSSCInput
      params strategy eps k scalars rolePackage :=
    MainFormalPostRolePackageDiagonalSSCInput.ofDiagonalConsistency
      bridge.diagonalConsistency
  obtain ⟨C_A, hC_A, hC_Astmt⟩ :=
    Preliminaries.completingToMeasurement
      (Outcome := Polynomial params) (ι := ι) strategy.state strategy.permInvState
      strategy.isNormalized (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      orthResidual.P_A.toSubMeas a0
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)
      scalars.zeta1 diagonalSSC.leftSelfConsistency orthResidual.leftCloseness
  obtain ⟨C_B, hC_B, hC_Bstmt⟩ :=
    Preliminaries.completingToMeasurement
      (Outcome := Polynomial params) (ι := ι) strategy.state strategy.permInvState
      strategy.isNormalized (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      orthResidual.P_B.toSubMeas a0
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)
      scalars.zeta1 diagonalSSC.rightSelfConsistency orthResidual.rightCloseness
  let Q_A : ProjMeas (Polynomial params) ι :=
    Preliminaries.completeAtOutcomeProj orthResidual.P_A a0
  let Q_B : ProjMeas (Polynomial params) ι :=
    Preliminaries.completeAtOutcomeProj orthResidual.P_B a0
  have leftCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily Q_A.toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1) := by
    simpa [Q_A, MakingMeasurementsProjective.orthonormalizeAndCompleteError, hC_A] using
      hC_Astmt.closenessAfterCompletion
  have rightCompletedClosenessLeft :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily Q_B.toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1) := by
    simpa [Q_B, MakingMeasurementsProjective.orthonormalizeAndCompleteError, hC_B] using
      hC_Bstmt.closenessAfterCompletion
  have leftStmt : MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement
      strategy.state (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      orthResidual.P_A Q_A a0 scalars.zeta1 := by
    exact
      { orthonormalizationCloseness := orthResidual.leftCloseness
        completedCloseness := leftCompletedCloseness }
  have rightStmt : MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement
      strategy.state (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      orthResidual.P_B Q_B a0 scalars.zeta1 := by
    exact
      { orthonormalizationCloseness := orthResidual.rightCloseness
        completedCloseness := rightCompletedClosenessLeft }
  have hζ2 : MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1 ≤
      scalars.zeta2 :=
    MainFormalCascadeScalars.orthonormalizeAndCompleteError_zeta1_le_zeta2 scalars hsmall
  have hline156Handoff :=
    (open MakingMeasurementsProjective.ProjectivizationSelfConsistencyHandoff in
      ofOrthonormalizeAndCompleteStatements strategy.permInvState hpre leftStmt rightStmt hζ2)
  have hline156 : Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas)
      scalars.zeta3 := by
    simpa [Q_A, Q_B, MainFormalCascadeScalars.zeta3, cascadeZeta3] using
      MakingMeasurementsProjective.ProjectivizationSelfConsistencyHandoff.fullPolynomialConsistency
        hline156Handoff
  have hself : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas)
      (scalars.zeta3 / 2) := by
    let leftConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => Q_A
    let rightConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => Q_B
    have happrox : Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
        (IdxProjMeas.toIdxSubMeas leftConst)
        (IdxProjMeas.toIdxSubMeas rightConst)
        (2 * (scalars.zeta3 / 2)) := by
      change Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Q_A.toSubMeas) (constSubMeasFamily Q_B.toSubMeas)
        (2 * (scalars.zeta3 / 2))
      convert hline156 using 1
      ring
    have hcons :=
      Preliminaries.approxToSimeq strategy.state (uniformDistribution Unit)
        leftConst rightConst (scalars.zeta3 / 2) happrox
    simpa [Q_A, Q_B, leftConst, rightConst, constSubMeasFamily, IdxProjMeas.toIdxSubMeas]
      using hcons
  have hleftPoly : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      (scalars.zeta1 + 10 * Real.rpow scalars.zeta1 (1 / (8 : Error))) := by
    simpa [Q_A] using
      (open MainFormalPostRolePackageDiagonalOrthonormalizationResidual in
        leftPolynomialConsistency_with_orthonormalization_loss orthResidual a0 hpre)
  have hrightPre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1 :=
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1 hpre
  have hrightPoly : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Q_B.toSubMeas)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (scalars.zeta1 + 10 * Real.rpow scalars.zeta1 (1 / (8 : Error))) := by
    simpa [Q_B] using
      (open MainFormalPostRolePackageDiagonalOrthonormalizationResidual in
        rightPolynomialConsistency_with_orthonormalization_loss orthResidual a0 hrightPre)
  have hprojEval : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas)
      (scalars.zeta3 / 2) := by
    simpa [Q_A, Q_B] using
      projectiveEvaluationConsistency_ofFullPolynomialConsistency Q_A Q_B hline156
  have hleftEval : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      (scalars.zeta1 + 10 * Real.rpow scalars.zeta1 (1 / (8 : Error))) := by
    simpa [Q_A] using
      consRel_constPolynomialEvaluation strategy.state Q_A.toMeasurement
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement) hleftPoly
  have hrightEval : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_B.toSubMeas)
      (polynomialEvaluationFamily params
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (scalars.zeta1 + 10 * Real.rpow scalars.zeta1 (1 / (8 : Error))) := by
    simpa [Q_B] using
      consRel_constPolynomialEvaluation strategy.state Q_B.toMeasurement
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement) hrightPoly
  have hpointA : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params Q_B.toSubMeas)
      (mainFormalError params k eps) :=
    MainFormalCascadeProjectiveCompletionTransportResidual.pointAConsistency_of_repairedLine169
      rolePackage.roleMeasurement Q_A Q_B
      unsym.pointAConsistency hleftEval hprojEval
  have hpointB : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (mainFormalError params k eps) :=
    MainFormalCascadeProjectiveCompletionTransportResidual.pointBConsistency_of_repairedLine169
      rolePackage.roleMeasurement Q_A Q_B
      unsym.pointBConsistency hrightEval hprojEval
  exact ⟨Q_A, Q_B, hpointA, hpointB,
    ConsRel.mono (MainFormalCascadeScalars.zeta3_div_two_le_mainFormalError scalars) hself⟩

/-- Generic repaired Step-6 assembly once the concrete role residual is known. -/
theorem mainFormal_ofRoleResidualAndRepairedBridge
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (bridge : MainFormalRepairedBridgeHypotheses params strategy eps k hpass
      scalars roleResidual) :
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
          (mainFormalError params k eps) :=
  baseMainFormal_ofRepairedBaseBridge hsmall roleResidual bridge



/--
`thm:main-formal` from `test_definition.tex`.

The bipartite tensor placement follows the paper:
- **1a**: `A^A_u ⊗ I ≈_ν I ⊗ G^B_{[g(u)=a]}` — G_B on **right**
- **1b**: `I ⊗ A^B_u ≈_ν G^A_{[g(u)=a]} ⊗ I` — G_A on **left**, A^B on **right**
- **2**: `G^A_g ⊗ I ≈_ν I ⊗ G^B_g` — G_B on **right**

The `k`-bound boundary records the statement fix from issue #906: the paper's
successor proof applies the Section 6 / Pasting-side wrappers, whose checked
side condition is `400 * params.m * params.d ≤ k`. The public theorem therefore
exposes this stronger hypothesis instead of trying to derive it from the paper's
printed `params.m * params.d ≤ k` assumption.

After first separating off the saturated-error branch, the checked role-package
infrastructure now exposes the base producer, an ordinary branch-level successor
producer, and an answer-valued branch-level successor producer:

* the base handoff `strategySymmetrization_mainInductionBaseCase`, packaged as
  `MainFormalRolePackageBranchResidual.base`, and
* the predecessor/successor handoff
  `MainFormalRolePackageBranchResidual.successor`, which carries a bundled
  `Parameters.SuccessorDecomposition`, transported passing strategy, bundled
  `MainFormalSuccessorBoundary`, and
* the answer-valued predecessor/successor handoff
  `MainFormalRolePackageBranchResidual.answerSuccessor`, which carries the
  analogous `MainFormalSuccessorAnswerBoundary`.
The branch conversion receives the public current-dimension large-`k` hypothesis
and weakens it to the predecessor side condition `400 * pred.m * pred.d ≤ k`.

For an arbitrary current parameter bundle, the predecessor decomposition itself is
now formalized by `Parameters.successorDecompositionOfNeOne`; what remains
external is producing the successor-boundary data and the later completion /
line-169 residuals. No checked lemma here claims that the former intermediate
range `params.m * params.d ≤ k < 400 * params.m * params.d` is vacuous.

Universe note: the Lean statement uses `[FieldModel.{0} params.q]`, matching the
base-universe field-model assumption of the public Section 6 successor wrapper.
This is a current Lean API limitation, not a paper constraint; once the Section 6
wrapper is universe-polymorphic, this public theorem should be generalized as
well.

Fixes #137, #239, #906, #1099.
-/
theorem mainFormal
    (params : Parameters) [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (eps : Error)
    (hd : 0 < params.d)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k)
    (hbaseBridge : (scalars : MainFormalCascadeScalars params eps k) →
      ∀ (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k),
      MainFormalRepairedBridgeHypotheses params strategy eps k hpass scalars roleResidual) :
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
  -- TODO(#422): The induction-side handoffs needed by the final
  -- `mainFormal` assembly are standalone checked declarations:
  -- * base branch: `strategySymmetrization_mainInductionBaseCase`,
  -- * weighted successor boundary fields:
  --   `mainFormalSuccessorAxisWeightedBound_ofPass` and
  --   `mainFormalSuccessorDiagonalWeightedBound_ofPass`,
  -- * successor Section 6 wrapper call:
  --   `mainFormalSuccessorMainInductionPublicWrapper`, and
  -- * vacuous branch: `mainFormal_trivial_witness`.
  --
  -- The remaining paper-faithful target is now narrowed past the Step 5
  -- Schwartz--Zippel handoff, the line-116 triangle step, the duplicated
  -- pre-projective consistency field inside the projectivization handoff, the
  -- unused Section 6 consistency field inside the unsymmetrization package, the
  -- line-171--173 data-processing step for the `ζ₁` links, and the final `ζ₄`
  -- point-triangle assembly to the paper-shaped Step 6 witness residual
  -- `MainFormalCascadeRolePackageResidualProjectiveCompletionResidual`.  The scalar
  -- cascade side conditions are discharged below: if `mainFormalError ≥ 1`, the
  -- theorem is vacuous; otherwise the pass condition gives `0 ≤ ε`, while
  -- `mainFormalError < 1` rules out `ε > 1` and `d > q`.
  --
  -- The repaired line-169 transport is now formalized: once a concrete
  -- `roleResidual` and repaired bridge input are available,
  -- `mainFormal_ofRoleResidualAndRepairedBridge` finishes the base Step-6
  -- assembly using the sharper pre-completion loss
  -- `ζ₁ + 10 * ζ₁^(1/8)`.  The self-improvement assumptions are packaged as
  -- `SelfImprovement.SelfImprovementBridgeInputs`.  The remaining `mainFormal`
  -- hole still needs:
  --
  -- 1. **Section 6 role residual** via base/successor branch:
  --    - `MainFormalRolePackageBranchResidual` constructed from either
  --      `base` (if `params.m = 1`), `successor`, or the answer-valued
  --      `answerSuccessor`,
  --    - ordinary or answer-valued recursive induction witnesses,
  --    - ordinary or answer-valued per-slice self-improvement package producers.
  --
  -- 2. **Line-130 orthonormalization inputs**:
  --    - `MainFormalPostRolePackageDiagonalOrthonormalizationInput`:
  --      spectral-truncation and locality-preserving repair witnesses
  --      for both unsymmetrized POVMs.
  --
  -- 3. **Completion input** for the two POVMs, derived through
  --    `completingToMeasurement`.  In the repaired base route this is supplied as
  --    additional diagonal consistency for the two unsymmetrized POVMs, beyond
  --    the line-130 cross relation, and is converted to the `BipartiteSSCRel`
  --    hypotheses consumed by the completion theorem.
  --
  -- 4. **Repaired line-169 transport**.  The paper's exact `ζ₁` replacement step
  --    is false as printed; the checked local repair compares with the
  --    orthonormalized submeasurement before completion and incurs the smaller
  --    loss `ζ₁ + 10 * ζ₁^(1/8)`, which is still absorbed by
  --    `mainFormalError`.
  --
  -- The full downstream cascade from the role package through the projective
  -- targets is already checked; once the residual above is supplied, the
  -- remaining proof is trivial.  Item 4 replaces the older generic `triangleSub`
  -- route whose loss was `ζ₁ + sqrt ζ₂` rather than the printed `ζ₁`.

  by_cases herr : 1 ≤ mainFormalError params k eps
  · exact mainFormal_trivial_witness params strategy eps k herr
  · have hepsNN : 0 ≤ eps := SameSpaceProjStrat.eps_nonneg_of_passes hpass
    let scalars : MainFormalCascadeScalars params eps k :=
      MainFormalCascadeScalars.ofNontrivialMainFormal hepsNN hk0 herr
    by_cases hm1 : params.m = 1
    · -- Base case (m = 1): role residual from checked handoff,
      -- bridge from the external `hbaseBridge` hypothesis.
      rcases MainFormalRolePackageResidual.ofBaseCase params strategy eps k hpass hm1 with
        ⟨roleResidual⟩
      exact mainFormal_ofRoleResidualAndRepairedBridge herr roleResidual
        (hbaseBridge scalars roleResidual)
    · have hprojectiveCompletionResidual :
          Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
            (params := params) (strategy := strategy) (eps := eps)
            (hpass := hpass) (k := k) (scalars := scalars)) := by
        -- Successor case (m > 1): the answer-valued recursive-slice adapter is
        -- available, but this theorem still has no predecessor per-slice induction
        -- package or answer-side self-improvement bridge inputs in scope.
        -- TODO(#931, #834, #422): supply those successor inputs and assemble the
        -- resulting role residual into a Step 6 witness residual.
        sorry
      rcases hprojectiveCompletionResidual with ⟨projectiveCompletionResidual⟩
      let rolePackage := projectiveCompletionResidual.roleResidual.rolePackage scalars
      have hpre : ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily
            (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
          (constSubMeasFamily
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
          scalars.zeta1 := by
        simpa [rolePackage] using
          projectiveCompletionResidual.roleResidual.diagonalConsistency scalars
      let rolePackageResidualLeftCompletionTransportResidual :
          MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual
            (params := params) (strategy := strategy) (eps := eps)
            (hpass := hpass) (k := k) (scalars := scalars) :=
        projectiveCompletionResidual.toLeftCompletionTransportResidual herr
      have hpreForResidual : ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily
            (unsymmetrizedLeftPOVM
              (rolePackageResidualLeftCompletionTransportResidual.roleResidual.rolePackage
                scalars).roleMeasurement).toSubMeas)
          (constSubMeasFamily
            (unsymmetrizedRightPOVM
              (rolePackageResidualLeftCompletionTransportResidual.roleResidual.rolePackage
                scalars).roleMeasurement).toSubMeas)
          scalars.zeta1 := by
        open MainFormalCascadeRolePackageResidualProjectiveCompletionResidual in
        simpa [rolePackage, rolePackageResidualLeftCompletionTransportResidual,
          toLeftCompletionTransportResidual] using hpre
      have rolePackageResidualCompletionTransportResidual :
          MainFormalCascadeRolePackageResidualCompletionTransportResidual
            (params := params) (strategy := strategy) (eps := eps)
            (hpass := hpass) (k := k) (scalars := scalars) :=
        rolePackageResidualLeftCompletionTransportResidual
          |>.toRolePackageResidualCompletionTransportResidual hpreForResidual
      have rolePackagedCompletionTransportResidual :
          MainFormalCascadeRolePackagedCompletionTransportResidual params strategy eps k scalars :=
        rolePackageResidualCompletionTransportResidual.toRolePackagedCompletionTransportResidual
      have completionTransportResidual :
          MainFormalCascadeProjectiveCompletionTransportResidual params strategy eps k scalars :=
        rolePackagedCompletionTransportResidual.toCompletionTransportResidual
      have projectiveTargets :
          MainFormalCascadeProjectiveStageTargets params strategy eps k scalars :=
        completionTransportResidual.toProjectiveStageTargets hpass
      exact MainFormalNativeTargets.toMainFormal
        (projectiveTargets.toTransportTargets.toCascadeTargets.toNativeTargets)

end Test

end MIPStarRE.LDT
