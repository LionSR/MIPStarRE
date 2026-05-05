import MIPStarRE.LDT.Test.MainTheorem.DiagonalCompletion
import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency

/-!
# Main-formal native targets

Target and residual packages used by the final `mainFormal` assembly.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Paper-shaped residual for the still-external data in the non-vacuous branch.

The proof body consumes this package in paper order: first it reads the concrete
role residual, then derives the unsymmetrized POVMs, line-116 evaluated
consistency, and Step-5 full `G^A/G^B` consistency, and only then consumes the
post-role Step 6 completion data whose `P^A/P^B` provenance is tied to that
line-130 consistency. -/
structure MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The explicit isolated Section 6 residual. -/
  roleResidual : MainFormalRolePackageResidual params strategy eps hpass k
  /-- Step 6 completion data after line-130 orthonormalization of the role blocks. -/
  postRoleDiagonalCompletion :
    MainFormalPostRolePackageDiagonalCompletionResidual params strategy eps k scalars
      (roleResidual.rolePackage scalars)

namespace MainFormalCascadeRolePackageResidualProjectiveCompletionResidual

/-- Assemble the final live residual once the concrete Section 6 role residual and
the post-role line-130 completion residual have both been produced. -/
theorem nonempty_ofRoleResidualAndCompletion
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (hcompletion : Nonempty (MainFormalPostRolePackageDiagonalCompletionResidual
      params strategy eps k scalars (roleResidual.rolePackage scalars))) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      params strategy eps hpass k scalars) := by
  rcases hcompletion with ⟨completion⟩
  exact ⟨{ roleResidual := roleResidual, postRoleDiagonalCompletion := completion }⟩

/-- Assemble the final live residual from a concrete Section 6 role residual, the
line-130 orthonormalization bridge inputs, and a producer for the remaining
completion/match-mass obligations for the projective submeasurements obtained from
line 130.

This is the precise remaining shape of the final `mainFormal` hole after the
paper-order handoffs have been named. -/
theorem nonempty_ofRoleResidualAndDiagonalInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (input : MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars))
    (completionProducer :
      MainFormalPostRolePackageDiagonalOrthonormalizationResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars) →
        MainFormalPostRolePackageDiagonalCompletionResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars)) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      params strategy eps hpass k scalars) := by
  have hpre := roleResidual.diagonalConsistency scalars
  rcases MainFormalPostRolePackageDiagonalOrthonormalizationResidual.nonempty_ofDiagonalInputs
      hsmall hpre input with ⟨orthResidual⟩
  exact nonempty_ofRoleResidualAndCompletion roleResidual ⟨completionProducer orthResidual⟩

/-- Assemble the final live residual using explicit completion inputs rather than
an opaque `completionProducer`.

A caller supplies, for each line-130 orthonormalization residual produced from
the bridge inputs, the concrete distinguished outcomes, completed-closeness
proofs, and orthonormalization match-mass preservation facts packaged as
`MainFormalPostRolePackageDiagonalCompletionInput`.  This theorem converts that
package into the old producer shape by `toCompletionResidual`.

**Status:** currently unused (no callers).  The more analytic variant
`nonempty_ofRoleResidualAndDiagonalInputsAndCompletingToMeasurementInputs` (and
its alias `nonempty_ofRoleResidualAndBridgeInputsAndCompletingToMeasurementInputs`)
expose the same endpoint with explicit `BipartiteSSCRel` and match-mass inputs
instead of a pre-packaged `CompletionInput`. -/
theorem nonempty_ofRoleResidualAndDiagonalInputsAndCompletionInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (input : MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars))
    (completionInputProducer :
      ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars),
        MainFormalPostRolePackageDiagonalCompletionInput
          params strategy eps k scalars (roleResidual.rolePackage scalars) orthResidual) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      params strategy eps hpass k scalars) :=
  nonempty_ofRoleResidualAndDiagonalInputs hsmall roleResidual input fun orthResidual =>
    (completionInputProducer orthResidual).toCompletionResidual

/-- Assemble the final live residual from the exact analytic completion witnesses.

This is the paper-shaped replacement for the generic `completionProducer`: after
line 130 produces `P^A` and `P^B`, the caller provides
* distinguished completion outcomes `a_A`, `a_B`,
* strong self-consistency for the two unsymmetrized role POVMs, and
* orthonormalization match-mass preservation for the two produced
  submeasurements.

The proof invokes `completingToMeasurement` to derive the two completed-closeness
fields and then packages them through
`MainFormalPostRolePackageDiagonalCompletionInput.toCompletionResidual`. -/
theorem nonempty_ofRoleResidualAndDiagonalInputsAndCompletingToMeasurementInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (input : MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars))
    (a_A a_B : Polynomial params)
    (leftSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM
            (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
        scalars.zeta1)
    (rightSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM
            (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
        scalars.zeta1)
    (leftMatchMassPreservation :
      ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars),
        MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
          (unsymmetrizedLeftPOVM
            (roleResidual.rolePackage scalars).roleMeasurement)
          orthResidual.P_A
          (unsymmetrizedRightPOVM
            (roleResidual.rolePackage scalars).roleMeasurement))
    (rightMatchMassPreservation :
      ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars),
        MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
          (unsymmetrizedRightPOVM
            (roleResidual.rolePackage scalars).roleMeasurement)
          orthResidual.P_B
          (unsymmetrizedLeftPOVM
            (roleResidual.rolePackage scalars).roleMeasurement)) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      params strategy eps hpass k scalars) := by
  have hpre := roleResidual.diagonalConsistency scalars
  rcases MainFormalPostRolePackageDiagonalOrthonormalizationResidual.nonempty_ofDiagonalInputs
      hsmall hpre input with ⟨orthResidual⟩
  rcases MainFormalPostRolePackageDiagonalCompletionInput.nonempty_ofCompletingToMeasurementInputs
      orthResidual a_A a_B
        leftSelfConsistency rightSelfConsistency
        (leftMatchMassPreservation orthResidual)
        (rightMatchMassPreservation orthResidual) with ⟨completionInput⟩
  exact nonempty_ofRoleResidualAndCompletion roleResidual
    ⟨completionInput.toCompletionResidual⟩

/-- Assemble the final live residual from the paper line-130 cross consistency,
the orthonormalization inputs, and the P-level match-mass preservation data.

This is the live Lean Step 6 route: the checked role residual
reconstructs line 130 as a cross `ConsRel`, the orthonormalization wrapper
produces `P^A,P^B`, and the remaining completion step is discharged directly from
that cross relation plus the construction-level match-mass preservation facts,
without asking callers for separate diagonal strong self-consistency packages. -/
theorem nonempty_ofRoleResidualAndDiagonalInputsAndMatchMassPreservation
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (input : MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars))
    (a_A a_B : Polynomial params)
    (leftMatchMassPreservation :
      ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars),
        MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
          (unsymmetrizedLeftPOVM
            (roleResidual.rolePackage scalars).roleMeasurement)
          orthResidual.P_A
          (unsymmetrizedRightPOVM
            (roleResidual.rolePackage scalars).roleMeasurement))
    (rightMatchMassPreservation :
      ∀ orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars),
        MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
          (unsymmetrizedRightPOVM
            (roleResidual.rolePackage scalars).roleMeasurement)
          orthResidual.P_B
          (unsymmetrizedLeftPOVM
            (roleResidual.rolePackage scalars).roleMeasurement)) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      params strategy eps hpass k scalars) := by
  have hpre := roleResidual.diagonalConsistency scalars
  rcases MainFormalPostRolePackageDiagonalOrthonormalizationResidual.nonempty_ofDiagonalInputs
      hsmall hpre input with ⟨orthResidual⟩
  have hcompletion :
      Nonempty (MainFormalPostRolePackageDiagonalCompletionInput
        params strategy eps k scalars (roleResidual.rolePackage scalars) orthResidual) :=
    (open MainFormalPostRolePackageDiagonalCompletionInput in
      nonempty_ofDiagonalConsistencyAndMatchMassPreservation)
        orthResidual a_A a_B hpre
        (leftMatchMassPreservation orthResidual)
        (rightMatchMassPreservation orthResidual)
  rcases hcompletion with ⟨completionInput⟩
  exact nonempty_ofRoleResidualAndCompletion roleResidual
    ⟨completionInput.toCompletionResidual⟩

/-- Bridge-shape alias for
`nonempty_ofRoleResidualAndDiagonalInputsAndCompletingToMeasurementInputs`
accepting the orthonormalization inputs under the `…BridgeInputs` name.

The alias is definitional (the bridge `abbrev` unfolds in-place) and exists
only as a documented entry point for callers that carry the bridge wrapper.

**Status:** currently unused (no callers).  The underlying theorem
`nonempty_ofRoleResidualAndDiagonalInputsAndCompletingToMeasurementInputs` is the
canonical form; this alias is retained for callers that hold the bridge-wrapper
type. -/
alias nonempty_ofRoleResidualAndBridgeInputsAndCompletingToMeasurementInputs :=
  nonempty_ofRoleResidualAndDiagonalInputsAndCompletingToMeasurementInputs

/-- Convert the combined residual to the left-completion residual after the paper
line-130 consistency has been derived separately. -/
noncomputable def toLeftCompletionTransportResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      params strategy eps hpass k scalars)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual
      params strategy eps hpass k scalars :=
  open MainFormalCascadeRolePackageResidualLeftCompletionTransportResidual in
  { roleResidual := residual.roleResidual
    postRoleResidual :=
      residual.postRoleDiagonalCompletion.toProjectiveCompletionResidual
        |>.toPostRolePackageLeftCompletionTransportResidual hsmall }

end MainFormalCascadeRolePackageResidualProjectiveCompletionResidual

namespace MainFormalCascadeTransportTargets

/-- Add the already-discharged scalar package back to the transport-only targets. -/
noncomputable def toCascadeTargets {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (targets : MainFormalCascadeTransportTargets params strategy eps k scalars) :
    MainFormalCascadeTargets params strategy eps k where
  scalars := scalars
  leftMeasurement := targets.leftMeasurement
  rightMeasurement := targets.rightMeasurement
  pointAConsistency := targets.pointAConsistency
  pointBConsistency := targets.pointBConsistency
  selfConsistency := targets.selfConsistency

end MainFormalCascadeTransportTargets

/-- Paper-native final targets for the remaining `mainFormal` assembly.

This structure deliberately stops before the final error-envelope weakening. Its
three consistency fields are exactly the native conclusions reached in
`references/ldt-paper/inductive_step.tex`:

* `eq:one-goal` (lines 175--181):
  $A^{\mathrm A,u}_a \otimes I \simeq_{\zeta_4}
    I \otimes Q^{\mathrm B}_{[g(u)=a]}$;
* `eq:another-goal` (lines 182--185):
  $I \otimes A^{\mathrm B,u}_a \simeq_{\zeta_4}
    Q^{\mathrm A}_{[g(u)=a]} \otimes I$;
* `eq:third-goal` (lines 160--162):
  $Q^{\mathrm A}_g \otimes I \simeq_{\zeta_3/2} I \otimes Q^{\mathrm B}_g$.

The two bound fields record the already-formalized Step 8 absorption of
`\zeta_4` and `\zeta_3/2` into `mainFormalError`. Constructing this package from
Section 6 and the unsymmetrization / Schwartz--Zippel / projectivization chain is
the live residual; the projection theorem below is only the final paper-faithful
packaging step. -/
structure MainFormalNativeTargets
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ) where
  /-- The projective measurement denoted $Q^{\mathrm A}$ in the paper. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The projective measurement denoted $Q^{\mathrm B}$ in the paper. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- The paper's self-consistency error `\zeta_3`. -/
  zeta3 : Error
  /-- The paper's two point-consistency error `\zeta_4`. -/
  zeta4 : Error
  /-- Native form of `eq:one-goal`, before weakening to `mainFormalError`. -/
  pointAConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      zeta4
  /-- Native form of `eq:another-goal`, before weakening to `mainFormalError`. -/
  pointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      zeta4
  /-- Native form of `eq:third-goal`, before its point-evaluation data processing. -/
  selfConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (zeta3 / 2)
  /-- Step 8 scalar absorption for the two point-consistency targets. -/
  pointErrorLe : zeta4 ≤ mainFormalError params k eps
  /-- Step 8 scalar absorption for the self-consistency target. -/
  selfErrorLe : zeta3 / 2 ≤ mainFormalError params k eps

namespace MainFormalNativeTargets

/-- Final packaging step for `thm:main-formal` once the formal native targets have
been constructed. This only weakens the native `\zeta_4` and `\zeta_3/2` bounds to
`mainFormalError` using `ConsRel.mono`; all substantive transport work is in the
construction of `MainFormalNativeTargets`. -/
theorem toMainFormal {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (targets : MainFormalNativeTargets params strategy eps k) :
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
  · exact ConsRel.mono targets.pointErrorLe targets.pointAConsistency
  · exact ConsRel.mono targets.pointErrorLe targets.pointBConsistency
  · exact ConsRel.mono targets.selfErrorLe targets.selfConsistency

end MainFormalNativeTargets

namespace MainFormalCascadeTargets

/-- Convert exact cascade-error targets into `MainFormalNativeTargets` by applying
the already-formalized Step 8 scalar absorption lemmas.

This is still only packaging: the assumptions are the `eq:one-goal`,
`eq:another-goal`, and `eq:third-goal` statements at the formal cascade errors
from `inductive_step.tex` lines 159--185, with the Step 6 `ζ₂` scalar widened
as documented in `ErrorCascade.lean`. -/
noncomputable def toNativeTargets {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (targets : MainFormalCascadeTargets params strategy eps k) :
    MainFormalNativeTargets params strategy eps k where
  leftMeasurement := targets.leftMeasurement
  rightMeasurement := targets.rightMeasurement
  zeta3 := targets.scalars.zeta3
  zeta4 := targets.scalars.zeta4
  pointAConsistency := targets.pointAConsistency
  pointBConsistency := targets.pointBConsistency
  selfConsistency := targets.selfConsistency
  pointErrorLe := MainFormalCascadeScalars.zeta4_le_mainFormalError targets.scalars
  selfErrorLe := MainFormalCascadeScalars.zeta3_div_two_le_mainFormalError targets.scalars

end MainFormalCascadeTargets

end Test

end MIPStarRE.LDT
