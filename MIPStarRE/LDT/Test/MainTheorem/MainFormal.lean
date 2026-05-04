import MIPStarRE.LDT.Test.MainTheorem.DiagonalCompletion

/-!
# Main-formal target assembly

Statement-preserving slice of `MIPStarRE.LDT.Test.MainTheorem`.
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

Fixes #137, #239, #906.
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
      MainFormalBaseBridgeHypotheses params strategy eps k hpass scalars roleResidual) :
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
  -- The match-mass monotonicity structure
  -- `MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation`, the
  -- lift theorem `of_submeasurement_match_mass_and_completion`, and the
  -- line-130 completion wrapper
  -- `nonempty_ofRoleResidualAndDiagonalInputsAndCompletingToMeasurementInputs`
  -- are now available.  The self-improvement assumptions are packaged as
  -- `SelfImprovement.SelfImprovementBridgeInputs`.  The remaining `mainFormal` hole
  -- still needs:
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
  -- 3. **Completion closeness** for the two POVMs, derived through
  --    `completingToMeasurement`.  Needs `BipartiteSSCRel` for the
  --    unsymmetrized POVMs (external).
  --
  -- 4. **Match-mass preservation** values (type
  --    `MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation`)
  --    for both sides.  With these, `of_submeasurement_match_mass_and_completion`
  --    produces the `ProjectivizationMatchMassMonotonicity` needed by
  --    `leftConsistency` / `rightConsistency` for the exact paper `ζ₁` links.
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
    have hprojectiveCompletionResidual :
        Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
          (params := params) (strategy := strategy) (eps := eps)
          (hpass := hpass) (k := k) (scalars := scalars)) := by
      by_cases hm1 : params.m = 1
      · -- Base case (m = 1): role residual from checked handoff,
        -- bridge from the external `hbaseBridge` hypothesis.
        rcases MainFormalRolePackageResidual.ofBaseCase params strategy eps k hpass hm1 with
          ⟨roleResidual⟩
        exact baseProjectiveCompletionResidual_ofBaseBridge herr roleResidual
          (hbaseBridge scalars roleResidual)
      · -- Successor case (m > 1): the answer-valued recursive-slice adapter is
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
