import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency.Handoff

/-!
# Projective evaluation handoff residuals

This module records the intermediate residual in which polynomial-level
line-169 consistency has been supplied and the two pointwise line-172
consistency links are obtained by data processing.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Polynomial-level line-169 residual before the line-172 data-processing step.

Paper origin: `references/ldt-paper/inductive_step.tex:150-173`, from
`\label{eq:G-with-Q-A}` through the point-evaluation data-processing step.

This package is narrower than `MainFormalCascadeProjectiveHandoffResidual`: the
line-172 evaluated `ζ₁` links are no longer fields.  Instead it asks for the
polynomial-level statements from `inductive_step.tex` lines 167--173,

* `Q^A_g ⊗ I ≃_{ζ₁} I ⊗ G^B_g`, and
* its Bob-role mirror `Q^B_g ⊗ I ≃_{ζ₁} I ⊗ G^A_g`,

both over the constant polynomial question.  The theorem
`toProjectiveHandoffResidual` below proves the paper's data-processing move from
line 171 to line 172 for both links. -/
structure MainFormalCascadeProjectiveEvaluationHandoffResidual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The role-register polynomial POVM produced by the Section 6 induction call. -/
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  /-- Step 3: role-block extraction plus the two factor-two estimates. -/
  unsymmetrization :
    UnsymmetrizationBridgePackage params strategy roleMeasurement scalars.sigma
  /-- The completed projective measurement denoted $Q^{\mathrm A}$. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The completed projective measurement denoted $Q^{\mathrm B}$. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Step 6 line-156 handoff from pre-projective consistency and completion closeness. -/
  projectivization :
    MakingMeasurementsProjective.ProjectivizationSelfConsistencyHandoff strategy.state
      (unsymmetrizedLeftPOVM roleMeasurement) (unsymmetrizedRightPOVM roleMeasurement)
      leftMeasurement rightMeasurement scalars.zeta1 scalars.zeta2
  /-- Paper line 169, before the data-processing step at lines 171--173:
  $Q^{\mathrm A}_g\otimes I \simeq_{\zeta_1} I\otimes G^{\mathrm B}_g$. -/
  leftProjectiveRightPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Bob-role mirror of paper line 169, before point-evaluation data processing. -/
  rightProjectiveLeftPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas)
      scalars.zeta1

namespace MainFormalCascadeProjectiveEvaluationHandoffResidual

/-- Apply the paper's line-171--173 data-processing step to the two polynomial
`ζ₁` links and recover the previous evaluated handoff residual.

Paper origin: `references/ldt-paper/inductive_step.tex:167-173`. -/
noncomputable def toProjectiveHandoffResidual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveEvaluationHandoffResidual
      params strategy eps k scalars) :
    MainFormalCascadeProjectiveHandoffResidual params strategy eps k scalars where
  roleMeasurement := residual.roleMeasurement
  unsymmetrization := residual.unsymmetrization
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  projectivization := residual.projectivization
  leftProjectiveRightPOVMConsistency := by
    simpa using
      consRel_constPolynomialEvaluation strategy.state
        residual.leftMeasurement.toMeasurement
        (unsymmetrizedRightPOVM residual.roleMeasurement)
        residual.leftProjectiveRightPOVMPolynomialConsistency
  rightProjectiveLeftPOVMConsistency := by
    simpa using
      consRel_constPolynomialEvaluation strategy.state
        residual.rightMeasurement.toMeasurement
        (unsymmetrizedLeftPOVM residual.roleMeasurement)
        residual.rightProjectiveLeftPOVMPolynomialConsistency

end MainFormalCascadeProjectiveEvaluationHandoffResidual

end Test

end MIPStarRE.LDT
