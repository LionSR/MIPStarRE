import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency.Evaluation

/-!
# Projective handoff residuals

This module contains the projective handoff residual which packages the
line-156 projectivization handoff together with the two evaluated line-172
links to the unsymmetrized role measurements.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Residual after wiring the merged Step 3 and line-156 projectivization packages.

Paper origin: `references/ldt-paper/inductive_step.tex:150-185`, the
projective handoff and final two point-consistency estimates in the proof of
`\label{thm:main-formal}`.

This package is narrower than `MainFormalCascadeProjectiveAssemblyResidual`:

* the unsymmetrized POVMs must be the actual role blocks of a role-register
  measurement `G`, with the two factor-two bounds supplied by
  `UnsymmetrizationBridgePackage`;
* the line-156 approximation must come from
  `MakingMeasurementsProjective.ProjectivizationSelfConsistencyHandoff`;
* the remaining point-transport work is isolated to the two line-172 style
  evaluated `ζ₁` links from the completed projective measurements back to the
  pre-projective role blocks.  The two native `ζ₄` point goals are then proved
  below by the paper's `prop:simeq-triangle-inequality` route. -/
structure MainFormalCascadeProjectiveHandoffResidual
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
  /-- Paper line 172: after evaluating at a point,
  $Q^{\mathrm A}_{[g(u)=a]}\otimes I \simeq_{\zeta_1}
  I\otimes G^{\mathrm B}_{[g(u)=a]}$. -/
  leftProjectiveRightPOVMConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params (unsymmetrizedRightPOVM roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- The Bob-role analogue of paper line 172, used for `eq:another-goal`. -/
  rightProjectiveLeftPOVMConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      (polynomialEvaluationFamily params (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas)
      scalars.zeta1

namespace MainFormalCascadeProjectiveHandoffResidual

/-- Evaluated version of the projective self-consistency from the line-156 handoff. -/
theorem projectiveEvaluationConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveHandoffResidual params strategy eps k scalars) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2) := by
  have hlineRaw :=
    MakingMeasurementsProjective.ProjectivizationSelfConsistencyHandoff.fullPolynomialConsistency
      residual.projectivization
  have hline :
      Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily residual.leftMeasurement.toSubMeas)
        (constSubMeasFamily residual.rightMeasurement.toSubMeas) scalars.zeta3 := by
    simpa [MainFormalCascadeScalars.zeta3, cascadeZeta3] using hlineRaw
  exact projectiveEvaluationConsistency_ofFullPolynomialConsistency
    residual.leftMeasurement residual.rightMeasurement hline

/-- Derive paper `eq:one-goal` from `eq:cons-b`, line 172, and evaluated line 164. -/
theorem pointAConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveHandoffResidual params strategy eps k scalars) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      scalars.zeta4 := by
  let pointA : IdxMeas (Point params) (Fq params) ι :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementA
  let rightG : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params
      (unsymmetrizedRightPOVM residual.roleMeasurement)
  let leftQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.leftMeasurement.toMeasurement
  let rightQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.rightMeasurement.toMeasurement
  have hAB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas rightG)
      (2 * scalars.sigma) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params
        (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      (2 * scalars.sigma)
    exact residual.unsymmetrization.pointAConsistency
  have hCB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightG)
      scalars.zeta1 := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params
        (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1
    exact residual.leftProjectiveRightPOVMConsistency
  have hCD : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightQ)
      (scalars.zeta3 / 2) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)
    exact residual.projectiveEvaluationConsistency
  have htriangle :=
    Preliminaries.simeqTriangleInequality strategy.state
      (uniformDistribution (Point params)) strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params))
      pointA rightG leftQ rightQ
      (2 * scalars.sigma) scalars.zeta1 (scalars.zeta3 / 2)
      hAB hCB hCD
  simpa [pointA, rightG, leftQ, rightQ, polynomialEvaluationMeasurementFamily,
    MainFormalCascadeScalars.zeta4, cascadeZeta4] using htriangle

/-- Derive paper `eq:another-goal` by the Bob-role mirror of the `eq:one-goal`
triangle, using swap symmetry to orient the intermediate consistency relations. -/
theorem pointBConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveHandoffResidual params strategy eps k scalars) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      scalars.zeta4 := by
  let pointB : IdxMeas (Point params) (Fq params) ι :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementB
  let leftG : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params
      (unsymmetrizedLeftPOVM residual.roleMeasurement)
  let rightQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.rightMeasurement.toMeasurement
  let leftQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.leftMeasurement.toMeasurement
  have hLeftGPointB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftG) (IdxMeas.toIdxSubMeas pointB)
      (2 * scalars.sigma) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params
        (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * scalars.sigma)
    exact residual.unsymmetrization.pointBConsistency
  have hAB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointB) (IdxMeas.toIdxSubMeas leftG)
      (2 * scalars.sigma) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas leftG)
      (IdxMeas.toIdxSubMeas pointB) (2 * scalars.sigma) hLeftGPointB
  have hCB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas rightQ) (IdxMeas.toIdxSubMeas leftG)
      scalars.zeta1 := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (polynomialEvaluationFamily params
        (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1
    exact residual.rightProjectiveLeftPOVMConsistency
  have hLeftQRightQ : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightQ)
      (scalars.zeta3 / 2) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)
    exact residual.projectiveEvaluationConsistency
  have hCD : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas rightQ) (IdxMeas.toIdxSubMeas leftQ)
      (scalars.zeta3 / 2) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas leftQ)
      (IdxMeas.toIdxSubMeas rightQ) (scalars.zeta3 / 2) hLeftQRightQ
  have htriangle : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointB) (IdxMeas.toIdxSubMeas leftQ)
      scalars.zeta4 := by
    have hraw :=
      Preliminaries.simeqTriangleInequality strategy.state
        (uniformDistribution (Point params)) strategy.isNormalized
        (uniformDistribution_weight_sum_le_one (Point params))
        pointB leftG rightQ leftQ
        (2 * scalars.sigma) scalars.zeta1 (scalars.zeta3 / 2)
        hAB hCB hCD
    simpa [MainFormalCascadeScalars.zeta4, cascadeZeta4] using hraw
  have htarget :=
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas pointB)
      (IdxMeas.toIdxSubMeas leftQ) scalars.zeta4 htriangle
  simpa [pointB, leftG, rightQ, leftQ, polynomialEvaluationMeasurementFamily] using htarget

/-- Assemble the previous projective-assembly residual from the narrower handoff
residual using the checked Step 3, line-156, and point-triangle wrappers above.

Paper origin: `references/ldt-paper/inductive_step.tex:150-185`. -/
noncomputable def toProjectiveAssemblyResidual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveHandoffResidual params strategy eps k scalars) :
    MainFormalCascadeProjectiveAssemblyResidual params strategy eps k scalars where
  unsymmetrized :=
    MainFormalCascadeUnsymmetrizedPOVMTargets.ofUnsymmetrizationBridge
      residual.roleMeasurement residual.unsymmetrization
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  pointAConsistency := residual.pointAConsistency
  pointBConsistency := residual.pointBConsistency
  fullPolynomialConsistency := by
    intro hpre
    have hpre' : ConsRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
        (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
        scalars.zeta1 := by
      simpa [MainFormalCascadeUnsymmetrizedPOVMTargets.ofUnsymmetrizationBridge]
        using hpre
    let handoff : MakingMeasurementsProjective.ProjectivizationSelfConsistencyHandoff
        strategy.state (unsymmetrizedLeftPOVM residual.roleMeasurement)
        (unsymmetrizedRightPOVM residual.roleMeasurement)
        residual.leftMeasurement residual.rightMeasurement scalars.zeta1 scalars.zeta2 :=
      { preProjectiveConsistency := hpre'
        leftCompletionCloseness := residual.projectivization.leftCompletionCloseness
        rightCompletionCloseness := residual.projectivization.rightCompletionCloseness }
    have hline :=
      MakingMeasurementsProjective.ProjectivizationSelfConsistencyHandoff.fullPolynomialConsistency
        handoff
    simpa [MainFormalCascadeScalars.zeta3, cascadeZeta3] using hline

end MainFormalCascadeProjectiveHandoffResidual

end Test

end MIPStarRE.LDT
