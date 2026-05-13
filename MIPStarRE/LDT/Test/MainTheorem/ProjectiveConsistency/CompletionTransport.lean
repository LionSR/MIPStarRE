import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency.Evaluation
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Handoff

/-!
# Projective completion transport residuals

This module contains the finer projective completion residual.  It reconstructs
the line-156 handoff from completion closeness and transports the repaired
line-169 consistency estimates to the two final point-consistency targets.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Finer residual for the projective completion and paper line-169 handoff.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`, the
projectivization/completion and line-169 handoff in the proof of
`\label{thm:main-formal}`.

This residual records only the data that remains after the checked
role-unsymmetrization and pre-projective consistency steps.  The Section 6
consistency field of `UnsymmetrizationBridgePackage` and the pre-projective
consistency field of `ProjectivizationSelfConsistencyHandoff` are reconstructed
downstream from the two paper factor-two role-block estimates and `hpass` via
the checked line-116 triangle and Step 5 Schwartz--Zippel theorem.
The remaining open data are exactly what is still missing after those mechanical
steps:

* the role-register measurement and the two factor-two estimates from
  `inductive_step.tex` lines 97--108;
* the two completion-closeness estimates from lines 146--147; and
* the two exact polynomial line-169 `ζ₁` links (Alice side and the role-reversed
  Bob-side analogue), before line-171 data processing. -/
structure MainFormalCascadeProjectiveCompletionTransportResidual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The role-register polynomial POVM produced by the Section 6 induction call. -/
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  /-- Paper `eq:cons-b` / lines 97--108: original Alice point measurements are
  consistent with the Bob-role extraction, with the factor-two loss. -/
  pointARightPOVMConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params (unsymmetrizedRightPOVM roleMeasurement).toSubMeas)
      (2 * scalars.sigma)
  /-- Paper `eq:cons-a` / lines 105--108: the Alice-role extraction is consistent
  with original Bob point measurements, with the factor-two loss. -/
  leftPOVMPointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * scalars.sigma)
  /-- The completed projective measurement denoted $Q^{\mathrm A}$. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The completed projective measurement denoted $Q^{\mathrm B}$. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Left-register completion closeness, paper line 146 (`eq:G-with-Q-A`). -/
  leftCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily leftMeasurement.toSubMeas.liftLeft)
      scalars.zeta2
  /-- Right-register completion closeness, paper line 147. -/
  rightCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleMeasurement).toSubMeas.liftRight)
      (constSubMeasFamily rightMeasurement.toSubMeas.liftRight)
      scalars.zeta2
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

namespace MainFormalCascadeProjectiveCompletionTransportResidual

/-- View the factor-two role-block fields as the pre-projective target record. -/
noncomputable def toUnsymmetrizedPOVMTargets
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars) :
    MainFormalCascadeUnsymmetrizedPOVMTargets params strategy eps k scalars where
  leftPOVM := unsymmetrizedLeftPOVM residual.roleMeasurement
  rightPOVM := unsymmetrizedRightPOVM residual.roleMeasurement
  leftPOVMPointBConsistency := residual.leftPOVMPointBConsistency
  pointARightPOVMConsistency := residual.pointARightPOVMConsistency

/-- Reconstruct paper line 116 from the factor-two role-block estimates and the
original point-agreement bound. -/
noncomputable def toPreProjectiveSelfConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalCascadePreProjectiveSelfConsistency params strategy eps k scalars :=
  residual.toUnsymmetrizedPOVMTargets.toPreProjectiveSelfConsistency hpass

/-- Rebuild the Step 6 line-156 handoff from a freshly supplied Step 5
pre-projective consistency proof and the two completion-closeness fields. -/
noncomputable def projectivizationSelfConsistencyHandoff
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    MakingMeasurementsProjective.ProjectivizationSelfConsistencyHandoff strategy.state
      (unsymmetrizedLeftPOVM residual.roleMeasurement)
      (unsymmetrizedRightPOVM residual.roleMeasurement)
      residual.leftMeasurement residual.rightMeasurement scalars.zeta1 scalars.zeta2 where
  preProjectiveConsistency := hpre
  leftCompletionCloseness := residual.leftCompletionCloseness
  rightCompletionCloseness := residual.rightCompletionCloseness

/-- Paper line 156, reconstructed from Step 5 and completion closeness rather
than stored as an independent residual field. -/
theorem fullPolynomialConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily residual.leftMeasurement.toSubMeas)
      (constSubMeasFamily residual.rightMeasurement.toSubMeas)
      scalars.zeta3 := by
  have hline :=
    MakingMeasurementsProjective.ProjectivizationSelfConsistencyHandoff.fullPolynomialConsistency
      (residual.projectivizationSelfConsistencyHandoff hpre)
  simpa [MainFormalCascadeScalars.zeta3, cascadeZeta3] using hline

/-- Evaluated version of the projective self-consistency from reconstructed
line 156. -/
theorem projectiveEvaluationConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2) := by
  let pre := residual.toPreProjectiveSelfConsistency hpass
  have hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1 := by
    simpa [pre, toPreProjectiveSelfConsistency, toUnsymmetrizedPOVMTargets]
      using pre.fullSelfConsistency
  exact projectiveEvaluationConsistency_ofFullPolynomialConsistency
    residual.leftMeasurement residual.rightMeasurement (residual.fullPolynomialConsistency hpre)

/-- Point-goal transport from the repaired polynomial line-169 estimate.

Compared with the paper's exact line-169 `\zeta_1` link, this uses the checked
local repair `\zeta_1 + 10 \zeta_1^{1/8}` and then weakens the resulting point
error directly to `mainFormalError`. -/
theorem pointAConsistency_of_repairedLine169
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (roleMeasurement : Measurement (Polynomial params) (Role × ι))
    (leftMeasurement rightMeasurement : ProjMeas (Polynomial params) ι)
    (hAB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params (unsymmetrizedRightPOVM roleMeasurement).toSubMeas)
      (2 * scalars.sigma))
    (hCB : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params (unsymmetrizedRightPOVM roleMeasurement).toSubMeas)
      (scalars.zeta1 + 10 * Real.rpow scalars.zeta1 (1 / (8 : Error))))
    (hCD : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      (mainFormalError params k eps) := by
  let pointA : IdxMeas (Point params) (Fq params) ι :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementA
  let rightG : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params (unsymmetrizedRightPOVM roleMeasurement)
  let leftQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params leftMeasurement.toMeasurement
  let rightQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params rightMeasurement.toMeasurement
  have htriangle :=
    Preliminaries.simeqTriangleInequality strategy.state
      (uniformDistribution (Point params)) strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params))
      pointA rightG leftQ rightQ
      (2 * scalars.sigma)
      (scalars.zeta1 + 10 * Real.rpow scalars.zeta1 (1 / (8 : Error)))
      (scalars.zeta3 / 2)
      (by simpa [pointA, rightG, polynomialEvaluationMeasurementFamily] using hAB)
      (by simpa [leftQ, rightG, polynomialEvaluationMeasurementFamily] using hCB)
      (by simpa [leftQ, rightQ, polynomialEvaluationMeasurementFamily] using hCD)
  exact ConsRel.mono
    (MainFormalCascadeScalars.repairedLine169PointError_le_mainFormalError scalars)
    (by simpa [pointA, rightG, leftQ, rightQ, polynomialEvaluationMeasurementFamily,
      add_assoc, add_left_comm, add_comm] using htriangle)

/-- Bob-side mirror of `pointAConsistency_of_repairedLine169`. -/
theorem pointBConsistency_of_repairedLine169
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (roleMeasurement : Measurement (Polynomial params) (Role × ι))
    (leftMeasurement rightMeasurement : ProjMeas (Polynomial params) ι)
    (hAB : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * scalars.sigma))
    (hCB : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      (polynomialEvaluationFamily params (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas)
      (scalars.zeta1 + 10 * Real.rpow scalars.zeta1 (1 / (8 : Error))))
    (hCD : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (mainFormalError params k eps) := by
  let pointB : IdxMeas (Point params) (Fq params) ι :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementB
  let leftG : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params (unsymmetrizedLeftPOVM roleMeasurement)
  let rightQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params rightMeasurement.toMeasurement
  let leftQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params leftMeasurement.toMeasurement
  have hAB' : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointB) (IdxMeas.toIdxSubMeas leftG) (2 * scalars.sigma) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas leftG)
      (IdxMeas.toIdxSubMeas pointB) (2 * scalars.sigma)
      (by simpa [pointB, leftG, polynomialEvaluationMeasurementFamily] using hAB)
  have hCD' : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas rightQ) (IdxMeas.toIdxSubMeas leftQ) (scalars.zeta3 / 2) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas leftQ)
      (IdxMeas.toIdxSubMeas rightQ) (scalars.zeta3 / 2)
      (by simpa [leftQ, rightQ, polynomialEvaluationMeasurementFamily] using hCD)
  have htriangle :=
    Preliminaries.simeqTriangleInequality strategy.state
      (uniformDistribution (Point params)) strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params))
      pointB leftG rightQ leftQ
      (2 * scalars.sigma)
      (scalars.zeta1 + 10 * Real.rpow scalars.zeta1 (1 / (8 : Error)))
      (scalars.zeta3 / 2)
      hAB'
      (by simpa [rightQ, leftG, polynomialEvaluationMeasurementFamily] using hCB)
      hCD'
  have htarget : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointB) (IdxMeas.toIdxSubMeas leftQ)
      (mainFormalError params k eps) :=
    ConsRel.mono
      (MainFormalCascadeScalars.repairedLine169PointError_le_mainFormalError scalars)
      (by simpa [pointB, leftG, rightQ, leftQ, polynomialEvaluationMeasurementFamily,
        add_assoc, add_left_comm, add_comm] using htriangle)
  exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
    (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas pointB)
    (IdxMeas.toIdxSubMeas leftQ) (mainFormalError params k eps) htarget

/-- Derive paper `eq:one-goal` from `eq:cons-b`, line 172 obtained by data
processing line 169, and evaluated line 164. -/
theorem pointAConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
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
    exact residual.pointARightPOVMConsistency
  have hCB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightG)
      scalars.zeta1 := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params
        (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1
    simpa using
      consRel_constPolynomialEvaluation strategy.state
        residual.leftMeasurement.toMeasurement
        (unsymmetrizedRightPOVM residual.roleMeasurement)
        residual.leftProjectiveRightPOVMPolynomialConsistency
  have hCD : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightQ)
      (scalars.zeta3 / 2) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)
    exact residual.projectiveEvaluationConsistency hpass
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
triangle, again data-processing the polynomial line-169 mirror first. -/
theorem pointBConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
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
    exact residual.leftPOVMPointBConsistency
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
    simpa using
      consRel_constPolynomialEvaluation strategy.state
        residual.rightMeasurement.toMeasurement
        (unsymmetrizedLeftPOVM residual.roleMeasurement)
        residual.rightProjectiveLeftPOVMPolynomialConsistency
  have hLeftQRightQ : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightQ)
      (scalars.zeta3 / 2) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)
    exact residual.projectiveEvaluationConsistency hpass
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

end MainFormalCascadeProjectiveCompletionTransportResidual

end Test

end MIPStarRE.LDT
