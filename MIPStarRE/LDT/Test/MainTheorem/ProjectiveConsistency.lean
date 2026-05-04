import MIPStarRE.LDT.Test.MainTheorem.UnsymmetrizedTargets

/-!
# Projective consistency transport

Statement-preserving slice of `MIPStarRE.LDT.Test.MainTheorem`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- A constant full-polynomial consistency statement postprocesses to pointwise
polynomial evaluation with the same error.

This is the data-processing move used after paper line 156: once
`Q^A_g \otimes I \simeq I \otimes Q^B_g` is available over the single
polynomial question, evaluating both polynomial outcomes at a point `u` preserves
consistency over the uniform point distribution. -/
private theorem consRel_constPolynomialEvaluation
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (A B : Measurement (Polynomial params) ι) {δ : Error}
    (h : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) δ) :
    ConsRel ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params A.toSubMeas)
      (polynomialEvaluationFamily params B.toSubMeas) δ := by
  classical
  let Aconst : IdxSubMeas (Point params) (Polynomial params) ι := fun _ => A.toSubMeas
  let Bconst : IdxSubMeas (Point params) (Polynomial params) ι := fun _ => B.toSubMeas
  have hconstPoint :
      ConsRel ψ (uniformDistribution (Point params)) Aconst Bconst δ := by
    rcases h with ⟨hbound⟩
    constructor
    have hpoint_avg :
        avgOver (uniformDistribution (Point params))
            (fun _ : Point params => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) =
          qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
      haveI : Nonempty (Point params) := by infer_instance
      simpa using
        (avgOver_uniform_const (α := Point params)
          (qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas))
    have hunit_eq :
        bipartiteConsError ψ (uniformDistribution Unit)
            (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) =
          qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
      have hunit_avg :
          avgOver (uniformDistribution Unit)
              (fun _ : Unit => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) =
            qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
        simpa using
          (avgOver_uniform_const (α := Unit)
            (qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas))
      simpa [bipartiteConsError, constSubMeasFamily] using hunit_avg
    calc
      bipartiteConsError ψ (uniformDistribution (Point params)) Aconst Bconst
          = avgOver (uniformDistribution (Point params))
              (fun _ : Point params => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) := by
            rfl
      _ = qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := hpoint_avg
      _ = bipartiteConsError ψ (uniformDistribution Unit)
            (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) :=
            hunit_eq.symm
      _ ≤ δ := hbound
  have hprocessed :=
    Preliminaries.consRelDataProcessing_questionDependent ψ
      (uniformDistribution (Point params)) Aconst Bconst δ (fun u g => g u) hconstPoint
  simpa [Aconst, Bconst, polynomialEvaluationFamily, evaluateAt] using hprocessed

/-- Turn a line-156 projective approximation into the evaluated consistency used
in the final point-consistency triangles.

The proof first applies the projective converse of `prop:simeq-to-approx` at the
polynomial level, then uses question-dependent data processing to evaluate both
projective polynomial measurements at each point. -/
private theorem projectiveEvaluationConsistency_ofFullPolynomialConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    (Q_A Q_B : ProjMeas (Polynomial params) ι) {ζ₃ : Error}
    (hline : Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas) ζ₃) :
    ConsRel ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) (ζ₃ / 2) := by
  let leftConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => Q_A
  let rightConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => Q_B
  have happrox :
      Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
        (IdxProjMeas.toIdxSubMeas leftConst)
        (IdxProjMeas.toIdxSubMeas rightConst) (2 * (ζ₃ / 2)) := by
    change Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas) (constSubMeasFamily Q_B.toSubMeas)
      (2 * (ζ₃ / 2))
    convert hline using 1
    ring
  have hcons :=
    Preliminaries.approxToSimeq ψ (uniformDistribution Unit)
      leftConst rightConst (ζ₃ / 2) happrox
  simpa [leftConst, rightConst, constSubMeasFamily, IdxProjMeas.toIdxSubMeas]
    using consRel_constPolynomialEvaluation ψ Q_A.toMeasurement Q_B.toMeasurement hcons

/-- Residual after wiring the merged Step 3 and line-156 projectivization packages.

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
residual using the checked Step 3, line-156, and point-triangle wrappers above. -/
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

/-- Polynomial-level line-169 residual before the line-172 data-processing step.

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
`ζ₁` links and recover the previous evaluated handoff residual. -/
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

/-- Finer residual for the projective completion and paper line-169 handoff.

This package is strictly weaker than
`MainFormalCascadeProjectiveEvaluationHandoffResidual`.  It no longer asks for the
unused Section 6 consistency field inside `UnsymmetrizationBridgePackage`, and it
no longer asks for the pre-projective consistency field inside
`ProjectivizationSelfConsistencyHandoff`: both are reconstructed downstream from the two
paper factor-two role-block estimates and `hpass` via the checked line-116
triangle and Step 5 Schwartz--Zippel wrapper.  The remaining open data are exactly
what is still missing after those mechanical steps:

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

/-- The older line-169 residual contains all fields needed by the finer
completion-transport residual; this coercion documents that the new target is a
strict weakening of the previous one. -/
noncomputable def ofProjectiveEvaluationHandoffResidual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveEvaluationHandoffResidual
      params strategy eps k scalars) :
    MainFormalCascadeProjectiveCompletionTransportResidual params strategy eps k scalars where
  roleMeasurement := residual.roleMeasurement
  pointARightPOVMConsistency := residual.unsymmetrization.pointAConsistency
  leftPOVMPointBConsistency := residual.unsymmetrization.pointBConsistency
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  leftCompletionCloseness := residual.projectivization.leftCompletionCloseness
  rightCompletionCloseness := residual.projectivization.rightCompletionCloseness
  leftProjectiveRightPOVMPolynomialConsistency :=
    residual.leftProjectiveRightPOVMPolynomialConsistency
  rightProjectiveLeftPOVMPolynomialConsistency :=
    residual.rightProjectiveLeftPOVMPolynomialConsistency

/-- View the factor-two role-block fields as the pre-projective target package. -/
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

/-- Assemble the projective-stage targets directly from the finer residual.  This
reconstructs the duplicated pre-projective consistency field from the factor-two
role-block estimates and `hpass`, then combines it with the completion-closeness
fields for line 156. -/
noncomputable def toProjectiveStageTargets
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionTransportResidual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalCascadeProjectiveStageTargets params strategy eps k scalars where
  preSelfConsistency := residual.toPreProjectiveSelfConsistency hpass
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  pointAConsistency := residual.pointAConsistency hpass
  pointBConsistency := residual.pointBConsistency hpass
  fullPolynomialConsistency := by
    intro hpre
    have hpre' : ConsRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
        (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
        scalars.zeta1 := by
      simpa [toPreProjectiveSelfConsistency, toUnsymmetrizedPOVMTargets] using hpre
    exact residual.fullPolynomialConsistency hpre'

end MainFormalCascadeProjectiveCompletionTransportResidual

end Test

end MIPStarRE.LDT
