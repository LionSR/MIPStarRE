import MIPStarRE.LDT.Test.MainTheorem.RoleRegister

/-!
# Unsymmetrized target records

Unsymmetrization and projective-stage targets for the `mainFormal` assembly.
This module records the unsymmetrized POVM targets supplied by the
existing factor-two unsymmetrization estimates from
`Test/Unsymmetrization.lean` and applies the checked Step 5
Schwartz–Zippel bridge in `MainFormalCascadePreProjectiveSelfConsistency`
to convert an evaluated pre-projective link into the full-polynomial
self-consistency relation at error `ζ₁`.  The subsequent stage-target
structures (`MainFormalCascadeUnsymmetrizedPOVMTargets`,
`MainFormalCascadeTargets`,
`MainFormalCascadeTransportTargets`,
`MainFormalCascadeProjectiveStageTargets`) form the cascade that
carries the unsymmetrized POVMs through the projective-consistency
handoff to the native `ζ₄` point-consistency targets.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  factor-two unsymmetrization estimates (`\label{eq:cons-a}`,
  `\label{eq:cons-b}`; lines 104–108), cross-consistency chain
  (`\label{eq:G-self-consistency}`; lines 109–133), and projective
  assembly (lines 134–172).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{rem:main-formal-unsymmetrization-bridge}` and
  `\label{rem:main-formal-lean-residual-records}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Evaluate a polynomial-valued complete measurement at every point.

The public `polynomialEvaluationFamily` forgets completeness because most later
statements only need submeasurements.  The triangle inequality used in the
main-formal assembly is stated for complete measurements, so this local helper
keeps the same postprocessing while retaining the proof that totals remain `1`. -/
noncomputable def polynomialEvaluationMeasurementFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (G : Measurement (Polynomial params) ι) :
    IdxMeas (Point params) (Fq params) ι :=
  fun u =>
    { toSubMeas := evaluateAt params u G.toSubMeas
      total_eq_one := by
        simpa [evaluateAt, postprocess_total] using G.total_eq_one }

/-- Paper lines 84--117 after applying the Section 6 polynomial measurement and
unsymmetrizing it.

The fields are the two `2σ` consistency estimates obtained from the role-register
block extraction, corresponding to `eq:cons-a` and `eq:cons-b` in
`references/ldt-paper/inductive_step.tex` lines 97--109.  The theorem
`toPreProjectiveSelfConsistency` below combines these with the original
point-measurement agreement from the test to prove paper line 116 by
`prop:simeq-triangle-inequality`. -/
structure MainFormalCascadeUnsymmetrizedPOVMTargets
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The POVM denoted $G^{\mathrm A}$ after unsymmetrizing the Section 6 measurement. -/
  leftPOVM : Measurement (Polynomial params) ι
  /-- The POVM denoted $G^{\mathrm B}$ after unsymmetrizing the Section 6 measurement. -/
  rightPOVM : Measurement (Polynomial params) ι
  /-- Paper `eq:cons-a`: $G^{\mathrm A}_{[g(u)=a]}\otimes I
  \simeq_{2\sigma} I\otimes A^{\mathrm B,u}_a$. -/
  leftPOVMPointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftPOVM.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * scalars.sigma)
  /-- Paper `eq:cons-b`: $A^{\mathrm A,u}_a\otimes I
  \simeq_{2\sigma} I\otimes G^{\mathrm B}_{[g(u)=a]}$. -/
  pointARightPOVMConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightPOVM.toSubMeas)
      (2 * scalars.sigma)

namespace MainFormalCascadeUnsymmetrizedPOVMTargets

/-- Build the line-97--109 unsymmetrized POVM target package from the standalone
Step 3 bridge data.

Paper origin: `references/ldt-paper/inductive_step.tex:97-109`.

The extracted POVMs are definitionally the principal role blocks
`unsymmetrizedLeftPOVM G` and `unsymmetrizedRightPOVM G` supplied by
`MIPStarRE.LDT.Test.Unsymmetrization`; the two consistency fields are exactly the
factor-two estimates recorded in `UnsymmetrizationBridgePackage`. -/
noncomputable def ofUnsymmetrizationBridge
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (G : Measurement (Polynomial params) (Role × ι))
    (bridge : UnsymmetrizationBridgePackage params strategy G scalars.sigma) :
    MainFormalCascadeUnsymmetrizedPOVMTargets params strategy eps k scalars where
  leftPOVM := unsymmetrizedLeftPOVM G
  rightPOVM := unsymmetrizedRightPOVM G
  leftPOVMPointBConsistency := bridge.pointBConsistency
  pointARightPOVMConsistency := bridge.pointAConsistency

end MainFormalCascadeUnsymmetrizedPOVMTargets

/-- The geometry/transport part of the remaining Section 3 assembly at the exact
cascade errors.

Compared with `MainFormalNativeTargets`, this package removes the final Step 8
weakening obligations: the point and self-consistency errors are fixed to the
paper's cascade quantities derived from `MainFormalCascadeScalars`. Constructing
this package is still the substantive unsymmetrization, Schwartz--Zippel, and
projectivization work of `inductive_step.tex` lines 84--185. -/
structure MainFormalCascadeTargets
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ) where
  /-- Scalar side conditions and the paper-defined `ν, σ, ζᵢ` cascade. -/
  scalars : MainFormalCascadeScalars params eps k
  /-- The projective measurement denoted $Q^{\mathrm A}$ in the paper. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The projective measurement denoted $Q^{\mathrm B}$ in the paper. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Native form of `eq:one-goal` at the paper-defined `ζ₄`. -/
  pointAConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      scalars.zeta4
  /-- Native form of `eq:another-goal` at the paper-defined `ζ₄`. -/
  pointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      scalars.zeta4
  /-- Native form of `eq:third-goal` at the paper-defined `ζ₃/2`. -/
  selfConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)

/-- The transport-only part of the remaining Section 3 assembly once the scalar
cascade has been discharged.

Compared with `MainFormalCascadeTargets`, this package is parameterized by an
already-constructed `MainFormalCascadeScalars`. The field shapes intentionally
mirror the transport fields of `MainFormalCascadeTargets`, so downstream changes
to the native `ConsRel` targets should keep the two records synchronized. It
therefore records only the unsymmetrization, Schwartz--Zippel, and
projectivization targets from `inductive_step.tex` lines 84--185. -/
structure MainFormalCascadeTransportTargets
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The projective measurement denoted $Q^{\mathrm A}$ in the paper. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The projective measurement denoted $Q^{\mathrm B}$ in the paper. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Native form of `eq:one-goal` at the paper-defined `ζ₄`. -/
  pointAConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      scalars.zeta4
  /-- Native form of `eq:another-goal` at the paper-defined `ζ₄`. -/
  pointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      scalars.zeta4
  /-- Native form of `eq:third-goal` at the paper-defined `ζ₃/2`. -/
  selfConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)

/-- The pre-projectivization Step 5 handoff for `mainFormal`.

This record stops at paper line 116, before the Schwartz--Zippel expansion.  The
field `evaluatedSelfConsistency` is the evaluated consistency estimate

`G^A_[g(u)=a] \otimes I \simeq_{2σ + 2√(3ε+2σ)} I \otimes G^B_[g(u)=a]`.

The theorem `fullSelfConsistency` below applies the already-formalized Step 5
Schwartz--Zippel bridge (`inductive_step.tex` lines 119--133) to obtain the
full-polynomial consistency estimate at exactly `ζ₁`. -/
structure MainFormalCascadePreProjectiveSelfConsistency
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The POVM denoted $G^{\mathrm A}$ in the paper, before projectivization. -/
  leftPOVM : Measurement (Polynomial params) ι
  /-- The POVM denoted $G^{\mathrm B}$ in the paper, before projectivization. -/
  rightPOVM : Measurement (Polynomial params) ι
  /-- Paper line 116, before the Step 5 Schwartz--Zippel loss `md/q`. -/
  evaluatedSelfConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftPOVM.toSubMeas)
      (polynomialEvaluationFamily params rightPOVM.toSubMeas)
      (2 * scalars.sigma + 2 * Real.sqrt (3 * eps + 2 * scalars.sigma))

namespace MainFormalCascadePreProjectiveSelfConsistency

/-- Step 5 of `mainFormal`: evaluated consistency plus Schwartz--Zippel gives
full-polynomial consistency at the paper-defined error `ζ₁`.

This is the Lean counterpart of `inductive_step.tex` lines 119--133.  The
algebraic expansion and the `md/q` collision bound are both already proved in
`MIPStarRE.LDT.Test.SchwartzZippelStep`; this theorem only specializes that API
to the cascade notation used by the main theorem. -/
theorem fullSelfConsistency {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (pre : MainFormalCascadePreProjectiveSelfConsistency params strategy eps k scalars) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily pre.leftPOVM.toSubMeas)
      (constSubMeasFamily pre.rightPOVM.toSubMeas)
      scalars.zeta1 := by
  simpa [MainFormalCascadeScalars.zeta1, cascadeZeta1, Nat.cast_mul, add_assoc,
    add_left_comm, add_comm] using
    (mainFormalStep5_selfConsistency_ofExpansionResidual params strategy.state
      strategy.isNormalized pre.leftPOVM.toSubMeas pre.rightPOVM.toSubMeas
      (2 * scalars.sigma + 2 * Real.sqrt (3 * eps + 2 * scalars.sigma))
      pre.evaluatedSelfConsistency)

end MainFormalCascadePreProjectiveSelfConsistency

namespace MainFormalCascadeUnsymmetrizedPOVMTargets

/-- Paper line 116 from the two unsymmetrized consistency estimates and the
original point-measurement agreement.

This is the `prop:simeq-triangle-inequality` step in
`references/ldt-paper/inductive_step.tex` lines 110--117.  The two fields of
`MainFormalCascadeUnsymmetrizedPOVMTargets` provide the `2σ` links
`eq:cons-a`/`eq:cons-b`; `SameSpaceProjStrat.point_agreement_le_three_mul` provides the
middle `3ε` agreement from the low-individual-degree test. -/
noncomputable def toPreProjectiveSelfConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (targets : MainFormalCascadeUnsymmetrizedPOVMTargets params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalCascadePreProjectiveSelfConsistency params strategy eps k scalars where
  leftPOVM := targets.leftPOVM
  rightPOVM := targets.rightPOVM
  evaluatedSelfConsistency := by
    let leftEval : IdxMeas (Point params) (Fq params) ι :=
      polynomialEvaluationMeasurementFamily params targets.leftPOVM
    let rightEval : IdxMeas (Point params) (Fq params) ι :=
      polynomialEvaluationMeasurementFamily params targets.rightPOVM
    let pointA : IdxMeas (Point params) (Fq params) ι :=
      IdxProjMeas.toIdxMeas strategy.pointMeasurementA
    let pointB : IdxMeas (Point params) (Fq params) ι :=
      IdxProjMeas.toIdxMeas strategy.pointMeasurementB
    have hleft :
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxMeas.toIdxSubMeas leftEval)
          (IdxMeas.toIdxSubMeas pointB)
          (2 * scalars.sigma) := by
      change ConsRel strategy.state (uniformDistribution (Point params))
        (polynomialEvaluationFamily params targets.leftPOVM.toSubMeas)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
        (2 * scalars.sigma)
      exact targets.leftPOVMPointBConsistency
    have hpoint :
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxMeas.toIdxSubMeas pointA)
          (IdxMeas.toIdxSubMeas pointB)
          (3 * eps) := by
      exact ⟨SameSpaceProjStrat.point_agreement_le_three_mul hpass⟩
    have hright :
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxMeas.toIdxSubMeas pointA)
          (IdxMeas.toIdxSubMeas rightEval)
          (2 * scalars.sigma) := by
      change ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (polynomialEvaluationFamily params targets.rightPOVM.toSubMeas)
        (2 * scalars.sigma)
      exact targets.pointARightPOVMConsistency
    have htriangle :=
      Preliminaries.simeqTriangleInequality strategy.state
        (uniformDistribution (Point params)) strategy.isNormalized
        (uniformDistribution_weight_sum_le_one (Point params))
        leftEval pointB pointA rightEval
        (2 * scalars.sigma) (3 * eps) (2 * scalars.sigma)
        hleft hpoint hright
    simpa [leftEval, rightEval, pointA, pointB, polynomialEvaluationMeasurementFamily]
      using htriangle

end MainFormalCascadeUnsymmetrizedPOVMTargets

namespace MainFormalRolePackageResidual

/-- Reconstruct paper line 130 directly from a concrete Section 6 role residual.

This names the paper-order handoff used several times below: first extract the
role-measurement record, then unsymmetrize it, prove line 116 by the point-measurement
triangle, and finally apply the checked Schwartz--Zippel Step 5 bridge. -/
noncomputable def diagonalConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageResidual params strategy eps hpass k)
    (scalars : MainFormalCascadeScalars params eps k) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM (residual.rolePackage scalars).roleMeasurement).toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM (residual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1 := by
  let rolePackage := residual.rolePackage scalars
  let bridge := rolePackage.toUnsymmetrizationBridge
  let targets : MainFormalCascadeUnsymmetrizedPOVMTargets params strategy eps k scalars :=
    MainFormalCascadeUnsymmetrizedPOVMTargets.ofUnsymmetrizationBridge
      rolePackage.roleMeasurement bridge
  let pre := targets.toPreProjectiveSelfConsistency hpass
  simpa [rolePackage, pre] using pre.fullSelfConsistency

end MainFormalRolePackageResidual

/-- The remaining projective-stage transport package for `mainFormal`.

Compared with `MainFormalCascadeTransportTargets`, this package has already
split off the Step 5 Schwartz--Zippel handoff.  It asks for the line-156
projective approximation as a bridge out of the proved pre-projective
self-consistency at `ζ₁`; the conversion from that `≈_{ζ₃}` statement to the
native `eq:third-goal` consistency statement is proved by
`toTransportTargets` using the projective converse of `prop:simeq-to-approx`.
The two point-consistency targets remain explicit residual fields at the paper's
`ζ₄`, corresponding to `eq:one-goal` and `eq:another-goal`. -/
structure MainFormalCascadeProjectiveStageTargets
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- Pre-projective `G^A,G^B` data through the Step 5 evaluated estimate. -/
  preSelfConsistency :
    MainFormalCascadePreProjectiveSelfConsistency params strategy eps k scalars
  /-- The projective measurement denoted $Q^{\mathrm A}$ in the paper. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The projective measurement denoted $Q^{\mathrm B}$ in the paper. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Native form of `eq:one-goal` at the paper-defined `ζ₄`. -/
  pointAConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      scalars.zeta4
  /-- Native form of `eq:another-goal` at the paper-defined `ζ₄`. -/
  pointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      scalars.zeta4
  /-- Paper line 156, produced from the Step 5 full-polynomial consistency at `ζ₁`
  and the projectivization/completion approximation chain. -/
  fullPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily preSelfConsistency.leftPOVM.toSubMeas)
      (constSubMeasFamily preSelfConsistency.rightPOVM.toSubMeas)
      scalars.zeta1 →
    Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      scalars.zeta3

namespace MainFormalCascadeProjectiveStageTargets

/-- Convert the line-156 projective approximation package into the transport-only
cascade targets.

The only mathematical step performed here is the projective converse of
`prop:simeq-to-approx`: for projective measurements, an `≈_{ζ₃}` relation gives
`≃_{ζ₃/2}`, which is exactly paper `eq:third-goal` (lines 159--162). -/
noncomputable def toTransportTargets {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (targets : MainFormalCascadeProjectiveStageTargets params strategy eps k scalars) :
    MainFormalCascadeTransportTargets params strategy eps k scalars where
  leftMeasurement := targets.leftMeasurement
  rightMeasurement := targets.rightMeasurement
  pointAConsistency := targets.pointAConsistency
  pointBConsistency := targets.pointBConsistency
  selfConsistency := by
    let leftConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => targets.leftMeasurement
    let rightConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => targets.rightMeasurement
    have hpre := targets.preSelfConsistency.fullSelfConsistency
    have happroxLine := targets.fullPolynomialConsistency hpre
    have happroxAtZeta :
        Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
          (IdxProjMeas.toIdxSubMeas leftConst)
          (IdxProjMeas.toIdxSubMeas rightConst)
          scalars.zeta3 := by
      change Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily targets.leftMeasurement.toSubMeas)
        (constSubMeasFamily targets.rightMeasurement.toSubMeas)
        scalars.zeta3
      exact happroxLine
    have happrox :
        Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
          (IdxProjMeas.toIdxSubMeas leftConst)
          (IdxProjMeas.toIdxSubMeas rightConst)
          (2 * (scalars.zeta3 / 2)) := by
      convert happroxAtZeta using 1
      ring
    have hcons :=
      Preliminaries.approxToSimeq strategy.state (uniformDistribution Unit)
        leftConst rightConst (scalars.zeta3 / 2) happrox
    simpa [leftConst, rightConst, constSubMeasFamily, IdxProjMeas.toIdxSubMeas]
      using hcons

end MainFormalCascadeProjectiveStageTargets

end Test

end MIPStarRE.LDT
