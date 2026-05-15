import MIPStarRE.LDT.Test.MainTheorem.DiagonalCompletion

/-!
# Main-formal final target assembly

Final target projection used by the `mainFormal` assembly.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

namespace MainFormalProjectiveCompletionTransportWitness

/-- Construct the final projective completion-transport witness from a concrete
role-register witness.

Paper origin: `references/ldt-paper/inductive_step.tex:130-173`.

This is the source-shaped internal construction target for the non-vacuous
branch of `mainFormal`.  It reconstructs the paper line-130 cross consistency
from the role witness and constructs the line-130 orthonormalization witness.
The remaining completion step is the explicit proof obligation in
`MainFormalDiagonalCompletionWitness.nonempty_ofDiagonalConsistency`;
no match-mass or diagonal-consistency data is accepted as an extra input.

**Unfaithful:** This construction currently depends transitively on
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_with_matchMass`,
whose exact match-mass preservation conclusion is not yet derived from
`references/ldt-paper/inductive_step.tex:130-173`.  This is documented in
issue #1610.  Elimination: prove the exact construction-level monotonicity from
the paper hypotheses, or route the final theorem through the repaired line-169
estimate with its explicit loss.
-/
theorem nonempty_ofRoleWitness
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleInductionWitness : MainFormalRoleInductionWitness params strategy eps hpass k) :
    Nonempty (MainFormalProjectiveCompletionTransportWitness
      params strategy eps k scalars) := by
  have hpre := roleInductionWitness.diagonalConsistency scalars
  rcases MainFormalDiagonalOrthonormalizationWitness.nonempty_ofDiagonalConsistency
      hpre with ⟨orthWitness⟩
  have hcompletion :
      Nonempty (MainFormalDiagonalCompletionWitness
        params strategy eps k scalars (roleInductionWitness.roleWitness scalars)) :=
    MainFormalDiagonalCompletionWitness.nonempty_ofDiagonalConsistency
      orthWitness hpre
  rcases hcompletion with ⟨completion⟩
  exact ⟨completion.toProjectiveCompletionTransportWitness hsmall hpre⟩

end MainFormalProjectiveCompletionTransportWitness

namespace MainFormalProjectiveCompletionTransportWitness

/-- Convert the reconstructed line-156 projective approximation into the native
`eq:third-goal` self-consistency estimate.

The only mathematical step performed here is the projective converse of
`prop:simeq-to-approx`: for projective measurements, an `≈_{ζ₃}` relation gives
`≃_{ζ₃/2}`, which is exactly paper `eq:third-goal`
(`references/ldt-paper/inductive_step.tex:159-162`). -/
theorem selfConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (witness : MainFormalProjectiveCompletionTransportWitness
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily witness.leftMeasurement.toSubMeas)
      (constSubMeasFamily witness.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2) := by
  let leftConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => witness.leftMeasurement
  let rightConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => witness.rightMeasurement
  let pre := witness.toPreProjectiveSelfConsistency hpass
  have hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM witness.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM witness.roleMeasurement).toSubMeas)
      scalars.zeta1 := by
    simpa [
      pre,
      MainFormalProjectiveCompletionTransportWitness.toPreProjectiveSelfConsistency,
      MainFormalProjectiveCompletionTransportWitness.toUnsymmetrizedPOVMTargets
    ] using pre.fullSelfConsistency
  have happroxLine := witness.fullPolynomialConsistency hpre
  have happroxAtZeta :
      Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
        (IdxProjMeas.toIdxSubMeas leftConst)
        (IdxProjMeas.toIdxSubMeas rightConst)
        scalars.zeta3 := by
    change Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily witness.leftMeasurement.toSubMeas)
      (constSubMeasFamily witness.rightMeasurement.toSubMeas)
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
  simpa [leftConst, rightConst, constSubMeasFamily, IdxProjMeas.toIdxSubMeas] using hcons

/-- Final packaging step for `thm:main-formal` once the projective-completion
transport witness has been constructed.

* `eq:one-goal` (lines 175--181):
  $A^{\mathrm A,u}_a \otimes I \simeq_{\zeta_4}
    I \otimes Q^{\mathrm B}_{[g(u)=a]}$;
* `eq:another-goal` (lines 182--185):
  $I \otimes A^{\mathrm B,u}_a \simeq_{\zeta_4}
    Q^{\mathrm A}_{[g(u)=a]} \otimes I$;
* `eq:third-goal` (lines 160--162):
  $Q^{\mathrm A}_g \otimes I \simeq_{\zeta_3/2} I \otimes Q^{\mathrm B}_g$.

This theorem performs only the Step 8 weakening from the paper cascade errors
to `mainFormalError` using `ConsRel.mono`; the substantive construction is in
the projective-completion transport witness. -/
theorem toMainFormal {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (witness : MainFormalProjectiveCompletionTransportWitness
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
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
  refine ⟨witness.leftMeasurement, witness.rightMeasurement, ?_, ?_, ?_⟩
  · exact ConsRel.mono
      (MainFormalCascadeScalars.zeta4_le_mainFormalError scalars)
      (witness.pointAConsistency hpass)
  · exact ConsRel.mono
      (MainFormalCascadeScalars.zeta4_le_mainFormalError scalars)
      (witness.pointBConsistency hpass)
  · exact ConsRel.mono
      (MainFormalCascadeScalars.zeta3_div_two_le_mainFormalError scalars)
      (witness.selfConsistency hpass)

end MainFormalProjectiveCompletionTransportWitness

end Test

end MIPStarRE.LDT
