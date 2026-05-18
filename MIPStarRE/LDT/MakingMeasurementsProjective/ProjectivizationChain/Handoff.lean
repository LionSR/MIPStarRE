import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic

/-!
# Section 5 — projectivization self-consistency handoff

This module contains the self-consistency handoff theorems for the
orthonormalization projectivization chain in the main inductive step.  The statements
convert pre-projective consistency and completion closeness into the projective
consistency estimates used after `Q^A` and `Q^B` have been built.
-/

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.LDT

namespace ProjectivizationSelfConsistencyHandoff

/-- Projective self-consistency for the completed measurements.

From line-131 consistency `G_A ⊗ I ≃_{ζ₁} I ⊗ G_B`,
`prop:simeq-to-approx` gives `G_A ⊗ I ≈_{2ζ₁} I ⊗ G_B`.  Combining this with
the two completion closeness estimates by the **three-step** squared-distance
triangle gives

`Q_A ⊗ I ≈_{3(ζ₂ + 2ζ₁ + ζ₂)} I ⊗ Q_B`,

which is exactly the paper's `ζ₃ = 6ζ₁ + 6ζ₂`
(`inductive_step.tex:154--158`). -/
theorem fullPolynomialConsistency {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    {G_A G_B : Measurement Outcome ι} {Q_A Q_B : ProjMeas Outcome ι}
    {ζ₁ ζ₂ : Error}
    (handoff : ProjectivizationSelfConsistencyHandoff ψ G_A G_B Q_A Q_B ζ₁ ζ₂) :
    MIPStarRE.LDT.Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas)
      (6 * ζ₁ + 6 * ζ₂) := by
  let GLeft : IdxMeas Unit Outcome ι := fun _ => G_A
  let GRight : IdxMeas Unit Outcome ι := fun _ => G_B
  have hpreMeas : ConsRel ψ (uniformDistribution Unit)
      (IdxMeas.toIdxSubMeas GLeft) (IdxMeas.toIdxSubMeas GRight) ζ₁ := by
    simpa [GLeft, GRight, ldt_simp] using
      handoff.preProjectiveConsistency
  have hGBip :=
    MIPStarRE.LDT.Preliminaries.simeqToApprox ψ (uniformDistribution Unit)
      GLeft GRight ζ₁ hpreMeas
  have hmid : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily G_B.toSubMeas.liftRight)
      (2 * ζ₁) := by
    constructor
    simpa [GLeft, GRight, ldt_simp] using
      hGBip.leftRightSquaredDistanceBound
  have hleftSymm : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas.liftLeft)
      (constSubMeasFamily G_A.toSubMeas.liftLeft) ζ₂ := by
    exact MIPStarRE.LDT.Preliminaries.sddRel_symm ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily Q_A.toSubMeas.liftLeft) ζ₂
      handoff.leftCompletionCloseness
  have htri := MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_triangle_three ψ
    (uniformDistribution Unit)
    (constSubMeasFamily Q_A.toSubMeas.liftLeft)
    (constSubMeasFamily G_A.toSubMeas.liftLeft)
    (constSubMeasFamily G_B.toSubMeas.liftRight)
    (constSubMeasFamily Q_B.toSubMeas.liftRight)
    ζ₂ (2 * ζ₁) ζ₂ hleftSymm hmid handoff.rightCompletionCloseness
  constructor
  change sddError ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas.liftLeft)
      (constSubMeasFamily Q_B.toSubMeas.liftRight) ≤ 6 * ζ₁ + 6 * ζ₂
  calc
    sddError ψ (uniformDistribution Unit)
        (constSubMeasFamily Q_A.toSubMeas.liftLeft)
        (constSubMeasFamily Q_B.toSubMeas.liftRight)
        ≤ 3 * (ζ₂ + 2 * ζ₁ + ζ₂) := htri.squaredDistanceBound
    _ = 6 * ζ₁ + 6 * ζ₂ := by ring

/-- The honest Alice-side transport statement derivable from the existing
projectivization handoff alone has the generic `triangleSub` loss
`ζ₁ + sqrt ζ₂`.

This theorem is useful as a checked comparison point for the orthonormalization
blocker: it shows exactly what the current SDD-closeness API provides without
the stronger match-mass preservation invariant above. -/
theorem leftConsistency_with_triangleSub_loss {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)} (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} {Q_A Q_B : ProjMeas Outcome ι}
    {ζ₁ ζ₂ : Error}
    (handoff : ProjectivizationSelfConsistencyHandoff ψ G_A G_B Q_A Q_B ζ₁ ζ₂) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      (ζ₁ + Real.sqrt ζ₂) := by
  let GLeft : IdxMeas Unit Outcome ι := fun _ => G_A
  let GRight : IdxMeas Unit Outcome ι := fun _ => G_B
  let QLeft : IdxMeas Unit Outcome ι := fun _ => Q_A.toMeasurement
  have hAC : ConsRel ψ (uniformDistribution Unit)
      (IdxMeas.toIdxSubMeas GLeft) (IdxMeas.toIdxSubMeas GRight) ζ₁ := by
    simpa [GLeft, GRight, constSubMeasFamily, IdxMeas.toIdxSubMeas]
      using handoff.preProjectiveConsistency
  have hAB : SDDRel ψ (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas GLeft))
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas QLeft)) ζ₂ := by
    simpa [GLeft, QLeft, constSubMeasFamily, IdxMeas.toIdxSubMeas,
      IdxSubMeas.liftLeft] using handoff.leftCompletionCloseness
  have h := MIPStarRE.LDT.Preliminaries.triangleSub ψ (uniformDistribution Unit) hψ
      (uniformDistribution_weight_sum_le_one Unit) GLeft QLeft
      (IdxMeas.toIdxSubMeas GRight) ζ₁ ζ₂ hAC hAB
  simpa [GLeft, GRight, QLeft, constSubMeasFamily, IdxMeas.toIdxSubMeas] using h

/-- The honest Bob-side transport available from the existing projectivization
handoff alone, before applying any permutation-symmetry flip, also incurs the
`ζ₁ + sqrt ζ₂` `triangleSub` loss. -/
theorem rightConsistency_with_triangleSub_loss {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)} (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} {Q_A Q_B : ProjMeas Outcome ι}
    {ζ₁ ζ₂ : Error}
    (handoff : ProjectivizationSelfConsistencyHandoff ψ G_A G_B Q_A Q_B ζ₁ ζ₂) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas)
      (ζ₁ + Real.sqrt ζ₂) := by
  let GLeft : IdxMeas Unit Outcome ι := fun _ => G_A
  let GRight : IdxMeas Unit Outcome ι := fun _ => G_B
  let QRight : IdxMeas Unit Outcome ι := fun _ => Q_B.toMeasurement
  have hAB : ConsRel ψ (uniformDistribution Unit)
      (IdxMeas.toIdxSubMeas GLeft) (IdxMeas.toIdxSubMeas GRight) ζ₁ := by
    simpa [GLeft, GRight, constSubMeasFamily, IdxMeas.toIdxSubMeas]
      using handoff.preProjectiveConsistency
  have hBD : SDDRel ψ (uniformDistribution Unit)
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas GRight))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas QRight)) ζ₂ := by
    simpa [GRight, QRight, constSubMeasFamily, IdxMeas.toIdxSubMeas,
      IdxSubMeas.liftRight] using handoff.rightCompletionCloseness
  have h := MIPStarRE.LDT.Preliminaries.triangleSub_right ψ (uniformDistribution Unit) hψ
      (uniformDistribution_weight_sum_le_one Unit) (IdxMeas.toIdxSubMeas GLeft)
      GRight QRight ζ₁ ζ₂ hAB hBD
  simpa [GLeft, GRight, QRight, constSubMeasFamily, IdxMeas.toIdxSubMeas] using h

end ProjectivizationSelfConsistencyHandoff

end MIPStarRE.LDT.MakingMeasurementsProjective
