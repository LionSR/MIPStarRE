import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.Preliminaries.Completion
import MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPStarRE.LDT.Preliminaries.DistanceBounds
import MIPStarRE.LDT.Preliminaries.Triangles

/-!
# Section 10 — Step 6 (orthonormalize-and-complete chain)

This file formalises **Step 6** of the eight-step pipeline used in the proof of
the main inductive step (`mainFormal`). In the paper, Step 6 is the
"projectivization chain" (`inductive_step.tex` lines 130–149) whose ultimate
goal is to produce projective measurements `Q^A`, `Q^B` close to `G^A`, `G^B`.
That chain has two analytic substeps:

1. **Orthonormalization** (`thm:orthonormalization`, cross-referenced from
   Section 5).
2. **Completion to a measurement** (`prop:completing-to-measurement`).

The completed measurement is then canonically projective: if
`P : ProjSubMeas Outcome ι`, then `P.total` is itself a projection and the
residual effect `I - Σ_a P_a = 1 - P.total` is orthogonal to the repaired
outcome. This file packages that observation so that Step 6 now directly
returns a `ProjMeas` witness.

The main theorem is therefore still named `orthonormalizeAndComplete`, because
its closeness estimate is obtained by composing the orthonormalization and
completion bounds exactly as in the paper, while additionally recording the
projective structure of the canonical completion.

The chain composes two existing pieces of infrastructure together with a short
projective-packaging lemma:

1. **Orthonormalization** (`MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization`,
   in `Theorems.lean`) — produces a projective sub-measurement
   `P : ProjSubMeas Outcome ι` close to `G` in state-dependent distance:
   `G_g ⊗ I ≈_{100·ζ^{1/4}} P_g ⊗ I`.

2. **Completion to a measurement**
   (`MIPStarRE.LDT.Preliminaries.completingToMeasurement`,
   in `Preliminaries/Theorems.lean`) — adjoins the missing mass `I − Σ_a P_a`
   at a distinguished outcome `a*` to produce a measurement `Q` with
   `G_g ⊗ I ≈_{2δ + 4√δ + 2ζ} Q_g ⊗ I` where `δ = 100·ζ^{1/4}`.

3. **Projective packaging of the completion**
   (`MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj`) — upgrades the same
   completed measurement to a `ProjMeas` without changing its underlying POVM.

The composition gives the `ζ₂` of the paper (`inductive_step.tex`, line 149):

    ζ₂ = 2 · (100·ζ^{1/4}) + 4 · √(100·ζ^{1/4}) + 2·ζ
       = 200·ζ^{1/4} + 40·ζ^{1/8} + 2·ζ.

The paper drops the `2·ζ` term in the closed-form `ζ₂ = 200·ζ^{1/4} + 40·ζ^{1/8}`
(it is absorbed when the global error is computed downstream); we keep the
literal output of the two lemmas for proof integrity, and leave the tighter
absorbed form as a downstream calculation.

## Status

- The orthonormalization step is mediated by
  `OrthonormalizationInput`, which now packages only the spectral-truncation
  and locality-preserving repair witnesses for the option-completed
  measurement used in the paper's reduction.
- The completion step uses the **fully-formalized** `completingToMeasurement`
  (`\leanok` in `blueprint/src/chapter/ch03_preliminaries.tex`), so no new
  bridge is introduced here.
- The output `Q` is now a `ProjMeas`. This uses the generic helper
  `Preliminaries.completeAtOutcomeProj`, whose proof relies only on the
  existing facts that `P.total` is a projection and that each `P_a` is
  absorbed by `P.total`.

## References

- Paper: `references/ldt-paper/inductive_step.tex` lines 130–149
  (Step 6 application of `lem:orthonormalization-main-lemma` +
  `prop:completing-to-measurement`).
- Paper: `references/ldt-paper/orthonormalization.tex` lines 67–77
  (`thm:orthonormalization`).
- Paper: `references/ldt-paper/preliminaries.tex` lines 1101–1170
  (`prop:completing-to-measurement`).
- Blueprint: `blueprint/src/chapter/ch10_induction.tex` lines 350–360
  (`eq:G-with-Q-A`).
- Blueprint: `blueprint/src/chapter/ch04_projective.tex`
  (orthonormalization theorem).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
  (completeAtOutcome completeAtOutcomeProj completingToMeasurement)

/-! ### Error functions -/

/-- The combined error of the orthonormalization + completion chain (Step 6).

Substituting `δ := orthonormalizationError ζ = 100·ζ^{1/4}` into the
closeness conclusion of `prop:completing-to-measurement`
(`2·δ + 4·√δ + 2·ζ`) gives

    `2 · (100·ζ^{1/4}) + 4 · √(100·ζ^{1/4}) + 2·ζ
       = 200·ζ^{1/4} + 40·ζ^{1/8} + 2·ζ`.

This is the literal error returned by composing the two existing lemmas.
The paper's `ζ₂ = 200·ζ^{1/4} + 40·ζ^{1/8}` (`inductive_step.tex`, line 149)
absorbs the residual `2·ζ` term into a downstream calculation; the
absorbed form is not needed for the present chain statement. -/
noncomputable def orthonormalizeAndCompleteError (ζ : Error) : Error :=
  2 * orthonormalizationError ζ +
    4 * Real.sqrt (orthonormalizationError ζ) +
    2 * ζ

/-! ### Permutation-invariant right-register transport -/

/-- On a permutation-invariant bipartite state, the state-dependent distance between
right-lifted local submeasurements equals the distance between their left lifts.

This is the Step 6 bookkeeping needed for the Bob-side completion estimate in
`inductive_step.tex` lines 140--147: `orthonormalizeAndComplete` naturally
returns a left-register bound, and the paper also uses the corresponding
right-register bound for $I \otimes G^{\mathrm B}$ and $I \otimes Q^{\mathrm B}$.
This is the submeasurement specialization of
`Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv`. -/
lemma qSDD_liftRight_eq_liftLeft_of_permInv
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (A B : SubMeas Outcome ι) :
    qSDD ψ A.liftRight B.liftRight = qSDD ψ A.liftLeft B.liftLeft := by
  simpa [qSDD, SubMeas.liftRight, SubMeas.liftLeft] using
    MIPStarRE.LDT.Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv
      (ψ := ψ) hperm A.outcome B.outcome

/-- Transport an `SDDRel` bound from left lifts to right lifts on a
permutation-invariant bipartite state. -/
lemma sddRel_liftRight_of_liftLeft_permInv
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) :
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B) δ →
      SDDRel ψ 𝒟 (IdxSubMeas.liftRight A) (IdxSubMeas.liftRight B) δ := by
  intro h
  have hsddeq :
      sddError ψ 𝒟 (IdxSubMeas.liftRight A) (IdxSubMeas.liftRight B) =
        sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B) := by
    unfold sddError avgOver
    refine Finset.sum_congr rfl ?_
    intro q _
    change 𝒟.weight q * qSDD ψ (A q).liftRight (B q).liftRight =
      𝒟.weight q * qSDD ψ (A q).liftLeft (B q).liftLeft
    rw [qSDD_liftRight_eq_liftLeft_of_permInv (ψ := ψ) hperm (A q) (B q)]
  constructor
  rw [hsddeq]
  exact h.squaredDistanceBound

/-! ### Line-156 triangle handoff -/

/-- Residual handoff for the projectivization part of Step 6.

The fields are exactly the hypotheses needed after the orthonormalization and
completion constructions have produced projective measurements `Q_A,Q_B` close to
the pre-projective measurements `G_A,G_B`.  The theorem
`ProjectivizationLine156Handoff.line156Approx` below turns this package into the
paper's line-156 approximation. -/
structure ProjectivizationLine156Handoff
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G_A G_B : Measurement Outcome ι) (Q_A Q_B : ProjMeas Outcome ι)
    (ζ₁ ζ₂ : Error) : Prop where
  /-- Paper line 131, obtained before projectivization. -/
  preProjectiveConsistency :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ₁
  /-- Left-register completion closeness, paper line 146 (`eq:G-with-Q-A`). -/
  leftCompletionCloseness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily Q_A.toSubMeas.liftLeft) ζ₂
  /-- Right-register completion closeness, paper line 147. -/
  rightCompletionCloseness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas.liftRight)
      (constSubMeasFamily Q_B.toSubMeas.liftRight) ζ₂

namespace ProjectivizationLine156Handoff

/-- Step 6 line-156 handoff.

From line-131 consistency `G_A ⊗ I ≃_{ζ₁} I ⊗ G_B`,
`prop:simeq-to-approx` gives `G_A ⊗ I ≈_{2ζ₁} I ⊗ G_B`.  Combining this with
the two completion closeness estimates by the **three-step** squared-distance
triangle gives

`Q_A ⊗ I ≈_{3(ζ₂ + 2ζ₁ + ζ₂)} I ⊗ Q_B`,

which is exactly the paper's `ζ₃ = 6ζ₁ + 6ζ₂`
(`inductive_step.tex:154--158`). -/
theorem line156Approx {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    {G_A G_B : Measurement Outcome ι} {Q_A Q_B : ProjMeas Outcome ι}
    {ζ₁ ζ₂ : Error}
    (handoff : ProjectivizationLine156Handoff ψ G_A G_B Q_A Q_B ζ₁ ζ₂) :
    MIPStarRE.LDT.Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas)
      (6 * ζ₁ + 6 * ζ₂) := by
  let GLeft : IdxMeas Unit Outcome ι := fun _ => G_A
  let GRight : IdxMeas Unit Outcome ι := fun _ => G_B
  have hpreMeas : ConsRel ψ (uniformDistribution Unit)
      (IdxMeas.toIdxSubMeas GLeft) (IdxMeas.toIdxSubMeas GRight) ζ₁ := by
    simpa [GLeft, GRight, constSubMeasFamily, IdxMeas.toIdxSubMeas] using
      handoff.preProjectiveConsistency
  have hGBip :=
    MIPStarRE.LDT.Preliminaries.simeqToApprox ψ (uniformDistribution Unit)
      GLeft GRight ζ₁ hpreMeas
  have hmid : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily G_B.toSubMeas.liftRight)
      (2 * ζ₁) := by
    constructor
    simpa [GLeft, GRight, constSubMeasFamily, IdxMeas.toIdxSubMeas,
      IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
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

end ProjectivizationLine156Handoff

/-! ### Line-169 match-mass monotonicity -/

/-- Match-mass monotonicity invariant needed for the paper's line-169
projectivization transport.

The ordinary Step 6 handoff records only state-dependent-distance closeness
`G_A ≈ Q_A` and `G_B ≈ Q_B`.  Combining those fields with
`prop:triangle-sub` gives a `ζ₁ + sqrt ζ₂` consistency loss, as witnessed by
`ProjectivizationLine156Handoff.leftConsistency_with_triangleSub_loss` and
`ProjectivizationLine156Handoff.rightConsistency_with_triangleSub_loss` below.
The paper-tight line-169 estimate at exactly `ζ₁` therefore needs a stronger
construction-level invariant: replacing `G_A` by `Q_A`, and symmetrically
replacing `G_B` by `Q_B`, must not decrease the diagonal match mass against the
opposite pre-projective measurement.

This structure records that invariant in its primitive match-mass form, rather
than restating the downstream `ConsRel` conclusion.  A future projectivization
constructor can produce this package from additional repair/completion data;
theorems in the namespace turn it into the exact line-169 consistency links. -/
structure ProjectivizationMatchMassMonotonicity
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G_A G_B : Measurement Outcome ι) (Q_A Q_B : ProjMeas Outcome ι) : Prop where
  /-- Alice-side match-mass monotonicity:
  `Q_A` preserves at least as much correlation with `G_B` as `G_A` did. -/
  leftMatchMassPreservation :
    qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≥
      qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas
  /-- Bob-side match-mass monotonicity, in the role-reversed orientation used by
  the line-169 mirror. -/
  rightMatchMassPreservation :
    qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas ≥
      qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas

namespace ProjectivizationMatchMassMonotonicity

/-- Exact Alice-side line-169 consistency from match-mass preservation.

For complete measurements the total-overlap term in `qBipartiteConsDefect` is
unchanged when `G_A` is replaced by `Q_A`; the match-mass inequality therefore
can only decrease the consistency defect. -/
theorem leftConsistency {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    {G_A G_B : Measurement Outcome ι} {Q_A Q_B : ProjMeas Outcome ι}
    (preservation : ProjectivizationMatchMassMonotonicity ψ G_A G_B Q_A Q_B)
    {ζ : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ := by
  rcases hpre with ⟨hpre⟩
  have hdefect :
      qBipartiteConsDefect ψ Q_A.toSubMeas G_B.toSubMeas ≤
        qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas := by
    unfold qBipartiteConsDefect
    have htotal : ev ψ (opTensor Q_A.toSubMeas.total G_B.toSubMeas.total) =
        ev ψ (opTensor G_A.toSubMeas.total G_B.toSubMeas.total) := by
      simp [Q_A.total_eq_one, G_A.total_eq_one]
    have hinner :
        ev ψ (opTensor Q_A.toSubMeas.total G_B.toSubMeas.total) -
            qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≤
          ev ψ (opTensor G_A.toSubMeas.total G_B.toSubMeas.total) -
            qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas := by
      rw [htotal]
      linarith [preservation.leftMatchMassPreservation]
    exact max_le_max le_rfl hinner
  have hpre' : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre
  constructor
  simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefect.trans hpre'

/-- Exact Bob-side line-169 consistency from the role-reversed match-mass
preservation invariant. -/
theorem rightConsistency {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    {G_A G_B : Measurement Outcome ι} {Q_A Q_B : ProjMeas Outcome ι}
    (preservation : ProjectivizationMatchMassMonotonicity ψ G_A G_B Q_A Q_B)
    {ζ : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas)
      (constSubMeasFamily G_A.toSubMeas) ζ) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_B.toSubMeas)
      (constSubMeasFamily G_A.toSubMeas) ζ := by
  rcases hpre with ⟨hpre⟩
  have hdefect :
      qBipartiteConsDefect ψ Q_B.toSubMeas G_A.toSubMeas ≤
        qBipartiteConsDefect ψ G_B.toSubMeas G_A.toSubMeas := by
    unfold qBipartiteConsDefect
    have htotal : ev ψ (opTensor Q_B.toSubMeas.total G_A.toSubMeas.total) =
        ev ψ (opTensor G_B.toSubMeas.total G_A.toSubMeas.total) := by
      simp [Q_B.total_eq_one, G_B.total_eq_one]
    have hinner :
        ev ψ (opTensor Q_B.toSubMeas.total G_A.toSubMeas.total) -
            qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas ≤
          ev ψ (opTensor G_B.toSubMeas.total G_A.toSubMeas.total) -
            qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas := by
      rw [htotal]
      linarith [preservation.rightMatchMassPreservation]
    exact max_le_max le_rfl hinner
  have hpre' : qBipartiteConsDefect ψ G_B.toSubMeas G_A.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre
  constructor
  simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefect.trans hpre'

end ProjectivizationMatchMassMonotonicity

namespace ProjectivizationLine156Handoff

/-- The honest Alice-side line-169 statement derivable from the existing Step 6
handoff alone has the generic `triangleSub` loss `ζ₁ + sqrt ζ₂`.

This theorem is useful as a checked comparison point for the projectivization
blocker: it shows exactly what the current SDD-closeness API provides without
the stronger match-mass preservation invariant above. -/
theorem leftConsistency_with_triangleSub_loss {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)} (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} {Q_A Q_B : ProjMeas Outcome ι}
    {ζ₁ ζ₂ : Error}
    (handoff : ProjectivizationLine156Handoff ψ G_A G_B Q_A Q_B ζ₁ ζ₂) :
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

/-- The honest Bob-side line-169 transport available from the existing Step 6
handoff alone, before applying any permutation-symmetry flip, also incurs the
`ζ₁ + sqrt ζ₂` `triangleSub` loss. -/
theorem rightConsistency_with_triangleSub_loss {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)} (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} {Q_A Q_B : ProjMeas Outcome ι}
    {ζ₁ ζ₂ : Error}
    (handoff : ProjectivizationLine156Handoff ψ G_A G_B Q_A Q_B ζ₁ ζ₂) :
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

end ProjectivizationLine156Handoff

/-! ### Output package -/

set_option linter.unusedFintypeInType false in
/-- Output package for the orthonormalization + completion chain (Step 6 of
the inductive step).

The chain takes a measurement `A : Measurement Outcome ι` together with a
`ζ`-bipartite-self-consistency hypothesis on `A.toSubMeas`, and produces:

* an intermediate projective sub-measurement `P : ProjSubMeas Outcome ι`
  satisfying the orthonormalization closeness `A ≈_{100·ζ^{1/4}} P` (paper
  `orthonormalization.tex` line 67);
* a completed projective measurement `Q : ProjMeas Outcome ι` obtained by
  adjoining the residual `I − Σ_a P_a` at a distinguished outcome `a₀`,
  satisfying the chain closeness
  `A ≈_{orthonormalizeAndCompleteError ζ} Q` (paper `inductive_step.tex`
  line 146, `eq:G-with-Q-A`).

The theorem `orthonormalizeAndComplete` separately records that the returned
`Q` has underlying measurement exactly
`completeAtOutcome P.toSubMeas a0`. Projectivity of that witness is supplied by
`Preliminaries.completeAtOutcomeProj`, so the structure below stores only the
analytic closeness obligations. -/
structure OrthonormalizeAndCompleteStatement
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A : Measurement Outcome ι)
    (P : ProjSubMeas Outcome ι)
    (Q : ProjMeas Outcome ι)
    (a0 : Outcome) (ζ : Error) : Prop where
  /-- The orthonormalization closeness statement
  `A ≈_{orthonormalizationError ζ} P` (paper:
  `orthonormalization.tex` line 67, post-lifting to the bipartite space). -/
  orthonormalizationCloseness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily P.toSubMeas.liftLeft)
      (orthonormalizationError ζ)
  /-- The chain closeness statement
  `A ≈_{orthonormalizeAndCompleteError ζ} Q` (paper:
  `inductive_step.tex` line 146, `eq:G-with-Q-A`). -/
  completedCloseness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily Q.toSubMeas.liftLeft)
      (orthonormalizeAndCompleteError ζ)

namespace OrthonormalizeAndCompleteStatement

/-- Bob/right-register form of the completion closeness in
`OrthonormalizeAndCompleteStatement`.

The main chain theorem records the left-register estimate because the analytic
completion lemma is stated on left lifts. On a permutation-invariant state, the
same squared-distance bound holds after placing both local measurements on the
right register, giving the paper's line-147 estimate for
$I \otimes G^{\mathrm B}$ and $I \otimes Q^{\mathrm B}$. -/
theorem completedCloseness_liftRight
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    {A : Measurement Outcome ι} {P : ProjSubMeas Outcome ι}
    {Q : ProjMeas Outcome ι} {a0 : Outcome} {ζ : Error}
    (stmt : OrthonormalizeAndCompleteStatement ψ A P Q a0 ζ) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftRight)
      (constSubMeasFamily Q.toSubMeas.liftRight)
      (orthonormalizeAndCompleteError ζ) :=
  sddRel_liftRight_of_liftLeft_permInv hperm (uniformDistribution Unit)
    (constSubMeasFamily A.toSubMeas) (constSubMeasFamily Q.toSubMeas)
    (orthonormalizeAndCompleteError ζ) stmt.completedCloseness

end OrthonormalizeAndCompleteStatement

namespace ProjectivizationLine156Handoff

/-- Build the line-156 projectivization handoff from the two
orthonormalize-and-complete statements.

This packages the exact Step 6 producer obligations for the current
`mainFormal` residual outside `Test/MainTheorem.lean`: a pre-projective
consistency proof, the Alice-side completion statement, and the Bob-side
completion statement. The Bob-side statement is transported from left lifts to
right lifts using permutation invariance, matching `inductive_step.tex` lines
146--147. The final argument allows callers to widen the literal composed
completion error to whichever scalar envelope they are using for `ζ₂`. -/
theorem ofOrthonormalizeAndCompleteStatements
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    {G_A G_B : Measurement Outcome ι}
    {P_A P_B : ProjSubMeas Outcome ι}
    {Q_A Q_B : ProjMeas Outcome ι}
    {a_A a_B : Outcome} {ζ ζ₁ ζ₂ : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ₁)
    (leftStmt : OrthonormalizeAndCompleteStatement ψ G_A P_A Q_A a_A ζ)
    (rightStmt : OrthonormalizeAndCompleteStatement ψ G_B P_B Q_B a_B ζ)
    (hζ : orthonormalizeAndCompleteError ζ ≤ ζ₂) :
    ProjectivizationLine156Handoff ψ G_A G_B Q_A Q_B ζ₁ ζ₂ := by
  refine
    { preProjectiveConsistency := hpre
      leftCompletionCloseness := ?_
      rightCompletionCloseness := ?_ }
  · exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono ψ
      (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily Q_A.toSubMeas.liftLeft)
      (orthonormalizeAndCompleteError ζ) ζ₂ hζ leftStmt.completedCloseness
  · exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono ψ
      (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas.liftRight)
      (constSubMeasFamily Q_B.toSubMeas.liftRight)
      (orthonormalizeAndCompleteError ζ) ζ₂ hζ
      (rightStmt.completedCloseness_liftRight hperm)

end ProjectivizationLine156Handoff

/-! ### Main theorem -/

set_option linter.unusedFintypeInType false in
/-- **Step 6 of the inductive step**: orthonormalize-and-complete chain.

Given:
* a permutation-invariant, normalized bipartite state `ψ`;
* a measurement `A : Measurement Outcome ι` with bipartite strong
  self-consistency at level `ζ`
  (paper: `inductive_step.tex` line 130, `eq:G-self-consistency`);
* a distinguished outcome `a₀ : Outcome` to absorb the residual mass during
  completion (paper: line 143, `prop:completing-to-measurement`);
* the orthonormalization bridge package carrying the spectral-truncation and
  locality-preserving repair witnesses for the option-completed measurement,

we obtain a projective sub-measurement `P` together with a projective
measurement `Q` satisfying the chain bound
`A ≈_{orthonormalizeAndCompleteError ζ} Q` from
`inductive_step.tex` line 146 (`eq:G-with-Q-A`).

The analytic part of the proof is a direct composition of the two existing
lemmas:
* `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization`
  (Step 6a; `orthonormalization.tex` line 67);
* `MIPStarRE.LDT.Preliminaries.completingToMeasurement`
  (Step 6b; `preliminaries.tex` line 1101).

The extra projective structure on `Q` comes from
`MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj`, which shows that the same
completed measurement is already projective.

The error `orthonormalizeAndCompleteError ζ` is *definitionally equal* to
`2 · orthonormalizationError ζ + 4 · √(orthonormalizationError ζ) + 2·ζ`,
which matches the closeness conclusion of `completingToMeasurement` after
substituting `δ := orthonormalizationError ζ`. -/
theorem orthonormalizeAndComplete
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (hperm : PermInvState ψ)
    (A : Measurement Outcome ι) (a0 : Outcome) (ζ : Error)
    (hssc :
      BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ)
    (hbridge : OrthonormalizationInput ψ A.toSubMeas ζ) :
    ∃ P : ProjSubMeas Outcome ι, ∃ Q : ProjMeas Outcome ι,
      Q.toMeasurement = completeAtOutcome P.toSubMeas a0 ∧
        OrthonormalizeAndCompleteStatement ψ A P Q a0 ζ := by
  -- Step 6a: apply orthonormalization to `A.toSubMeas`.
  obtain ⟨P, hClose⟩ :=
    orthonormalization (Outcome := Outcome) (ι := ι) ψ hperm hψ
      A.toSubMeas ζ hssc hbridge
  -- Step 6b: use the existing completion bound for the canonical completion
  -- of `P`, then repackage that same completed measurement as a `ProjMeas`.
  have hCompletedCloseness :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas.liftLeft)
        (constSubMeasFamily (completeAtOutcome P.toSubMeas a0).toSubMeas.liftLeft)
        (orthonormalizeAndCompleteError ζ) := by
    obtain ⟨Q, hQeq, hQstmt⟩ :=
      completingToMeasurement (Outcome := Outcome) (ι := ι) ψ hperm hψ
        A P.toSubMeas a0 (orthonormalizationError ζ) ζ hssc hClose
    simpa [orthonormalizeAndCompleteError, hQeq] using
      hQstmt.closenessAfterCompletion
  refine ⟨P, completeAtOutcomeProj P a0, rfl, ?_⟩
  refine
    { orthonormalizationCloseness := hClose
      completedCloseness := ?_ }
  simpa using hCompletedCloseness

end MIPStarRE.LDT.MakingMeasurementsProjective
