import MIPStarRE.LDT.Tactic.LdtSimp
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities
import MIPStarRE.LDT.Preliminaries.Completion
import MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPStarRE.LDT.Preliminaries.DistanceBounds
import MIPStarRE.LDT.Preliminaries.Triangles

/-!
# Section 10 — Step 6 (orthonormalize-and-complete chain)

This file formalises **Step 6** of the eight-step proof of the main inductive
step (`mainFormal`). In the paper, Step 6 is the orthonormalization and
completion argument (`inductive_step.tex` lines 130–149) whose ultimate goal is
to produce projective measurements `Q^A`, `Q^B` close to `G^A`, `G^B`. That
argument has two analytic substeps:

1. **Orthonormalization** (`thm:orthonormalization`, cross-referenced from
   Section 5).
2. **Completion to a measurement** (`prop:completing-to-measurement`).

The completed measurement is then canonically projective: if
`P : ProjSubMeas Outcome ι`, then `P.total` is itself a projection and the
residual effect `I - Σ_a P_a = 1 - P.total` is orthogonal to the repaired
outcome. This file records that observation so that Step 6 now directly
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

The composition gives the literal completion scalar
(`inductive_step.tex`, line 149 plus `prop:completing-to-measurement`):

    ζ₂ = 2 · (100·ζ^{1/4}) + 4 · √(100·ζ^{1/4}) + 2·ζ
       = 200·ζ^{1/4} + 40·ζ^{1/8} + 2·ζ.

The paper prints the closed-form `ζ₂ = 200·ζ^{1/4} + 40·ζ^{1/8}`.  The Lean
cascade uses the slightly widened absorbed scalar
`200·ζ^{1/4} + 42·ζ^{1/8}` downstream, since in the non-vacuous regime
`0 ≤ ζ ≤ 1` gives `2·ζ ≤ 2·ζ^{1/8}`.

## Status

- The orthonormalization step is mediated by
  `OrthonormalizationInput`, which now carries only the truncation
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
  (completeAtOutcome completeAtOutcomeProj completeAtOutcomeProj_toMeasurement
    completingToMeasurement)

/-! ### Error functions -/

/-- The combined error of the orthonormalization + completion chain (Step 6).

Substituting `δ := orthonormalizationError ζ = 100·ζ^{1/4}` into the
closeness conclusion of `prop:completing-to-measurement`
(`2·δ + 4·√δ + 2·ζ`) gives

    `2 · (100·ζ^{1/4}) + 4 · √(100·ζ^{1/4}) + 2·ζ
       = 200·ζ^{1/4} + 40·ζ^{1/8} + 2·ζ`.

This is the literal error returned by composing the two existing lemmas.
The paper's printed `ζ₂ = 200·ζ^{1/4} + 40·ζ^{1/8}` (`inductive_step.tex`,
line 149) drops the residual `2·ζ` term; the formal cascade absorbs it into
the widened scalar `200·ζ^{1/4} + 42·ζ^{1/8}`. -/
noncomputable def orthonormalizeAndCompleteError (ζ : Error) : Error :=
  2 * orthonormalizationError ζ +
    4 * Real.sqrt (orthonormalizationError ζ) +
    2 * ζ

/-- Square-root simplification for the orthonormalization error. -/
private theorem sqrt_orthonormalizationError_eq {ζ : Error} (hζ0 : 0 ≤ ζ) :
    Real.sqrt (orthonormalizationError ζ) = 10 * Real.rpow ζ (1 / (8 : Error)) := by
  have hsqrt100 : Real.sqrt (100 : Error) = 10 := by
    rw [← Real.sqrt_sq (show (0 : Error) ≤ 10 by norm_num)]
    norm_num
  have hsqrtRpow : Real.sqrt (Real.rpow ζ (1 / (4 : Error))) =
      Real.rpow ζ (1 / (8 : Error)) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow (Real.rpow ζ (1 / (4 : Error))) (1 / (2 : Error))
          = Real.rpow ζ ((1 / (4 : Error)) * (1 / (2 : Error))) := by
              simpa using
                (Real.rpow_mul hζ0 (1 / (4 : Error)) (1 / (2 : Error))).symm
      _ = Real.rpow ζ (1 / (8 : Error)) := by norm_num
  unfold orthonormalizationError
  calc
    Real.sqrt (100 * Real.rpow ζ (1 / (4 : Error)))
        = Real.sqrt (100 : Error) *
            Real.sqrt (Real.rpow ζ (1 / (4 : Error))) := by
            rw [Real.sqrt_mul (by norm_num : 0 ≤ (100 : Error))]
    _ = 10 * Real.rpow ζ (1 / (8 : Error)) := by
        rw [hsqrt100, hsqrtRpow]

/-- The formal cascade scalar with coefficient `42` absorbs the literal
orthonormalize-and-complete error in the non-vacuous unit regime. -/
theorem orthonormalizeAndCompleteError_le_absorbedZeta2 {ζ : Error}
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    orthonormalizeAndCompleteError ζ ≤
      200 * Real.rpow ζ (1 / (4 : Error)) +
        42 * Real.rpow ζ (1 / (8 : Error)) := by
  have hζ_le_eighth : ζ ≤ Real.rpow ζ (1 / (8 : Error)) := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_ge' hζ0 hζ1
        (show 0 ≤ 1 / (8 : Error) by positivity)
        (by norm_num : 1 / (8 : Error) ≤ (1 : Error)))
  unfold orthonormalizeAndCompleteError
  rw [sqrt_orthonormalizationError_eq hζ0]
  unfold orthonormalizationError
  nlinarith [hζ_le_eighth]

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

/-- Residual data for the projective-measurement part of Step 6.

The fields are exactly the hypotheses needed after the orthonormalization and
completion constructions have produced projective measurements `Q_A,Q_B` close to
the pre-projective measurements `G_A,G_B`.  The theorem
`ProjectivizationLine156Handoff.line156Approx` below turns this data into the
paper's line-156 approximation. -/
structure ProjectivizationLine156Handoff
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G_A G_B : Measurement Outcome ι) (Q_A Q_B : ProjMeas Outcome ι)
    (ζ₁ ζ₂ : Error) : Prop where
  /-- Paper line 131, obtained before the projective measurements are produced. -/
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

end ProjectivizationLine156Handoff

/-! ### Line-169 match-mass monotonicity -/

/-- Match-mass monotonicity invariant needed for the paper's line-169 replacement step.

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
than restating the downstream `ConsRel` conclusion.  A future constructor can
produce this data from additional repair/completion facts;
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

/-- Completing a projective submeasurement at one outcome can only increase its
diagonal match mass against a fixed right-side submeasurement.

The completed measurement is obtained by adding the positive residual
`1 - P.total` to a single outcome.  The corresponding extra contribution to
`qBipartiteMatchMass` is therefore nonnegative. -/
theorem completeAtOutcomeProj_left_matchMass_ge {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (P : ProjSubMeas Outcome ιA)
    (B : SubMeas Outcome ιB) (a0 : Outcome) :
    qBipartiteMatchMass ψ (completeAtOutcomeProj P a0).toSubMeas B ≥
      qBipartiteMatchMass ψ P.toSubMeas B := by
  classical
  unfold qBipartiteMatchMass
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases ha : a = a0
  · subst a
    have hres_nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ιA) - P.toSubMeas.total :=
      sub_nonneg.mpr P.toSubMeas.total_le_one
    have hextra_nonneg :
        0 ≤ ev ψ (opTensor ((1 : MIPStarRE.Quantum.Op ιA) - P.toSubMeas.total)
          (B.outcome a0)) :=
      ev_nonneg_of_psd ψ _ <| opTensor_nonneg hres_nonneg (B.outcome_pos a0)
    simp [completeAtOutcome, opTensor_add_left_local, ev_add]
    linarith
  · simp [completeAtOutcome, ha]

/-- Constructor for the line-169 match-mass invariant after the canonical
completion step.

It reduces the completed-measurement invariant to the corresponding monotonicity
facts for the projective submeasurements produced by orthonormalization.  The
completion residual contributes only nonnegative diagonal mass, so the exact
line-169 `ζ₁` links can later be recovered from these primitive inequalities. -/
theorem of_completeAtOutcomeProj {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)} {G_A G_B : Measurement Outcome ι}
    (P_A P_B : ProjSubMeas Outcome ι) (a_A a_B : Outcome)
    (hleft : qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas ≥
      qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas)
    (hright : qBipartiteMatchMass ψ P_B.toSubMeas G_A.toSubMeas ≥
      qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas) :
    ProjectivizationMatchMassMonotonicity ψ G_A G_B
      (completeAtOutcomeProj P_A a_A) (completeAtOutcomeProj P_B a_B) := by
  refine
    { leftMatchMassPreservation := ?_
      rightMatchMassPreservation := ?_ }
  · exact hleft.trans <|
      completeAtOutcomeProj_left_matchMass_ge ψ P_A G_B.toSubMeas a_A
  · exact hright.trans <|
      completeAtOutcomeProj_left_matchMass_ge ψ P_B G_A.toSubMeas a_B

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

/-! ### Orthonormalization match-mass preservation -/

/-- Match-mass preservation input for the orthonormalization step.

Asserts that the projective submeasurement `P` produced by orthonormalization
preserves at least as much bipartite correlation with a fixed partner
measurement `B` as the original measurement `G` did.  This is a
construction-level property of the specific orthonormalization used; it is NOT
a consequence of `SDDRel` closeness alone.  This structure is a hypothesis
container: it is itself unproved and must be supplied by the orthonormalization
construction.  It is packaged here as a named `Prop` structure so that the
`mainFormal` residual can receive it as a single field and the downstream
`leftConsistency` / `rightConsistency` theorems can recover the exact paper
line-169 `ζ₁` consistency links. -/
structure OrthonormalizationMatchMassPreservation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G : Measurement Outcome ι) (P : ProjSubMeas Outcome ι)
    (B : Measurement Outcome ι) : Prop where
  /-- The projective submeasurement `P` has at least as much diagonal match mass
  with `B` as the original `G` did. -/
  matchMassPreservation :
    qBipartiteMatchMass ψ P.toSubMeas B.toSubMeas ≥
      qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas

namespace OrthonormalizationMatchMassPreservation

/-- Pointwise domination of the source measurement by the orthonormalized
projective submeasurement implies match-mass preservation.

This is the local algebraic interface needed by the paper-tight line-169 route:
once the concrete orthonormalization construction proves
`G.outcome a ≤ P.outcome a` for every outcome `a`, the diagonal overlap against
any fixed partner measurement `B` can only increase.

In the present typing this hypothesis is stronger than the paper's
orthonormalization output.  Since `G` is a full `Measurement` and `P` is a
`ProjSubMeas`, summing `hpoint` forces `P.total = 1`; the positive differences
`P.outcome a - G.outcome a` must then vanish, so the usable case is essentially
pointwise equality `G.outcome a = P.outcome a` for every `a`.  Because `P` is
projective, this is the degenerate no-change situation where the source
measurement is already projective.

Thus this theorem is only a sufficient tautological constructor for that
degenerate scope.  It is not a nontrivial orthonormalization repair proof: the
paper gives state-dependent-distance closeness, not the operator inequality
`G.outcome a ≤ P.outcome a`. -/
theorem of_outcome_le {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    {ψ : QuantumState (ι × ι)} {G : Measurement Outcome ι}
    {P : ProjSubMeas Outcome ι} {B : Measurement Outcome ι}
    (hpoint : ∀ a : Outcome, G.outcome a ≤ P.outcome a) :
    OrthonormalizationMatchMassPreservation ψ G P B := by
  constructor
  unfold qBipartiteMatchMass
  exact Finset.sum_le_sum fun a _ =>
    ev_mono ψ _ _ <| opTensor_mono_left (hpoint a) (B.toSubMeas.outcome_pos a)

/-- Outcomewise expectation-level preservation for the orthonormalization step.

This is weaker than a pointwise operator inequality `G.outcome a ≤ P.outcome a`:
it asks only for the diagonal contribution tested against the fixed partner
measurement `B` and the ambient state `ψ`.  It supplies the exact match-mass
preservation that generic state-dependent-distance closeness alone does not
yield for the paper's line-169 `ζ₁` route, avoiding the `sqrt ζ₂` loss from
`triangleSub`. -/
structure OutcomeExpectationPreservation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G : Measurement Outcome ι) (P : ProjSubMeas Outcome ι)
    (B : Measurement Outcome ι) : Prop where
  /-- Each diagonal outcome contribution is preserved after replacing `G` by
  the projective submeasurement `P`. -/
  outcomeExpectation :
    ∀ a : Outcome,
      ev ψ (opTensor (G.outcome a) (B.outcome a)) ≤
        ev ψ (opTensor (P.outcome a) (B.outcome a))

/-- Summing the outcomewise expectation-level preservation inequalities gives
the primitive match-mass preservation input consumed by the line-169 interface.

This theorem is intentionally state- and partner-dependent.  It does not assert
that orthonormalization is monotone in the operator order; rather, it isolates
the exact non-degenerate expectation-level property that a concrete
orthonormalization repair must supply to avoid the generic `triangleSub` loss. -/
theorem of_outcome_expectation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)}
    {G : Measurement Outcome ι} {P : ProjSubMeas Outcome ι}
    {B : Measurement Outcome ι}
    (hpreserve : OutcomeExpectationPreservation ψ G P B) :
    OrthonormalizationMatchMassPreservation ψ G P B := by
  refine ⟨?_⟩
  unfold qBipartiteMatchMass
  exact Finset.sum_le_sum fun a _ => hpreserve.outcomeExpectation a

/-- The non-degenerate match-mass property needed from a concrete QXP repair.

For a local QXP layer with canonical projective family
`P_a = XHat† * T_a * XHat`, this asks that replacing the source measurement
`G_a` by `P_a` does not reduce the diagonal expectation against the fixed
partner measurement `B_a`, outcome by outcome.  This is an expectation-level
property of the state and partner measurement; it is weaker than pointwise
operator domination and is not implied by the existing SDD-closeness fields. -/
structure QXPLayerOutcomeExpectationPreservation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G B : Measurement Outcome ι) (data : QXPLayerData Outcome ι) : Prop where
  /-- Outcome-level match-mass contribution preserved by the QXP family `P`. -/
  outcomeExpectation :
    ∀ a : Outcome,
      ev ψ (opTensor (G.outcome a) (B.outcome a)) ≤
        ev ψ (opTensor (Pa data a) (B.outcome a))

/-- A QXP-layer outcome-expectation preservation witness supplies the
orthonormalization match-mass input for the canonical `qxpProjSubMeas`.

This is the current narrowed non-degenerate target for the exact line-169 route:
constructing `data` and proving the per-outcome expectation inequalities for
its paper projectors `P_a = XHat† T_a XHat` is sufficient to produce the
`OrthonormalizationMatchMassPreservation` consumed by the Step-6 completion
interface. -/
theorem of_qxp_outcome_expectation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)} {G B : Measurement Outcome ι}
    {data : QXPLayerData Outcome ι}
    (hpreserve : QXPLayerOutcomeExpectationPreservation ψ G B data) :
    OrthonormalizationMatchMassPreservation ψ G (qxpProjSubMeas data) B := by
  exact of_outcome_expectation
    ⟨fun a => by simpa [qxpProjSubMeas_outcome] using hpreserve.outcomeExpectation a⟩

end OrthonormalizationMatchMassPreservation

namespace ProjectivizationMatchMassMonotonicity

/-- Construct `ProjectivizationMatchMassMonotonicity` from match-mass preservation
for the intermediate projective submeasurements produced by orthonormalization.

This is the **P-level producer** that unblocks the exact paper line-169 `ζ₁`
consistency links in `mainFormal`.  Given match-mass inequalities for the
projective submeasurements `P_A`, `P_B` and the fact that the completed
projective measurements `Q_A`, `Q_B` are the canonical completions of `P_A`,
`P_B`, this lifts the preservation through the completion step.

Together with `leftConsistency` and `rightConsistency`, this fills the
`line169MatchMassMonotonicity` field of
`MainFormalPostRolePackageLeftCompletionLine169Residual`. -/
theorem of_submeasurement_match_mass_and_completion
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)} {G_A G_B : Measurement Outcome ι}
    (P_A P_B : ProjSubMeas Outcome ι) (a_A a_B : Outcome)
    (Q_A Q_B : ProjMeas Outcome ι)
    (hQALeft : Q_A.toMeasurement = completeAtOutcome P_A.toSubMeas a_A)
    (hQBRight : Q_B.toMeasurement = completeAtOutcome P_B.toSubMeas a_B)
    (hleftPreservation : OrthonormalizationMatchMassPreservation ψ G_A P_A G_B)
    (hrightPreservation : OrthonormalizationMatchMassPreservation ψ G_B P_B G_A) :
    ProjectivizationMatchMassMonotonicity ψ G_A G_B Q_A Q_B := by
  rcases hleftPreservation with ⟨hleft⟩
  rcases hrightPreservation with ⟨hright⟩
  have hQALeftProj : Q_A = completeAtOutcomeProj P_A a_A :=
    ProjMeas.ext fun a =>
      congrArg (fun (M : Measurement Outcome ι) => M.outcome a)
        (hQALeft.trans (completeAtOutcomeProj_toMeasurement P_A a_A).symm)
  have hQBRightProj : Q_B = completeAtOutcomeProj P_B a_B :=
    ProjMeas.ext fun a =>
      congrArg (fun (M : Measurement Outcome ι) => M.outcome a)
        (hQBRight.trans (completeAtOutcomeProj_toMeasurement P_B a_B).symm)
  rw [hQALeftProj, hQBRightProj]
  exact of_completeAtOutcomeProj P_A P_B a_A a_B hleft hright

/-- Construct the line-169 match-mass invariant from pointwise domination of the
two orthonormalized submeasurements and the canonical completion equalities.

This inherits the degenerate scope of
`OrthonormalizationMatchMassPreservation.of_outcome_le`.  With
`G_A G_B : Measurement Outcome ι` and `P_A P_B : ProjSubMeas Outcome ι`, the
pointwise domination hypotheses are only expected when the source measurements
already agree pointwise with the projective submeasurements (equivalently, in
the no-change/projective-source case).  The theorem is therefore a sufficient
constructor that composes the completion step with tautological preservation
witnesses, not a nontrivial orthonormalization repair proof. -/
theorem of_completion_and_outcome_le
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)} {G_A G_B : Measurement Outcome ι}
    (P_A P_B : ProjSubMeas Outcome ι) (a_A a_B : Outcome)
    (Q_A Q_B : ProjMeas Outcome ι)
    (hQALeft : Q_A.toMeasurement = completeAtOutcome P_A.toSubMeas a_A)
    (hQBRight : Q_B.toMeasurement = completeAtOutcome P_B.toSubMeas a_B)
    (hleftPoint : ∀ a : Outcome, G_A.outcome a ≤ P_A.outcome a)
    (hrightPoint : ∀ a : Outcome, G_B.outcome a ≤ P_B.outcome a) :
    ProjectivizationMatchMassMonotonicity ψ G_A G_B Q_A Q_B :=
  of_submeasurement_match_mass_and_completion P_A P_B a_A a_B Q_A Q_B
    hQALeft hQBRight
    (OrthonormalizationMatchMassPreservation.of_outcome_le hleftPoint)
    (OrthonormalizationMatchMassPreservation.of_outcome_le hrightPoint)

end ProjectivizationMatchMassMonotonicity

namespace ProjectivizationLine156Handoff

/-- The honest Alice-side line-169 statement derivable from the existing Step 6
handoff alone has the generic `triangleSub` loss `ζ₁ + sqrt ζ₂`.

This theorem is useful as a checked comparison point for the Step 6
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

/-! ### Local line-169 repair via pre-completion orthonormalization -/

namespace ProjectivizationLine169Repair

/-- A left-lifted `≈`-statement controls the loss in diagonal bipartite match
mass against a fixed partner measurement by the square root of the SDD error.

This is the single-question `Unit` specialization of
`prop:easy-approx-from-approx_delta`, written directly in the bipartite
`qBipartiteMatchMass` notation used by the Step 6 projectivization chain. -/
private theorem qBipartiteMatchMass_ge_sub_sqrt_of_sdd
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (G : Measurement Outcome ι) (P : SubMeas Outcome ι) (B : Measurement Outcome ι)
    {ε : Error}
    (hclose : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G.toSubMeas.liftLeft)
      (constSubMeasFamily P.liftLeft)
      ε) :
    qBipartiteMatchMass ψ P B.toSubMeas ≥
      qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas - Real.sqrt ε := by
  have hgap :=
    MIPStarRE.LDT.Preliminaries.easyApproxFromApproxDelta ψ hψ
      (uniformDistribution Unit) (uniformDistribution_weight_sum_le_one Unit)
      (constSubMeasFamily G.toSubMeas.liftLeft)
      (constSubMeasFamily P.liftLeft)
      (constSubMeasFamily B.toSubMeas.liftRight)
      ε hclose
  have hgap' :
      |qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas -
          qBipartiteMatchMass ψ P B.toSubMeas| ≤
        Real.sqrt ε := by
    simpa [avgOver, uniformDistribution, constSubMeasFamily,
      qBipartiteMatchMass, SubMeas.liftLeft, SubMeas.liftRight,
      leftTensor_mul_rightTensor_eq_opTensor] using hgap
  have hdiff :
      qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas -
          qBipartiteMatchMass ψ P B.toSubMeas ≤
        Real.sqrt ε :=
    (abs_le.mp hgap').2
  linarith

/-- Completing the orthonormalized submeasurement after comparing it to the
source measurement before completion yields a repaired line-169 transport with
additive loss `√ε`.

This avoids the larger `ζ + √ζ₂` loss that comes from applying `triangleSub`
only after the completion step.  The completion itself contributes no further
loss here, because it only adds nonnegative diagonal match mass at the chosen
outcome. -/
theorem leftConsistency_of_completion_and_sdd
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} (P_A : ProjSubMeas Outcome ι) (a_A : Outcome)
    {ζ ε : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      ζ)
    (horth : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily P_A.toSubMeas.liftLeft)
      ε) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (completeAtOutcomeProj P_A a_A).toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      (ζ + Real.sqrt ε) := by
  let Q_A := completeAtOutcomeProj P_A a_A
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) = 1 :=
    ev_one_of_isNormalized ψ hψ
  have hmatchG :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas) ≤ ζ := by
      simpa [qBipartiteConsDefect, qBipartiteMatchMass, G_A.total_eq_one,
        G_B.total_eq_one, opTensor] using hpre_q
    have hinner :
        ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ :=
      le_trans (le_max_right 0 _) hmax
    simpa [hone] using hinner
  have hmatchP :
      qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas - Real.sqrt ε :=
    qBipartiteMatchMass_ge_sub_sqrt_of_sdd ψ hψ G_A P_A.toSubMeas G_B horth
  have hmatchQ :
      qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas - Real.sqrt ε := by
    calc
      qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas
          ≥ qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas :=
            ProjectivizationMatchMassMonotonicity.completeAtOutcomeProj_left_matchMass_ge
              ψ P_A G_B.toSubMeas a_A
      _ ≥ qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas - Real.sqrt ε := hmatchP
  have hmatchQ' :
      1 - qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≤ ζ + Real.sqrt ε := by
    linarith
  have hdefectQ :
      qBipartiteConsDefect ψ Q_A.toSubMeas G_B.toSubMeas ≤ ζ + Real.sqrt ε := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas) ≤
          ζ + Real.sqrt ε := by
      exact max_le_iff.mpr
        ⟨add_nonneg hζ0 (Real.sqrt_nonneg _), by simpa [hone] using hmatchQ'⟩
    simpa [qBipartiteConsDefect, qBipartiteMatchMass, Q_A.total_eq_one,
      G_B.total_eq_one, opTensor] using hmax
  constructor
  simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefectQ

/-- Bob-side mirror of `leftConsistency_of_completion_and_sdd`, still using the
pre-completion orthonormalization comparison and the fact that completion adds
only nonnegative diagonal match mass. -/
theorem rightConsistency_of_completion_and_sdd
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} (P_B : ProjSubMeas Outcome ι) (a_B : Outcome)
    {ζ ε : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas)
      (constSubMeasFamily G_A.toSubMeas)
      ζ)
    (horth : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas.liftLeft)
      (constSubMeasFamily P_B.toSubMeas.liftLeft)
      ε) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (completeAtOutcomeProj P_B a_B).toSubMeas)
      (constSubMeasFamily G_A.toSubMeas)
      (ζ + Real.sqrt ε) := by
  let Q_B := completeAtOutcomeProj P_B a_B
  have hpre_q : qBipartiteConsDefect ψ G_B.toSubMeas G_A.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_B.toSubMeas G_A.toSubMeas) hpre_q
  have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) = 1 :=
    ev_one_of_isNormalized ψ hψ
  have hmatchG :
      1 - qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas ≤ ζ := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas) ≤ ζ := by
      simpa [qBipartiteConsDefect, qBipartiteMatchMass, G_B.total_eq_one,
        G_A.total_eq_one, opTensor] using hpre_q
    have hinner :
        ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas ≤ ζ :=
      le_trans (le_max_right 0 _) hmax
    simpa [hone] using hinner
  have hmatchP :
      qBipartiteMatchMass ψ P_B.toSubMeas G_A.toSubMeas ≥
        qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas - Real.sqrt ε :=
    qBipartiteMatchMass_ge_sub_sqrt_of_sdd ψ hψ G_B P_B.toSubMeas G_A horth
  have hmatchQ :
      qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas ≥
        qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas - Real.sqrt ε := by
    calc
      qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas
          ≥ qBipartiteMatchMass ψ P_B.toSubMeas G_A.toSubMeas :=
            ProjectivizationMatchMassMonotonicity.completeAtOutcomeProj_left_matchMass_ge
              ψ P_B G_A.toSubMeas a_B
      _ ≥ qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas - Real.sqrt ε := hmatchP
  have hmatchQ' :
      1 - qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas ≤ ζ + Real.sqrt ε := by
    linarith
  have hdefectQ :
      qBipartiteConsDefect ψ Q_B.toSubMeas G_A.toSubMeas ≤ ζ + Real.sqrt ε := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas) ≤
          ζ + Real.sqrt ε := by
      exact max_le_iff.mpr
        ⟨add_nonneg hζ0 (Real.sqrt_nonneg _), by simpa [hone] using hmatchQ'⟩
    simpa [qBipartiteConsDefect, qBipartiteMatchMass, Q_B.total_eq_one,
      G_A.total_eq_one, opTensor] using hmax
  constructor
  simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefectQ

/-- Checked local repair of the paper's line-169 Alice-side replacement step.

Instead of applying `triangleSub` after completion, compare `G_A` directly with
the orthonormalized submeasurement `P_A`, whose `≈`-error is
`orthonormalizationError ζ = 100·ζ^{1/4}`.  The resulting additive loss is
`√(100·ζ^{1/4}) = 10·ζ^{1/8}`, and the completion step itself does not increase
the defect. -/
theorem leftConsistency_with_orthonormalization_loss
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} (P_A : ProjSubMeas Outcome ι) (a_A : Outcome)
    {ζ : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      ζ)
    (horth : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily P_A.toSubMeas.liftLeft)
      (orthonormalizationError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (completeAtOutcomeProj P_A a_A).toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      (ζ + 10 * Real.rpow ζ (1 / (8 : Error))) := by
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  simpa [sqrt_orthonormalizationError_eq hζ0] using
    leftConsistency_of_completion_and_sdd ψ hψ P_A a_A hpre horth

/-- Bob-side mirror of `leftConsistency_with_orthonormalization_loss`. -/
theorem rightConsistency_with_orthonormalization_loss
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} (P_B : ProjSubMeas Outcome ι) (a_B : Outcome)
    {ζ : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas)
      (constSubMeasFamily G_A.toSubMeas)
      ζ)
    (horth : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas.liftLeft)
      (constSubMeasFamily P_B.toSubMeas.liftLeft)
      (orthonormalizationError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (completeAtOutcomeProj P_B a_B).toSubMeas)
      (constSubMeasFamily G_A.toSubMeas)
      (ζ + 10 * Real.rpow ζ (1 / (8 : Error))) := by
  have hpre_q : qBipartiteConsDefect ψ G_B.toSubMeas G_A.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_B.toSubMeas G_A.toSubMeas) hpre_q
  simpa [sqrt_orthonormalizationError_eq hζ0] using
    rightConsistency_of_completion_and_sdd ψ hψ P_B a_B hpre horth

end ProjectivizationLine169Repair

/-! ### Output data -/

set_option linter.unusedFintypeInType false in
/-- Output data for the orthonormalization + completion chain (Step 6 of
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

/-- Build the line-156 Step 6 residual data from the two
orthonormalize-and-complete statements.

This records the exact Step 6 producer obligations for the current
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
* the orthonormalization bridge data carrying the truncation and
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
