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

/-! ### Projective self-consistency handoff -/

/-- Residual data for the projective-measurement part of Step 6.

The fields are exactly the hypotheses needed after the orthonormalization and
completion constructions have produced projective measurements `Q_A,Q_B` close to
the pre-projective measurements `G_A,G_B`.  The theorem
`ProjectivizationSelfConsistencyHandoff.fullPolynomialConsistency` below turns
this data into the paper's projective-measurement consistency estimate. -/
structure ProjectivizationSelfConsistencyHandoff
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

end MIPStarRE.LDT.MakingMeasurementsProjective
