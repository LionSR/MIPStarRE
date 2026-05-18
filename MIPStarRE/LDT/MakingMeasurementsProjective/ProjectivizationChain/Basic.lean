import MIPStarRE.LDT.Tactic.LdtSimp
import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities
import MIPStarRE.LDT.Preliminaries.Completion
import MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPStarRE.LDT.Preliminaries.DistanceBounds
import MIPStarRE.LDT.Preliminaries.Triangles

/-!
# Section 5 — basic projectivization data

This module contains the scalar estimates and elementary transport lemmas used
by the orthonormalization projectivization chain.  The mathematical source is the
orthonormalization-and-completion argument in `inductive_step.tex`, lines
130--149, together with the orthonormalization theorem and the completion
proposition cited there.

The declarations here are deliberately prior to the construction of the final
projective measurements.  They record the literal scalar obtained by composing
orthonormalization with completion, its absorbed form in the unit-error regime,
the right-register transport available under permutation invariance, and the
residual hypotheses passed to the self-consistency handoff theorem.  The actual
projective-measurement output theorem is in `ProjectivizationChain.Output`.

The scalar computation is

    ζ₂ = 2 · (100·ζ^{1/4}) + 4 · √(100·ζ^{1/4}) + 2·ζ
       = 200·ζ^{1/4} + 40·ζ^{1/8} + 2·ζ.

The paper prints the closed form `ζ₂ = 200·ζ^{1/4} + 40·ζ^{1/8}`.  The Lean
cascade uses the slightly widened absorbed scalar
`200·ζ^{1/4} + 42·ζ^{1/8}` downstream, since in the non-vacuous regime
`0 ≤ ζ ≤ 1` gives `2·ζ ≤ 2·ζ^{1/8}`.

## Status

- The orthonormalization step uses the source theorem `orthonormalization`.
  The theorem has a tracked proof gap for the sharp paper constant; this file
  no longer exposes its proof-stage construction data as a hypothesis of the
  orthonormalization projectivization output statement.
- The completion step uses the **fully-formalized** `completingToMeasurement`
  (`\leanok` in `blueprint/src/chapter/ch03_preliminaries.tex`), so no new
  bridge is introduced here.
- The output `Q` is now a `ProjMeas`. This uses the generic helper
  `Preliminaries.completeAtOutcomeProj`, whose proof relies only on the
  existing facts that `P.total` is a projection and that each `P_a` is
  absorbed by `P.total`.

## References

- Paper: `references/ldt-paper/inductive_step.tex` lines 130–149
  (application of `lem:orthonormalization-main-lemma` +
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

/-! ### Error functions -/

/-- The combined error of the orthonormalization and completion chain.

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
protected theorem sqrt_orthonormalizationError_eq {ζ : Error} (hζ0 : 0 ≤ ζ) :
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
  have hsqrt :=
    MIPStarRE.LDT.MakingMeasurementsProjective.sqrt_orthonormalizationError_eq hζ0
  rw [hsqrt]
  unfold orthonormalizationError
  nlinarith [hζ_le_eighth]

/-! ### Permutation-invariant right-register transport -/

/-- On a permutation-invariant bipartite state, the state-dependent distance between
right-lifted local submeasurements equals the distance between their left lifts.

This is the bookkeeping needed for the Bob-side completion estimate in
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

/-- Handoff data for the projective-measurement part of the orthonormalization proof.

**Faithful encoding:** The three fields record the paper's pre-projective
consistency and the two completion-closeness estimates from
`references/ldt-paper/inductive_step.tex:130-149`.  This is not a bridge or
residual assumption on a source theorem: `ProjectivizationChain.Output`
constructs the record from the orthonormalization and completion outputs before
`ProjectivizationChain.Handoff` uses it.

The fields are exactly the hypotheses needed after the orthonormalization and
completion constructions have produced projective measurements `Q_A,Q_B` close to
the pre-projective measurements `G_A,G_B`.  The theorem
`ProjectivizationSelfConsistencyHandoff.fullPolynomialConsistency` in
`ProjectivizationChain.Handoff` turns this data into the paper's
projective-measurement consistency estimate. -/
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
