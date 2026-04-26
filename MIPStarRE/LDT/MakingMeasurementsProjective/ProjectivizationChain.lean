import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.Preliminaries.ComparisonCore
import MIPStarRE.LDT.Preliminaries.Completion
import MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPStarRE.LDT.Preliminaries.Triangles

open scoped BigOperators MatrixOrder Matrix ComplexOrder

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

/-! ### Line-156 triangle handoff -/

/-- Three-vector version of the normalized-trace triangle inequality.

This is the algebra behind the paper's Step 6 use of
`prop:triangle-inequality-for-approx_delta` at `inductive_step.tex:154--158`: if
`X - W` is decomposed as three successive differences, the squared norm is
bounded by `3` times the sum of the three squared norms. -/
private theorem normalizedTrace_triangle_three {n : Type*} [Fintype n]
    (ρ D₁ D₂ D₃ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    Complex.re (MIPStarRE.Quantum.normalizedTrace
        (ρ * (((D₁ + D₂ + D₃)ᴴ) * (D₁ + D₂ + D₃)))) ≤
      3 * (Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁))) +
        Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₂ᴴ * D₂))) +
        Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₃ᴴ * D₃)))) := by
  let S := ((D₁ + D₂ + D₃)ᴴ) * (D₁ + D₂ + D₃)
  let E12 := (D₁ - D₂)ᴴ * (D₁ - D₂)
  let E13 := (D₁ - D₃)ᴴ * (D₁ - D₃)
  let E23 := (D₂ - D₃)ᴴ * (D₂ - D₃)
  let Base := D₁ᴴ * D₁ + D₂ᴴ * D₂ + D₃ᴴ * D₃
  have h_para : S + (E12 + E13 + E23) = Base + Base + Base := by
    simp only [S, E12, E13, E23, Base, Matrix.conjTranspose_add,
      Matrix.conjTranspose_sub, add_mul, mul_add, sub_mul, mul_sub]
    abel
  have h_trace_id :
      MIPStarRE.Quantum.normalizedTrace (ρ * S) +
          (MIPStarRE.Quantum.normalizedTrace (ρ * E12) +
            MIPStarRE.Quantum.normalizedTrace (ρ * E13) +
            MIPStarRE.Quantum.normalizedTrace (ρ * E23)) =
        MIPStarRE.Quantum.normalizedTrace (ρ * Base) +
          MIPStarRE.Quantum.normalizedTrace (ρ * Base) +
          MIPStarRE.Quantum.normalizedTrace (ρ * Base) := by
    calc
      MIPStarRE.Quantum.normalizedTrace (ρ * S) +
          (MIPStarRE.Quantum.normalizedTrace (ρ * E12) +
            MIPStarRE.Quantum.normalizedTrace (ρ * E13) +
            MIPStarRE.Quantum.normalizedTrace (ρ * E23))
          = MIPStarRE.Quantum.normalizedTrace
              (ρ * (S + (E12 + E13 + E23))) := by
              simp [Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add, add_assoc]
      _ = MIPStarRE.Quantum.normalizedTrace (ρ * (Base + Base + Base)) := by
              rw [h_para]
      _ = MIPStarRE.Quantum.normalizedTrace (ρ * Base) +
            MIPStarRE.Quantum.normalizedTrace (ρ * Base) +
            MIPStarRE.Quantum.normalizedTrace (ρ * Base) := by
              simp [Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add, add_assoc]
  have h_re_id := congrArg Complex.re h_trace_id
  simp only [Complex.add_re] at h_re_id
  have h_base :
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * Base)) =
        Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁))) +
        Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₂ᴴ * D₂))) +
        Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₃ᴴ * D₃))) := by
    simp [Base, Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add,
      Complex.add_re, add_assoc]
  have h12 := MIPStarRE.LDT.normalizedTrace_diff_sq_nonneg ρ D₁ D₂ hρ
  have h13 := MIPStarRE.LDT.normalizedTrace_diff_sq_nonneg ρ D₁ D₃ hρ
  have h23 := MIPStarRE.LDT.normalizedTrace_diff_sq_nonneg ρ D₂ D₃ hρ
  rw [h_base] at h_re_id
  linarith

/-- Three-step operator triangle inequality for squared state-dependent distance. -/
private theorem ev_diff_triangle_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y Z W : MIPStarRE.Quantum.Op ι) :
    ev ψ ((X - W)ᴴ * (X - W)) ≤
      3 * (ev ψ ((X - Y)ᴴ * (X - Y)) +
        ev ψ ((Y - Z)ᴴ * (Y - Z)) +
        ev ψ ((Z - W)ᴴ * (Z - W))) := by
  simp only [ev]
  have hdecomp : X - W = (X - Y) + (Y - Z) + (Z - W) := by abel
  rw [hdecomp]
  exact normalizedTrace_triangle_three ψ.density (X - Y) (Y - Z) (Z - W)
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd)

/-- Questionwise three-step triangle inequality for `qSDD`. -/
private lemma qSDD_triangle_three {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B C D : SubMeas Outcome ι) :
    qSDD ψ A D ≤ 3 * (qSDD ψ A B + qSDD ψ B C + qSDD ψ C D) := by
  unfold qSDD qSDDCore
  calc
    ∑ a, ev ψ (((A.outcome a - D.outcome a)ᴴ) *
        (A.outcome a - D.outcome a))
        ≤ ∑ a, 3 * (ev ψ (((A.outcome a - B.outcome a)ᴴ) *
            (A.outcome a - B.outcome a)) +
            ev ψ (((B.outcome a - C.outcome a)ᴴ) *
              (B.outcome a - C.outcome a)) +
            ev ψ (((C.outcome a - D.outcome a)ᴴ) *
              (C.outcome a - D.outcome a))) := by
          exact Finset.sum_le_sum fun a _ =>
            ev_diff_triangle_three ψ (A.outcome a) (B.outcome a)
              (C.outcome a) (D.outcome a)
    _ = 3 * (∑ a, ev ψ (((A.outcome a - B.outcome a)ᴴ) *
          (A.outcome a - B.outcome a)) +
          ∑ a, ev ψ (((B.outcome a - C.outcome a)ᴴ) *
            (B.outcome a - C.outcome a)) +
          ∑ a, ev ψ (((C.outcome a - D.outcome a)ᴴ) *
            (C.outcome a - D.outcome a))) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Three-step triangle inequality for `SDDRel`, with the paper's `3` factor. -/
private lemma sddRel_triangle_three {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C D : IdxSubMeas Question Outcome ι) (δ₁ δ₂ δ₃ : Error) :
    SDDRel ψ 𝒟 A B δ₁ → SDDRel ψ 𝒟 B C δ₂ → SDDRel ψ 𝒟 C D δ₃ →
      SDDRel ψ 𝒟 A D (3 * (δ₁ + δ₂ + δ₃)) := by
  intro hAB hBC hCD
  constructor
  have hpoint : ∀ q, qSDD ψ (A q) (D q) ≤
      3 * (qSDD ψ (A q) (B q) + qSDD ψ (B q) (C q) +
        qSDD ψ (C q) (D q)) := by
    intro q
    exact qSDD_triangle_three ψ (A q) (B q) (C q) (D q)
  calc
    sddError ψ 𝒟 A D
        = avgOver 𝒟 (fun q => qSDD ψ (A q) (D q)) := rfl
    _ ≤ avgOver 𝒟 (fun q =>
          3 * (qSDD ψ (A q) (B q) + qSDD ψ (B q) (C q) +
            qSDD ψ (C q) (D q))) := by
          exact avgOver_mono 𝒟 _ _ hpoint
    _ = 3 * (sddError ψ 𝒟 A B + sddError ψ 𝒟 B C +
          sddError ψ 𝒟 C D) := by
          simp [sddError, avgOver_const_mul, avgOver_add, add_assoc]
    _ ≤ 3 * (δ₁ + δ₂ + δ₃) := by
          have hAB' := hAB.squaredDistanceBound
          have hBC' := hBC.squaredDistanceBound
          have hCD' := hCD.squaredDistanceBound
          nlinarith

set_option linter.unusedFintypeInType false in
/-- Residual handoff for the projectivization part of Step 6.

The fields are exactly the hypotheses needed after the orthonormalization and
completion constructions have produced projective measurements `Q_A,Q_B` close to
the pre-projective measurements `G_A,G_B`.  The theorem
`ProjectivizationLine156Handoff.line156Approx` below turns this package into the
paper's line-156 approximation. -/
structure ProjectivizationLine156Handoff
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
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

set_option linter.unusedFintypeInType false in
/-- Step 6 line-156 handoff.

From line-131 consistency `G_A ⊗ I ≃_{ζ₁} I ⊗ G_B`,
`prop:simeq-to-approx` gives `G_A ⊗ I ≈_{2ζ₁} I ⊗ G_B`.  Combining this with
the two completion closeness estimates by the **three-step** squared-distance
triangle gives

`Q_A ⊗ I ≈_{3(ζ₂ + 2ζ₁ + ζ₂)} I ⊗ Q_B`,

which is exactly the paper's `ζ₃ = 6ζ₁ + 6ζ₂`
(`inductive_step.tex:154--158`). -/
theorem line156Approx {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
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
  have htri := sddRel_triangle_three ψ (uniformDistribution Unit)
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
