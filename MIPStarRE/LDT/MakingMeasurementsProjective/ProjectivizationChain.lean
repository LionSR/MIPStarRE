import MIPStarRE.LDT.MakingMeasurementsProjective.Theorems

/-!
# Section 10 — Step 6 (orthonormalize-and-complete chain)

This file formalises **Step 6** of the eight-step pipeline used in the proof of
the main inductive step (`mainFormal`). In the paper, Step 6 is the
"projectivization chain" (`inductive_step.tex` lines 130–149) whose ultimate
goal is to produce projective measurements `Q^A`, `Q^B` close to `G^A`, `G^B`.
That chain has two substeps:

1. **Orthonormalization** (`thm:orthonormalization`, cross-referenced from
   Section 5).
2. **Completion to a measurement** (`prop:completing-to-measurement`).

followed by a separate promotion of the completed measurement to a
projective measurement (`\polymeas{m}{q}{d}`), needed for Step 7's
invocation of `prop:simeq-to-approx`.

This file formalises *only* the first two substeps — orthonormalization
followed by completion — which together yield measurements `Q^A`, `Q^B`
close to `G^A`, `G^B` in state-dependent distance. The subsequent promotion
of `Q` to a `ProjMeas` is tracked as an explicit follow-up (see the
`Note (Q-projective)` section below). The main theorem is therefore named
`orthonormalizeAndComplete` to accurately describe what is proven here,
while the module/file name retains the paper's `ProjectivizationChain`
terminology for the overall pipeline step.

The chain composes two existing pieces of infrastructure:

1. **Orthonormalization** (`MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization`,
   in `Theorems.lean`) — produces a projective sub-measurement
   `P : ProjSubMeas Outcome ι` close to `G` in state-dependent distance:
   `G_g ⊗ I ≈_{100·ζ^{1/4}} P_g ⊗ I`.

2. **Completion to a measurement**
   (`MIPStarRE.LDT.Preliminaries.completingToMeasurement`,
   in `Preliminaries/Theorems.lean`) — adjoins the missing mass `I − Σ_a P_a`
   at a distinguished outcome `a*` to produce a measurement `Q` with
   `G_g ⊗ I ≈_{2δ + 4√δ + 2ζ} Q_g ⊗ I` where `δ = 100·ζ^{1/4}`.

The composition gives the `ζ₂` of the paper (`inductive_step.tex`, line 149):

    ζ₂ = 2 · (100·ζ^{1/4}) + 4 · √(100·ζ^{1/4}) + 2·ζ
       = 200·ζ^{1/4} + 40·ζ^{1/8} + 2·ζ.

The paper drops the `2·ζ` term in the closed-form `ζ₂ = 200·ζ^{1/4} + 40·ζ^{1/8}`
(it is absorbed when the global error is computed downstream); we keep the
literal output of the two lemmas for proof integrity, and leave the tighter
absorbed form as a downstream calculation.

## Status

- The orthonormalization step is mediated by
  `OrthonormalizationBridgePackage`, isolating the still-unformalized linear
  algebra (cf. `MakingMeasurementsProjective/Statements.lean`).
- The completion step uses the **fully-formalized** `completingToMeasurement`
  (`\leanok` in `blueprint/src/chapter/ch03_preliminaries.tex`), so no new
  bridge is introduced here.
- The output `Q` is a `Measurement`, not a `ProjMeas`. Promoting `Q` to a
  projective measurement requires pairwise orthogonality of the
  underlying projective sub-measurement `P`; this is recorded as
  `Note (Q-projective)` below and tracked separately (the paper uses the
  fact only to invoke `prop:simeq-to-approx`, not for the closeness bound
  proven here).

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
open MIPStarRE.LDT.Preliminaries (completingToMeasurement completeAtOutcome)

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

/-! ### Output package -/

set_option linter.unusedFintypeInType false in
/-- Output package for the orthonormalization + completion chain (Step 6 of
the inductive step).

The chain takes a measurement `A : Measurement Outcome ι` together with a
`ζ`-bipartite-self-consistency hypothesis on `A.toSubMeas`, and produces:

* an intermediate projective sub-measurement `P : ProjSubMeas Outcome ι`
  satisfying the orthonormalization closeness `A ≈_{100·ζ^{1/4}} P` (paper
  `orthonormalization.tex` line 67);
* a completed measurement `Q : Measurement Outcome ι` obtained by
  adjoining the residual `I − Σ_a P_a` at a distinguished outcome `a₀`,
  satisfying the chain closeness
  `A ≈_{orthonormalizeAndCompleteError ζ} Q` (paper `inductive_step.tex`
  line 146, `eq:G-with-Q-A`).

The `completionFormula` field exposes the canonical structural form of the
completion (cf. `Preliminaries.completeAtOutcome`).

## Note (Q-projective)

For the downstream paper argument
(`prop:simeq-to-approx` after `eq:third-goal`), the completed measurement `Q`
must additionally be a *projective* measurement. Promoting `Q` to `ProjMeas`
requires pairwise orthogonality of `P` (each `P_a · P_b = 0` for `a ≠ b`),
which holds because `Σ_a P_a ≤ 1` and each `P_a` is a projection. This step
is intentionally separated from the closeness statement here and tracked as
a follow-up. -/
structure OrthonormalizeAndCompleteStatement
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : Measurement Outcome ι)
    (P : ProjSubMeas Outcome ι)
    (Q : Measurement Outcome ι)
    (a0 : Outcome) (ζ : Error) : Prop where
  /-- The orthonormalization closeness statement
  `A ≈_{orthonormalizationError ζ} P` (paper:
  `orthonormalization.tex` line 67, post-lifting to the bipartite space). -/
  orthonormalizationCloseness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily P.toSubMeas.liftLeft)
      (orthonormalizationError ζ)
  /-- `Q` is the canonical completion of `P` at the distinguished outcome
  `a₀` (`Preliminaries.completeAtOutcome`). -/
  completionFormula :
    Q = completeAtOutcome P.toSubMeas a0
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
* the orthonormalization bridge package isolating the still-unformalized
  linear-algebra step inside `thm:orthonormalization`,

we obtain a projective sub-measurement `P` together with a measurement `Q`
satisfying the chain bound `A ≈_{orthonormalizeAndCompleteError ζ} Q` from
`inductive_step.tex` line 146 (`eq:G-with-Q-A`).

Note that `Q` is delivered as a `Measurement`, not a `ProjMeas`; the
promotion to a projective measurement required for Step 7 is deferred (see
`Note (Q-projective)` on `OrthonormalizeAndCompleteStatement`).

The proof is a direct composition of the two existing lemmas:
* `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization`
  (Step 6a; `orthonormalization.tex` line 67);
* `MIPStarRE.LDT.Preliminaries.completingToMeasurement`
  (Step 6b; `preliminaries.tex` line 1101).

The error `orthonormalizeAndCompleteError ζ` is *definitionally equal* to
`2 · orthonormalizationError ζ + 4 · √(orthonormalizationError ζ) + 2·ζ`,
which matches the closeness conclusion of `completingToMeasurement` after
substituting `δ := orthonormalizationError ζ`. -/
theorem orthonormalizeAndComplete
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (hperm : PermInvState ψ)
    (A : Measurement Outcome ι) (a0 : Outcome) (ζ : Error)
    (hssc :
      BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ)
    (hbridge : OrthonormalizationBridgePackage ψ A.toSubMeas ζ) :
    ∃ P : ProjSubMeas Outcome ι, ∃ Q : Measurement Outcome ι,
      OrthonormalizeAndCompleteStatement ψ A P Q a0 ζ := by
  -- Step 6a: apply orthonormalization to A.toSubMeas.
  obtain ⟨P, hClose⟩ :=
    orthonormalization (Outcome := Outcome) (ι := ι) ψ hψ hperm
      A.toSubMeas ζ hssc hbridge
  -- Step 6b: complete P to a measurement Q via completeAtOutcome at a0.
  obtain ⟨Q, hQstmt⟩ :=
    completingToMeasurement (Outcome := Outcome) (ι := ι) ψ hperm hψ
      A P.toSubMeas a0 (orthonormalizationError ζ) ζ hssc hClose
  refine ⟨P, Q, ?_⟩
  refine
    { orthonormalizationCloseness := hClose
      completionFormula := hQstmt.completionFormula
      completedCloseness := ?_ }
  -- The closeness from completingToMeasurement is
  -- `SDDRel ψ … (2·δ + 4·√δ + 2·ζ)` with `δ := orthonormalizationError ζ`,
  -- which is exactly `orthonormalizeAndCompleteError ζ` by definition.
  exact hQstmt.closenessAfterCompletion

end MIPStarRE.LDT.MakingMeasurementsProjective
