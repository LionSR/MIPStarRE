import MIPStarRE.LDT.MakingMeasurementsProjective.Statements

/-!
# Section 5 — Sorry'd producers for the orthonormalization analytic core

Per the live `*Statement` ledger #1379 ("preferred pattern: sorry'd producers
over extra-hypotheses"), this file exposes the analytic obligations of the
Chapter 4 orthonormalization argument as named theorems with `sorry`. The
purpose is to make the proof frontier visible to `rg sorry`: anyone scanning
the codebase for outstanding obligations finds these stubs and their
paper-origin docstrings, instead of having to trace the extra-hypothesis chain
through `mainFormal`.

The two obligations packaged here are:

1. **`spectralTruncationProducer`** — paper origin
   `references/ldt-paper/orthonormalization.tex` lines 414–446
   (`\label{lem:projective-non-measurement}` together with the supporting
   technical inequality `\label{lem:trunc-inequality}` at lines 447–500). This
   produces the truncated family `R = {R_a}`, projectivity, the closeness
   bound `≈_{2√ζ}`, the sum-equals-total field, and the
   `R ≤ (1+2√ζ) · I` total bound from a normalized state and the
   almost-projector hypothesis on `A`.

2. **`leftLiftedProjectivizationRepairProducer`** — paper origin
   `references/ldt-paper/orthonormalization.tex` lines 534–740 (the late
   repair stage of the orthogonalization-lemma proof, which produces a
   genuine projective sub-measurement from a rounded family while preserving
   the left-lifted product form `P_a ⊗ I`).

Both are tracked by **#1032** ("Formalize spectral-truncation and
locality-preserving repair lemmas"). Once their proofs are filled in, the
extra-hypothesis chain through `OrthonormalizationInput`,
`SpectralTruncationInput`, and `LeftLiftedProjectivizationRepairInput` can be
collapsed by replacing those caller-side hypotheses with calls to these
producers — the consumer-rewire phase of #1379's migration plan.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

/-- Producer for `SpectralTruncationStatement`.

Tracks **#1032**. Paper origin: `references/ldt-paper/orthonormalization.tex`
lines 414–446 (`\label{lem:projective-non-measurement}`) together with the
supporting technical inequality `\label{lem:trunc-inequality}` at lines
447–500.

The paper's proof picks `0 < δ ≤ 1/2` and defines the truncation function
`trunc_δ : [0,1] → {0,1}` by `trunc_δ(x) = 1 ↔ x ≥ 1 - δ`. For each
outcome `a` it sets

```
R_a := trunc_δ(A_a)
     = ∑_i trunc_δ(λ_{a,i}) · |u_{a,i}⟩⟨u_{a,i}|
```

using the eigendecomposition of `A_a`. The technical lemma `trunc-inequality`
then gives `(x - trunc_δ(x))² ≤ (1/δ) · (x - x²)` for all `x ∈ [0,1]`, which
combined with the almost-projector hypothesis
`∑_a ⟨A_a - A_a²⟩ ≤ ζ` yields `≈_{2√ζ}` after optimizing `δ`. The total
bound `R ≤ (1+2√ζ) · I` follows from the same calculation.

The formal proof is the upstream analytic obligation tracked by #1032 and is
not yet discharged in Lean.

The companion `spectralTruncationInputDischarge` packages this producer in the
`SpectralTruncationInput` shape consumed by downstream callers.

Note: `SpectralTruncationStatement` is data-bearing (it carries the chosen
truncated family), so this is a `noncomputable def`, not a `theorem`. -/
noncomputable def spectralTruncationProducer
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (_hψ : ψ.IsNormalized)
    (_hbound : ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ) :
    SpectralTruncationStatement ψ A ζ := by
  sorry

/-- Discharged form of `SpectralTruncationInput` produced by
`spectralTruncationProducer`. Consumers that currently take a
`SpectralTruncationInput` extra hypothesis can be rewired to call this
directly once the consumer-rewire phase of #1379's migration plan lands. -/
noncomputable def spectralTruncationInputDischarge
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    SpectralTruncationInput ψ A ζ :=
  fun hψ hbound => spectralTruncationProducer ψ A ζ hψ hbound

/-- Producer for `LeftLiftedProjectivizationRepairInput`.

Tracks **#1032**. Paper origin: `references/ldt-paper/orthonormalization.tex`
lines 534–740 (the late repair stage of the orthogonalization-lemma proof).

The paper's proof transports the rounded family produced by
`lem:projective-non-measurement` through the `Q/X/X̂/P` algebra (now formalized
as `QXPLayerData` and the rectangular polar decomposition for the sigma-range
embedding, PR #1237 / closed #1117 / closed #1228) to a genuine projective
sub-measurement `P = {P_a}` with closeness
`A_a ⊗ I ≈_{roundingToProjectiveError ζ} P_a ⊗ I`. The locality-preserving
form (output `P_a ⊗ I` rather than an arbitrary lifted family) is the
specialization needed by `orthonormalizationMainLemma` and thereby by
`mainFormal`'s base-case bridge.

The formal proof is the locality-preserving-repair half of #1032 and is not
yet discharged in Lean.

The companion `leftLiftedProjectivizationRepairInputDischarge` packages this
producer in the `LeftLiftedProjectivizationRepairInput` shape consumed by
downstream callers. -/
theorem leftLiftedProjectivizationRepairProducer
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : Measurement Outcome ι) (ζ : Error)
    (_hSpectral :
      SpectralTruncationStatement ψ (leftLiftedMeasurement (ιB := ι) A) ζ) :
    ∃ P : ProjSubMeas Outcome ι,
      RoundedProjMeasStatement ψ (leftLiftedMeasurement (ιB := ι) A)
        (ProjSubMeas.liftLeft P) (roundingToProjectiveError ζ) := by
  sorry

/-- Discharged form of `LeftLiftedProjectivizationRepairInput` produced by
`leftLiftedProjectivizationRepairProducer`. -/
def leftLiftedProjectivizationRepairInputDischarge
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : Measurement Outcome ι) (ζ : Error) :
    LeftLiftedProjectivizationRepairInput ψ A ζ :=
  fun hSpectral => leftLiftedProjectivizationRepairProducer ψ A ζ hSpectral

end MIPStarRE.LDT.MakingMeasurementsProjective
