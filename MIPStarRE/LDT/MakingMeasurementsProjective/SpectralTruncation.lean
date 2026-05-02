import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.Core
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities
import MIPStarRE.LDT.Basic.MeasurementLift

/-!
# Section 5 — Spectral truncation conversion lemmas

This file provides conversion lemmas from `RoundingToProjectorsWitness`
(the witness type consumed by `projectiveLowRankSum`) to the downstream
types `RankReductionWitness` (via `projectiveLowRankSum`) and
`SpectralTruncationStatement` (for the orthonormalization pipeline).

## Gap summary

The following paper lemma from Section 5 has not yet received a Lean proof:

- **`lem:projective-non-measurement`** (spectral truncation):
  `∑_a ⟨ψ| A_a - A_a² |ψ⟩ ≤ 2ζ` → `∃ R, RoundingToProjectorsWitness ψ A ζ R`.

Once a constructive proof is available, callers will supply a
`RoundingToProjectorsWitness` directly, at which point the lemmas below
provide the bridge to the rank-reduction and orthonormalization layers.

## What this file provides

- `rankReductionWitness_of_bridge` — pass a `RoundingToProjectorsWitness` to
  `projectiveLowRankSum`, obtaining `QLayerData` and `RankReductionWitness`
- `spectralTruncationStatement_of_bridge` — convert a `RoundingToProjectorsWitness`
  to a `SpectralTruncationStatement`
  (requires the closeness bound weakened to `2√ζ` per paper; see #1032)

## References

- `references/ldt-paper/orthonormalization.tex` (lines 420–550 for spectral truncation,
  lines 559–878 for rank reduction and QXP)
- Blueprint: Chapter 4 (`blueprint/src/chapter/ch04_projective.tex`)
- Issues: #1032 (tracking), #422 (mainFormal), #834 (Step 6)
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

/-! ### Rank reduction bridge

Given a `RoundingToProjectorsWitness` (the output of the still-unformalized
`lem:projective-non-measurement`), call `projectiveLowRankSum` to produce
`QLayerData` and `RankReductionWitness`. -/

/-- Given a `RoundingToProjectorsWitness`, the small-error hypotheses,
and the source almost-projectivity, produce the paper's Q-layer data
`QLayerData` and the rank-reduction witness `RankReductionWitness`.

This def calls `projectiveLowRankSum` from `QXPLayer/RankReduction.lean`. -/
lemma rankReductionWitness_of_witness {Outcome : Type uOutcome}
    [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized)
    (hζ_nonneg : 0 ≤ ζ)
    (hζ_le : ζ ≤ 1 / (4 : Error))
    (R : OpFamily Outcome ι)
    (hwitness : RoundingToProjectorsWitness ψ A ζ R)
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data :=
  projectiveLowRankSum ψ A ζ hψ hζ_nonneg hζ_le R hwitness
    source_almost_projective

/-! ### Spectral truncation statement conversion

Convert a `RoundingToProjectorsWitness` to a `SpectralTruncationStatement`.
The two types are field-for-field identical after `SpectralTruncationStatement.closeness`
was weakened to `2√ζ`. -/

/-- Convert a `RoundingToProjectorsWitness` to a `SpectralTruncationStatement`.

This is a structural field-for-field copy: both types carry the same data
(rounded family, projectivity, `2√ζ` closeness, total bound `1 + 2√ζ`).

The mathematical content of `lem:projective-non-measurement` — constructing
the rounded family — is the caller's responsibility when building a
`RoundingToProjectorsWitness`. See #1032 for the constructive proof track. -/
noncomputable def spectralTruncationStatement_of_witness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (R : OpFamily Outcome ι)
    (hwitness : RoundingToProjectorsWitness ψ A ζ R) :
    SpectralTruncationStatement ψ A ζ :=
  ⟨R, hwitness.projective, hwitness.closeness, hwitness.sum_eq_total,
    hwitness.total_le⟩

end MIPStarRE.LDT.MakingMeasurementsProjective
