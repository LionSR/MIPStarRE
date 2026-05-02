import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.Core
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities
import MIPStarRE.LDT.Basic.MeasurementLift

/-!
# Section 5 — Spectral truncation bridge

This file provides a bridge structure and conversion lemmas for the
still-unformalized spectral-truncation step of `lem:projective-non-measurement`.

## Gap summary

The following paper lemma from Section 5 has not yet received a Lean proof:

- **`lem:projective-non-measurement`** (spectral truncation):
  `∑_a ⟨ψ| A_a - A_a² |ψ⟩ ≤ 2ζ` → `∃ R, RoundingToProjectorsWitness ψ A ζ R`.

The bridge structure `ProjectiveNonMeasurementBridgeInput` names the
rounded family and its paper-compatible error bounds so that callers can
supply a constructive witness once one is available.

## What this file provides

- `ProjectiveNonMeasurementBridgeInput` — explicit hypotheses for spectral truncation
- `roundingToProjectorsWitness_of_bridge` — convert to `RoundingToProjectorsWitness`
- `rankReductionWitness_of_bridge` — calls `projectiveLowRankSum`
- `spectralTruncationStatement_of_bridge` — convert to `SpectralTruncationStatement`
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

/-! ### Spectral truncation bridge input

These hypotheses name the still-unformalized content of
`lem:projective-non-measurement`: given an almost-projective measurement
(whose total idempotence defect is controlled) and the standard small-error
and normalization hypotheses, a rounded family of projectors `R_a` can be
constructed with controlled `SDDOpRel` and total-mass bounds. -/

/-- Explicit bridge input for the spectral truncation lemma
`lem:projective-non-measurement`.

Given `ψ` normalized, `0 ≤ ζ ≤ 1/4`, and the almost-projectivity bound
`∑_a ev ψ (A_a - A_a²) ≤ 2ζ`, produce a rounded projective family with
paper-compatible error bounds (closeness `2√ζ`, total bound `1 + 2√ζ`).

This structure is a named landing point for future Lean proofs of the
truncation-function step.  It is a structural sigma form of
`RoundingToProjectorsWitness`, kept as a separate declaration so that
callers can construct it directly from an unformalized `lem:projective-non-measurement`
witness without going through the internal rank-reduction layer.

Issue: #1032. -/
structure ProjectiveNonMeasurementBridgeInput {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) : Type (max 1 uOutcome uι) where
  /-- The rounded projective family `R_a`. -/
  roundedFamily : OpFamily Outcome ι
  /-- Each `R_a` is a projection. -/
  projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (roundedFamily.outcome a)
  /-- Closeness in state-dependent operator distance: `A_a ≈_{2√ζ} R_a`. -/
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily roundedFamily)
      (2 * spectralTruncationError ζ)
  /-- The total operator is the sum of the rounded family. -/
  sum_eq_total : ∑ a, roundedFamily.outcome a = roundedFamily.total
  /-- The total operator is bounded by `(1 + 2√ζ) · I`. -/
  total_le :
    roundedFamily.total ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)

/-- Convert the bridge input to `RoundingToProjectorsWitness`, the witness type
consumed by `projectiveLowRankSum`.  This is a structural copy: the bridge
carries the same fields as the downstream witness. -/
def toRoundingToProjectorsWitness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    (input : ProjectiveNonMeasurementBridgeInput ψ A ζ) :
    RoundingToProjectorsWitness ψ A ζ input.roundedFamily where
  projective := input.projective
  closeness := input.closeness
  sum_eq_total := input.sum_eq_total
  total_le := input.total_le

/-! ### Conversion lemmas

The lemmas below connect the bridge input to the downstream
`RoundingToProjectorsWitness` (for rank reduction) and
`SpectralTruncationStatement` (for the orthonormalization pipeline). -/

/-- Given the spectral truncation bridge input, produce a
`RoundingToProjectorsWitness` for consumption by `projectiveLowRankSum`. -/
lemma roundingToProjectorsWitness_of_bridge {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (input : ProjectiveNonMeasurementBridgeInput ψ A ζ) :
    RoundingToProjectorsWitness ψ A ζ input.roundedFamily :=
  toRoundingToProjectorsWitness input

/-- Given the spectral truncation bridge input, the small-error hypotheses,
and the source almost-projectivity, produce the paper's Q-layer data
`QLayerData` and the rank-reduction witness `RankReductionWitness`.

This def calls `projectiveLowRankSum` from `QXPLayer/RankReduction.lean`
with the rounded projectors from the bridge input. -/
lemma rankReductionWitness_of_bridge {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized)
    (hζ_nonneg : 0 ≤ ζ)
    (hζ_le : ζ ≤ 1 / (4 : Error))
    (input : ProjectiveNonMeasurementBridgeInput ψ A ζ)
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data :=
  projectiveLowRankSum ψ A ζ hψ hζ_nonneg hζ_le
    input.roundedFamily
    (toRoundingToProjectorsWitness input)
    source_almost_projective

/-- Given the spectral truncation bridge input, produce a
`SpectralTruncationStatement` at error `ζ`.

This is a structural field-for-field conversion: the bridge already
carries the same fields as `SpectralTruncationStatement` (after
`SpectralTruncationStatement.closeness` was weakened to `2√ζ` to match
the paper's bound at `references/ldt-paper/orthonormalization.tex:417`).

The mathematical content of `lem:projective-non-measurement` — constructing
the rounded family — is the caller's responsibility when building a
`ProjectiveNonMeasurementBridgeInput`. See #1032 for the constructive
proof track. -/
noncomputable def spectralTruncationStatement_of_bridge {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (input : ProjectiveNonMeasurementBridgeInput ψ A ζ) :
    SpectralTruncationStatement ψ A ζ where
  roundedFamily := input.roundedFamily
  projective := input.projective
  closeness := input.closeness
  sum_eq_total := input.sum_eq_total
  total_le := input.total_le

end MIPStarRE.LDT.MakingMeasurementsProjective
