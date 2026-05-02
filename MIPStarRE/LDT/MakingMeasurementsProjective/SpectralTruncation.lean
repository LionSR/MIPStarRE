import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.Core
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities
import MIPStarRE.LDT.Basic.MeasurementLift

/-!
# Section 5 — Spectral truncation and locality-preserving repair bridges

This file provides bridge structures and lemmas that name the still-unformalized
spectral-truncation and locality-preserving repair steps and their downstream
consumers (`SpectralTruncationInput`, `OrthonormalizationInput`).

## Gap summary

The following paper lemmas from Section 5 have not yet received Lean proofs:

1. **`lem:projective-non-measurement`** (spectral truncation):
   `∑_a ⟨ψ| A_a - A_a² |ψ⟩ ≤ 2ζ` → `∃ R, RoundingToProjectorsWitness ψ A ζ R`.

2. **`QXPLayerData` construction** from `QLayerData`:
   Building the `X`, `XHat` matrices with the identities `Xᴴ X = Q`,
   `XHat XHatᴴ = I`, and `Xᴴ XHat = √Q`.

Both are exposed as explicit structure fields below.

## What this file provides

- `ProjectiveNonMeasurementBridgeInput` — explicit hypotheses for spectral truncation
- `ProjectivizationRepairBridgeInput` — bundles the full chain inputs (caller supplies)
- `roundingToProjectorsWitness_of_bridge` — trivial wrapper
- `rankReductionWitness_of_bridge` — calls `projectiveLowRankSum`
- `spectralTruncationStatement_of_bridge` — field-for-field conversion to
  `SpectralTruncationStatement`
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
paper-compatible error bounds.

This structure is kept as a named landing point for future Lean proofs of
the truncation-function step. Once a constructive proof is available, the
downstream lemmas in this file will produce `SpectralTruncationInput`. -/
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

/-- Convenience: convert a bridge input to the internal witness structure. -/
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

/-! ### QXPLayer construction bridge

The paper's `Q/X/XHat/P` construction (from `QLayerData` to `QXPLayerData`)
requires explicit matrices `X` and `XHat` satisfying:
- `Xᴴ * X = Q` (right Gram)
- `XHat * XHatᴴ = I` (coisometry)
- `Xᴴ * XHat = √Q` (mixed product)

Building these from the `QLayerData` is currently unformalized.
The `qxpConstruction` field in `ProjectivizationRepairBridgeInput` names this
missing construction; the QXP data is returned as `QXPLayerData` tied to the
input `QLayerData` by a dependent equality. -/

/-! ### Projectivization repair bridge input

This structure bundles all the currently unformalized inputs needed to
produce a `LeftLiftedProjectivizationRepairInput` from the spectral truncation
and QXP construction steps.

Once both gaps are closed by constructive proofs, a conversion lemma will
produce the `LeftLiftedProjectivizationRepairInput` needed at the `mainFormal`
site. Until then, the caller supplies the output of these fields directly. -/

/-- Explicit bridge input for the full chain from almost-projectivity through
rank reduction and QXP construction to a left-lifted projective submeasurement.

The `qxpConstruction` field is a function from `QLayerData` × `RankReductionWitness`
to `QXPLayerData` (with a dependent equality tying `d.qLayer = data`).  This
ensures that the Q-layer produced by rank reduction is the same Q-layer consumed
by the QXP construction. -/
structure ProjectivizationRepairBridgeInput {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) where
  /-- The spectral truncation bridge input producing the rounded projectors `R_a`. -/
  spectralInput : ProjectiveNonMeasurementBridgeInput ψ A ζ
  /-- The source almost-projectivity bound, consumed by rank reduction. -/
  source_almost_projective :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ
  /-- The QXP construction function: given Q-layer data and a rank-reduction
  witness, produce `QXPLayerData` whose `qLayer` is exactly the input `data`.

  This field must be instantiated once the constructive QXP transition from
  `QLayerData` to `QXPLayerData` is formalized. -/
  qxpConstruction :
    (data : QLayerData Outcome ι) → RankReductionWitness ψ A ζ data →
      { d : QXPLayerData Outcome ι // d.qLayer = data }

/-! ### Conversion lemmas

The lemmas below connect the bridge inputs to the downstream types
`SpectralTruncationInput` and `LeftLiftedProjectivizationRepairInput`. -/

/-- Given the spectral truncation bridge input, we can directly build a
`RoundingToProjectorsWitness`. This is a trivial wrapper around the bridge
fields, but gives the downstream rank-reduction theorem the type it expects. -/
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
