import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction

/-!
# Section 5 — Spectral truncation statement conversion

This file provides a structural conversion from `RoundingToProjectorsWitness`
(the witness type consumed by `projectiveLowRankSum`) to
`SpectralTruncationStatement` (for the orthonormalization pipeline).

The two types are field-for-field identical after
`SpectralTruncationStatement.closeness` was weakened to `2√ζ` to match
the paper's bound at `references/ldt-paper/orthonormalization.tex:417`.

## What this file provides

- `spectralTruncationStatement_of_witness` — field-for-field conversion
  from `RoundingToProjectorsWitness` to `SpectralTruncationStatement`
- `spectralTruncationInput_of_projectiveNonMeasurement` — noncomputable
  conversion from the named paper witness `projectiveNonMeasurement` to the
  `SpectralTruncationInput` interface consumed by orthonormalization

## References

- `references/ldt-paper/orthonormalization.tex` (lines 420–550)
- Blueprint: Chapter 4 (`blueprint/src/chapter/ch04_projective.tex`)
- Issues: #1032 (tracking), #422 (mainFormal), #834 (Step 6)
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

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

/-! ### Spectral input from the named paper witness -/

/-- Build `SpectralTruncationInput` from the named
`lem:projective-non-measurement` witness.

The paper's spectral truncation step is represented in the QXP layer by
`projectiveNonMeasurement`, which is a proposition asserting the existence of a
rounded projective family with the same bounds as `SpectralTruncationStatement`.
The `SpectralTruncationInput` interface is data-valued, so this conversion uses
choice to extract the rounded family and then applies
`spectralTruncationStatement_of_witness`.

This does not prove `lem:projective-non-measurement`; it moves the remaining
constructive obligation to that named paper statement instead of the raw
`SpectralTruncationInput` shape. -/
noncomputable def spectralTruncationInput_of_projectiveNonMeasurement
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hprojective : projectiveNonMeasurement ψ A ζ) :
    SpectralTruncationInput ψ A ζ :=
  fun _hψ _halmostProjective =>
    let R : OpFamily Outcome ι := Classical.choose hprojective
    let hR : RoundingToProjectorsWitness ψ A ζ R :=
      Classical.choose_spec hprojective
    spectralTruncationStatement_of_witness ψ A ζ R hR

end MIPStarRE.LDT.MakingMeasurementsProjective
