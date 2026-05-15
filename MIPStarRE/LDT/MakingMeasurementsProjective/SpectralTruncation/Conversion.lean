import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction

/-!
# Spectral Truncation Interface Conversions

This file contains the structural conversions from the paper witness
`projectiveNonMeasurement` and the rounded-projector witness used by the QXP
rank-reduction layer to the `SpectralTruncationStatement` and
`SpectralTruncationInput` interfaces used by orthonormalization.

The conversions are field-for-field copies.  The constructive spectral
truncation theorem, which produces such a rounded projective family from the
paper's almost-projective hypothesis, is proved in the sibling proof-layer
module `SpectralTruncation.ProjectiveNonMeasurement`.
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
`RoundingToProjectorsWitness`. -/
noncomputable def spectralTruncationStatement_of_witness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (R : OpFamily Outcome ι)
    (hwitness : RoundingToProjectorsWitness ψ A ζ R) :
    SpectralTruncationStatement ψ A ζ :=
  ⟨R, hwitness.projective, hwitness.closeness, hwitness.sum_eq_total,
    hwitness.total_le⟩

namespace SpectralTruncationStatement

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-531`
(`\label{lem:projective-non-measurement}`; rounding-to-projectors lemma
with `2√ζ` closeness and `(1+2√ζ)·I` total bound).

Convert a spectral-truncation statement back to the rounded-projector
witness consumed by the QXP rank-reduction layer.

The conversion is structural.  It does not recover the source almost-projective
estimate, because that estimate is not a field of `SpectralTruncationStatement`;
rank-reduction constructors which need it therefore keep it as a separate
hypothesis. -/
noncomputable def toRoundingToProjectorsWitness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    (h : SpectralTruncationStatement ψ A ζ) :
    RoundingToProjectorsWitness ψ A ζ h.roundedFamily where
  projective := h.projective
  closeness := h.closeness
  sum_eq_total := h.sum_eq_total
  total_le := h.total_le

end SpectralTruncationStatement

/-! ### Rank-reduction from spectral truncation -/

/-- Feed a spectral-truncation statement into the QXP rank-reduction layer.

The statement `SpectralTruncationStatement` remembers the rounded projectors
and their distance from the source measurement.  The rank-reduction witness also
records the source almost-projectivity estimate, so that estimate remains an
explicit hypothesis here.  This is the precise interface needed when the
orthonormalization spectral input is followed by the paper's
`Q -> X -> Xhat -> P` repair layer. -/
lemma projectiveLowRankSum_of_spectralTruncationStatement
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1 / 4)
    (hSpectral : SpectralTruncationStatement ψ A ζ)
    (hsource :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data :=
  projectiveLowRankSum_of_roundingWitness ψ A ζ hψ hζ hζ_le hSpectral.roundedFamily
    hSpectral.toRoundingToProjectorsWitness hsource

/-- Feed a spectral-truncation input directly into the QXP rank-reduction
layer.

This is the constructor form most useful to downstream orthonormalization
callers: the spectral input supplies the rounded projectors from the normalized
state and source defect, and the same defect is then enlarged from `ζ` to
`2ζ` for the rank-reduction witness. -/
lemma projectiveLowRankSum_of_spectralTruncationInput
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1 / 4)
    (hspectral : SpectralTruncationInput ψ A ζ)
    (hsource :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  have hsource_two :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ := by
    linarith
  exact projectiveLowRankSum_of_spectralTruncationStatement ψ A ζ hψ hζ hζ_le
    (hspectral hψ hsource) hsource_two

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
